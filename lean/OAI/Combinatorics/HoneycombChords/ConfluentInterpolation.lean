import OAI.Combinatorics.HoneycombChords.LaurentTransfer
import OAI.Combinatorics.HoneycombChords.InterpolationDefinitions
import OAI.Combinatorics.HoneycombChords.ConfluentZeros

namespace OAI

/-! Confluent spectral zeros and physical rational interpolation.

This development follows the finite strip transfer calculation for critical honeycomb
walks in the companion paper on uniform marked polygon estimates. -/

section
open scoped ContDiff Matrix.Norms.Elementwise
namespace CriticalHoneycomb.Transfer.Reflection
@[fun_prop] lemma contDiff_sine (m : ℕ∞ω) : ContDiff ℝ m sine := by
  unfold sine
  exact Complex.ofRealCLM.contDiff.comp Real.contDiff_sin
lemma contDiff_Q (m : ℕ∞ω) : ContDiff ℝ m Q := by
  unfold Q
  exact ((contDiff_sine m).comp (contDiff_const.add contDiff_id)).mul
    ((contDiff_sine m).comp (contDiff_const.add contDiff_id))
lemma contDiff_bulkNumerator (m : ℕ∞ω) : ContDiff ℝ m bulkNumerator := by
  apply contDiff_pi.2; intro p
  apply contDiff_pi.2; intro q
  unfold bulkNumerator
  split <;> (try simp only [coeffA,coeffH,coeffV,coeffC,coeffD,Q,S]) <;> fun_prop
lemma contDiffAt_spectralR (m : ℕ∞ω) (u : ℝ) (hu : Q u≠0) :
    ContDiffAt ℝ m spectralR u := by
  exact ((contDiff_Q m).contDiffAt.inv hu).smul (contDiff_bulkNumerator m).contDiffAt
lemma contDiffAt_boundary0 (m : ℕ∞ω) (t : ℝ) (ht : sine (gamma+t)≠0) :
    ContDiffAt ℝ m boundary0 t := by
  apply contDiffAt_pi.2; intro p
  apply contDiffAt_pi.2; intro q
  unfold boundary0
  split_ifs
  · exact contDiffAt_const
  · simpa only [div_eq_mul_inv,Function.comp_apply,id_eq,Pi.inv_apply] using
      (((contDiff_sine m).comp (contDiff_const.sub contDiff_id)).contDiffAt).mul
        ((((contDiff_sine m).comp (contDiff_const.add contDiff_id)).contDiffAt).inv ht)
  · exact contDiffAt_const
lemma contDiffAt_boundary1 (m : ℕ∞ω) (t : ℝ) (ht : sine (gamma+t)≠0) :
    ContDiffAt ℝ m boundary1 t := by
  have h : ContDiffAt ℝ m (fun u => sine (2*u)/sine (gamma+u)) t :=
    by simpa only [div_eq_mul_inv,Function.comp_apply,id_eq,Pi.inv_apply] using
      (((contDiff_sine m).comp (contDiff_const.mul contDiff_id)).contDiffAt).mul
        ((((contDiff_sine m).comp (contDiff_const.add contDiff_id)).contDiffAt).inv ht)
  apply contDiffAt_pi.2; intro p
  apply contDiffAt_pi.2; intro q
  unfold boundary1
  split_ifs
  · exact h
  · exact contDiffAt_const.mul h
  · exact contDiffAt_const
end CriticalHoneycomb.Transfer.Reflection
namespace CriticalHoneycomb.Transfer.RowExchange
open Reflection
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma contDiffAt_matrix_entry {a c k : Type*} [Fintype a] [Fintype c]
    [NormedAddCommGroup k] [NormedSpace ℝ k]
    {m : ℕ∞ω} {f : E→Matrix a c k} {u : E} (h : ContDiffAt ℝ m f u) (i : a) (j : c) :
    ContDiffAt ℝ m (fun x=>f x i j) u := contDiffAt_pi.1 (contDiffAt_pi.1 h i) j
lemma contDiffAt_row (m : ℕ∞ω) (n : ℕ) (A : E→Fin n→Local) (u : E)
    (hA : ∀ i,ContDiffAt ℝ m (fun x=>A x i) u) (s t : Space n) :
    ContDiffAt ℝ m (fun x=>row n (A x) s t) u := by
  induction n with
  | zero => exact contDiffAt_const
  | succ n ih =>
    apply contDiffAt_pi.2; intro i
    apply contDiffAt_pi.2; intro j
    change ContDiffAt ℝ m (fun x=>∑ k,block (A x 0) (s 0) (t 0) i k*
      row n (Fin.tail (A x)) (Fin.tail s) (Fin.tail t) k j) u
    apply ContDiffAt.sum
    intro k hk
    exact (contDiffAt_matrix_entry (hA 0) (i,s 0) (k,t 0)).mul
      (contDiffAt_matrix_entry (ih (fun x=>Fin.tail (A x)) (fun i=>hA i.succ) _ _) k j)
end CriticalHoneycomb.Transfer.RowExchange

end

section
open scoped ContDiff
namespace CriticalHoneycomb.BoundaryJet
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
@[simp] lemma base_sub (a b : Jet) : base (a-b)=base a-base b := rfl
@[simp] lemma left_sub (a b : Jet) : left (a-b)=left a-left b := rfl
@[simp] lemma right_sub (a b : Jet) : right (a-b)=right a-right b := rfl
@[simp] lemma both_sub (a b : Jet) : both (a-b)=both a-both b := rfl

def SmoothJetAt (m : ℕ∞ω) (f : E→Jet) (x : E) : Prop :=
  ContDiffAt ℝ m (fun y=>base (f y)) x ∧
  ContDiffAt ℝ m (fun y=>left (f y)) x ∧
  ContDiffAt ℝ m (fun y=>right (f y)) x ∧
  ContDiffAt ℝ m (fun y=>both (f y)) x
lemma SmoothJetAt.const (m : ℕ∞ω) (a : Jet) (x : E) : SmoothJetAt m (fun _=>a) x :=
  ⟨contDiffAt_const,contDiffAt_const,contDiffAt_const,contDiffAt_const⟩
lemma SmoothJetAt.add {m : ℕ∞ω} {f g : E→Jet} {x : E}
    (hf : SmoothJetAt m f x) (hg : SmoothJetAt m g x) :
    SmoothJetAt m (fun y=>f y+g y) x := by
  refine ⟨?_,?_,?_,?_⟩ <;> simp only [base_add,left_add,right_add,both_add]
  · exact hf.1.add hg.1
  · exact hf.2.1.add hg.2.1
  · exact hf.2.2.1.add hg.2.2.1
  · exact hf.2.2.2.add hg.2.2.2
lemma SmoothJetAt.sub {m : ℕ∞ω} {f g : E→Jet} {x : E}
    (hf : SmoothJetAt m f x) (hg : SmoothJetAt m g x) :
    SmoothJetAt m (fun y=>f y-g y) x := by
  refine ⟨?_,?_,?_,?_⟩ <;> simp only [base_sub,left_sub,right_sub,both_sub]
  · exact hf.1.sub hg.1
  · exact hf.2.1.sub hg.2.1
  · exact hf.2.2.1.sub hg.2.2.1
  · exact hf.2.2.2.sub hg.2.2.2
lemma SmoothJetAt.mul {m : ℕ∞ω} {f g : E→Jet} {x : E}
    (hf : SmoothJetAt m f x) (hg : SmoothJetAt m g x) :
    SmoothJetAt m (fun y=>(f y*g y : Jet)) x := by
  refine ⟨?_,?_,?_,?_⟩ <;> simp only [base_mul,left_mul,right_mul,both_mul]
  · exact hf.1.mul hg.1
  · exact (hf.1.mul hg.2.1).add (hf.2.1.mul hg.1)
  · exact (hf.1.mul hg.2.2.1).add (hf.2.2.1.mul hg.1)
  · exact (((hf.1.mul hg.2.2.2).add (hf.2.1.mul hg.2.2.1)).add
      (hf.2.2.1.mul hg.2.1)).add (hf.2.2.2.mul hg.1)
lemma SmoothJetAt.sum {ι : Type*} (s : Finset ι) {m : ℕ∞ω} {f : ι→E→Jet} {x : E}
    (hf : ∀ i∈s,SmoothJetAt m (f i) x) : SmoothJetAt m (fun y=>∑ i∈s,f i y) x := by
  refine ⟨?_,?_,?_,?_⟩ <;> simp only [base_sum,left_sum,right_sum,both_sum]
  · exact ContDiffAt.sum (fun i hi=>(hf i hi).1)
  · exact ContDiffAt.sum (fun i hi=>(hf i hi).2.1)
  · exact ContDiffAt.sum (fun i hi=>(hf i hi).2.2.1)
  · exact ContDiffAt.sum (fun i hi=>(hf i hi).2.2.2)
lemma SmoothJetAt.C {m : ℕ∞ω} {f : E→ℂ} {x : E} (hf : ContDiffAt ℝ m f x) :
    SmoothJetAt m (fun y=>C (f y)) x := by
  exact ⟨by simpa only [base_C] using hf,by simpa only [left_C] using contDiffAt_const,
    by simpa only [right_C] using contDiffAt_const,by simpa only [both_C] using contDiffAt_const⟩
lemma SmoothJetAt.reflect {m : ℕ∞ω} {f : E→Jet} {x : E} (hf : SmoothJetAt m f x) :
    SmoothJetAt m (fun y=>reflectJet (f y)) x := by
  refine ⟨?_,?_,?_,?_⟩ <;>
    simp only [reflectJet_apply,reflected_base,reflected_left,reflected_right,reflected_both]
  · exact Complex.conjCLE.contDiff.contDiffAt.comp x hf.1
  · exact Complex.conjCLE.contDiff.contDiffAt.comp x hf.2.2.1
  · exact Complex.conjCLE.contDiff.contDiffAt.comp x hf.2.1
  · exact Complex.conjCLE.contDiff.contDiffAt.comp x hf.2.2.2
end CriticalHoneycomb.BoundaryJet

end

section
open scoped ContDiff Matrix.Norms.Elementwise
namespace CriticalHoneycomb.Transfer.SpectralFamily
open Reflection RowExchange BoundaryJet RasterGrid
open scoped Matrix BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma contDiffAt_row_curve (m : ℕ∞ω) (N : ℕ) (Ξ : E→Fin N→ℝ) (f : E→ℝ) (x : E)
    (hΞ : ∀ i,ContDiffAt ℝ m (fun y=>Ξ y i) x) (hf : ContDiffAt ℝ m f x)
    (hQ : ∀ i,Q (f x+Ξ x i)≠0) (s t : Space N) :
    ContDiffAt ℝ m (fun y=>row N (exactSites N (Ξ y) (f y)) s t) x := by
  apply contDiffAt_row
  intro i
  exact (contDiffAt_spectralR _ _ (hQ i)).comp x (hf.add (hΞ i))
lemma contDiffAt_bulkRows_curve (m : ℕ∞ω) (N : ℕ) (Ξ : E→Fin N→ℝ) (f : E→ℝ) (x : E)
    (hΞ : ∀ i,ContDiffAt ℝ m (fun y=>Ξ y i) x) (hf : ContDiffAt ℝ m f x)
    (hns : Nonsingular N (Ξ x) (f x)) (s t : Space N) :
    ContDiffAt ℝ m (fun y=>bulkRows N (Ξ y) (f y) s t) x := by
  apply contDiffAt_pi.2;intro p
  apply contDiffAt_pi.2;intro q
  unfold bulkRows forward
  simp only [Matrix.sum_apply]
  apply ContDiffAt.sum;intro v hv
  exact (contDiffAt_matrix_entry (contDiffAt_row_curve m N Ξ f x hΞ hf
    (fun i=>(hns.2.2 i).1) s v) p.1 q.1).mul
      (contDiffAt_matrix_entry (contDiffAt_row_curve m N Ξ (fun y=>b-f y) x hΞ
        (contDiffAt_const.sub hf) (fun i=>(hns.2.2 i).2) v t) p.2 q.2)
lemma smoothJetAt_K (m : ℕ∞ω) (e : Jet) (f : E→ℝ) (x : E)
    (hf : ContDiffAt ℝ m f x) (hu : sine (gamma+f x)≠0) (p : Pair) :
    SmoothJetAt m (fun y=>K e (f y) p) x := by
  have h0 : ContDiffAt ℝ m (fun y=>K0 (f y) p) x :=
    contDiffAt_const.mul ((contDiffAt_matrix_entry (contDiffAt_boundary0 m (f x) hu) p.1 p.2.rev).comp x hf)
  have h1 : ContDiffAt ℝ m (fun y=>K1 (f y) p) x :=
    contDiffAt_const.mul ((contDiffAt_matrix_entry (contDiffAt_boundary1 m (f x) hu) p.1 p.2.rev).comp x hf)
  exact SmoothJetAt.C h0 |>.add ((SmoothJetAt.const m e x).mul (SmoothJetAt.C h1))
lemma smoothJetAt_T_curve (m : ℕ∞ω) (N : ℕ) (Ξ : E→Fin N→ℝ) (f : E→ℝ) (x : E)
    (hΞ : ∀ i,ContDiffAt ℝ m (fun y=>Ξ y i) x) (hf : ContDiffAt ℝ m f x)
    (hns : Nonsingular N (Ξ x) (f x)) (s t : Space N) :
    SmoothJetAt m (fun y=>T N (Ξ y) (f y) s t) x := by
  unfold T
  apply SmoothJetAt.sum;intro p hp
  apply SmoothJetAt.sum;intro q hq
  exact ((smoothJetAt_K m eL (fun y=>b-f y) x (contDiffAt_const.sub hf) hns.2.1 p).mul
      (SmoothJetAt.C (contDiffAt_matrix_entry (contDiffAt_bulkRows_curve m N Ξ f x hΞ hf hns s t) p q))).mul
          (smoothJetAt_K m eR f x hf hns.1 q)
lemma smoothJetAt_reorient (m : ℕ∞ω) (n : ℕ)
    (M : E→Matrix (Space n) (Space n) Jet) (x : E)
    (hM : ∀ s t,SmoothJetAt m (fun y=>M y s t) x) (s t : Space n) :
    SmoothJetAt m (fun y=>reorient n (M y) s t) x :=
  (hM (reflectedSites n s) (reflectedSites n t)).reflect
lemma smoothJetAt_commonScalar (m : ℕ∞ω) (W : ℕ)
    (M : E→Matrix (Column (W+1)) (Column (W+1)) Jet) (x : E)
    (hM : ∀ s t,SmoothJetAt m (fun y=>M y s t) x) :
    SmoothJetAt m (fun y=>commonScalar W (M y)) x := by
  unfold commonScalar Matrix.mulVec dotProduct
  apply SmoothJetAt.sum;intro s hs
  apply SmoothJetAt.mul (SmoothJetAt.const _ _ _)
  apply SmoothJetAt.sum;intro t ht
  exact (hM s t).mul (SmoothJetAt.const _ _ _)
lemma smoothJetAt_matrix_mul {ι : Type*} [Fintype ι] (m : ℕ∞ω)
    (M N : E→Matrix ι ι Jet) (x : E)
    (hM : ∀ s t,SmoothJetAt m (fun y=>M y s t) x)
    (hN : ∀ s t,SmoothJetAt m (fun y=>N y s t) x) (s t : ι) :
    SmoothJetAt m (fun y=>(M y*N y) s t) x := by
  change SmoothJetAt m (fun y=>∑ z,(M y s z*N y z t : Jet)) x
  exact SmoothJetAt.sum Finset.univ (fun z _=>(hM s z).mul (hN z t))
end CriticalHoneycomb.Transfer.SpectralFamily

end

section

open scoped ContDiff Matrix.Norms.Elementwise
namespace CriticalHoneycomb.Transfer.SpectralFamily
open Reflection RowExchange BoundaryJet RasterGrid
open scoped Matrix BigOperators
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
noncomputable def fusionDefect (N : ℕ) (ξ : Fin N→ℝ) (u : ℝ) :
    Matrix (Space N) (Space N) Jet :=
  T N ξ (gamma+u-L)*T N ξ (gamma+u+L)-T N ξ (gamma+u)
def FusionRegular (N : ℕ) (ξ : Fin N→ℝ) (u : ℝ) : Prop :=
  Nonsingular N ξ (gamma+u-L) ∧ Nonsingular N ξ (gamma+u+L) ∧ Nonsingular N ξ (gamma+u)
noncomputable def physicalDefect (W : ℕ) (ξ : Fin (W+1)→ℝ) (u : ℝ) : ℂ :=
  both (commonScalar W (reorient (W+1) (fusionDefect (W+1) ξ u)))
lemma centered_T_reflect (N : ℕ) (ξ : Fin N→ℝ) (u : ℝ)
    (hu : Nonsingular N ξ (gamma+u)) :
    T N ξ (gamma-u)=T N ξ (gamma+u) := by
  have h : gamma-u=b-(gamma+u) := by simp only [gamma,b]; ring
  rw [h,←source_spectral_reflection N ξ (gamma+u) hu]
lemma fusionRegular_neg (N : ℕ) (ξ : Fin N→ℝ) (u : ℝ) (hu : FusionRegular N ξ u) :
    FusionRegular N ξ (-u) := by
  have h1 : gamma+-u-L=b-(gamma+u+L) := by simp only [gamma,b,L];ring
  have h2 : gamma+-u+L=b-(gamma+u-L) := by simp only [gamma,b,L];ring
  have h3 : gamma+-u=b-(gamma+u) := by simp only [gamma,b];ring
  exact ⟨by rw [h1];exact nonsingular_reflect _ _ _ hu.2.1,
    by rw [h2];exact nonsingular_reflect _ _ _ hu.1,
    by rw [h3];exact nonsingular_reflect _ _ _ hu.2.2⟩
lemma fusionDefect_reflect (N : ℕ) (ξ : Fin N→ℝ) (u : ℝ) (hu : FusionRegular N ξ u) :
    fusionDefect N ξ (-u)=fusionDefect N ξ u := by
  have hm : T N ξ (gamma+-u-L)=T N ξ (gamma+u+L) := by
    convert centered_T_reflect N ξ (u+L) (by convert hu.2.1 using 1 ; ring) using 1 <;> congr 1 <;> ring
  have hp : T N ξ (gamma+-u+L)=T N ξ (gamma+u-L) := by
    convert centered_T_reflect N ξ (u-L) (by convert hu.1 using 1 ; ring) using 1 <;> congr 1 <;> ring
  have hc : T N ξ (gamma+-u)=T N ξ (gamma+u) := by
    simpa only [sub_eq_add_neg] using centered_T_reflect N ξ u hu.2.2
  unfold fusionDefect
  rw [hm,hp,hc,(source_global_spectral_commutation N ξ _ _ hu.2.1 hu.1).eq]
lemma fusionDefect_node (N : ℕ) (ξ : Fin N→ℝ) (i : Fin N) (u : ℝ)
    (hn : u=L/2-ξ i ∨ u=L/2+ξ i) (hr : FusionRegular N ξ u) :
    fusionDefect N ξ u=0 := by
  have hn' : gamma+-u=L-ξ i ∨ gamma+-u=L+ξ i := by
    rcases hn with hn|hn
    · right;rw [hn];unfold gamma L;ring
    · left;rw [hn];unfold gamma L;ring
  have hr':=fusionRegular_neg N ξ u hr
  rw [←fusionDefect_reflect N ξ u hr,fusionDefect,
    source_global_spectral_fusion N ξ i (gamma+-u) hn' hr'.1 hr'.2.1 hr'.2.2,sub_self]
lemma physicalDefect_node (W : ℕ) (ξ : Fin (W+1)→ℝ) (i : Fin (W+1)) (u : ℝ)
    (hn : u=L/2-ξ i ∨ u=L/2+ξ i) (hr : FusionRegular (W+1) ξ u) :
    physicalDefect W ξ u=0 := by
  unfold physicalDefect
  rw [fusionDefect_node _ _ i u hn hr]
  simp [reorient,commonScalar,Matrix.mulVec,dotProduct,both]
lemma physicalDefect_reflect (W : ℕ) (ξ : Fin (W+1)→ℝ) (u : ℝ)
    (hr : FusionRegular (W+1) ξ u) : physicalDefect W ξ (-u)=physicalDefect W ξ u := by
  unfold physicalDefect
  rw [fusionDefect_reflect _ _ _ hr]
lemma reorient_sub (n : ℕ) (M N : Matrix (Space n) (Space n) Jet) :
    reorient n (M-N)=reorient n M-reorient n N := by
  funext s t
  exact map_sub reflectJet _ _
lemma commonScalar_sub (W : ℕ) (M N : Matrix (Column (W+1)) (Column (W+1)) Jet) :
    commonScalar W (M-N)=commonScalar W M-commonScalar W N := by
  unfold commonScalar
  rw [Matrix.sub_mulVec,dotProduct_sub]
lemma physicalDefect_homogeneous (W : ℕ) (u : ℝ)
    (hr : FusionRegular (W+1) (homogeneous (W+1)) u) :
    physicalDefect W (homogeneous (W+1)) u=physicalP W (u-L)+physicalP W (u+L)-physicalP W u := by
  unfold physicalDefect fusionDefect
  rw [reorient_sub,reorient_mul,commonScalar_sub]
  change both (commonScalar W (physicalFamily (W+1) (gamma+u-L)*physicalFamily (W+1) (gamma+u+L))-
    physicalScalar W (gamma+u))=_
  rw [commonScalar_mul_line W _ _ (physical_common_line W _ hr.2.1),both_sub]
  change both (physicalScalar W (gamma+u-L)*physicalScalar W (gamma+u+L))-both (physicalScalar W (gamma+u))=_
  rw [both_mul_normalized _ _ (physicalScalar_base W _ hr.1) (physicalScalar_base W _ hr.2.1)
      (physicalScalar_singles W _ hr.1).1 (physicalScalar_singles W _ hr.1).2]
  simp only [physicalP,add_sub_assoc,add_assoc]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma smoothJetAt_fusionDefect (m : ℕ∞ω) (N : ℕ) (Ξ : E→Fin N→ℝ) (f : E→ℝ) (x : E)
    (hΞ : ∀ i,ContDiffAt ℝ m (fun y=>Ξ y i) x) (hf : ContDiffAt ℝ m f x)
    (hr : FusionRegular N (Ξ x) (f x)) (s t : Space N) :
    SmoothJetAt m (fun y=>fusionDefect N (Ξ y) (f y) s t) x := by
  have hm : ∀ v w,SmoothJetAt m (fun y=>T N (Ξ y) (gamma+f y-L) v w) x :=
    smoothJetAt_T_curve m N Ξ (fun y=>gamma+f y-L) x hΞ
      ((contDiffAt_const.add hf).sub contDiffAt_const) hr.1
  have hp : ∀ v w,SmoothJetAt m (fun y=>T N (Ξ y) (gamma+f y+L) v w) x :=
    smoothJetAt_T_curve m N Ξ (fun y=>gamma+f y+L) x hΞ
      ((contDiffAt_const.add hf).add contDiffAt_const) hr.2.1
  have hc : ∀ v w,SmoothJetAt m (fun y=>T N (Ξ y) (gamma+f y) v w) x :=
    smoothJetAt_T_curve m N Ξ (fun y=>gamma+f y) x hΞ
      (contDiffAt_const.add hf) hr.2.2
  exact (smoothJetAt_matrix_mul m _ _ x hm hp s t).sub (hc s t)
lemma contDiffAt_physicalDefect (m : ℕ∞ω) (W : ℕ) (Ξ : E→Fin (W+1)→ℝ) (f : E→ℝ) (x : E)
    (hΞ : ∀ i,ContDiffAt ℝ m (fun y=>Ξ y i) x) (hf : ContDiffAt ℝ m f x)
    (hr : FusionRegular (W+1) (Ξ x) (f x)) :
    ContDiffAt ℝ m (fun y=>physicalDefect W (Ξ y) (f y)) x := by
  have hD := smoothJetAt_fusionDefect m (W+1) Ξ f x hΞ hf hr
  have hR := smoothJetAt_reorient m (W+1) (fun y=>fusionDefect (W+1) (Ξ y) (f y)) x hD
  exact (smoothJetAt_commonScalar m W (fun y=>reorient (W+1) (fusionDefect (W+1) (Ξ y) (f y))) x hR).2.2.2
end CriticalHoneycomb.Transfer.SpectralFamily

end

section
namespace CriticalHoneycomb.Transfer.SpectralFamily
open Reflection RowExchange BoundaryJet RasterGrid
lemma L_pos : 0 < L := by unfold L; positivity
lemma nonsingular_core (N : ℕ) (ξ : Fin N→ℝ) (hξ : ∀ i,-L < ξ i ∧ ξ i < 0)
    (t : ℝ) (ht : 0<t ∧ t<4*L) : Nonsingular N ξ t := by
  have hπ:=Real.pi_pos
  simp only [L] at ht
  refine ⟨?_,?_,fun i=>⟨?_,?_⟩⟩
  · apply sine_ne_zero_interval <;> simp only [gamma] <;> linarith
  · apply sine_ne_zero_interval <;> simp only [gamma,b] <;> linarith
  · have hi:=hξ i
    simp only [L] at hi
    unfold Q
    apply mul_ne_zero <;> apply sine_ne_zero_interval <;> (try simp only [b] at *) <;> linarith
  · have hi:=hξ i
    simp only [L] at hi
    unfold Q
    apply mul_ne_zero <;> apply sine_ne_zero_interval <;> (try simp only [b] at *) <;> linarith
noncomputable def perturb (N : ℕ) (r : ℝ) (i : Fin N) : ℝ := -L/2+((i.val:ℝ)+1)*r
noncomputable def radius (N : ℕ) : ℝ := L/(4*((N:ℝ)+1))
lemma radius_pos (N : ℕ) : 0 < radius N := by unfold radius;exact div_pos L_pos (by positivity)
lemma radius_mul (N : ℕ) : radius N*((N:ℝ)+1)=L/4 := by
  unfold radius
  have h : (N:ℝ)+1 ≠ 0 := by positivity
  field_simp
lemma perturb_zero (N : ℕ) : perturb N 0=homogeneous N := by funext i;simp [perturb,homogeneous]
lemma perturb_core (N : ℕ) {r : ℝ} (hr : |r| < radius N) :
    ∀ i,-L < perturb N r i ∧ perturb N r i < 0 := by
  intro i
  have hi : (i.val:ℝ)+1 ≤ (N:ℝ)+1 := by exact_mod_cast Nat.le_of_lt i.isLt |> Nat.succ_le_succ
  have hi0 : 0 ≤ (i.val:ℝ)+1 := by positivity
  have hN : 0 < (N:ℝ)+1 := by positivity
  have hB := mul_lt_mul_of_pos_right hr hN
  rw [radius_mul] at hB
  have hab : |((i.val:ℝ)+1)*r| < L/4 := by
    rw [abs_mul,abs_of_nonneg hi0]
    calc _ ≤ |r| *((N:ℝ)+1) := by nlinarith [abs_nonneg r]
         _ < L/4 := hB
  rw [abs_lt] at hab
  unfold perturb
  constructor <;> linarith [L_pos]
lemma perturb_regular (N : ℕ) {r u x : ℝ} (hx : 0≤x ∧ x≤L)
    (hr : |r| < radius N) (hu : |u-x| < radius N*((N:ℝ)+1)) :
    FusionRegular N (perturb N r) u := by
  rw [radius_mul,abs_lt] at hu
  have hL:=L_pos
  have hg : gamma=3*L/2 := by unfold gamma L;ring
  refine ⟨nonsingular_core N _ (perturb_core N hr) _ ?_,
    nonsingular_core N _ (perturb_core N hr) _ ?_,
    nonsingular_core N _ (perturb_core N hr) _ ?_⟩ <;> rw [hg] <;> constructor <;> linarith
end CriticalHoneycomb.Transfer.SpectralFamily

end

section
open scoped ContDiff
namespace CriticalHoneycomb.Transfer.SpectralFamily
open Reflection RowExchange BoundaryJet RasterGrid
open CriticalHoneycomb.Analysis
noncomputable def zeroSlope (N i : ℕ) : ℝ :=
  (i:ℝ)-N+(if i<N then 0 else 1)
lemma zeroSlope_strict (N : ℕ) : StrictMono (zeroSlope N) := by
  intro i j hij
  have hij' : (i:ℝ)<j := by exact_mod_cast hij
  simp only [zeroSlope]
  split_ifs with hi hj hj <;> (try omega) <;> linarith
lemma zeroSlope_bound (N i : ℕ) (hi : i<2*N) : |zeroSlope N i| ≤ (N:ℝ)+1 := by
  have hi' : (i:ℝ)<2*N := by exact_mod_cast hi
  have hi0 : (0:ℝ) ≤ i := by positivity
  rw [abs_le]
  unfold zeroSlope
  split_ifs <;> constructor <;> linarith
lemma zeroSlope_signed (N i : ℕ) (hi : i<2*N) :
    ∃ k : Fin N,zeroSlope N i=((k.val:ℝ)+1) ∨ zeroSlope N i=-((k.val:ℝ)+1) := by
  by_cases h : i<N
  · let k : Fin N:=⟨N-1-i,by omega⟩
    refine ⟨k,Or.inr ?_⟩
    have hk : k.val+1+i=N := by dsimp [k];omega
    have hk' : (k.val:ℝ)+1+i=N := by exact_mod_cast hk
    simp only [zeroSlope,ite_eq_left h]
    linarith
  · let k : Fin N:=⟨i-N,by omega⟩
    refine ⟨k,Or.inl ?_⟩
    have hk : k.val+N=i := by dsimp [k];omega
    have hk' : (k.val:ℝ)+N=i := by exact_mod_cast hk
    simp only [zeroSlope,ite_eq_right h]
    linarith
lemma perturb_signed_zero (W : ℕ) (r u : ℝ) (i : Fin (W+1))
    (hu : u=((i.val:ℝ)+1)*r ∨ u=-(((i.val:ℝ)+1)*r))
    (hr : FusionRegular (W+1) (perturb (W+1) r) u) :
    physicalDefect W (perturb (W+1) r) u=0 := by
  rcases hu with hu|hu
  · apply physicalDefect_node W _ i u (Or.inr ?_) hr
    rw [hu];unfold perturb;ring
  · have hn : physicalDefect W (perturb (W+1) r) (-u)=0 := by
      apply physicalDefect_node W _ i (-u) (Or.inr ?_) (fusionRegular_neg _ _ _ hr)
      rw [hu];unfold perturb;ring
    rw [physicalDefect_reflect _ _ _ hr] at hn
    exact hn
lemma affine_node_close {r δ C a : ℝ} (hr : 0<r) (hrd : r<δ) (hC : 0<C) (ha : |a|≤C) :
    |r*a| < δ*C := by
  rw [abs_mul,abs_of_pos hr]
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left ha hr.le) (mul_lt_mul_of_pos_right hrd hC)
lemma smooth_perturb_defect (W : ℕ) {r u x : ℝ} (hx : 0≤x ∧ x≤L)
    (hr : |r| < radius (W+1)) (hu : |u-x| < radius (W+1)*((W+1:ℕ)+1:ℝ)) :
    ContDiffAt ℝ ∞ (fun p : ℝ×ℝ=>physicalDefect W (perturb (W+1) p.1) p.2) (r,u) := by
  exact contDiffAt_physicalDefect ∞ W (fun p : ℝ×ℝ=>perturb (W+1) p.1) Prod.snd (r,u)
    (by intro i;unfold perturb;fun_prop) (by fun_prop) (perturb_regular _ hx hr hu)

lemma physicalDefect_zero_jets (W j : ℕ) (hj : j<2*(W+1)) :
    iteratedDeriv j (physicalDefect W (homogeneous (W+1))) 0=0 := by
  let a : Fin (j+1)→ℝ:=fun i=>zeroSlope (W+1) i.val
  have ha : StrictMono a := fun _ _ h=>zeroSlope_strict (W+1) h
  have hb : ∀ i,|a i|≤((W+1:ℕ):ℝ)+1 := fun i=>zeroSlope_bound _ _ (by omega)
  have hm := confluent_affine_complex j (fun r=>physicalDefect W (perturb (W+1) r)) 0
    a ha (((W+1:ℕ):ℝ)+1) (by positivity) hb (radius (W+1)) (radius_pos _) ?_ ?_
  · simpa only [perturb_zero] using hm
  · intro r hr hd i
    have hi : i.val<2*(W+1) := by omega
    have hclose : |(0+r*a i)-0| < radius (W+1)*(((W+1:ℕ):ℝ)+1) := by
      simpa using affine_node_close hr hd (show (0:ℝ)<((W+1:ℕ):ℝ)+1 by positivity) (hb i)
    have hreg:=perturb_regular (W+1) ⟨le_rfl,L_pos.le⟩
      (show |r| < radius (W+1) by rwa [abs_of_pos hr]) hclose
    obtain ⟨k,hk|hk⟩:=zeroSlope_signed (W+1) i.val hi
    · exact perturb_signed_zero W r _ k (Or.inl (by dsimp [a];rw [hk];ring)) hreg
    · exact perturb_signed_zero W r _ k (Or.inr (by dsimp [a];rw [hk];ring)) hreg
  · intro r u hr hu
    exact smooth_perturb_defect W ⟨le_rfl,L_pos.le⟩ hr hu

lemma physicalDefect_L_jets (W j : ℕ) (hj : j<W+1) :
    iteratedDeriv j (physicalDefect W (homogeneous (W+1))) L=0 := by
  let a : Fin (j+1)→ℝ:=fun i=>(i.val:ℝ)-(W+1:ℕ)
  have ha : StrictMono a := by
    intro i k hik
    exact sub_lt_sub_right (by exact_mod_cast hik) _
  have hb : ∀ i,|a i|≤((W+1:ℕ):ℝ)+1 := by
    intro i
    have hi : (i.val:ℝ)<(W+1:ℕ) := by exact_mod_cast (show i.val<W+1 by omega)
    have hi0 : (0:ℝ) ≤ i.val := by positivity
    rw [abs_le];dsimp [a];constructor <;> linarith
  have hm := confluent_affine_complex j (fun r=>physicalDefect W (perturb (W+1) r)) L
    a ha (((W+1:ℕ):ℝ)+1) (by positivity) hb (radius (W+1)) (radius_pos _) ?_ ?_
  · simpa only [perturb_zero] using hm
  · intro r hr hd i
    have hclose : |(L+r*a i)-L| < radius (W+1)*(((W+1:ℕ):ℝ)+1) := by
      simpa using affine_node_close hr hd (show (0:ℝ)<((W+1:ℕ):ℝ)+1 by positivity) (hb i)
    have hreg:=perturb_regular (W+1) ⟨L_pos.le,le_rfl⟩
      (show |r| < radius (W+1) by rwa [abs_of_pos hr]) hclose
    let k : Fin (W+1):=⟨W-i.val,by omega⟩
    have hk : k.val+1+i.val=W+1 := by dsimp [k];omega
    have hk' : (k.val:ℝ)+1+i.val=(W+1:ℕ) := by exact_mod_cast hk
    apply physicalDefect_node W _ k _ (Or.inl ?_) hreg
    dsimp [perturb,a]
    nlinarith
  · intro r u hr hu
    exact smooth_perturb_defect W ⟨L_pos.le,le_rfl⟩ hr hu
lemma physicalDefect_eventually (W : ℕ) {x : ℝ} (hx : 0≤x ∧ x≤L) :
    physicalDefect W (homogeneous (W+1)) =ᶠ[nhds x]
      (fun u=>physicalP W (u-L)+physicalP W (u+L)-physicalP W u) := by
  have hd : 0 < radius (W+1)*(((W+1:ℕ):ℝ)+1) := mul_pos (radius_pos _) (by positivity)
  have he : ∀ᶠ u in nhds x,|u-x| < radius (W+1)*(((W+1:ℕ):ℝ)+1) := by
    filter_upwards [Metric.ball_mem_nhds x hd] with u hu
    simpa only [Real.dist_eq] using (Metric.mem_ball.mp hu)
  filter_upwards [he] with u hu
  apply physicalDefect_homogeneous
  rw [←perturb_zero]
  exact perturb_regular _ hx (by simpa using radius_pos (W+1)) hu

theorem physicalP_zero_fusion_jets (W j : ℕ) (hj : j<2*(W+1)) :
    iteratedDeriv j (fun u : ℝ=>physicalP W (u-L)+physicalP W (u+L)-physicalP W u) 0=0 := by
  rw [←Filter.EventuallyEq.iteratedDeriv_eq j (physicalDefect_eventually W ⟨le_rfl,L_pos.le⟩)]
  exact physicalDefect_zero_jets W j hj

theorem physicalP_L_fusion_jets (W j : ℕ) (hj : j<W+1) :
    iteratedDeriv j (fun u : ℝ=>physicalP W (u-L)+physicalP W (u+L)-physicalP W u) L=0 := by
  rw [←Filter.EventuallyEq.iteratedDeriv_eq j (physicalDefect_eventually W ⟨L_pos.le,le_rfl⟩)]
  exact physicalDefect_L_jets W j hj
end CriticalHoneycomb.Transfer.SpectralFamily

end


section
namespace CriticalHoneycomb.Transfer.SpectralFamily.Trig
open Polynomial Reflection CriticalHoneycomb.FiniteFunctional Filter Topology
lemma polePoly_eval (N : ℕ) (X : ℂ) :
    (polePoly N).eval X=interpolationDenominator N X := by
  simp only [polePoly,eval_mul,eval_pow,eval_add,eval_X,eval_C]
  rfl
lemma physicalNumerator_eval (W : ℕ) (u : ℝ)
    (hu : Nonsingular (W+1) (homogeneous (W+1)) (gamma+u)) :
    (physicalNumerator W).eval (Real.cos (2*u):ℂ)=
      interpolationDenominator (W+1) (Real.cos (2*u):ℂ)*physicalP W u := by
  rw [physicalNumerator,eval_mul,eval_C,cosinePoly_physical W u hu,den_cos]
  change (2:ℂ)^(2*(W+1)+1)*
    ((2:ℂ)⁻¹^(2*(W+1)+1)*((Real.cos (2*u):ℂ)+1)^(W+1)*
      ((Real.cos (2*u):ℂ)+(Real.cos (2*L):ℂ))^(W+1+1)*physicalP W u)=_
  rw [inv_pow,←mul_assoc,←mul_assoc,←mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ (by norm_num)),one_mul]
  rfl
lemma interpolationDenominator_ne (W : ℕ) (u : ℝ)
    (hu : Nonsingular (W+1) (homogeneous (W+1)) (gamma+u)) :
    interpolationDenominator (W+1) (Real.cos (2*u):ℂ)≠0 := by
  have hd:=(homogeneous_nonsingular_den _ (by omega) u).mp hu
  rw [den_cos] at hd
  change ((Real.cos (2*u):ℂ)+1)^(W+1)*
    ((Real.cos (2*u):ℂ)+(Real.cos (2*L):ℂ))^(W+1+1)≠0
  rw [mul_assoc] at hd
  exact (mul_ne_zero_iff.mp hd).2
lemma interpolant_is_physical {W : ℕ} {ρ : ℂ} {P : Polynomial ℂ}
    (hP : physicalNumerator W=(C 4*X+C ρ)*polePoly (W+1)+P)
    (u : ℝ) (hu : Nonsingular (W+1) (homogeneous (W+1)) (gamma+u)) :
    interpolant (W+1) ρ P u=physicalP W u := by
  have he:=congrArg (fun p : Polynomial ℂ=>p.eval (Real.cos (2*u):ℂ)) hP
  rw [physicalNumerator_eval W u hu,eval_add,eval_mul,eval_add,eval_mul,eval_C,
    eval_X,eval_C,polePoly_eval] at he
  have hd:=interpolationDenominator_ne W u hu
  unfold interpolant
  apply mul_right_cancel₀ hd
  rw [add_mul,div_mul_cancel₀ _ hd]
  exact he.symm.trans (mul_comm _ _)
lemma interpolant_is_physical_interval {W : ℕ} {ρ : ℂ} {P : Polynomial ℂ}
    (hP : physicalNumerator W=(C 4*X+C ρ)*polePoly (W+1)+P)
    {u : ℝ} (hu0 : -b<u) (hu1 : u<b) : interpolant (W+1) ρ P u=physicalP W u := by
  apply interpolant_is_physical hP u
  apply homogeneous_nonsingular_interval
  · dsimp [b,gamma,L] at hu0 ⊢;linarith
  · linarith
lemma interpolant_fusion_eventually {W : ℕ} {ρ : ℂ} {P : Polynomial ℂ}
    (hP : physicalNumerator W=(C 4*X+C ρ)*polePoly (W+1)+P)
    {x : ℝ} (hx : 0≤x ∧ x≤L) :
    (fun u : ℝ=>interpolant (W+1) ρ P (u-L)+interpolant (W+1) ρ P (u+L)-
      interpolant (W+1) ρ P u)=ᶠ[𝓝 x]
    (fun u : ℝ=>physicalP W (u-L)+physicalP W (u+L)-physicalP W u) := by
  have hlo : L-b<x := by have hp:=Real.pi_pos;dsimp [L,b] at hx ⊢;linarith [hx.1]
  have hhi : x<b-L := by have hp:=Real.pi_pos;dsimp [L,b] at hx ⊢;linarith [hx.2]
  filter_upwards [Ioo_mem_nhds hlo hhi] with u hu
  have hp:=L_pos
  rw [interpolant_is_physical_interval hP (by linarith [hu.1]) (by linarith [hu.2]),
    interpolant_is_physical_interval hP (by linarith [hu.1]) (by linarith [hu.2]),
    interpolant_is_physical_interval hP (by linarith [hu.1]) (by linarith [hu.2])]
end CriticalHoneycomb.Transfer.SpectralFamily.Trig

end

section
namespace CriticalHoneycomb.FiniteFunctional
open Polynomial Transfer.SpectralFamily Transfer.SpectralFamily.Trig
open Transfer.Reflection
lemma bridgeMass_actual_tsum (W : ℕ) : bridgeMass (W+1)=
    ENNReal.ofReal (∑' γ : StrictBridge (W+1),kappa^γ.val.length) := by
  simp only [bridgeMass,Nat.add_one_ne_zero,ite_false,weight]
  symm
  apply ENNReal.ofReal_tsum_of_nonneg
  · intro γ
    exact (pow_pos FiniteContinuation.kappa_positive _).le
  · exact StripExhaustion.real_strip_summable W

theorem source_physical_spectral_interpolation : PhysicalSpectralInterpolation := by
  intro N hN
  obtain ⟨W,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : N≠0)
  obtain ⟨ρ,P,hdeg,hP⟩:=physicalNumerator_decomposition W
  refine ⟨∑' γ : StrictBridge (W+1),kappa^γ.val.length,ρ,P,?_,bridgeMass_actual_tsum W,hdeg,?_,?_,?_,?_,?_⟩
  · exact tsum_nonneg (fun γ=>(pow_pos FiniteContinuation.kappa_positive _).le)
  · rw [interpolant_is_physical_interval hP (by dsimp [b,L];linarith [Real.pi_pos])
      (by dsimp [b,L];linarith [Real.pi_pos])]
    exact physicalP_mass W
  · change interpolant (W+1) ρ P (3*L/2)=0
    rw [interpolant_is_physical_interval hP (by dsimp [b,L];linarith [Real.pi_pos])
      (by dsimp [b,L];linarith [Real.pi_pos])]
    exact (physicalP_endpoint_zeros W).1
  · change interpolant (W+1) ρ P (5*L/2)=0
    rw [interpolant_is_physical_interval hP (by dsimp [b,L];linarith [Real.pi_pos])
      (by dsimp [b,L];linarith [Real.pi_pos])]
    exact (physicalP_endpoint_zeros W).2
  · intro j hj
    change iteratedDeriv j (fun u : ℝ=>interpolant (W+1) ρ P (u-L)+
      interpolant (W+1) ρ P (u+L)-interpolant (W+1) ρ P u) 0=0
    rw [Filter.EventuallyEq.iteratedDeriv_eq j (interpolant_fusion_eventually hP ⟨le_rfl,L_pos.le⟩)]
    exact physicalP_zero_fusion_jets W j hj
  · intro j hj
    change iteratedDeriv j (fun u : ℝ=>interpolant (W+1) ρ P (u-L)+
      interpolant (W+1) ρ P (u+L)-interpolant (W+1) ρ P u) L=0
    rw [Filter.EventuallyEq.iteratedDeriv_eq j (interpolant_fusion_eventually hP ⟨L_pos.le,le_rfl⟩)]
    exact physicalP_L_fusion_jets W j hj
end CriticalHoneycomb.FiniteFunctional

end

end OAI
