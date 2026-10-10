import OAI.Combinatorics.HoneycombChords.OrderedDeterminants

namespace OAI

/-!
# Positive function flags and orthogonality

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory Filter
/-- Orthogonality forces at least m distinct zeros (indeed m sign changes) for
continuous functions against a m-dimensional zero-at-origin jet flag. The measure
and the squared p-coordinate are those used by the actual strip pairing. -/
theorem zero_jet_flag_integral_nonzero {m : ℕ} (b : ℕ → ℝ) (f w : ℝ → ℝ)
    (hb : Monotone (fun i : Fin (m+1)=>b i)) (hb0 : ∀ i : Fin (m+1),0 ≤ b i) (hbfirst : b 0=0)
    (hf : Continuous f) (hw : ∀ p,0<p → 0<w p)
    (hi : ∀ i : Fin m,IntegrableOn (fun p=>f (p^2)*zeroJet b i (p^2)*w p) (Set.Ioi 0))
    (s : Finset ℝ) (hs : ∀ x ∈ s,0 < x) (hz : ∀ x,0 < x → (f x = 0 ↔ x ∈ s)) (hc : s.card < m) :
    ∃ i : Fin m,(∫ p in Set.Ioi (0:ℝ),f (p^2)*zeroJet b i (p^2)*w p)≠0 := by
  classical
  by_contra hall
  push Not at hall
  obtain ⟨k,hk,a,hnonneg,hpos⟩ := zero_jet_flag_sign_matching b f hb hb0 hbfirst hf s hs hz hc
  let F : Fin (k+1) → ℝ → ℝ := fun i p=>a i*(f (p^2)*zeroJet b i (p^2)*w p)
  let H : ℝ → ℝ := fun p=>f (p^2)*zeroJetCombination b a (p^2)
  let g : ℝ → ℝ := fun p=>H p*w p
  have heq : g=fun p=>∑ i,F i p := by
    funext p
    dsimp [g,H,F,zeroJetCombination]
    rw [mul_sum,sum_mul]
    apply sum_congr rfl
    intro i _
    ring
  have hiF (i : Fin (k+1)) : IntegrableOn (F i) (Set.Ioi 0) := (hi (i.castLE hk)).const_mul (a i)
  have hig : IntegrableOn g (Set.Ioi 0) := by rw [heq];exact integrable_finsetSum _ (fun i _=>hiF i)
  have hzero : (∫ p in Set.Ioi (0:ℝ),g p)=0 := by
    rw [heq,integral_finsetSum _ (fun i _=>hiF i)]
    apply sum_eq_zero
    intro i _
    rw [show (F i)=fun p=>a i*(f (p^2)*zeroJet b i (p^2)*w p) from rfl,
      integral_const_mul]
    have hz := hall (i.castLE hk)
    change (∫ p in Set.Ioi (0:ℝ),f (p^2)*zeroJet b i (p^2)*w p)=0 at hz
    rw [hz,mul_zero]
  have hgnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (0:ℝ))] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    exact mul_nonneg (hnonneg (p^2) (sq_pos_of_pos hp)) (hw p hp).le
  have hH : Continuous H := by
    exact (hf.comp (continuous_id.pow 2)).mul ((zeroJetCombination_continuous b a).comp (continuous_id.pow 2))
  let U : Set ℝ := Set.Ioi 0 ∩ {p | 0<H p}
  have hopen : IsOpen U := isOpen_Ioi.inter (isOpen_lt continuous_const hH)
  obtain ⟨R,hR⟩ := (insert 0 s).finite_toSet.bddAbove
  let x := R+1
  have hR0 : 0≤R := hR (by simp)
  have hx : 0 < x := by dsimp [x];linarith
  have hxs : x∉s := by
    intro h
    have hh : x≤R := hR (mem_insert_of_mem h)
    dsimp [x] at hh
    linarith
  have hune : U.Nonempty := by
    refine ⟨Real.sqrt x,Real.sqrt_pos.mpr hx,?_⟩
    dsimp [H]
    rw [Real.sq_sqrt hx.le]
    exact hpos x hx (fun h=>hxs ((hz x hx).mp h))
  have hup : 0<(volume.restrict (Set.Ioi (0:ℝ))) U := by
    rw [Measure.restrict_apply hopen.measurableSet,Set.inter_eq_left.mpr Set.inter_subset_left]
    exact hopen.measure_pos volume hune
  have hus : U⊆Function.support g := by
    intro p hp
    exact (mul_pos hp.2 (hw p hp.1)).ne'
  have hgpos : 0<∫ p in Set.Ioi (0:ℝ),g p :=
    (integral_pos_iff_support_of_nonneg_ae hgnonneg hig).mpr (hup.trans_le (measure_mono hus))
  exact hgpos.ne' hzero
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Finset MeasureTheory
lemma zeroJet_linear_zero_set {n : ℕ} (b : ℕ → ℝ) (a : Fin n → ℝ) (t : ℝ)
    (hb : Monotone (fun i : Fin (n+1)=>b i)) (hb0 : ∀ i : Fin (n+1),0 ≤ b i)
    (hbfirst : b 0=0) (ha : a ≠ 0) :
    ∃ s : Finset ℝ,(∀ x∈s,0<x) ∧
      (∀ x,0<x → ((x-t)*zeroJetCombination b a x=0 ↔ x∈s)) ∧ s.card ≤ n := by
  classical
  let Z := (zeroJetCombination_finite_zeros b a hb hb0 hbfirst ha).toFinset
  have hZ : ∀ x,x∈Z ↔ 0<x ∧ zeroJetCombination b a x=0 := fun x=>Set.Finite.mem_toFinset _
  have hZcard : Z.card<n := zeroJetCombination_zeros_card_lt b a hb hb0 hbfirst ha Z (fun x hx=>(hZ x).mp hx)
  let s := (insert t Z).filter (fun x=>0<x)
  refine ⟨s,fun x hx=>(mem_filter.mp hx).2,?_,?_⟩
  · intro x hx
    simp only [s,mem_filter,mem_insert,hZ,mul_eq_zero,sub_eq_zero]
    constructor
    · intro hh
      exact ⟨hh.imp_right (fun h=>⟨hx,h⟩),hx⟩
    · rintro ⟨h|h,_⟩
      · exact Or.inl h
      · exact Or.inr h.2
  · have h : s.card ≤ Z.card+1 := (card_filter_le _ _).trans (card_insert_le _ _)
    omega
/-- The constant removed at zero gives exactly the stronger zero count
required for the first step of the second interlacing chain. -/
theorem zero_jet_linear_nonorthogonality {n m : ℕ} (b c : ℕ → ℝ) (a : Fin n → ℝ)
    (w : ℝ → ℝ) (t : ℝ) (hnm : n < m)
    (hb : Monotone (fun i : Fin (n+1)=>b i)) (hc : Monotone (fun i : Fin m=>c i))
    (hb0 : ∀ i : Fin (n+1),0 ≤ b i) (hc0 : ∀ i : Fin m,0 ≤ c i)
    (hbfirst : b 0=0) (ha : a ≠ 0) (hw : ∀ p,0<p → 0<w p)
    (hi : ∀ j : Fin m,IntegrableOn (fun p=>(p^2-t)*zeroJetCombination b a (p^2)*
      cosineKernelJet (nodalOrder c j) 0 (c j) (p^2)*w p) (Set.Ioi 0)) :
    ∃ j : Fin m,(∫ p in Set.Ioi (0:ℝ),(p^2-t)*zeroJetCombination b a (p^2)*
      cosineKernelJet (nodalOrder c j) 0 (c j) (p^2)*w p) ≠ 0 := by
  obtain ⟨s,hs,hz,hcard⟩ := zeroJet_linear_zero_set b a t hb hb0 hbfirst ha
  exact jet_flag_integral_nonzero c (fun x=>(x-t)*zeroJetCombination b a x) w hc hc0
    ((continuous_id.sub continuous_const).mul (zeroJetCombination_continuous b a))
    hw hi s hs hz (hcard.trans_lt hnm)
theorem zero_jet_linear_zero_nonorthogonality {n m : ℕ} (b c : ℕ → ℝ) (a : Fin n → ℝ)
    (w : ℝ → ℝ) (t : ℝ) (hnm : n < m)
    (hb : Monotone (fun i : Fin (n+1)=>b i)) (hc : Monotone (fun i : Fin (m+1)=>c i))
    (hb0 : ∀ i : Fin (n+1),0 ≤ b i) (hc0 : ∀ i : Fin (m+1),0 ≤ c i)
    (hbfirst : b 0=0) (hcfirst : c 0=0) (ha : a ≠ 0) (hw : ∀ p,0<p → 0<w p)
    (hi : ∀ j : Fin m,IntegrableOn (fun p=>(p^2-t)*zeroJetCombination b a (p^2)*zeroJet c j (p^2)*w p) (Set.Ioi 0)) :
    ∃ j : Fin m,(∫ p in Set.Ioi (0:ℝ),(p^2-t)*zeroJetCombination b a (p^2)*zeroJet c j (p^2)*w p) ≠ 0 := by
  obtain ⟨s,hs,hz,hcard⟩ := zeroJet_linear_zero_set b a t hb hb0 hbfirst ha
  exact zero_jet_flag_integral_nonzero c (fun x=>(x-t)*zeroJetCombination b a x) w hc hc0 hcfirst
    ((continuous_id.sub continuous_const).mul (zeroJetCombination_continuous b a))
    hw hi s hs hz (hcard.trans_lt hnm)
lemma pole_zeroJetCombination_linear_pair_integrable {n m : ℕ} (b c : ℕ → ℝ)
    (a : Fin n → ℝ) {z : ℝ} (hz : 0<z) (t : ℝ)
    (hbfirst : b 0=0) (hb0 : ∀ i : Fin (n+1),0 ≤ b i) (hc0 : ∀ i : Fin m,0 ≤ c i)
    (hb1 : ∀ i : Fin (n+1),b i ≤ (3*angle/2)^2) (hc1 : ∀ i : Fin m,c i ≤ angle^2)
    (j : Fin m) :
    IntegrableOn (fun p=>(p^2-t)*zeroJetCombination b a (p^2)*
      cosineKernelJet (nodalOrder c j) 0 (c j) (p^2)*poleAdjustedDensity z p) (Set.Ioi 0) := by
  simpa only [zeroJetLift_eq b a hbfirst] using
    pole_jetCombination_linear_pair_integrable b c (zeroJetLift b a) hz t hb0 hc0 hb1 hc1 j
lemma pole_zeroJetCombination_linear_zero_pair_integrable {n m : ℕ} (b c : ℕ → ℝ)
    (a : Fin n → ℝ) {z : ℝ} (hz : 0<z) (t : ℝ)
    (hbfirst : b 0=0) (hcfirst : c 0=0)
    (hb0 : ∀ i : Fin (n+1),0 ≤ b i) (hc0 : ∀ i : Fin (m+1),0 ≤ c i)
    (hb1 : ∀ i : Fin (n+1),b i ≤ (3*angle/2)^2) (hc1 : ∀ i : Fin (m+1),c i ≤ angle^2)
    (j : Fin m) :
    IntegrableOn (fun p=>(p^2-t)*zeroJetCombination b a (p^2)*zeroJet c j (p^2)*poleAdjustedDensity z p) (Set.Ioi 0) := by
  have hi:=pole_zeroJetCombination_linear_pair_integrable b c a hz t hbfirst hb0 hc0 hb1 hc1 j.succ
  have hi0:=pole_zeroJetCombination_linear_pair_integrable b c a hz t hbfirst hb0 hc0 hb1 hc1 0
  simp only [Fin.val_zero,jet_first_constant c hcfirst,mul_one] at hi0
  apply (hi.sub (hi0.mul_const (cosineKernelJet (nodalOrder c (j.val+1)) 0 (c (j.val+1)) 0))).congr
  filter_upwards with p
  dsimp [zeroJet]
  ring
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Finset Matrix MeasureTheory
lemma twoKnot_first (N : ℕ) (hN : 0<N) : twoKnotLabels N 0=0 := by
  simp [twoKnotLabels,hN]
lemma interiorKnot_first (N : ℕ) (hN : 0<N) (t : ℝ) : interiorKnotLabels N t 0=0 := by
  simp [interiorKnotLabels,hN]
lemma zero_interior_row_before (N j : ℕ) {s : ℝ} (hs : 0<s) (hsL : s<angle) (hj : j+1<N) (x : ℝ) :
    zeroJet (interiorKnotLabels N s) j x=zeroJet (twoKnotLabels N) j x := by
  simp [zeroJet,interiorKnot_nodalOrder N (j+1) hs hsL,twoKnot_nodalOrder,interiorKnotLabels,twoKnotLabels,hj]
lemma zero_interior_row_at (N j : ℕ) {s : ℝ} (hs : 0<s) (hsL : s<angle) (hj : j+1=N) (p : ℝ) :
    zeroJet (interiorKnotLabels N s) j (p^2)=Real.cosh (s*p)-1 := by
  simp only [zeroJet,interiorKnot_nodalOrder N N hs hsL,ite_false,hj,ite_true,
    interiorKnotLabels,lt_self_iff_false]
  rw [cosineKernelJet_zero_zero_cosh (sq_nonneg s) (sq_nonneg p),Real.sqrt_sq hs.le]
  rw [show Real.cosh (s*Real.sqrt (p^2))=Real.cosh (s*p) by
    rw [Real.sqrt_sq_eq_abs];rcases le_total 0 p with hp|hp
    · rw [abs_of_nonneg hp]
    · rw [abs_of_nonpos hp,mul_neg,Real.cosh_neg]]
  rw [cosineKernelJet_zero_zero_cosh (sq_nonneg s) (by norm_num)]
  norm_num
lemma zero_interior_row_after (N j : ℕ) (hN : 0<N) {s : ℝ} (hs : 0<s) (hsL : s<angle) (hj : N<j+1) (x : ℝ) :
    zeroJet (interiorKnotLabels N s) j x=zeroJet (twoKnotLabels N) (j-1) x := by
  have hh : ¬j+1<N := by omega
  have hh' : j+1≠N := by omega
  have hj0 : 0<j := by omega
  have hj' : ¬j-1+1<N := by omega
  have he : j+1-(N+1)=j-1+1-N := by omega
  simp [zeroJet,interiorKnot_nodalOrder N (j+1) hs hsL,twoKnot_nodalOrder,interiorKnotLabels,twoKnotLabels,hh,hh',hj',he]
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset
lemma familyCombination_unique {n : ℕ} (F : ℕ → ℝ → ℝ) (a : Fin n → ℝ) (x : Fin n → ℝ)
    (hF : PositiveEvaluation (fun i : Fin n=>F i)) (hx : Function.Injective x) (hx0 : ∀ i,0 < x i)
    (hz : ∀ i,familyCombination F a (x i)=0) : a=0 := by
  have hd : (evaluationMatrix (fun i : Fin n=>F i) x).det ≠ 0 := by
    have h:=evaluation_det_product_pos _ _ hF hF x hx hx0
    exact fun he=>by rw [he,zero_mul] at h;exact lt_irrefl _ h
  apply (Matrix.vecMul_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd)))
  ext j
  dsimp only
  rw [Matrix.zero_vecMul]
  exact hz j
lemma familyCombination_zeros_card_lt {n : ℕ} (F : ℕ → ℝ → ℝ) (a : Fin n → ℝ)
    (hF : PositiveEvaluation (fun i : Fin n=>F i)) (ha : a ≠ 0)
    (s : Finset ℝ) (hs : ∀ x ∈ s,0 < x ∧ familyCombination F a x=0) : s.card < n := by
  classical
  by_contra hc
  obtain ⟨t,ht,htc⟩ := Finset.exists_subset_card_eq (le_of_not_gt hc)
  let o := t.equivFinOfCardEq htc
  let x : Fin n → ℝ := fun i=>(o.symm i).val
  apply ha
  apply familyCombination_unique F a x hF
  · intro i j he
    exact o.symm.injective (Subtype.ext he)
  · intro i
    exact (hs _ (ht (o.symm i).property)).1
  · intro i
    exact (hs _ (ht (o.symm i).property)).2
lemma familyCombination_finite_zeros {n : ℕ} (F : ℕ → ℝ → ℝ) (a : Fin n → ℝ)
    (hF : PositiveEvaluation (fun i : Fin n=>F i)) (ha : a ≠ 0) :
    {x : ℝ | 0 < x ∧ familyCombination F a x=0}.Finite := by
  by_contra hf
  obtain ⟨s,hs,hcard⟩ := Set.Infinite.exists_subset_card_eq hf n
  have h:=familyCombination_zeros_card_lt F a hF ha s (fun x hx=>hs hx)
  omega
lemma family_linear_zero_set {n : ℕ} (F : ℕ → ℝ → ℝ) (a : Fin n → ℝ) (r : ℝ)
    (hF : PositiveEvaluation (fun i : Fin n=>F i)) (ha : a ≠ 0) :
    ∃ s : Finset ℝ,(∀ x ∈ s,0 < x) ∧ (∀ x,0 < x → ((x-r)*familyCombination F a x=0 ↔ x ∈ s)) ∧ s.card ≤ n := by
  classical
  let Z := (familyCombination_finite_zeros F a hF ha).toFinset
  have hZ : ∀ x,x ∈ Z ↔ 0 < x ∧ familyCombination F a x=0 := fun _=>Set.Finite.mem_toFinset _
  have hc : Z.card < n := familyCombination_zeros_card_lt F a hF ha Z (fun x hx=>(hZ x).mp hx)
  let s := (insert r Z).filter (fun x=>0 < x)
  refine ⟨s,fun x hx=>(mem_filter.mp hx).2,?_,?_⟩
  · intro x hx
    simp only [s,mem_filter,mem_insert,hZ,mul_eq_zero,sub_eq_zero]
    constructor
    · intro hh
      exact ⟨hh.imp_right (fun h=>⟨hx,h⟩),hx⟩
    · rintro ⟨h|h,_⟩
      · exact Or.inl h
      · exact Or.inr h.2
  · have h : s.card  ≤  Z.card+1 := (card_filter_le _ _).trans (card_insert_le _ _)
    omega
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset
lemma familyTestCoeffs_last {n : ℕ} (F : ℕ → ℝ → ℝ) (v : Fin n → ℝ) :
    familyTestCoeffs F v (Fin.last n)=(-1:ℝ)^n*(evaluationMatrix (fun i : Fin n=>F i) v).det := by
  simp only [familyTestCoeffs,Fin.val_last,Fin.succAbove_last,Fin.val_castSucc]
  rfl
lemma familyTest_zero {n : ℕ} (F : ℕ → ℝ → ℝ) (v : Fin n → ℝ) (i : Fin n) :
    familyCombination F (familyTestCoeffs F v) (v i)=0 := by
  rw [familyTest_eq_det]
  apply Matrix.det_zero_of_column_eq (i:=0) (j:=i.succ) (Fin.succ_ne_zero _).symm
  intro k
  simp [evaluationMatrix]
lemma familyCombination_sub {n : ℕ} (F : ℕ → ℝ → ℝ) (a b : Fin n → ℝ) (x : ℝ) :
    familyCombination F (a-b) x=familyCombination F a x-familyCombination F b x := by
  simp [familyCombination,sub_mul,sum_sub_distrib]
lemma familyCombination_last_zero {n : ℕ} (F : ℕ → ℝ → ℝ) (a : Fin (n+1) → ℝ)
    (ha : a (Fin.last n)=0) (x : ℝ) :
    familyCombination F a x=familyCombination F (fun i : Fin n=>a i.castSucc) x := by
  simp [familyCombination,Fin.sum_univ_castSucc,ha]
/-- A monic combination with the maximum number of positive zeros has the
same orientation at those zeros as a monic ordinary polynomial. -/
theorem monic_family_sign {n : ℕ} (F : ℕ → ℝ → ℝ) (a : Fin (n+1) → ℝ) (v : Fin n → ℝ)
    (hF : PositiveEvaluation (fun i : Fin (n+1)=>F i))
    (hF0 : PositiveEvaluation (fun i : Fin n=>F i))
    (ha : a (Fin.last n)=1) (hv : StrictMono v) (hv0 : ∀ i,0 < v i)
    (haz : ∀ i,familyCombination F a (v i)=0) {x : ℝ} (hx : 0 < x) (hxv : ∀ i,x ≠ v i) :
    0 < familyCombination F a x*(∏ i,(x-v i)) := by
  let T := familyTestCoeffs F v
  let D := (evaluationMatrix (fun i : Fin n=>F i) v).det
  have hD : 0 < D := hF0 v hv hv0
  have hT : T (Fin.last n)=(-1:ℝ)^n*D := familyTestCoeffs_last F v
  let c : Fin (n+1) → ℝ := (fun i=>T (Fin.last n)*a i)-T
  have hc : c (Fin.last n)=0 := by simp [c,ha]
  have hcz (i : Fin n) : familyCombination F c (v i)=0 := by
    rw [show c=(fun i=>T (Fin.last n)*a i)-T from rfl,familyCombination_sub,familyCombination_smul,haz,mul_zero]
    rw [show T=familyTestCoeffs F v from rfl,familyTest_zero,sub_self]
  have hc0 : (fun i : Fin n=>c i.castSucc)=0 :=
    familyCombination_unique F _ v hF0 hv.injective hv0 (fun i=>by
      rw [←familyCombination_last_zero F c hc];exact hcz i)
  have hcall : c=0 := by
    ext i
    refine Fin.lastCases hc (fun j=>congrFun hc0 j) i
  have he : familyCombination F T x=T (Fin.last n)*familyCombination F a x := by
    have h := congrArg (fun b=>familyCombination F b x) hcall
    rw [show c=(fun i=>T (Fin.last n)*a i)-T from rfl,familyCombination_sub,familyCombination_smul] at h
    have hz : familyCombination F (0 : Fin (n+1) → ℝ) x=0 := by simp [familyCombination]
    rw [hz] at h
    linarith
  have hh:=familyTest_sign_product F v hF hv hv0 hx hxv
  change 0 < familyCombination F T x*(∏ i,(v i-x)) at hh
  have hn : (∏ i : Fin n,(v i-x))=(-1:ℝ)^n*(∏ i,(x-v i)) := by
    simp_rw [show ∀ i : Fin n,v i-x=(-1:ℝ)*(x-v i) from fun i=>by ring]
    rw [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin]
  rw [he,hT,hn] at hh
  have hs : ((-1:ℝ)^n)^2=1 := by rw [←pow_mul,show n*2=2*n by omega,pow_mul];norm_num
  have heq : ((-1:ℝ)^n*D*familyCombination F a x)*((-1:ℝ)^n*∏ i,(x-v i))=
      D*(familyCombination F a x*∏ i,(x-v i)) := by
    calc
      _ = ((-1:ℝ)^n)^2 * (D*(familyCombination F a x*∏ i,(x-v i))) := by ring
      _ = _ := by rw [hs,one_mul]
  rw [heq] at hh
  exact pos_of_mul_pos_right hh hD.le
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory Filter
/-- Orthogonality forces at least m distinct zeros (indeed m sign changes) for
continuous functions against a positive m-dimensional function flag. The measure
and the squared p-coordinate are those used by the actual strip pairing. -/
theorem positive_flag_integral_nonzero {m : ℕ} (B : ℕ → ℝ → ℝ) (f w : ℝ → ℝ)
    (hB : PositiveFlag B m) (hBc : ∀ i : Fin m,Continuous (B i))
    (hf : Continuous f) (hw : ∀ p,0<p → 0<w p)
    (hi : ∀ i : Fin m,IntegrableOn (fun p=>f (p^2)*B i (p^2)*w p) (Set.Ioi 0))
    (s : Finset ℝ) (hs : ∀ x ∈ s,0 < x) (hz : ∀ x,0 < x → (f x = 0 ↔ x ∈ s)) (hc : s.card < m) :
    ∃ i : Fin m,(∫ p in Set.Ioi (0:ℝ),f (p^2)*B i (p^2)*w p)≠0 := by
  classical
  by_contra hall
  push Not at hall
  obtain ⟨k,hk,a,hnonneg,hpos⟩ := positive_flag_sign_matching B f hB hf s hs hz hc
  let F : Fin (k+1) → ℝ → ℝ := fun i p=>a i*(f (p^2)*B i (p^2)*w p)
  let H : ℝ → ℝ := fun p=>f (p^2)*familyCombination B a (p^2)
  let g : ℝ → ℝ := fun p=>H p*w p
  have heq : g=fun p=>∑ i,F i p := by
    funext p
    dsimp [g,H,F,familyCombination]
    rw [mul_sum,sum_mul]
    apply sum_congr rfl
    intro i _
    ring
  have hiF (i : Fin (k+1)) : IntegrableOn (F i) (Set.Ioi 0) := (hi (i.castLE hk)).const_mul (a i)
  have hig : IntegrableOn g (Set.Ioi 0) := by rw [heq];exact integrable_finsetSum _ (fun i _=>hiF i)
  have hzero : (∫ p in Set.Ioi (0:ℝ),g p)=0 := by
    rw [heq,integral_finsetSum _ (fun i _=>hiF i)]
    apply sum_eq_zero
    intro i _
    rw [show (F i)=fun p=>a i*(f (p^2)*B i (p^2)*w p) from rfl,
      integral_const_mul]
    have hz := hall (i.castLE hk)
    change (∫ p in Set.Ioi (0:ℝ),f (p^2)*B i (p^2)*w p)=0 at hz
    rw [hz,mul_zero]
  have hgnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (0:ℝ))] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    exact mul_nonneg (hnonneg (p^2) (sq_pos_of_pos hp)) (hw p hp).le
  have hH : Continuous H := by
    exact (hf.comp (continuous_id.pow 2)).mul ((familyCombination_continuous B a (fun i=>hBc (i.castLE hk))).comp (continuous_id.pow 2))
  let U : Set ℝ := Set.Ioi 0 ∩ {p | 0<H p}
  have hopen : IsOpen U := isOpen_Ioi.inter (isOpen_lt continuous_const hH)
  obtain ⟨R,hR⟩ := (insert 0 s).finite_toSet.bddAbove
  let x := R+1
  have hR0 : 0≤R := hR (by simp)
  have hx : 0 < x := by dsimp [x];linarith
  have hxs : x∉s := by
    intro h
    have hh : x≤R := hR (mem_insert_of_mem h)
    dsimp [x] at hh
    linarith
  have hune : U.Nonempty := by
    refine ⟨Real.sqrt x,Real.sqrt_pos.mpr hx,?_⟩
    dsimp [H]
    rw [Real.sq_sqrt hx.le]
    exact hpos x hx (fun h=>hxs ((hz x hx).mp h))
  have hup : 0<(volume.restrict (Set.Ioi (0:ℝ))) U := by
    rw [Measure.restrict_apply hopen.measurableSet,Set.inter_eq_left.mpr Set.inter_subset_left]
    exact hopen.measure_pos volume hune
  have hus : U⊆Function.support g := by
    intro p hp
    exact (mul_pos hp.2 (hw p hp.1)).ne'
  have hgpos : 0<∫ p in Set.Ioi (0:ℝ),g p :=
    (integral_pos_iff_support_of_nonneg_ae hgnonneg hig).mpr (hup.trans_le (measure_mono hus))
  exact hgpos.ne' hzero
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory
/-- The maximal zero count at a real pencil root. In particular the root is
positive and distinct from the zeros of its root function. -/
theorem flag_orthogonal_linear_zeros {n : ℕ} (F G : ℕ → ℝ → ℝ) (a : Fin (n+1) → ℝ)
    (w : ℝ → ℝ) (r : ℝ)
    (hF : PositiveEvaluation (fun i : Fin (n+1)=>F i))
    (hG : PositiveFlag G (n+1)) (hFc : ∀ i : Fin (n+1),Continuous (F i))
    (hGc : ∀ i : Fin (n+1),Continuous (G i)) (ha : a ≠ 0) (hw : ∀ p,0 < p → 0 < w p)
    (hi : ∀ i : Fin (n+1),IntegrableOn (fun p=>(p^2-r)*familyCombination F a (p^2)*G i (p^2)*w p) (Set.Ioi 0))
    (ho : ∀ i : Fin (n+1),(∫ p in Set.Ioi (0:ℝ),(p^2-r)*familyCombination F a (p^2)*G i (p^2)*w p)=0) :
    ∃ Z : Finset ℝ,Z.card=n ∧ (∀ x,x ∈ Z ↔ 0 < x ∧ familyCombination F a x=0) ∧ 0 < r ∧ r ∉ Z := by
  classical
  let Z := (familyCombination_finite_zeros F a hF ha).toFinset
  have hZ : ∀ x,x ∈ Z ↔ 0 < x ∧ familyCombination F a x=0 := fun _=>Set.Finite.mem_toFinset _
  have hc : Z.card < n+1 := familyCombination_zeros_card_lt F a hF ha Z (fun x hx=>(hZ x).mp hx)
  let s := (insert r Z).filter (fun x=>0 < x)
  have hs : ∀ x ∈ s,0 < x := fun x hx=>(mem_filter.mp hx).2
  have hz : ∀ x,0 < x → ((x-r)*familyCombination F a x=0 ↔ x ∈ s) := by
    intro x hx
    simp only [s,mem_filter,mem_insert,hZ,mul_eq_zero,sub_eq_zero]
    constructor
    · intro hh
      exact ⟨hh.imp_right (fun h=>⟨hx,h⟩),hx⟩
    · rintro ⟨h|h,_⟩
      · exact Or.inl h
      · exact Or.inr h.2
  have hsc : n+1 ≤ s.card := by
    by_contra hh
    obtain ⟨i,hi⟩ := positive_flag_integral_nonzero G (fun x=>(x-r)*familyCombination F a x) w hG hGc
      ((continuous_id.sub continuous_const).mul (familyCombination_continuous F a hFc)) hw hi s hs hz (by omega)
    exact hi (ho i)
  have hsc' : s.card  ≤  Z.card+1 := (card_filter_le _ _).trans (card_insert_le _ _)
  have hZc : Z.card=n := by omega
  have hzfilter : Z.filter (fun x=>0 < x)=Z := filter_eq_self.mpr (fun x hx=>((hZ x).mp hx).1)
  have hr : 0 < r := by
    by_contra h
    have he : s=Z := by simp [s,filter_insert,h,hzfilter]
    rw [he,hZc] at hsc
    omega
  have hrZ : r ∉ Z := by
    intro h
    have he : s=Z := by dsimp [s];rw [insert_eq_of_mem h,hzfilter]
    rw [he,hZc] at hsc
    omega
  exact ⟨Z,hZc,hZ,hr,hrZ⟩
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory Filter
lemma positive_continuous_pairing (f H w : ℝ → ℝ)
    (hf : Continuous f) (hH : Continuous H) (hw : ∀ p,0 < p → 0 < w p)
    (hi : IntegrableOn (fun p=>f (p^2)*H (p^2)*w p) (Set.Ioi 0))
    (hn : ∀ x,0 < x → 0 ≤ f x*H x) (hp : ∃ x,0 < x ∧ 0 < f x*H x) :
    0 < ∫ p in Set.Ioi (0:ℝ),f (p^2)*H (p^2)*w p := by
  let K : ℝ → ℝ := fun p=>f (p^2)*H (p^2)
  let g : ℝ → ℝ := fun p=>K p*w p
  have hgn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0:ℝ))] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    exact mul_nonneg (hn (p^2) (sq_pos_of_pos hp)) (hw p hp).le
  have hK : Continuous K := (hf.comp (continuous_id.pow 2)).mul (hH.comp (continuous_id.pow 2))
  let U : Set ℝ := Set.Ioi 0 ∩ {p | 0 < K p}
  have hopen : IsOpen U := isOpen_Ioi.inter (isOpen_lt continuous_const hK)
  have hune : U.Nonempty := by
    obtain ⟨x,hx,hp⟩ := hp
    refine ⟨Real.sqrt x,Real.sqrt_pos.mpr hx,?_⟩
    dsimp [K]
    rwa [Real.sq_sqrt hx.le]
  have hup : 0 < (volume.restrict (Set.Ioi (0:ℝ))) U := by
    rw [Measure.restrict_apply hopen.measurableSet,Set.inter_eq_left.mpr Set.inter_subset_left]
    exact hopen.measure_pos volume hune
  have hus : U⊆Function.support g := by
    intro p hp
    exact (mul_pos hp.2 (hw p hp.1)).ne'
  exact (integral_pos_iff_support_of_nonneg_ae hgn hi).mpr (hup.trans_le (measure_mono hus))
lemma family_pairing_integral {n : ℕ} (G : ℕ → ℝ → ℝ) (a : Fin n → ℝ) (f w : ℝ → ℝ)
    (hi : ∀ i : Fin n,IntegrableOn (fun p=>f (p^2)*G i (p^2)*w p) (Set.Ioi 0)) :
    IntegrableOn (fun p=>f (p^2)*familyCombination G a (p^2)*w p) (Set.Ioi 0) ∧
    (∫ p in Set.Ioi (0:ℝ),f (p^2)*familyCombination G a (p^2)*w p)=
      ∑ i,a i*(∫ p in Set.Ioi (0:ℝ),f (p^2)*G i (p^2)*w p) := by
  have he : (fun p=>f (p^2)*familyCombination G a (p^2)*w p)=
      fun p=>∑ i,a i*(f (p^2)*G i (p^2)*w p) := by
    funext p
    simp only [familyCombination,mul_sum,sum_mul]
    apply sum_congr rfl
    intro i _
    ring
  have hi' (i : Fin n) := (hi i).const_mul (a i)
  rw [he]
  constructor
  · exact integrable_finsetSum _ (fun i _=>hi' i)
  · rw [integral_finsetSum _ (fun i _=>hi' i)]
    simp only [integral_const_mul]
lemma family_pairing_last {n : ℕ} (G : ℕ → ℝ → ℝ) (a : Fin (n+1) → ℝ) (f w : ℝ → ℝ)
    (hi : ∀ i : Fin (n+1),IntegrableOn (fun p=>f (p^2)*G i (p^2)*w p) (Set.Ioi 0))
    (hz : ∀ i : Fin n,(∫ p in Set.Ioi (0:ℝ),f (p^2)*G i (p^2)*w p)=0) :
    (∫ p in Set.Ioi (0:ℝ),f (p^2)*familyCombination G a (p^2)*w p)=
      a (Fin.last n)*(∫ p in Set.Ioi (0:ℝ),f (p^2)*G n (p^2)*w p) := by
  rw [(family_pairing_integral G a f w hi).2,Fin.sum_univ_castSucc]
  have h : (∑ i : Fin n,a i.castSucc*(∫ p in Set.Ioi (0:ℝ),f (p^2)*G i.castSucc (p^2)*w p))=0 := by
    apply sum_eq_zero
    intro i _
    rw [show G i.castSucc=G i from rfl,hz,mul_zero]
  rw [h,zero_add]
  rfl
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory
/-- Chebyshev interpolation gives positive orientation of a border pairing at a real root. -/
theorem monic_cross_pairing_pos {n : ℕ} (F G : ℕ → ℝ → ℝ) (a : Fin (n+1) → ℝ)
    (w : ℝ → ℝ) (r : ℝ) (hF : PositiveFlag F (n+1)) (hG : PositiveFlag G (n+2))
    (hFc : ∀ i : Fin (n+1),Continuous (F i)) (hGc : ∀ i : Fin (n+2),Continuous (G i))
    (ha : a (Fin.last n)=1) (hw : ∀ p,0 < p → 0 < w p)
    (hi : ∀ i : Fin (n+2),IntegrableOn (fun p=>(p^2-r)*familyCombination F a (p^2)*G i (p^2)*w p) (Set.Ioi 0))
    (ho : ∀ i : Fin (n+1),(∫ p in Set.Ioi (0:ℝ),(p^2-r)*familyCombination F a (p^2)*G i (p^2)*w p)=0) :
    0 < (∫ p in Set.Ioi (0:ℝ),(p^2-r)*familyCombination F a (p^2)*G (n+1) (p^2)*w p) := by
  classical
  have han : a  ≠  0 := by intro he;have hh:=congrFun he (Fin.last n);simp [ha] at hh
  obtain ⟨Z,hZc,hZ,hr,hrZ⟩ := flag_orthogonal_linear_zeros F G a w r (hF _ le_rfl)
    (fun k hk=>hG k (by omega)) hFc (fun i=>hGc i.castSucc) han hw (fun i=>hi i.castSucc) ho
  let o := Z.orderIsoOfFin hZc
  let v : Fin n → ℝ := fun i=>(o i).val
  have hv : StrictMono v := o.strictMono
  have hv0 i : 0 < v i := ((hZ _).mp (o i).property).1
  have haz i : familyCombination F a (v i)=0 := ((hZ _).mp (o i).property).2
  have hprod (x : ℝ) : (∏ i : Fin n,(x-v i))=∏ z ∈ Z,(x-z) := by
    calc
      _ = ∏ z : Z,(x-z.val) := Equiv.prod_comp o.toEquiv (fun z : Z=>x-z.val)
      _ = _ := Finset.prod_attach _ _
  let S := insert r Z
  have hSc : S.card=n+1 := by simp [S,card_insert_of_notMem hrZ,hZc]
  have hS0 : ∀ x ∈ S,0 < x := by
    intro x hx
    rcases mem_insert.mp hx with he|hz
    · exact he ▸ hr
    · exact ((hZ x).mp hz).1
  let q := S.orderIsoOfFin hSc
  let u : Fin (n+1) → ℝ := fun i=>(q i).val
  have hu : StrictMono u := q.strictMono
  have hu0 i : 0 < u i := hS0 _ (q i).property
  have hprodS (x : ℝ) : (∏ i : Fin (n+1),(x-u i))=∏ z ∈ S,(x-z) := by
    calc
      _ = ∏ z : S,(x-z.val) := Equiv.prod_comp q.toEquiv (fun z : S=>x-z.val)
      _ = _ := Finset.prod_attach _ _
  let g : ℝ → ℝ := fun x=>(x-r)*familyCombination F a x
  have hgsign (x : ℝ) (hx : 0 < x) (hxS : x ∉ S) : 0 < g x*(∏ z ∈ S,(x-z)) := by
    have hxZ : x ∉ Z := fun h=>hxS (mem_insert_of_mem h)
    have hxr : x ≠ r := fun h=>hxS (h ▸ mem_insert_self _ _)
    have hxv i : x ≠ v i := fun h=>hxZ (h.symm ▸ (o i).property)
    have hh:=monic_family_sign F a v (hF _ le_rfl) (hF _ (by omega)) ha hv hv0 haz hx hxv
    rw [hprod] at hh
    have hp:=mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hxr)) hh
    dsimp [g,S]
    rw [prod_insert hrZ]
    nlinarith only [hp]
  let e : ℝ := (-1)^(n+1)
  let B : Fin (n+2) → ℝ := fun i=>e*familyTestCoeffs G u i
  have hBl : 0 < B (Fin.last (n+1)) := by
    change 0 < e*familyTestCoeffs G u (Fin.last (n+1))
    rw [familyTestCoeffs_last]
    have hD:=hG (n+1) (by omega) u hu hu0
    have he : e*((-1:ℝ)^(n+1))=1 := by dsimp [e];rw [←pow_add,show n+1+(n+1)=2*(n+1) by omega,pow_mul];norm_num
    rw [←mul_assoc,he,one_mul]
    exact hD
  have hBsign (x : ℝ) (hx : 0 < x) (hxS : x ∉ S) :
      0 < familyCombination G B x*(∏ z ∈ S,(x-z)) := by
    have hxu i : x ≠ u i := fun h=>hxS (h.symm ▸ (q i).property)
    have hh:=familyTest_sign_product G u (hG _ le_rfl) hu hu0 hx hxu
    have hn : (∏ i : Fin (n+1),(u i-x))=e*(∏ z ∈ S,(x-z)) := by
      simp_rw [show ∀ i : Fin (n+1),u i-x=(-1:ℝ)*(x-u i) from fun i=>by ring]
      rw [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,hprodS]
    rw [hn] at hh
    dsimp [B]
    rw [familyCombination_smul]
    nlinarith only [hh]
  have hstrict (x : ℝ) (hx : 0 < x) (hxS : x ∉ S) : 0 < g x*familyCombination G B x := by
    have hh:=mul_pos (hgsign x hx hxS) (hBsign x hx hxS)
    have he : (g x*(∏ z ∈ S,(x-z)))*(familyCombination G B x*(∏ z ∈ S,(x-z)))=
        (g x*familyCombination G B x)*(∏ z ∈ S,(x-z))^2 := by ring
    rw [he] at hh
    exact pos_of_mul_pos_left hh (sq_nonneg _)
  have hn (x : ℝ) (hx : 0 < x) : 0 ≤ g x*familyCombination G B x := by
    by_cases hxS : x ∈ S
    · have hg : g x=0 := by
        rcases mem_insert.mp hxS with h|h
        · simp [g,h]
        · simp [g,((hZ x).mp h).2]
      simp [hg]
    · exact (hstrict x hx hxS).le
  have hp : ∃ x,0 < x ∧ 0 < g x*familyCombination G B x := by
    obtain ⟨R,hR⟩ := (insert 0 S).finite_toSet.bddAbove
    have hR0 : 0 ≤ R := hR (by simp)
    refine ⟨R+1,by linarith,hstrict _ (by linarith) ?_⟩
    intro hh
    have h := hR (mem_insert_of_mem hh)
    linarith
  have hc : Continuous g := (continuous_id.sub continuous_const).mul (familyCombination_continuous F a hFc)
  have hpos := positive_continuous_pairing g (familyCombination G B) w hc
    (familyCombination_continuous G B hGc) hw (family_pairing_integral G B g w hi).1 hn hp
  rw [family_pairing_last G B g w hi ho] at hpos
  exact pos_of_mul_pos_right hpos hBl.le
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset

theorem det_border_last_column {n : ℕ} (B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (h : Fin (n+1) → ℝ) (hh : h (Fin.last n)=1)
    (hz : ∀ i : Fin n,(B *ᵥ h) i.castSucc=0) :
    B.det = (B *ᵥ h) (Fin.last n) *
      (B.submatrix Fin.castSucc Fin.castSucc).det := by
  classical
  let C := updateCol B (Fin.last n) (B *ᵥ h)
  have hdet : C.det=B.det := by
    have he : B *ᵥ h=(fun i=>∑ j,h j • B i j) := by
      ext i
      simp only [mulVec, dotProduct, smul_eq_mul]
      apply sum_congr rfl
      intro j _
      ring
    dsimp [C]
    rw [he,det_updateCol_sum,hh,one_smul]
  rw [←hdet,det_succ_column C (Fin.last n)]
  rw [Fin.sum_univ_castSucc]
  have hz' : ∀ i : Fin n,C i.castSucc (Fin.last n)=0 := by
    intro i
    simpa [C] using hz i
  simp only [hz',mul_zero,zero_mul,sum_const_zero,zero_add]
  have hm : C.submatrix (Fin.last n).succAbove (Fin.last n).succAbove=
      B.submatrix Fin.castSucc Fin.castSucc := by
    ext i j
    simp [C,Fin.succAbove_last]
  rw [hm]
  simp only [C,updateCol_self,Fin.val_last]
  rw [show n+n=2*n by omega,pow_mul]
  norm_num

 theorem det_double_border_at_nullvectors {n : ℕ}
    (B : Matrix (Fin (n+2)) (Fin (n+2)) ℝ)
    (a h : Fin (n+1) → ℝ) (ha : a (Fin.last n)=1) (hh : h (Fin.last n)=1)
    (hla : a ᵥ* (B.submatrix Fin.castSucc Fin.castSucc)=0)
    (hrh : (B.submatrix Fin.castSucc Fin.castSucc) *ᵥ h=0) :
    B.det = - (B.submatrix (fun i : Fin n=>i.castSucc.castSucc)
      (fun i : Fin n=>i.castSucc.castSucc)).det *
      ((Fin.lastCases 0 a) ᵥ* B) (Fin.last (n+1)) *
      (B *ᵥ (Fin.lastCases 0 h)) (Fin.last (n+1)) := by
  classical
  let j : Fin (n+2) := (Fin.last n).castSucc
  let aa : Fin (n+2) → ℝ := Fin.lastCases 0 a
  let C := updateRow B j (aa ᵥ* B)
  have hdet : C.det=B.det := by
    have he : aa ᵥ* B=∑ k,aa k • B k := by
      ext i
      simp only [vecMul, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    dsimp [C]
    rw [he,det_updateRow_sum]
    simp [aa,j,ha]
  have hz (i : Fin (n+1)) : (aa ᵥ* B) i.castSucc=0 := by
    have H:=congrFun hla i
    simpa [vecMul,dotProduct,Fin.sum_univ_castSucc,aa,submatrix_apply] using H
  have hentry (i : Fin (n+1)) : C j i.castSucc=0 := by simpa [C] using hz i
  rw [←hdet,det_succ_row C j,Fin.sum_univ_castSucc]
  simp only [hentry,mul_zero,zero_mul,sum_const_zero,zero_add]
  have hs : (-1:ℝ)^(j.val+(Fin.last (n+1)).val)= -1 := by
    change (-1:ℝ)^(n+(n+1))= -1
    rw [show n+(n+1)=2*n+1 by omega,pow_succ,pow_mul]
    norm_num
  rw [hs]
  let D := C.submatrix j.succAbove (Fin.last (n+1)).succAbove
  have hi (i : Fin n) : j.succAbove i.castSucc=i.castSucc.castSucc := by
    apply Fin.succAbove_castSucc_of_lt
    change i.val<n
    exact i.isLt
  have hj : j.succAbove (Fin.last n)=Fin.last (n+1) := by
    apply Fin.succAbove_ne_last_last
    exact Fin.castSucc_ne_last _
  have hD (i k : Fin (n+1)) : D i k=B (j.succAbove i) k.castSucc := by
    simp [D,C,Fin.succAbove_last]
  have hDz (i : Fin n) : (D *ᵥ h) i.castSucc=0 := by
    have H:=congrFun hrh i.castSucc
    simp only [mulVec,dotProduct,submatrix_apply] at H ⊢
    simp_rw [hD,hi]
    exact H
  have hDl : (D *ᵥ h) (Fin.last n)=
      (B *ᵥ (Fin.lastCases 0 h)) (Fin.last (n+1)) := by
    simp only [mulVec,dotProduct]
    simp_rw [hD,hj]
    conv_rhs => rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_castSucc,Fin.lastCases_last,mul_zero,add_zero]
  have hDP : D.submatrix Fin.castSucc Fin.castSucc=
      B.submatrix (fun i : Fin n=>i.castSucc.castSucc) (fun i : Fin n=>i.castSucc.castSucc) := by
    ext i k
    exact (hD i.castSucc k.castSucc).trans (by rw [hi];rfl)
  change -1*C j (Fin.last (n+1))*D.det= _
  rw [det_border_last_column D h hh hDz,hDl,hDP]
  simp only [C,updateRow_self]
  dsimp [aa]
  ring
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end

end OAI
