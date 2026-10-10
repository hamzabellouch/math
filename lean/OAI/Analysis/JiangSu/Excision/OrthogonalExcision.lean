import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Excision.PureStateOrthogonalExtension
import OAI.Analysis.JiangSu.Excision.PureStateNorming
import OAI.Analysis.JiangSu.Excision.ExcisionTraceProjection
import OAI.Analysis.JiangSu.Nonunital.KernelCutoff

namespace OAI

noncomputable section


namespace NonunitalSI
open Pureness CurrentMain NonunitalGamma PureStateExcision Filter Topology CStarAlgebra
open scoped ComplexOrder ENNReal

variable {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (NormalizedTrace A)] [CompactSpace (NormalizedTrace A)]
variable [TopologicalSpace.SeparableSpace A] (U : Ultrafilter ℕ)
local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U
local notation "D" => Unitization ℂ N
local notation "B" => Unitization ℂ A
local notation "q" => NonunitalGamma.normToTracial (A := A) U
local notation "Q" => unitizedNormToTracial (A := A) U
local notation "ι" => NonunitalGamma.normInclusion (A := A) U
local notation "ρ" => unitizedNormInclusion (A := A) U
local notation "L" => familyLimitTrace (fun τ : NormalizedTrace A => NormalizedTrace.unitized τ) U

theorem pure_state_orthogonal_extension
    (hsimple : NonunitalGamma.TopologicallySimple A)
    (hprojectionless : ∀ p : A,IsStarProjection p → p=0)
    (hcone : AllDenselyFiniteTracesBounded A) (hcmp : NonunitalGamma.StrictComparison hcone)
    (hfree : (U : Filter ℕ) ≤ atTop)
    (E F : N) (he : 0≤E) (hen : ‖E‖≤1) (hsmall : q E=0)
    (hf : 0≤F) (hfn : ‖F‖≤1)
    (hcentral : ∀ a : A,Commute F (ι a))
    (hprojection : IsStarProjection (q F))
    {t : ℝ} (ht : 0<t) (hlarge : ∀ s : ℕ → NormalizedTrace A,2*t ≤ ((L s).functional (q F)).re)
    (φ : B →ₚ[ℂ] ℂ) (hφ1 : φ 1=1)
    (hpure : ofPositiveState φ hφ1∈(realStateCarrier (A := B)).extremePoints ℝ)
    {m : ℕ} (r : Fin m → N) (hr : ∀ i,q (r i)=0) :
    ∃ z : N,‖z‖≤1 ∧ star z*z=E ∧ F*z=z ∧
      (∀ a : B,star (Unitization.inr z)*ρ a*Unitization.inr z=φ a • Unitization.inr E) ∧
      (∀ i a,star (Unitization.inr (r i))*ρ a*Unitization.inr z=0) ∧
      (∀ i a,star (Unitization.inr z)*ρ a*Unitization.inr (r i)=0) := by
  classical
  obtain ⟨d,hd,hdp,hdn,hdr,hdF,hdA⟩ := trace_kernel_cutoff_finite U hfree F r hr
  let G : D := (1-Unitization.inr d)*Unitization.inr F*(1-Unitization.inr d)
  have hgp0 : 0≤(Unitization.inr F : D) := Unitization.inr_nonneg_iff.mpr hf
  have hgpn : ‖(Unitization.inr F : D)‖≤1 := by simpa only [Unitization.norm_inr] using hfn
  obtain ⟨hgp,hgn,hgF⟩ := CStarExcision.cutoff_preserves_bound hgp0 hgpn
    (Unitization.inr_nonneg_iff.mpr hdp : (0 : D)≤Unitization.inr d)
    (by simpa only [Unitization.norm_inr] using hdn)
    (hdF.map (Unitization.inrNonUnitalStarAlgHom ℂ N))
  have hG0 : G.fst=0 := by
    simp only [G,Unitization.fst_mul,
      Unitization.fst_inr,mul_zero,zero_mul]
  let g : N := G.snd
  have hg : (Unitization.inr g : D)=G := inr_snd_of_fst_eq_zero G hG0
  have hqg : q g=q F := by
    rw [←unitizedNormToTracial_inr,hg]
    simp only [G,map_mul,map_sub,map_one,unitizedNormToTracial_inr,hd,sub_zero,one_mul,mul_one]
  have hgc (a : B) : Commute G (ρ a) :=
    (((Commute.one_left _).sub_left (commute_unitizedInclusion U d hdA a)).mul_left
      (commute_unitizedInclusion U F hcentral a)).mul_left
        ((Commute.one_left _).sub_left (commute_unitizedInclusion U d hdA a))
  have hgcA (a : A) : g*ι a=ι a*g := by
    apply Unitization.inr_injective (R := ℂ)
    simpa only [Unitization.inr_mul,hg,unitizedNormInclusion_inr] using (hgc (Unitization.inr a)).eq
  obtain ⟨z,hzn,hze,hgz,hza⟩ := pure_state_excision_of_trace_projection U hsimple hprojectionless hcone hcmp hfree
    E g he hen hsmall (Unitization.inr_nonneg_iff.mp (hg.symm ▸ hgp))
    (by rw [←Unitization.norm_inr (𝕜 := ℂ),hg]; exact hgn) hgcA
    (by rwa [hqg]) ht (fun s => by simpa only [hqg] using hlarge s) φ hφ1 hpure
  have hgZ : G*Unitization.inr z=Unitization.inr z := by
    rw [←hg,←Unitization.inr_mul,hgz]
  have hfZ : (Unitization.inr F : D)*Unitization.inr z=Unitization.inr z :=
    CStarExcision.support_monotone ((norm_le_one_iff_of_nonneg _ hgp0).mp hgpn) hgF hgZ
  have hfz : F*z=z := Unitization.inr_injective (R := ℂ) (by simpa only [Unitization.inr_mul] using hfZ)
  have hgr (i : Fin m) : G*Unitization.inr (r i)=0 := by
    simp only [G,mul_assoc,sub_mul,one_mul,←Unitization.inr_mul,hdr i,sub_self,mul_zero]
  have hrG (i : Fin m) : star (Unitization.inr (r i))*G=0 := by
    have hGstar : star G=G := hgp.star_eq
    simpa only [star_mul,hGstar,star_zero] using congrArg star (hgr i)
  have horth (i : Fin m) (a : B) : star (Unitization.inr (r i))*ρ a*Unitization.inr z=0 := by
    calc
      _=star (Unitization.inr (r i))*ρ a*(G*Unitization.inr z) := by rw [hgZ]
      _=star (Unitization.inr (r i))*(ρ a*G)*Unitization.inr z := by noncomm_ring
      _=star (Unitization.inr (r i))*(G*ρ a)*Unitization.inr z := by rw [(hgc a).eq]
      _=(star (Unitization.inr (r i))*G)*ρ a*Unitization.inr z := by noncomm_ring
      _=0 := by rw [hrG,zero_mul,zero_mul]
  refine ⟨z,hzn,hze,hfz,excision_unitizedInclusion U E z hze φ hφ1 hza,horth,?_⟩
  intro i a
  have hh := congrArg star (horth i (star a))
  simpa only [star_mul,map_star,star_star,star_zero,mul_assoc] using hh

end NonunitalSI


namespace NonunitalSI
open Pureness CurrentMain NonunitalGamma PureStateExcision Filter Topology CStarAlgebra NuclearNorm CStarExcision
open scoped ComplexOrder ENNReal

variable {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (NormalizedTrace A)] [CompactSpace (NormalizedTrace A)] [TopologicalSpace.SeparableSpace A]
variable (U : Ultrafilter ℕ)
local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U
local notation "D" => Unitization ℂ N
local notation "B" => Unitization ℂ A
local notation "q" => NonunitalGamma.normToTracial (A := A) U
local notation "Q" => unitizedNormToTracial (A := A) U
local notation "ρ" => unitizedNormInclusion (A := A) U
local notation "ι" => NonunitalGamma.normInclusion (A := A) U
local notation "L" => familyLimitTrace (fun τ : NormalizedTrace A => NormalizedTrace.unitized τ) U

 theorem nuclear_list_excision
    (hsimple : NonunitalGamma.TopologicallySimple A)
    (hprojectionless : ∀ p : A,IsStarProjection p → p=0)
    (hcone : AllDenselyFiniteTracesBounded A) (hcmp : NonunitalGamma.StrictComparison hcone)
    (hfree : (U : Filter ℕ) ≤ atTop)
    (E F : N) (he : 0≤E) (hen : ‖E‖≤1) (hsmall : q E=0)
    (hec : ∀ a : A,Commute E (ι a))
    (hf : 0≤F) (hfn : ‖F‖≤1) (hfc : ∀ a : A,Commute F (ι a))
    (hprojection : IsStarProjection (q F))
    {t : ℝ} (ht : 0<t) (hlarge : ∀ s : ℕ → NormalizedTrace A,2*t ≤ ((L s).functional (q F)).re)
    (φ : B →ₚ[ℂ] ℂ) (hφ1 : φ 1=1)
    (hpure : ofPositiveState φ hφ1∈(realStateCarrier (A := B)).extremePoints ℝ)
    (R : List (StateRow (A := B))) :
    ∃ v : N,q v=0 ∧ F*v=v ∧ ∀ a : selfAdjoint B,
      star (Unitization.inr v)*ρ (a:B)*Unitization.inr v=
        ρ (stateRowSum φ R a :B)*Unitization.inr E := by
  classical
  induction R with
  | nil =>
    refine ⟨0,map_zero q,mul_zero F,?_⟩
    intro a
    simp [stateRowSum]
  | cons R S ih =>
    obtain ⟨v,hvq,hvF,hv⟩ := ih
    obtain ⟨z,_hzn,hze,hzF,hz,hvz,_hzv⟩ := pure_state_orthogonal_extension U hsimple hprojectionless hcone hcmp hfree
      E F he hen hsmall hf hfn hfc hprojection ht hlarge φ hφ1 hpure
      (fun _ : Fin 1 => v) (fun _ => hvq)
    have hzq : q z=0 := by
      apply (CStarRing.star_mul_self_eq_zero_iff _).mp
      rw [←map_star,←map_mul,hze,hsmall]
    let W : D := stateRowElement (ρ).toNonUnitalStarAlgHom R (Unitization.inr z)
    have hW0 : W.fst=0 := by
      change (Unitization.fstHom ℂ N) W=0
      simp only [W,stateRowElement,assembled,map_sum,map_mul,Unitization.fstHom_apply,
        Unitization.fst_inr,mul_zero,zero_mul,Finset.sum_const_zero]
    let w : N := W.snd
    have hwI : (Unitization.inr w : D)=W := inr_snd_of_fst_eq_zero W hW0
    have hwq : q w=0 := by
      rw [←unitizedNormToTracial_inr,hwI]
      simp only [W,stateRowElement,assembled,map_sum,map_mul,unitizedNormToTracial_inr,
        hzq,mul_zero,zero_mul,Finset.sum_const_zero]
    have hwF : F*w=w := by
      apply Unitization.inr_injective (R := ℂ)
      rw [Unitization.inr_mul,hwI]
      exact stateRowElement_support (ρ).toNonUnitalStarAlgHom R (Unitization.inr F) (Unitization.inr z)
        (fun a => (commute_unitizedInclusion U F hfc a).eq)
        (by rw [←Unitization.inr_mul,hzF])
    have hw (a : selfAdjoint B) : star W*ρ (a:B)*W=ρ (R.map φ a : B)*Unitization.inr E :=
      stateRowElement_compress (ρ).toNonUnitalStarAlgHom R φ (Unitization.inr z) (Unitization.inr E)
        (fun a => (commute_unitizedInclusion U E hec a).eq) hz a
    have hcross (a : B) : star (Unitization.inr v)*ρ a*W=0 :=
      stateRowElement_cross (ρ).toNonUnitalStarAlgHom R (Unitization.inr v) (Unitization.inr z) (hvz 0) a
    have hcross' (a : selfAdjoint B) : star W*ρ (a:B)*Unitization.inr v=0 := by
      have hh := congrArg star (hcross (a:B))
      simpa only [star_mul,←map_star,a.property.star_eq,star_star,star_zero,mul_assoc] using hh
    refine ⟨w+v,by rw [map_add,hwq,hvq,add_zero],by rw [mul_add,hwF,hvF],?_⟩
    intro a
    rw [Unitization.inr_add,hwI]
    calc
      star (W+Unitization.inr v)*ρ (a:B)*(W+Unitization.inr v)=
          star W*ρ (a:B)*W+star (Unitization.inr v)*ρ (a:B)*Unitization.inr v := by
        simp only [star_add,add_mul,mul_add,hcross (a:B),hcross' a,add_zero,zero_add]
      _=ρ (R.map φ a : B)*Unitization.inr E+ρ (stateRowSum φ S a : B)*Unitization.inr E := by rw [hw,hv]
      _=ρ (stateRowSum φ (R::S) a : B)*Unitization.inr E := by
        change ρ (R.map φ a : B)*Unitization.inr E+ρ (stateRowSum φ S a : B)*Unitization.inr E =
          ρ ((R.map φ a : B)+(stateRowSum φ S a : B))*Unitization.inr E
        rw [map_add,add_mul]

end NonunitalSI


namespace NonunitalSI
open Pureness CurrentMain NonunitalGamma PureStateExcision
open scoped ComplexOrder InnerProductSpace ComplexStarModule

section Norming
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
 theorem exists_pure_positive_state_norming [Nontrivial A] (a : A) (ha : 0≤a) :
    ∃ (f : A →ₚ[ℂ] ℂ) (hf : f 1=1),
      ofPositiveState f hf∈(realStateCarrier (A := A)).extremePoints ℝ ∧ f a=(‖a‖:ℂ) := by
  let a₀ : selfAdjoint A := ⟨a,IsSelfAdjoint.of_nonneg ha⟩
  let F : Set (WeakDual ℝ (selfAdjoint A)) := realStateCarrier∩{f | f a₀=‖a‖}
  have hcompact : IsCompact F := realStateCarrier_isCompact.inter_right
    (isClosed_eq (WeakDual.eval_continuous a₀) continuous_const)
  have hnonempty : F.Nonempty := by
    obtain ⟨f,hf,hfa⟩ := Pureness.exists_positiveState_norming a ha
    refine ⟨ofPositiveState f hf,ofPositiveState_mem f hf,?_⟩
    change (f a).re=‖a‖
    rw [hfa,Complex.ofReal_re]
  have hle (f : WeakDual ℝ (selfAdjoint A)) (hf : f∈realStateCarrier) : f a₀≤‖a‖ := by
    calc
      f a₀≤‖f a₀‖ := le_abs_self _
      _≤‖f.toStrongDual‖*‖a₀‖ := f.toStrongDual.le_opNorm a₀
      _≤1*‖a₀‖ := mul_le_mul_of_nonneg_right hf.2 (norm_nonneg _)
      _=‖a‖ := one_mul _
  have hextreme : IsExtreme ℝ realStateCarrier F := by
    refine ⟨Set.inter_subset_left,?_⟩
    intro x hx y hy z hz hseg
    refine ⟨hx,?_⟩
    rcases hseg with ⟨r,s,hr,hs,hrs,heq⟩
    have hv := congrArg (fun g : WeakDual ℝ (selfAdjoint A) => g a₀) heq
    change r*x a₀+s*y a₀=z a₀ at hv
    rw [hz.2] at hv
    have hx' := hle x hx
    have hy' := hle y hy
    have hnorm := congrArg (fun u : ℝ => u*‖a‖) hrs
    have hys := mul_nonneg hs.le (sub_nonneg.mpr hy')
    apply le_antisymm hx'
    by_contra! hlt
    have hpos := mul_pos hr (sub_pos.mpr hlt)
    nlinarith
  let : LocallyConvexSpace ℝ (WeakDual ℝ (selfAdjoint A)) := WeakBilin.locallyConvexSpace
  obtain ⟨g,hg⟩ := hcompact.extremePoints_nonempty hnonempty
  have hgs := hextreme.extremePoints_subset_extremePoints hg
  refine ⟨toPositiveState g hgs.1,toPositiveState_one g hgs.1,?_,?_⟩
  · rw [ofPositiveState_toPositiveState]; exact hgs
  · change toPositiveState g hgs.1 (a₀:A)=_
    rw [toPositiveState_apply,hg.1.2]

end Norming

variable {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A]

theorem exists_faithful_pure_unitized_state
    (hsimple : NonunitalGamma.TopologicallySimple A)
    (hprojectionless : ∀ p : A,IsStarProjection p → p=0) :
    ∃ (φ : Unitization ℂ A →ₚ[ℂ] ℂ) (hφ1 : φ 1=1),
      ofPositiveState φ hφ1∈(realStateCarrier (A := Unitization ℂ A)).extremePoints ℝ ∧
      Function.Injective φ.gnsStarAlgHom := by
  obtain ⟨a,ha⟩ := exists_ne (0 : A)
  let b : A := star a*a
  have hb : b≠0 := fun h => ha ((CStarRing.star_mul_self_eq_zero_iff a).mp h)
  obtain ⟨φ,hφ1,hpure,hφ⟩ := exists_pure_positive_state_norming
    (Unitization.inr b : Unitization ℂ A) (Unitization.inr_nonneg_iff.mpr (star_mul_self_nonneg a))
  refine ⟨φ,hφ1,hpure,?_⟩
  apply unitization_representation_injective hsimple hprojectionless φ.gnsStarAlgHom
  refine ⟨b,?_⟩
  intro hz
  have hv := Pureness.stateGNS_vector_value φ (Unitization.inr b)
  rw [hz,zero_apply,inner_zero_right,hφ] at hv
  have hbn : ‖b‖=0 := by
    have h := congrArg Complex.re hv
    simpa only [Complex.zero_re,Complex.ofReal_re,Unitization.norm_inr] using h.symm
  exact hb (norm_eq_zero.mp hbn)

end NonunitalSI

end

end OAI
