import Mathlib
import OAI.Geometry.BallPacking.Fredholm.CompactFredholmAlternative
import OAI.Geometry.BallPacking.Necessity.LocalCharts

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity
section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E]
local instance finiteReductionInst1 : NormedAddCommGroup (HolderSpace ℂ E ((1:ℝ)/3)) := inferInstance
local instance finiteReductionInst2 : NormedSpace ℝ (HolderSpace ℂ E ((1:ℝ)/3)) := inferInstance
local instance finiteReductionInst3 : NormedAddCommGroup (HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3)) := inferInstance
local instance finiteReductionInst4 : NormedSpace ℝ (HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3)) := inferInstance
local instance finiteReductionInst5 (R : ℝ) : NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
local instance finiteReductionInst6 (R : ℝ) : NormedSpace ℝ (CompactHolderSpace E R) := inferInstance

 

def compactHolderMul (R : ℝ) (A : HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3)) :
    CompactHolderSpace E R →L[ℝ] CompactHolderSpace E R :=
  ((holderCLM ((1:ℝ)/3) A).comp (compactHolderSubmodule R).subtypeL).codRestrict
    (compactHolderSubmodule R) (by
      intro g z hz
      change holderValue ((1:ℝ)/3) A z (holderValue ((1:ℝ)/3) g.val z)=0
      rw [g.property z hz,map_zero])

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
@[simp] lemma compactHolderMul_value (R : ℝ)
    (A : HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3)) (g : CompactHolderSpace E R) (z : ℂ) :
    compactHolderValue R (compactHolderMul R A g) z =
      holderValue ((1:ℝ)/3) A z (compactHolderValue R g z) := rfl

lemma frameInverse_smooth {η : E → E →L[ℝ] E →L[ℝ] ℝ}
    {B : E →L[ℝ] E} {J : E → E →L[ℝ] E} {u : ℂ → E}
    (hB : ∀ x, CompatibleWith (η x) B) (hJc : ∀ x, CompatibleWith (η x) (J x))
    (hJ : ContDiff ℝ ∞ J) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (fun z => (crFrame B J u z).inverse) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  exact (crFrame_invertible hB hJc u z).contDiffAt_map_inverse.comp z
    (crFrame_smooth hJ hu).contDiffAt

omit [CompleteSpace E] in
lemma frameInverse_compact_difference {η : E → E →L[ℝ] E →L[ℝ] ℝ}
    {B : E →L[ℝ] E} {J : E → E →L[ℝ] E} {u : ℂ → E}
    (hB : ∀ x, CompatibleWith (η x) B) (hJc : ∀ x, CompatibleWith (η x) (J x))
    (hc : HasCompactSupport (fun x => J x-B)) (hup : IsProperMap u) :
    HasCompactSupport (fun z => (crFrame B J u z).inverse-
      (1/2:ℝ) • ContinuousLinearMap.id ℝ E) := by
  have hh := crFrame_compact_difference (hB 0).1 hc hup
  rw [hasCompactSupport_iff_eventuallyEq] at hh ⊢
  filter_upwards [hh] with z hz
  have hA : crFrame B J u z=2 • ContinuousLinearMap.id ℝ E := sub_eq_zero.mp hz
  apply sub_eq_zero.mpr
  ext v
  have hv : crFrame B J u z ((1/2:ℝ) • v)=v := by
    rw [hA]
    simp only [smul_apply,ContinuousLinearMap.id_apply]
    module
  have hd := (crFrame_invertible hB hJc u z).inverse_apply_self ((1/2:ℝ) • v)
  rw [hv] at hd
  exact hd

 

def inverseFrameHolder {η : E → E →L[ℝ] E →L[ℝ] ℝ}
    {B : E →L[ℝ] E} {J : E → E →L[ℝ] E} {u : ℂ → E}
    (hB : ∀ x, CompatibleWith (η x) B) (hJc : ∀ x, CompatibleWith (η x) (J x))
    (hJ : ContDiff ℝ ∞ J) (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport (fun x => J x-B)) (hup : IsProperMap u) :
    HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3) :=
  holderConst ((1:ℝ)/3) ((1/2:ℝ) • ContinuousLinearMap.id ℝ E)+
    smoothHolderField (fun z => (crFrame B J u z).inverse-(1/2:ℝ) • ContinuousLinearMap.id ℝ E)
      ((frameInverse_smooth hB hJc hJ hu).sub contDiff_const)
      (frameInverse_compact_difference hB hJc hc hup)

@[simp] lemma inverseFrameHolder_value {η : E → E →L[ℝ] E →L[ℝ] ℝ}
    {B : E →L[ℝ] E} {J : E → E →L[ℝ] E} {u : ℂ → E}
    (hB : ∀ x, CompatibleWith (η x) B) (hJc : ∀ x, CompatibleWith (η x) (J x))
    (hJ : ContDiff ℝ ∞ J) (hu : ContDiff ℝ ∞ u)
    (hc : HasCompactSupport (fun x => J x-B)) (hup : IsProperMap u) (z : ℂ) :
    holderValue ((1:ℝ)/3) (inverseFrameHolder hB hJc hJ hu hc hup) z =
      (crFrame B J u z).inverse := by
  simp only [inverseFrameHolder,map_add,BoundedContinuousFunction.add_apply,
    smoothHolderField_value]
  change (1/2:ℝ) • ContinuousLinearMap.id ℝ E+
    ((crFrame B J u z).inverse-(1/2:ℝ) • ContinuousLinearMap.id ℝ E)=_
  abel

end

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E]
local instance finiteReductionInst7 (α : ℝ) : NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance
local instance finiteReductionInst8 (α : ℝ) : NormedSpace ℝ (HolderSpace ℂ E α) := inferInstance
local instance finiteReductionInst9 (α : ℝ) : NormedAddCommGroup (C1HolderSpace E α) := inferInstance
local instance finiteReductionInst10 (α : ℝ) : NormedSpace ℝ (C1HolderSpace E α) := inferInstance
local instance finiteReductionInst11 (R : ℝ) : NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
local instance finiteReductionInst12 (R : ℝ) : NormedSpace ℝ (CompactHolderSpace E R) := inferInstance

 

theorem exists_normalized_nonlinear_chart
    {η : E → E →L[ℝ] E →L[ℝ] ℝ} {J : E → E →L[ℝ] E}
    (hB : ∀ x, CompatibleWith (η x) ((ContinuousLinearMap.lsmul ℝ ℂ) Complex.I))
    (hJc : ∀ x, CompatibleWith (η x) (J x)) (hJ : ContDiff ℝ ∞ J)
    (hc : HasCompactSupport (fun x => J x-(ContinuousLinearMap.lsmul ℝ ℂ) Complex.I))
    (p : (E × (ℂ →L[ℝ] E)) × C1HolderSpace E ((1:ℝ)/3))
    (hu : ContDiff ℝ ∞ (c1HolderAffineCurve ((1:ℝ)/3) p.1.1 p.1.2 p.2))
    (hup : IsProperMap (c1HolderAffineCurve ((1:ℝ)/3) p.1.1 p.1.2 p.2))
    (m : ℝ) (hm : 0 < m) (hA : ∀ z, m*‖z‖ ≤ ‖p.1.2 z‖)
    (hsol : ∀ z, crOperator J (c1HolderAffineCurve ((1:ℝ)/3) p.1.1 p.1.2 p.2) z=0) :
    let u := c1HolderAffineCurve ((1:ℝ)/3) p.1.1 p.1.2 p.2
    let B : E →L[ℝ] E := (ContinuousLinearMap.lsmul ℝ ℂ) Complex.I
    ∃ S : ℝ, 0 < S ∧ (∀ z : ℂ, S < ‖z‖ → normalizedFrameCoefficient B J u z=0) ∧
      ∀ R : ℝ, S ≤ R → ∃ F : CompactHolderSpace E R → CompactHolderSpace E R,
        ContDiffAt ℝ ∞ F 0 ∧ F 0=0 ∧ (fderiv ℝ F 0).IsFredholm ∧
        (∀ᶠ g in 𝓝 (0 : CompactHolderSpace E R), ∀ z,
          compactHolderValue R (F g) z=(crFrame B J u z).inverse
            (crOperator J (fun w => u w+framedMarkedVariation J u R g w) z)) ∧
        (∀ g z, compactHolderValue R (fderiv ℝ F 0 g) z=
          compactHolderValue R g z+normalizedFrameCoefficient B J u z (markedCRInverse R g z)) := by
  dsimp only
  let u := c1HolderAffineCurve ((1:ℝ)/3) p.1.1 p.1.2 p.2
  let B : E →L[ℝ] E := (ContinuousLinearMap.lsmul ℝ ℂ) Complex.I
  let Ainf : E →L[ℝ] E := 2 • ContinuousLinearMap.id ℝ E
  let P := fun z => crFrame B J u z-Ainf
  have hP : ContDiff ℝ ∞ P := (crFrame_smooth hJ hu).sub contDiff_const
  have hPc : HasCompactSupport P := crFrame_compact_difference (hB 0).1 hc hup
  have hAinf : ∀ v, Ainf (Complex.I • v)=Complex.I • Ainf v := by
    intro v
    simp only [Ainf,two_smul,add_apply,ContinuousLinearMap.id_apply,smul_add]
  have hPF (w : ℂ) : Ainf+P w=crFrame B J u w := by dsimp only [P]; abel
  obtain ⟨S₀,hS₀,hS₀R⟩ := compactMarkedCR_local_chart Ainf hAinf P hP hPc J hJ hc p m hm hA hsol
  let M := normalizedFrameCoefficient B J u
  have hMs : ContDiff ℝ ∞ M := normalizedFrameCoefficient_smooth hB hJc hJ hu
  have hMc : HasCompactSupport M := normalizedFrameCoefficient_compact (hB 0).1 hc hup
  obtain ⟨S₁,hS₁,hM₁⟩ := compactCoefficient_zero_outside hMc
  let S := max S₀ S₁
  have hM : ∀ z : ℂ, S < ‖z‖ → M z=0 := fun z hz =>
    hM₁ z ((le_max_right _ _).trans hz.le)
  refine ⟨S,lt_of_lt_of_le hS₀ (le_max_left _ _),hM,?_⟩
  intro R hR
  obtain ⟨hC,hCe,hCD⟩ := hS₀R R ((le_max_left _ _).trans hR)
  let C := compactMarkedCR R Ainf P hP hPc J hJ hc p
  let U := compactHolderMul R (inverseFrameHolder hB hJc hJ hu hc hup)
  let F := U ∘ C
  have hFs : ContDiffAt ℝ ∞ F 0 := U.contDiff.contDiffAt.comp 0 hC
  have hFD : HasFDerivAt F (U.comp (fderiv ℝ C 0)) 0 :=
    U.hasFDerivAt.comp 0 (hC.differentiableAt (by simp)).hasFDerivAt
  have hMv : ∀ z : ℂ, R < ‖z‖ → M z=0 := fun z hz => hM z (lt_of_le_of_lt hR hz)
  let T := markedCRLinear R M hMs hMc hMv
  have hDF : fderiv ℝ F 0=T := by
    rw [hFD.fderiv]
    apply ContinuousLinearMap.ext
    intro g
    apply Subtype.ext
    apply holderValue_injective ((1:ℝ)/3)
    ext z
    change compactHolderValue R (U (fderiv ℝ C 0 g)) z=compactHolderValue R (T g) z
    rw [compactHolderMul_value,inverseFrameHolder_value,hCD g z]
    simp only [hPF]
    rw [linearizedCR_normalizedFrame hB hJc
      ((crFrame_smooth hJ hu).differentiable (by simp))
      (markedCRInverse_differentiable R g) z,
      (crFrame_invertible hB hJc u z).inverse_apply_self]
    symm
    exact markedCRLinear_differential R M hMs hMc hMv g z
  have hFe : ∀ᶠ g in 𝓝 (0 : CompactHolderSpace E R), ∀ z,
      compactHolderValue R (F g) z=(crFrame B J u z).inverse
        (crOperator J (fun w => u w+framedMarkedVariation J u R g w) z) := by
    filter_upwards [hCe] with g hg
    intro z
    change compactHolderValue R (U (C g)) z=_
    rw [compactHolderMul_value,inverseFrameHolder_value,hg z]
    simp only [hPF]
    rfl
  have hF0 : F 0=0 := by
    apply Subtype.ext
    apply holderValue_injective ((1:ℝ)/3)
    ext z
    change compactHolderValue R (F 0) z=0
    rw [hFe.self_of_nhds z]
    have he : (fun w => u w+framedMarkedVariation J u R 0 w)=u := by
      funext w
      simp only [framedMarkedVariation,markedCRInverse,compactCRInverseValue,map_zero,
        BoundedContinuousFunction.coe_zero,Pi.zero_apply,sub_self,smul_zero,add_zero]
    rw [he,hsol z,map_zero]
  refine ⟨F,hFs,hF0,?_,hFe,?_⟩
  · rw [hDF]
    exact markedCRLinear_fredholm R M hMs hMc hMv
  · intro g z
    rw [hDF]
    change compactHolderValue R (markedCRLinear R M hMs hMc hMv g) z=_
    change compactHolderValue R g z+compactHolderValue R (markedCRLower R M hMs hMc hMv g) z=_
    rw [markedCRLower_value]

end
 

open scoped ContDiff Topology
open Set Function Filter

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter

 

theorem AffineLineCurve.exists_holder_profile {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u)
    (hJc : HasCompactSupport (fun x => J x-standardJ n)) :
    ∃ (b v : Phase n) (h : C1HolderSpace (Phase n) ((1:ℝ)/3)), v ≠ 0 ∧
      u = c1HolderAffineCurve ((1:ℝ)/3) b
        (((ContinuousLinearMap.id ℂ ℂ).smulRight v).restrictScalars ℝ) h := by
  obtain ⟨v,hv,hlim⟩ := hu.2.2.2.2
  let V := infinityGerm u v
  have hV : AnalyticAt ℂ V 0 := infinityGerm_analyticAt (hu.holomorphic_at_infinity hJc) hlim
  have hV0 : V 0=v := by simp [V,infinityGerm]
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝[≠] (0:ℂ)) := by
    rw [←Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_cobounded'
  have hconst : Tendsto (fun z => u z-z • v) (cocompact ℂ) (𝓝 (deriv V 0)) := by
    have hd := hV.differentiableAt.hasDerivAt.tendsto_slope.comp hi
    apply hd.congr'
    filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz
    have hz0 : z ≠ 0 := by simpa using hz
    simp only [Function.comp_apply,slope_def_module,sub_zero,inv_inv,hV0]
    simp only [V,infinityGerm,inv_ne_zero hz0,ite_false,inv_inv,smul_sub,smul_smul,
      mul_inv_cancel₀ hz0,one_smul]
  let g := crOperator (fun _ => standardJ n) u
  have hgs : ContDiff ℝ ∞ g := by
    have hd := hu.1.fderiv_right (show (∞ : WithTop ℕ∞)+1≤∞ by simp)
    exact (hd.clm_apply contDiff_const).sub
      (contDiff_const.clm_apply (hd.clm_apply contDiff_const))
  have hgc : HasCompactSupport g := by
    rw [hasCompactSupport_iff_eventuallyEq,coclosedCompact_eq_cocompact]
    filter_upwards [hu.holomorphic_at_infinity hJc] with z hz
    exact sub_eq_zero.mpr (differentiableAt_complex_iff_differentiableAt_real.mp hz).2
  obtain ⟨R,hR,hgR⟩ := compactCoefficient_zero_outside hgc
  let G : CompactHolderSpace (Phase n) R :=
    ⟨compactSmoothHolder ((1:ℝ)/3) (by positivity) (by norm_num) g hgs hgc,
      fun z hz => hgR z hz.le⟩
  have hG (z : ℂ) : compactHolderValue R G z=g z := rfl
  let h := compactCRInverse R G
  let f := compactCRInverseValue R G
  have hf : Differentiable ℝ f := (compactCRInverse_contDiff R G).differentiable (by simp)
  have hholo : Differentiable ℂ (fun z => u z-f z) := by
    intro z
    have hd := ((hu.1.differentiable (by simp) z).hasFDerivAt).sub ((hf z).hasFDerivAt)
    apply differentiableAt_complex_iff_differentiableAt_real.mpr
    refine ⟨hd.differentiableAt,?_⟩
    change fderiv ℝ (u-(f : ℂ → Phase n)) z Complex.I =
      Complex.I • fderiv ℝ (u-(f : ℂ → Phase n)) z 1
    rw [hd.fderiv]
    simp only [sub_apply,smul_sub]
    have he := compactCRInverse_rightInverse R G z
    rw [hG] at he
    change fderiv ℝ f z Complex.I-Complex.I • fderiv ℝ f z 1 =
      fderiv ℝ u z Complex.I-Complex.I • fderiv ℝ u z 1 at he
    exact sub_eq_sub_iff_sub_eq_sub.mp he.symm
  have hl : Tendsto (fun z => (u z-f z)-z • v) (cocompact ℂ) (𝓝 (deriv V 0)) := by
    have ht := hconst.sub (compactCRInverse_tendsto_zero R G)
    simpa only [sub_zero,sub_right_comm] using ht
  have he (z : ℂ) : (u z-f z)-z • v=deriv V 0 :=
    (hholo.sub (differentiable_id.smul_const v)).apply_eq_of_tendsto_cocompact z hl
  refine ⟨deriv V 0,v,h,hv,?_⟩
  funext z
  change u z=deriv V 0+z • v+f z
  rw [←he z]
  abel


open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
section
local instance finiteReductionInst13 (n : ℕ) (R : ℝ) : NormedAddCommGroup (CompactHolderSpace (Phase n) R) := inferInstance
local instance finiteReductionInst14 (n : ℕ) (R : ℝ) : NormedSpace ℝ (CompactHolderSpace (Phase n) R) := inferInstance

 

theorem AffineLineCurve.exists_nonlinear_fredholm_section {n : ℕ}
    {η : Phase n → Phase n →L[ℝ] Phase n →L[ℝ] ℝ} {J : Phase n → End n}
    (hB : ∀ x, CompatibleWith (η x) (standardJ n))
    (hJc : ∀ x, CompatibleWith (η x) (J x)) (hJ : ContDiff ℝ ∞ J)
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u) :
    ∃ S : ℝ, 0 < S ∧
      (∀ z : ℂ, S < ‖z‖ → normalizedFrameCoefficient (standardJ n) J u z=0) ∧
      ∀ R : ℝ, S ≤ R → ∃ F : CompactHolderSpace (Phase n) R → CompactHolderSpace (Phase n) R,
        ContDiffAt ℝ ∞ F 0 ∧ F 0=0 ∧ (fderiv ℝ F 0).IsFredholm ∧
        (∀ᶠ g in 𝓝 (0 : CompactHolderSpace (Phase n) R), ∀ z,
          compactHolderValue R (F g) z=(crFrame (standardJ n) J u z).inverse
            (crOperator J (fun w => u w+framedMarkedVariation J u R g w) z)) ∧
        (∀ g z, compactHolderValue R (fderiv ℝ F 0 g) z=
          compactHolderValue R g z+normalizedFrameCoefficient (standardJ n) J u z (markedCRInverse R g z)) := by
  obtain ⟨b,v,h,hv,he⟩ := hu.exists_holder_profile hc
  let A := ((ContinuousLinearMap.id ℂ ℂ).smulRight v).restrictScalars ℝ
  let P : (Phase n × (ℂ →L[ℝ] Phase n)) × C1HolderSpace (Phase n) ((1:ℝ)/3) := ((b,A),h)
  have hA (z : ℂ) : ‖v‖*‖z‖≤‖A z‖ := by
    change ‖v‖*‖z‖≤‖z • v‖
    rw [norm_smul,mul_comm]
  have hs (z : ℂ) : crOperator J u z=0 := by
    have hh := (hu.2.1 z).2 1
    simp only [mul_one] at hh
    exact sub_eq_zero.mpr hh
  have hu' : u=c1HolderAffineCurve ((1:ℝ)/3) P.1.1 P.1.2 P.2 := he
  have hh := exists_normalized_nonlinear_chart hB hJc hJ hc P
    (hu' ▸ hu.1) (hu' ▸ hu.isProperMap) ‖v‖ (norm_pos_iff.mpr hv) hA (hu' ▸ hs)
  simpa only [←hu',standardJ] using hh

 

theorem local_section_zero_iff {n : ℕ}
    {η : Phase n → Phase n →L[ℝ] Phase n →L[ℝ] ℝ} {J : Phase n → End n}
    (hB : ∀ x, CompatibleWith (η x) (standardJ n))
    (hJc : ∀ x, CompatibleWith (η x) (J x)) {u : ℂ → Phase n} {R : ℝ}
    {F : CompactHolderSpace (Phase n) R → CompactHolderSpace (Phase n) R}
    {g : CompactHolderSpace (Phase n) R}
    (hF : ∀ z, compactHolderValue R (F g) z=(crFrame (standardJ n) J u z).inverse
      (crOperator J (fun w => u w+framedMarkedVariation J u R g w) z)) :
    F g=0 ↔ ∀ z, crOperator J (fun w => u w+framedMarkedVariation J u R g w) z=0 := by
  constructor
  · intro hg z
    have hh := hF z
    rw [hg,map_zero,BoundedContinuousFunction.coe_zero,Pi.zero_apply] at hh
    have hi := (crFrame_invertible hB hJc u z).self_apply_inverse
      (crOperator J (fun w => u w+framedMarkedVariation J u R g w) z)
    rw [←hh,map_zero] at hi
    exact hi.symm
  · intro hg
    apply Subtype.ext
    apply holderValue_injective ((1:ℝ)/3)
    apply BoundedContinuousFunction.ext
    intro z
    change compactHolderValue R (F g) z=0
    rw [hF z,hg z,map_zero]

end

 

open scoped ContDiff Topology
open Set Function Filter
section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
local instance finiteReductionInst15 (S : Submodule ℝ E) : NormedAddCommGroup S := inferInstance
local instance finiteReductionInst16 (S : Submodule ℝ E) : NormedSpace ℝ S := inferInstance
local instance finiteReductionInst17 (S : Submodule ℝ F) : NormedAddCommGroup S := inferInstance
local instance finiteReductionInst18 (S : Submodule ℝ F) : NormedSpace ℝ S := inferInstance
local instance finiteReductionInst19 (S T : Submodule ℝ E) : NormedAddCommGroup (S × T) := inferInstance
local instance finiteReductionInst20 (S T : Submodule ℝ E) : NormedSpace ℝ (S × T) := inferInstance

 

theorem fredholm_local_finite_reduction {f : E → F}
    (hf : ContDiffAt ℝ ∞ f 0) (hf0 : f 0=0)
    (pkg : (fderiv ℝ f 0).FredholmPackage) :
    ∃ (φ : pkg.decDom.X₀ → pkg.decDom.X₁)
      (κ : pkg.decDom.X₀ → pkg.decCodom.X₀),
      ContDiffAt ℝ ∞ φ 0 ∧ φ 0=0 ∧ ContDiffAt ℝ ∞ κ 0 ∧ κ 0=0 ∧
      (∀ᶠ x : pkg.decDom.X₀ in 𝓝 0,
        f ((x : E)+(φ x : E))=0 ↔ κ x=0) ∧
      (∀ᶠ x : E in 𝓝 0,
        f x=0 ↔ ∃ k : pkg.decDom.X₀, x=(k : E)+(φ k : E) ∧ κ k=0) := by
  let : FiniteDimensional ℝ pkg.decDom.X₀ := pkg.decDom.finite_X₀
  let : FiniteDimensional ℝ pkg.decCodom.X₀ := pkg.decCodom.finite_X₀
  let : CompleteSpace pkg.decDom.X₁ := pkg.decDom.isTopCompl.isClosed.completeSpace_coe
  let : CompleteSpace pkg.decCodom.X₁ := pkg.decCodom.isTopCompl.isClosed.completeSpace_coe
  let D : (pkg.decDom.X₀ × pkg.decDom.X₁) ≃L[ℝ] E :=
    Submodule.prodEquivOfIsTopCompl _ _ pkg.decDom.isTopCompl.symm
  let P : F →L[ℝ] pkg.decCodom.X₁ := pkg.decCodom.proj
  let Q : F →L[ℝ] pkg.decCodom.X₀ :=
    pkg.decCodom.X₀.projectionOntoL _ pkg.decCodom.isTopCompl.symm
  let H : pkg.decDom.X₀ × pkg.decDom.X₁ → pkg.decCodom.X₁ := fun v => P (f (D v))
  have hD0 : D 0=0 := map_zero D
  have hH : ContDiffAt ℝ ∞ H 0 :=
    P.contDiff.contDiffAt.comp 0 ((show ContDiffAt ℝ ∞ f (D 0) by simpa using hf).comp 0 D.contDiff.contDiffAt)
  have hH0 : H 0=0 := by simp [H,hf0]
  have hd : HasFDerivAt H (P.comp ((fderiv ℝ f 0).comp D.toContinuousLinearMap)) 0 := by
    simpa only [H,Function.comp_def] using P.hasFDerivAt.comp 0
      ((show HasFDerivAt f (fderiv ℝ f 0) (D 0) by simpa using (hf.differentiableAt (by simp)).hasFDerivAt).comp 0 D.hasFDerivAt)
  have heq : (fderiv ℝ H 0).comp (ContinuousLinearMap.inr ℝ pkg.decDom.X₀ pkg.decDom.X₁)=
      pkg.equiv.toContinuousLinearMap := by
    rw [hd.fderiv]
    apply ContinuousLinearMap.ext
    intro x
    change P (fderiv ℝ f 0 (D (0,x)))=pkg.equiv x
    have hDx : D (0,x)=(x : E) := by simp [D,Submodule.prodEquivOfIsTopCompl_apply]
    have hx : fderiv ℝ f 0 (x : E)=(pkg.equiv x : F) := by
      simpa [FredholmDecomposition.proj] using congrArg (fun A : E →L[ℝ] F => A (x : E)) pkg.eq_equiv
    rw [hDx,hx]
    simp [P,FredholmDecomposition.proj]
  have hi : ((fderiv ℝ H 0).comp
      (ContinuousLinearMap.inr ℝ pkg.decDom.X₀ pkg.decDom.X₁)).IsInvertible := by
    rw [heq]
    exact ContinuousLinearMap.isInvertible_equiv
  let φ := hH.implicitFunction (by simp) hi
  have hφ0 : φ 0=0 := hH.implicitFunction_apply_self (by simp) hi
  have hφ : ContDiffAt ℝ ∞ φ 0 := hH.contDiffAt_implicitFunction (by simp) hi
  let κ : pkg.decDom.X₀ → pkg.decCodom.X₀ := fun k => Q (f (D (k,φ k)))
  have hκ : ContDiffAt ℝ ∞ κ 0 := by
    apply Q.contDiff.contDiffAt.comp 0
    have hfD : ContDiffAt ℝ ∞ f (D (0,φ 0)) := by simpa [hφ0,←Prod.zero_eq_mk] using hf
    exact hfD.comp 0 (D.contDiff.contDiffAt.comp 0 (contDiffAt_id.prodMk hφ))
  have hκ0 : κ 0=0 := by simp [κ,hφ0,←Prod.zero_eq_mk,hf0]
  have hPH : ∀ᶠ k in 𝓝 (0 : pkg.decDom.X₀), H (k,φ k)=0 := by
    simpa only [hH0,Prod.fst_zero] using hH.eventually_apply_implicitFunction (by simp) hi
  have hHe : ∀ᶠ v in 𝓝 (0 : pkg.decDom.X₀ × pkg.decDom.X₁),
      H v=0 ↔ φ v.1=v.2 := by
    simpa only [hH0] using hH.eventually_apply_eq_iff_implicitFunction (by simp) hi
  have hpq (y : F) : y=0 ↔ P y=0 ∧ Q y=0 := by
    let C := (Submodule.prodEquivOfIsTopCompl _ _ pkg.decCodom.isTopCompl).symm
    have hc : C y=(P y,Q y) := by
      simp [C,P,Q,FredholmDecomposition.proj,Submodule.prodEquivOfIsTopCompl_symm_apply]
    constructor
    · rintro rfl; simp
    · intro hy
      apply C.injective
      rw [hc,map_zero,hy.1,hy.2]
      rfl
  have hDe (k : pkg.decDom.X₀) : D (k,φ k)=(k : E)+(φ k : E) := rfl
  refine ⟨φ,κ,hφ,hφ0,hκ,hκ0,?_,?_⟩
  · filter_upwards [hPH] with k hk
    rw [←hDe,hpq]
    change (H (k,φ k)=0 ∧ κ k=0) ↔ κ k=0
    simp [hk]
  · have hDinv : Tendsto D.symm (𝓝 (0:E)) (𝓝 (0 : pkg.decDom.X₀ × pkg.decDom.X₁)) := by
      simpa using D.symm.continuous.tendsto (0:E)
    have hfirst : Tendsto (fun x : E => (D.symm x).1) (𝓝 0) (𝓝 (0 : pkg.decDom.X₀)) :=
      continuous_fst.continuousAt.tendsto.comp hDinv
    filter_upwards [hDinv.eventually hHe,hfirst.eventually hPH] with x hx hxP
    constructor
    · intro hfx
      have hHx : H (D.symm x)=0 := by simp [H,hfx]
      have hes : φ (D.symm x).1=(D.symm x).2 := hx.mp hHx
      refine ⟨(D.symm x).1,?_,?_⟩
      · rw [←hDe,hes]
        exact (D.apply_symm_apply x).symm
      · change Q (f (D ((D.symm x).1,φ (D.symm x).1)))=0
        rw [hes,Prod.mk.eta,ContinuousLinearEquiv.apply_symm_apply,hfx,map_zero]
    · rintro ⟨k,hxk,hκk⟩
      have hc : D.symm x=(k,φ k) := by
        rw [hxk,←hDe,ContinuousLinearEquiv.symm_apply_apply]
      apply (hpq (f x)).mpr
      constructor
      · have hkk : (D.symm x).1=k := congrArg Prod.fst hc
        rw [hkk] at hxP
        simpa only [H,hDe,←hxk] using hxP
      · simpa only [κ,hDe,←hxk] using hκk

end

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
section
local instance finiteReductionInst21 (n : ℕ) (R : ℝ) : NormedAddCommGroup (CompactHolderSpace (Phase n) R) := inferInstance
local instance finiteReductionInst22 (n : ℕ) (R : ℝ) : NormedSpace ℝ (CompactHolderSpace (Phase n) R) := inferInstance

 

theorem AffineLineCurve.exists_finite_reduction {n : ℕ}
    {η : Phase n → Phase n →L[ℝ] Phase n →L[ℝ] ℝ} {J : Phase n → End n}
    (hB : ∀ x, CompatibleWith (η x) (standardJ n))
    (hJc : ∀ x, CompatibleWith (η x) (J x)) (hJ : ContDiff ℝ ∞ J)
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u) :
    ∃ S : ℝ, 0 < S ∧ ∀ R : ℝ, S ≤ R →
      ∃ (F : CompactHolderSpace (Phase n) R → CompactHolderSpace (Phase n) R)
        (pkg : (fderiv ℝ F 0).FredholmPackage)
        (φ : pkg.decDom.X₀ → pkg.decDom.X₁)
        (κ : pkg.decDom.X₀ → pkg.decCodom.X₀),
        ContDiffAt ℝ ∞ F 0 ∧ F 0=0 ∧
        ContDiffAt ℝ ∞ φ 0 ∧ φ 0=0 ∧ ContDiffAt ℝ ∞ κ 0 ∧ κ 0=0 ∧
        (∀ᶠ g : CompactHolderSpace (Phase n) R in 𝓝 0,
          (∀ z, crOperator J (fun w => u w+framedMarkedVariation J u R g w) z=0) ↔
            ∃ k : pkg.decDom.X₀, g=(k : CompactHolderSpace (Phase n) R)+
              (φ k : CompactHolderSpace (Phase n) R) ∧ κ k=0) := by
  obtain ⟨S,hS,hM,hSection⟩ := hu.exists_nonlinear_fredholm_section hB hJc hJ hc
  refine ⟨S,hS,?_⟩
  intro R hR
  obtain ⟨F,hF,hF0,hFred,hFe,hDF⟩ := hSection R hR
  obtain ⟨pkg⟩ := hFred.nonempty_fredholmPackage
  obtain ⟨φ,κ,hφ,hφ0,hκ,hκ0,_,hred⟩ := fredholm_local_finite_reduction hF hF0 pkg
  refine ⟨F,pkg,φ,κ,hF,hF0,hφ,hφ0,hκ,hκ0,?_⟩
  filter_upwards [hFe,hred] with g hg hgr
  exact (local_section_zero_iff hB hJc hg).symm.trans hgr

end

 

 

open Set Function Filter Topology

 

open Set Function

 

open Set Function

 

open Function

 

open Set Function

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
local instance finiteReductionInst23 (n : ℕ) (R : ℝ) : NormedAddCommGroup (CompactHolderSpace (Phase n) R) := inferInstance
local instance finiteReductionInst24 (n : ℕ) (R : ℝ) : NormedSpace ℝ (CompactHolderSpace (Phase n) R) := inferInstance

 

theorem normalized_section_package_finrank {n : ℕ}
    {η : Phase n → Phase n →L[ℝ] Phase n →L[ℝ] ℝ} {J : Phase n → End n}
    (hB : ∀ x, CompatibleWith (η x) (standardJ n))
    (hJc : ∀ x, CompatibleWith (η x) (J x)) (hJ : ContDiff ℝ ∞ J)
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (hup : IsProperMap u) {R : ℝ}
    (hR : ∀ z : ℂ, R < ‖z‖ → normalizedFrameCoefficient (standardJ n) J u z=0)
    {F : CompactHolderSpace (Phase n) R → CompactHolderSpace (Phase n) R}
    (hDF : ∀ g z, compactHolderValue R (fderiv ℝ F 0 g) z=
      compactHolderValue R g z+normalizedFrameCoefficient (standardJ n) J u z (markedCRInverse R g z))
    (pkg : (fderiv ℝ F 0).FredholmPackage) :
    Module.finrank ℝ pkg.decDom.X₀=Module.finrank ℝ pkg.decCodom.X₀ := by
  let E := CompactHolderSpace (Phase n) R
  let M := normalizedFrameCoefficient (standardJ n) J u
  have hMs : ContDiff ℝ ∞ M := normalizedFrameCoefficient_smooth hB hJc hJ hu
  have hMc : HasCompactSupport M := normalizedFrameCoefficient_compact (hB 0).1 hc hup
  let T : E →L[ℝ] E := markedCRLower R M hMs hMc hR
  have hT : IsCompactOperator T := markedCRLower_compact R M hMs hMc hR
  have he : fderiv ℝ F 0 = ContinuousLinearMap.id ℝ E+T := by
    apply ContinuousLinearMap.ext
    intro g
    apply Subtype.ext
    apply holderValue_injective ((1:ℝ)/3)
    apply BoundedContinuousFunction.ext
    intro z
    change compactHolderValue R (fderiv ℝ F 0 g) z=compactHolderValue R (g+T g) z
    rw [map_add,BoundedContinuousFunction.add_apply,hDF]
    rw [show compactHolderValue R (T g) z=M z (markedCRInverse R g z) from markedCRLower_value R M hMs hMc hR g z]
  have hidx := compactPerturbation_index_zero T hT
  rw [←he,pkg.ker_eq,pkg.range_eq] at hidx
  exact hidx.trans (Submodule.quotientEquivOfIsCompl _ _ pkg.decCodom.isTopCompl.isCompl).finrank_eq

end HigherDimensionalBallPacking.Rigidity

end

namespace ContinuousLinearMap.FredholmPackage
open scoped _root_.ContinuousLinearMap _root_.ContinuousLinearMap.FredholmPackage
-- Preserve the namespace exported by this module.
end ContinuousLinearMap.FredholmPackage

end OAI
