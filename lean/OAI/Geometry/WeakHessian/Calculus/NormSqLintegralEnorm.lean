import Mathlib
import OAI.Geometry.WeakHessian.Calculus.ELpNormSq
import OAI.Geometry.WeakHessian.Transport.AeActionData

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set
open scoped NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace

namespace WeakHessian
variable {X : Type*} [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X] {m : Measure X}

omit [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [BorelSpace X] in
lemma norm_sq_eq_lintegral_enorm (D : Lp ℝ 2 m) :
    ENNReal.ofReal (‖D‖ ^ 2) = ∫⁻ x, ‖D x‖ₑ ^ 2 ∂m := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, Lp.enorm_def]
  exact eLpNorm_sq_eq_lintegral D (Lp.memLp D).aestronglyMeasurable

lemma norm_minimal_is_minimal {f D : Lp ℝ 2 m}
    (hD : IsLocalWeakUpperGradient m f D)
    (hmin : ∀ E : Lp ℝ 2 m, IsLocalWeakUpperGradient m f E → ‖D‖ ≤ ‖E‖) :
    IsMinimalLocalWeakUpperGradient m f D := by
  refine ⟨hD, fun E hE => ?_⟩
  let M : X → ℝ := fun x => min (D x) (E x)
  have hM : IsLocalWeakUpperGradient m f M :=
    hD.min_measurable hE (Lp.memLp f).aestronglyMeasurable.aemeasurable
  have hMb : ∀ᵐ x ∂m, ‖M x‖ ≤ D x := by
    filter_upwards [hD.2.1, hE.2.1] with x hx hy
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min hx hy)]
    exact min_le_left _ _
  have hMp : MemLp M 2 m := (Lp.memLp D).mono' hM.1.aestronglyMeasurable hMb
  let M' : Lp ℝ 2 m := hMp.toLp M
  have hM' : IsLocalWeakUpperGradient m f M' :=
    hM.congr_ae Filter.EventuallyEq.rfl hMp.coeFn_toLp.symm
  have hInt : (∫⁻ x, ‖D x‖ₑ ^ 2 ∂m) ≤ ∫⁻ x, ‖M x‖ₑ ^ 2 ∂m := by
    rw [← norm_sq_eq_lintegral_enorm D]
    calc
      ENNReal.ofReal (‖D‖ ^ 2) ≤ ENNReal.ofReal (‖M'‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hmin M' hM') 2)
      _ = ∫⁻ x, ‖M' x‖ₑ ^ 2 ∂m := norm_sq_eq_lintegral_enorm M'
      _ = _ := lintegral_congr_ae (hMp.coeFn_toLp.fun_comp (fun r : ℝ => ‖r‖ₑ ^ 2))
  have hsmall : (∫⁻ x, ‖M x‖ₑ ^ 2 ∂m) ≠ ∞ := by
    rw [← eLpNorm_sq_eq_lintegral M hMp.aestronglyMeasurable]
    exact (ENNReal.pow_lt_top hMp.eLpNorm_lt_top).ne
  have hle : (fun x => ‖M x‖ₑ ^ 2) ≤ᵐ[m] (fun x => ‖D x‖ₑ ^ 2) := by
    filter_upwards [hMb] with x hx
    apply pow_le_pow_left₀ (by positivity)
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hx.trans (le_abs_self _))
  have heq := ae_eq_of_ae_le_of_lintegral_le hle hsmall
    ((Lp.memLp D).aestronglyMeasurable.enorm.pow_const 2) hInt
  filter_upwards [heq, hD.2.1, hE.2.1] with x hx hdx hex
  have hreal := congrArg ENNReal.toReal hx
  simp only [Real.enorm_eq_ofReal_abs, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (abs_nonneg _)] at hreal
  have hMx : 0 ≤ M x := le_min hdx hex
  rw [abs_of_nonneg hMx, abs_of_nonneg hdx] at hreal
  have hequal : M x = D x := by nlinarith
  exact hequal ▸ min_le_right (D x) (E x)

lemma exists_minimalLocalWeakUpperGradient_l2 {f : X → ℝ} (hf : MemLp f 2 m)
    (h : ∃ D : X → ℝ, MemLp D 2 m ∧ IsLocalWeakUpperGradient m f D) :
    ∃ D : X → ℝ, IsMinimalLocalWeakUpperGradient m f D ∧ MemLp D 2 m := by
  obtain ⟨D0,hD0p,hD0⟩ := h
  let f' : Lp ℝ 2 m := hf.toLp f
  have hex : ∃ D : Lp ℝ 2 m, IsLocalWeakUpperGradient m f' D :=
    ⟨hD0p.toLp D0, hD0.congr_ae hf.coeFn_toLp.symm hD0p.coeFn_toLp.symm⟩
  obtain ⟨D,hD,hmin⟩ := exists_norm_minimal_upperGradient hex
  have hminimal := norm_minimal_is_minimal hD hmin
  refine ⟨D, ⟨hminimal.1.congr_ae hf.coeFn_toLp Filter.EventuallyEq.rfl, ?_⟩, Lp.memLp D⟩
  intro E hE
  exact hminimal.2 E (hE.congr_ae hf.coeFn_toLp.symm Filter.EventuallyEq.rfl)

lemma exists_minimalGradient_energy_le_cheeger
    (hfinite : FiniteOnBoundedSets m) {f : X → ℝ} (hf : MemLp f 2 m)
    (hch : cheegerEnergy m f < ∞) :
    ∃ D : Lp ℝ 2 m, IsMinimalLocalWeakUpperGradient m f D ∧
      ENNReal.ofReal (‖D‖ ^ 2 / 2) ≤ cheegerEnergy m f := by
  obtain ⟨E,hE,henergy⟩ := exists_upperGradient_energy_le_cheeger hfinite hf hch
  obtain ⟨D,hD,hmin⟩ := exists_norm_minimal_upperGradient
    ⟨E, hE.congr_ae hf.coeFn_toLp.symm Filter.EventuallyEq.rfl⟩
  have hminimal := norm_minimal_is_minimal hD hmin
  refine ⟨D, ⟨hminimal.1.congr_ae hf.coeFn_toLp Filter.EventuallyEq.rfl, ?_⟩, ?_⟩
  · intro E hE
    exact hminimal.2 E (hE.congr_ae hf.coeFn_toLp.symm Filter.EventuallyEq.rfl)
  · apply le_trans _ henergy
    apply ENNReal.ofReal_le_ofReal
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg D)
        (hmin E (hE.congr_ae hf.coeFn_toLp.symm Filter.EventuallyEq.rfl)) 2) (by norm_num)

end WeakHessian

end
end InlinedFile0

end OAI
