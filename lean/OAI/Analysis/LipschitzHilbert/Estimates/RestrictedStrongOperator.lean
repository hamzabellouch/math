import OAI.Analysis.LipschitzHilbert.Estimates.RestrictedStrongLp
import OAI.Analysis.LipschitzHilbert.Trees.SourceL2Gram

namespace OAI

/-! The restricted logarithmic estimate controls the actual L2 operator
norm. A finite truncation's preliminary continuity suffices; its original
continuity bound does not enter the final constant. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert
variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]

abbrev HilbertLp (μ : Measure X) := Lp (EuclideanSpace ℂ κ) 2 μ

def HasRestrictedLogBound (μ : Measure X)
    (B : HilbertLp (κ := κ) μ →L[ℝ] HilbertLp (κ := κ) μ →L[ℝ] ℂ) (C : ℝ) : Prop :=
  ∀ F G : Set X, MeasurableSet F → MeasurableSet G → μ F≠∞ → μ G≠∞ →
    0<μ.real F → 0<μ.real G →
    ∀ (u v : X → EuclideanSpace ℂ κ), Measurable u → Measurable v →
      (∀ x, ‖u x‖≤1) → (∀ x, ‖v x‖≤1) →
      (∀ x, x∉F → u x=0) → (∀ x, x∉G → v x=0) →
    ∀ (hu : MemLp u 2 μ) (hv : MemLp v 2 μ),
      ‖B (hu.toLp u) (hv.toLp v)‖≤C*((1+|Real.log (μ.real F/μ.real G)|)^3)⁻¹*
        Real.sqrt (μ.real F)*Real.sqrt (μ.real G)

theorem restricted_strong_Lp_norm (μ : Measure X)
    (B : HilbertLp (κ := κ) μ →L[ℝ] HilbertLp (κ := κ) μ →L[ℝ] ℂ)
    (C : ℝ) (hC : 0≤C) (hB : HasRestrictedLogBound μ B C)
    (f g : HilbertLp (κ := κ) μ) :
    ‖B f g‖≤4*C*restrictedStrongConstant*‖f‖*‖g‖ := by
  have h := restricted_strong_Lp μ B C hC hB f g
    (Lp.stronglyMeasurable f).measurable (Lp.stronglyMeasurable g).measurable (Lp.memLp f) (Lp.memLp g)
  have hroot (v : HilbertLp (κ := κ) μ) : Real.sqrt (∫ x, ‖v x‖^2 ∂μ)=‖v‖ := by
    rw [← memLp_toL2_norm_sq μ v (Lp.memLp v), Lp.toLp_coeFn, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg v)]
  simpa only [Lp.toLp_coeFn, hroot] using h

def operatorPairing (μ : Measure X)
    (T : HilbertLp (κ := κ) μ →L[ℝ] HilbertLp (κ := κ) μ) :
    HilbertLp (κ := κ) μ →L[ℝ] HilbertLp (κ := κ) μ →L[ℝ] ℂ :=
  (isBoundedBilinearMap_inner (𝕜 := ℂ)).toContinuousLinearMap.comp T

theorem operatorPairing_apply (μ : Measure X)
    (T : HilbertLp (κ := κ) μ →L[ℝ] HilbertLp (κ := κ) μ)
    (f g : HilbertLp (κ := κ) μ) : operatorPairing μ T f g=inner ℂ (T f) g := rfl

theorem restricted_strong_operator_norm (μ : Measure X)
    (T : HilbertLp (κ := κ) μ →L[ℝ] HilbertLp (κ := κ) μ)
    (C : ℝ) (hC : 0≤C) (hB : HasRestrictedLogBound μ (operatorPairing μ T) C) :
    ‖T‖≤4*C*restrictedStrongConstant := by
  have hconstant : 0≤4*C*restrictedStrongConstant :=
    mul_nonneg (mul_nonneg (by norm_num) hC) restrictedStrongConstant_pos.le
  apply T.opNorm_le_bound hconstant
  intro f
  have h := restricted_strong_Lp_norm μ (operatorPairing μ T) C hC hB f (T f)
  rw [operatorPairing_apply, inner_self_eq_norm_sq_to_K] at h
  simp only [norm_pow, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg (T f))] at h
  by_cases hz : ‖T f‖=0
  · rw [hz]
    exact mul_nonneg hconstant (norm_nonneg f)
  · have hp : 0<‖T f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    apply (mul_le_mul_iff_right₀ hp).mp
    simpa only [pow_two, mul_comm, mul_left_comm, mul_assoc] using h

end LipschitzHilbert

end

end OAI
