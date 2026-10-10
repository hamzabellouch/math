import OAI.Analysis.KadisonKastler.ScalarBoundaryMean
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner

namespace OAI

/-! # Matrix coefficients of the scalar boundary mean

A uniformly bounded family of weakly measurable operators gives a
sesquilinear family of scalar L-infinity classes. Applying the scalar
conditional expectation preserves its algebraic identities and bounds.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped BoundedContinuousFunction

noncomputable section

variable {G D H : Type*}
  [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The exact uniformly bounded measurable family needed for coefficient
averaging. The bound is retained as data to control the output operator. -/
structure UniformMeasurableOperators (G D H : Type*) [MeasurableSpace D]
    (μ : Measure D) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  eval : G → D → H →L[ℂ] H
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_le : ∀ g x, ‖eval g x‖ ≤ bound
  measurable : ∀ g ξ, AEStronglyMeasurable (fun x => eval g x ξ) μ

namespace UniformMeasurableOperators

variable (T : UniformMeasurableOperators G D H μ)

/-- A scalar matrix coefficient is an actual L-infinity class. -/
def coefficient (g : G) (ξ η : H) : ScalarLInfinity μ :=
  (memLp_top_of_bound ((T.measurable g ξ).const_inner)
    (T.bound * ‖ξ‖ * ‖η‖) (Eventually.of_forall fun x => by
      calc
        ‖inner ℂ η (T.eval g x ξ)‖ ≤ ‖η‖ * ‖T.eval g x ξ‖ := norm_inner_le_norm _ _
        _ ≤ ‖η‖ * (T.bound * ‖ξ‖) := mul_le_mul_of_nonneg_left
          ((T.eval g x).le_opNorm ξ |>.trans
            (mul_le_mul_of_nonneg_right (T.norm_le g x) (norm_nonneg ξ))) (norm_nonneg η)
        _ = _ := by ring)).toLp (fun x => inner ℂ η (T.eval g x ξ))

@[simp]
theorem coefficient_ae (g : G) (ξ η : H) :
    T.coefficient g ξ η =ᵐ[μ] fun x => inner ℂ η (T.eval g x ξ) := MemLp.coeFn_toLp _

section Finite

variable [IsFiniteMeasure μ]

theorem norm_coefficient_le (g : G) (ξ η : H) :
    ‖T.coefficient g ξ η‖ ≤ T.bound * ‖ξ‖ * ‖η‖ := by
  suffices hb : ∀ᵐ x ∂μ, ‖T.coefficient g ξ η x‖ ≤ T.bound * ‖ξ‖ * ‖η‖ by
    simpa using Lp.norm_le_of_ae_bound
      (mul_nonneg (mul_nonneg T.bound_nonneg (norm_nonneg ξ)) (norm_nonneg η)) hb
  filter_upwards [T.coefficient_ae g ξ η] with x hx
  rw [hx]
  calc
    _ ≤ ‖η‖ * ‖T.eval g x ξ‖ := norm_inner_le_norm _ _
    _ ≤ ‖η‖ * (T.bound * ‖ξ‖) := mul_le_mul_of_nonneg_left
      ((T.eval g x).le_opNorm ξ |>.trans
        (mul_le_mul_of_nonneg_right (T.norm_le g x) (norm_nonneg ξ))) (norm_nonneg η)
    _ = _ := by ring

end Finite

theorem coefficient_add_left (g : G) (ξ ζ η : H) :
    T.coefficient g (ξ + ζ) η = T.coefficient g ξ η + T.coefficient g ζ η := by
  apply Lp.ext
  filter_upwards [T.coefficient_ae g (ξ + ζ) η, T.coefficient_ae g ξ η,
    T.coefficient_ae g ζ η, Lp.coeFn_add (T.coefficient g ξ η) (T.coefficient g ζ η)]
      with x ha hb hc hd
  simp only [Pi.add_apply] at hd
  rw [ha, hd, hb, hc, map_add, inner_add_right]

theorem coefficient_smul_left (g : G) (c : ℂ) (ξ η : H) :
    T.coefficient g (c • ξ) η = c • T.coefficient g ξ η := by
  apply Lp.ext
  filter_upwards [T.coefficient_ae g (c • ξ) η, T.coefficient_ae g ξ η,
    Lp.coeFn_smul c (T.coefficient g ξ η)] with x ha hb hc
  simp only [Pi.smul_apply] at hc
  rw [ha, hc, hb, map_smul, inner_smul_right]
  rfl

theorem coefficient_add_right (g : G) (ξ η ζ : H) :
    T.coefficient g ξ (η + ζ) = T.coefficient g ξ η + T.coefficient g ξ ζ := by
  apply Lp.ext
  filter_upwards [T.coefficient_ae g ξ (η + ζ), T.coefficient_ae g ξ η,
    T.coefficient_ae g ξ ζ, Lp.coeFn_add (T.coefficient g ξ η) (T.coefficient g ξ ζ)]
      with x ha hb hc hd
  simp only [Pi.add_apply] at hd
  rw [ha, hd, hb, hc, inner_add_left]

theorem coefficient_smul_right (g : G) (c : ℂ) (ξ η : H) :
    T.coefficient g ξ (c • η) = star c • T.coefficient g ξ η := by
  apply Lp.ext
  filter_upwards [T.coefficient_ae g ξ (c • η), T.coefficient_ae g ξ η,
    Lp.coeFn_smul (star c) (T.coefficient g ξ η)] with x ha hb hc
  simp only [Pi.smul_apply] at hc
  rw [ha, hc, hb, inner_smul_left]
  rfl

variable [TopologicalSpace G] [DiscreteTopology G] [IsFiniteMeasure μ]

/-- All group coordinates of a coefficient form a uniformly bounded
family, the precise source space of the scalar mean. -/
def coefficientFamily (ξ η : H) : G →ᵇ ScalarLInfinity μ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun g => T.coefficient g ξ η) (T.bound * ‖ξ‖ * ‖η‖)
    (fun g => T.norm_coefficient_le g ξ η)

@[simp]
theorem coefficientFamily_apply (ξ η : H) (g : G) :
    T.coefficientFamily ξ η g = T.coefficient g ξ η := rfl

theorem norm_coefficientFamily_le (ξ η : H) :
    ‖T.coefficientFamily ξ η‖ ≤ T.bound * ‖ξ‖ * ‖η‖ :=
  (BoundedContinuousFunction.norm_le
    (mul_nonneg (mul_nonneg T.bound_nonneg (norm_nonneg ξ)) (norm_nonneg η))).mpr
    (fun g => T.norm_coefficient_le g ξ η)

theorem coefficientFamily_add_left (ξ ζ η : H) :
    T.coefficientFamily (ξ + ζ) η = T.coefficientFamily ξ η + T.coefficientFamily ζ η := by
  apply BoundedContinuousFunction.ext
  intro g
  exact T.coefficient_add_left g ξ ζ η

theorem coefficientFamily_smul_left (c : ℂ) (ξ η : H) :
    T.coefficientFamily (c • ξ) η = c • T.coefficientFamily ξ η := by
  apply BoundedContinuousFunction.ext
  intro g
  exact T.coefficient_smul_left g c ξ η

theorem coefficientFamily_add_right (ξ η ζ : H) :
    T.coefficientFamily ξ (η + ζ) = T.coefficientFamily ξ η + T.coefficientFamily ξ ζ := by
  apply BoundedContinuousFunction.ext
  intro g
  exact T.coefficient_add_right g ξ η ζ

theorem coefficientFamily_smul_right (c : ℂ) (ξ η : H) :
    T.coefficientFamily ξ (c • η) = star c • T.coefficientFamily ξ η := by
  apply BoundedContinuousFunction.ext
  intro g
  exact T.coefficient_smul_right g c ξ η

variable [Group G]

/-- Apply the scalar expectation to the actual coefficient family. -/
def meanCoefficient {α : NonsingularAction G D μ} (m : ScalarBoundaryMean α)
    (ξ η : H) : ScalarLInfinity μ := m.toCLM (T.coefficientFamily ξ η)

theorem norm_meanCoefficient_le {α : NonsingularAction G D μ} (m : ScalarBoundaryMean α)
    (ξ η : H) : ‖T.meanCoefficient m ξ η‖ ≤ T.bound * ‖ξ‖ * ‖η‖ :=
  (m.norm_le _).trans (T.norm_coefficientFamily_le ξ η)

theorem meanCoefficient_add_left {α : NonsingularAction G D μ} (m : ScalarBoundaryMean α)
    (ξ ζ η : H) :
    T.meanCoefficient m (ξ + ζ) η = T.meanCoefficient m ξ η + T.meanCoefficient m ζ η := by
  simp only [meanCoefficient, T.coefficientFamily_add_left, map_add]

theorem meanCoefficient_smul_left {α : NonsingularAction G D μ} (m : ScalarBoundaryMean α)
    (c : ℂ) (ξ η : H) : T.meanCoefficient m (c • ξ) η = c • T.meanCoefficient m ξ η := by
  simp only [meanCoefficient, T.coefficientFamily_smul_left, map_smul]

theorem meanCoefficient_add_right {α : NonsingularAction G D μ} (m : ScalarBoundaryMean α)
    (ξ η ζ : H) :
    T.meanCoefficient m ξ (η + ζ) = T.meanCoefficient m ξ η + T.meanCoefficient m ξ ζ := by
  simp only [meanCoefficient, T.coefficientFamily_add_right, map_add]

theorem meanCoefficient_smul_right {α : NonsingularAction G D μ} (m : ScalarBoundaryMean α)
    (c : ℂ) (ξ η : H) : T.meanCoefficient m ξ (c • η) = star c • T.meanCoefficient m ξ η := by
  simp only [meanCoefficient, T.coefficientFamily_smul_right, map_smul]

end UniformMeasurableOperators

end

end KadisonKastler

end OAI
