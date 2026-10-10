import OAI.Geometry.SurfaceImmersion.Geometry.JointCovarianceParameter
import OAI.Geometry.SurfaceImmersion.Primitive.PeriodicSubspace

namespace OAI

/-! The normal component of the periodic correction, including its actual
primitive, parameter smoothness, normalization, and support preservation. -/

noncomputable section
open MeasureTheory
open scoped ContDiff

universe u

namespace ClosedSurfaceR4.CovarianceCorrector

open PeriodicPrimitive

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

def integratedCorrector (V : P → C(Period, E)) (r : P → C(Period, ℝ))
    (q : P → ℝ) (p : P) (t : ℝ) : E :=
  primitive (fun s : ℝ => parameterCorrector V r q p (s : Period)) t

theorem contDiff_integratedCorrector {V : P → C(Period, E)}
    {r : P → C(Period, ℝ)} {q : P → ℝ}
    (hV : ContDiff ℝ ∞ (fun p : P × ℝ => V p.1 (p.2 : Period)))
    (hr : ContDiff ℝ ∞ (fun p : P × ℝ => r p.1 (p.2 : Period)))
    (hq : ContDiff ℝ ∞ q) (hqpos : ∀ p, 0 < q p)
    (hcircle : ∀ p t, inner ℝ (V p t) (V p t) = q p) :
    ContDiff ℝ ∞ (fun p : P × ℝ => integratedCorrector V r q p.1 p.2) :=
  contDiff_primitive_joint (contDiff_parameterCorrector_joint hV hr hq hqpos hcircle)

theorem integratedCorrector_spec {V : P → C(Period, E)}
    {r : P → C(Period, ℝ)} {q : P → ℝ}
    (hV : ContDiff ℝ ∞ (fun p : P × ℝ => V p.1 (p.2 : Period)))
    (hr : ContDiff ℝ ∞ (fun p : P × ℝ => r p.1 (p.2 : Period)))
    (hq : ContDiff ℝ ∞ q) (hqpos : ∀ p, 0 < q p)
    (hcircle : ∀ p t, inner ℝ (V p t) (V p t) = q p) (p : P) :
    Function.Periodic (integratedCorrector V r q p) 1 ∧
      (∫ t in 0..1, integratedCorrector V r q p t) = 0 ∧
      ∀ t : ℝ, HasDerivAt (integratedCorrector V r q p)
        (parameterCorrector V r q p (t : Period)) t := by
  have hs := (contDiff_parameterCorrector_joint hV hr hq hqpos hcircle).comp
    (contDiff_const.prodMk contDiff_id : ContDiff ℝ ∞ (fun t : ℝ => (p, t)))
  have hp : Function.Periodic (fun t : ℝ => parameterCorrector V r q p (t : Period)) 1 := by
    intro t
    change parameterCorrector V r q p ((t + 1 : ℝ) : Period) = _
    rw [AddCircle.coe_add_period]
  have hm : (∫ t in 0..1, parameterCorrector V r q p (t : Period)) = 0 := by
    rw [integral_lift_eq_haar]
    exact parameterCorrector_average hqpos hcircle p
  exact ⟨primitive_periodic hs.continuous hp hm, primitive_mean_zero hs.continuous,
    primitive_hasDerivAt hs.continuous⟩

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [FiniteDimensional ℝ E] in
/-- A zero prescribed fluctuation gives the zero explicit corrector. -/
theorem parameterCorrector_zero {V : P → C(Period, E)}
    {r : P → C(Period, ℝ)} {q : P → ℝ} {p : P}
    (hr : ∀ t, r p t = 0) (t : Period) : parameterCorrector V r q p t = 0 := by
  have hz : r p = 0 := by ext s; exact hr s
  have hm : covarianceSolution (V p) (r p) (q p) = 0 := by
    rw [covarianceSolution]
    have hw : weightedAverage (V p) (r p) = 0 := by
      rw [weightedAverage_apply]
      simp only [hr, zero_smul]
      exact average_const 0
    rw [hw, map_zero]
  simp only [parameterCorrector, correctedVector, correctedScalar, hm, hr,
    inner_zero_right, zero_div, add_zero, zero_smul, sub_zero, smul_zero]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [FiniteDimensional ℝ E] in
/-- Vanishing input outside the active patch gives a vanishing primitive
there, including all derivatives by the joint smoothness theorem. -/
theorem integratedCorrector_zero {V : P → C(Period, E)}
    {r : P → C(Period, ℝ)} {q : P → ℝ} {p : P}
    (hr : ∀ t, r p t = 0) (t : ℝ) : integratedCorrector V r q p t = 0 := by
  unfold integratedCorrector
  simp only [parameterCorrector_zero hr]
  exact primitive_zero t

theorem integratedCorrector_mem_submodule {V : P → C(Period, E)}
    {r : P → C(Period, ℝ)} {q : P → ℝ} (S : P → Submodule ℝ E)
    (hV : ContDiff ℝ ∞ (fun p : P × ℝ => V p.1 (p.2 : Period)))
    (hr : ContDiff ℝ ∞ (fun p : P × ℝ => r p.1 (p.2 : Period)))
    (hq : ContDiff ℝ ∞ q) (hqpos : ∀ p, 0 < q p)
    (hcircle : ∀ p t, inner ℝ (V p t) (V p t) = q p)
    (hmem : ∀ p t, V p t ∈ S p) (p : P) (t : ℝ) :
    integratedCorrector V r q p t ∈ S p := by
  have hs := (contDiff_parameterCorrector_joint hV hr hq hqpos hcircle).comp
    (contDiff_const.prodMk contDiff_id : ContDiff ℝ ∞ (fun t : ℝ => (p, t)))
  exact primitive_mem_submodule (S p) hs.continuous
    (fun s => parameterCorrector_mem_submodule S V r q hmem hqpos hcircle p (s : Period)) t

end ClosedSurfaceR4.CovarianceCorrector

end

end OAI
