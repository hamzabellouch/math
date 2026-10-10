import OAI.Geometry.SurfaceImmersion.Geometry.CurveFrameInverse

namespace OAI

/-! A genuine two-component normal defect for the derivative of a surface map. -/
noncomputable section
open Set Filter Matrix
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def coordinateDifferential (φ : Base → ProjectionTarget 3) (x : Base) : Base →L[ℝ] (Fin 3 → ℝ) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap.comp (fderiv ℝ φ x)

def transverseDerivative (φ : Base → ProjectionTarget 3) (x : Base) : Fin 3 → ℝ :=
  coordinateDifferential φ x (![1,0] : Base)

def normalDefect (φ : Base → ProjectionTarget 3) (a : Fin 3 → ℝ) (x : Base) : Base :=
  ((curveNormalLinear (transverseDerivative φ x) a).inverse
    (coordinateDifferential φ x (![0,1] : Base))).1

lemma coordinateDifferential_smooth {φ : Base → ProjectionTarget 3} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (coordinateDifferential φ) :=
  contDiff_const.clm_comp (hφ.fderiv_right (m := ∞) (by simp))

lemma transverseDerivative_smooth {φ : Base → ProjectionTarget 3} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (transverseDerivative φ) :=
  (coordinateDifferential_smooth hφ).clm_apply contDiff_const

lemma normalDefect_smooth {φ : Base → ProjectionTarget 3} (hφ : ContDiff ℝ ∞ φ)
    {a : Fin 3 → ℝ} {U : Set Base}
    (hu : ∀ x ∈ U, transverseDerivative φ x ≠ 0)
    (ha : ∀ x ∈ U, ∀ r : ℝ, r • transverseDerivative φ x ≠ a) :
    ContDiffOn ℝ ∞ (normalDefect φ a) U := by
  have hu' := transverseDerivative_smooth hφ
  have hcross : ContDiff ℝ ∞ (fun x => transverseDerivative φ x ⨯₃ a) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [cross_apply] <;> fun_prop
  have hframe : ContDiff ℝ ∞ (fun x => curveNormalLinear (transverseDerivative φ x) a) :=
    ((contDiff_const.smulRight hu').add contDiff_const).add (contDiff_const.smulRight hcross)
  intro x hx
  have hI := (curveNormalLinear_invertible (hu x hx) (ha x hx)).contDiffAt_map_inverse.comp x hframe.contDiffAt
  exact (hI.clm_apply ((coordinateDifferential_smooth hφ).clm_apply contDiff_const).contDiffAt).fst.contDiffWithinAt

lemma normalDefect_immersion_iff (φ : Base → ProjectionTarget 3) (a : Fin 3 → ℝ) (x : Base)
    (hu : transverseDerivative φ x ≠ 0)
    (ha : ∀ r : ℝ, r • transverseDerivative φ x ≠ a) :
    Function.Injective (fderiv ℝ φ x) ↔ normalDefect φ a x ≠ 0 := by
  let L := (curveNormalLinear (transverseDerivative φ x) a).inverse.comp (coordinateDifferential φ x)
  have hframe := curveNormalLinear_invertible hu ha
  have hI : Function.Injective (curveNormalLinear (transverseDerivative φ x) a).inverse := by
    intro v w hvw
    have hh := congrArg (curveNormalLinear (transverseDerivative φ x) a) hvw
    simpa only [hframe.self_apply_inverse] using hh
  have hL : L (![1,0] : Base) = ((0:Base),1) := curveNormalLinear_inverse_velocity hu ha
  have hequiv : Function.Injective (fderiv ℝ φ x) ↔ Function.Injective L := by
    constructor
    · intro h v w hEq
      apply h
      apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
      apply hI
      exact hEq
    · intro h v w hEq
      apply h
      change (curveNormalLinear (transverseDerivative φ x) a).inverse
        (EuclideanSpace.equiv (Fin 3) ℝ (fderiv ℝ φ x v)) = _
      rw [hEq]
      rfl
  exact hequiv.trans (normal_coordinates_injective_iff L hL)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
