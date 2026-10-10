import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.SuspensionExpressions
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarHamiltonian

namespace OAI

/-! The horizontal part of the autonomous suspension is the Hamiltonian
field of the planar slice at its current spatial phase. -/

noncomputable section
namespace ForcedComputation
open ShearFlows Set
open scoped ContDiff

def planeInclusion : Plane →L[ℝ] Space :=
  letI := ShearFlows.neZeroTwo
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0, ContinuousLinearMap.proj 1, 0]

theorem planeInclusion_basis (j : Fin 2) :
    planeInclusion (PlanarHamiltonian.basis j) = basis j.castSucc := by
  ext k
  fin_cases j <;> fin_cases k <;> simp [planeInclusion, PlanarHamiltonian.basis, basis]

theorem atHeight_hasFDerivAt (X : Plane) (z : ℝ) :
    HasFDerivAt (fun Y : Plane => atHeight Y z) planeInclusion X := by
  have he : (fun Y : Plane => atHeight Y z) = fun Y => planeInclusion Y + z • basis 2 := by
    funext Y k
    fin_cases k <;> simp [planeInclusion, atHeight, basis]
  rw [he]
  exact planeInclusion.hasFDerivAt.add_const (z • basis 2)

theorem spatialD_slice {H : Space → ℝ} (hH : ContDiff ℝ ∞ H)
    (X : Plane) (z : ℝ) (j : Fin 2) :
    PlanarHamiltonian.spatialD j (fun Y => H (atHeight Y z)) X =
      scalarD j.castSucc H (atHeight X z) := by
  have hd := (hH.differentiable (by simp) (atHeight X z)).hasFDerivAt.comp X
    (atHeight_hasFDerivAt X z)
  unfold PlanarHamiltonian.spatialD scalarD
  change fderiv ℝ (H ∘ fun Y => atHeight Y z) X (PlanarHamiltonian.basis j) = _
  rw [hd.fderiv]
  change fderiv ℝ H (atHeight X z) (planeInclusion (PlanarHamiltonian.basis j)) = _
  rw [planeInclusion_basis]

theorem suspensionField_atHeight {H : FieldExpr} (hH : H.Valid)
    (X : Plane) (z : ℝ) :
    SpatialExpression.suspensionField H (atHeight X z) =
      atHeight (PlanarHamiltonian.field
        (fun Y => SpatialExpression.spatialValue H (atHeight Y z)) X)
        (unitSpatialClock X) := by
  have hd := spatialD_slice (SpatialExpression.spatialValue_smooth hH) X z
  funext j
  fin_cases j
  · change scalarD 1 (SpatialExpression.spatialValue H) (atHeight X z) = _
    simpa [atHeight, PlanarHamiltonian.field] using (hd 1).symm
  · change -scalarD 0 (SpatialExpression.spatialValue H) (atHeight X z) = _
    simpa [atHeight, PlanarHamiltonian.field] using congrArg Neg.neg (hd 0).symm
  · change unitSpatialClock (horizontal (atHeight X z)) = unitSpatialClock X
    congr 1
    ext k
    fin_cases k <;> rfl

/-- The exact planar slice equation determines each finite interval of the
actual autonomous material flow. -/
theorem suspensionField_tracks_interval {H : FieldExpr} (hH : H.Valid)
    (hP : CubePeriodic 1 (SpatialExpression.spatialValue H))
    {ψ : ℝ → Plane} {Φ : ℝ → Space → Space} {a b : ℝ} (x : Space)
    (hc : ContinuousOn (suspensionPath ψ) (Icc a b))
    (hp : suspensionPath ψ a = Φ a x)
    (hψ : ∀ s ∈ Ico a b, HasDerivAt ψ
      (PlanarHamiltonian.field (fun Y => SpatialExpression.spatialValue H (atHeight Y s))
        (ψ s)) s)
    (hg : ∀ s ∈ Ico a b, unitSpatialClock (ψ s) = 1)
    (hΦ : IsMaterialFlow 1 (fun y => SpatialExpression.suspensionField H y.2) Φ) :
    EqOn (fun s => Φ s x) (suspensionPath ψ) (Icc a b) := by
  obtain ⟨K, hK⟩ := periodic_spatial_lipschitz (by norm_num : (0 : ℝ) < 1)
    (SpatialExpression.suspensionField_smooth hH)
    (SpatialExpression.suspensionField_periodic hH hP)
  apply hΦ.eqOn_of_candidate (fun _ => hK) x (suspensionPath ψ) hc hp
  intro s hs
  have hd := suspensionPath_hasDerivAt
    (V := fun t X => PlanarHamiltonian.field
      (fun Y => SpatialExpression.spatialValue H (atHeight Y t)) X)
    (g := unitSpatialClock) (hψ s hs) (hg s hs)
  have he : spatialSuspension
      (fun t X => PlanarHamiltonian.field
        (fun Y => SpatialExpression.spatialValue H (atHeight Y t)) X)
      unitSpatialClock (suspensionPath ψ s) =
      SpatialExpression.suspensionField H (suspensionPath ψ s) := by
    rw [suspensionPath, suspensionField_atHeight hH]
    simp only [spatialSuspension, atHeight_horizontal]
    rfl
  rwa [he] at hd

end ForcedComputation

end

end OAI
