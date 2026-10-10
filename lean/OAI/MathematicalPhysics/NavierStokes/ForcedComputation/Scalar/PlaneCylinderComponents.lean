import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CylinderLiftH2
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneClassicalRegularity

namespace OAI

/-! Component identities needed to transfer the planar L2 and strong time
derivative estimates to the three-dimensional classical solution. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set
open scoped ContDiff

theorem triangularVelocity_horizontal_component (a : ℝ → Plane → Plane)
    (w : ℝ → Plane → ℝ) (t : ℝ) (x : Space) (j : Fin 2) :
    triangularVelocity a w (t, x) j.castSucc = a t (horizontalLinear x) j := by
  fin_cases j <;> simp [triangularVelocity, triangularLift, planeInclusion, basis]

theorem triangularVelocity_vertically_periodic (a : ℝ → Plane → Plane)
    (w : ℝ → Plane → ℝ) (t : ℝ) :
    VerticallyPeriodic (fun x => triangularVelocity a w (t, x)) := by
  intro x n
  simp only [triangularVelocity, triangularLift, map_add, map_smul,
    horizontalLinear_basis_two, smul_zero, add_zero]

theorem planeTemporalDerivative_component {a : ℝ → Plane → Plane}
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) (t : ℝ) (x : Plane) (j : Fin 2) :
    planeTemporalDerivative (fun s y => a s y j) t x = deriv (fun s => a s x) t j := by
  have hscalar := planeTemporalDerivative_hasDerivAt (F := fun s y => a s y j)
    ((contDiff_apply ℝ ℝ j).comp ha) t x
  have hvector : HasDerivAt (fun s => a s x) (deriv (fun s => a s x) t) t :=
    ((ha.comp (contDiff_id.prodMk contDiff_const)).differentiable
    (by simp) t).hasDerivAt
  have hcoord := (ContinuousLinearMap.proj j : Plane →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hvector
  exact hscalar.unique hcoord

theorem GlobalPlaneScalarSolution.initialTimeDerivative_horizontal {ν : ℝ}
    {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : GlobalPlaneScalarSolution ν a h w)
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) {t : ℝ} (ht : 0 ≤ t)
    (x : Space) (j : Fin 2) :
    ShearFlows.initialTimeDerivative (triangularVelocity a w) t x j.castSucc =
      planeTemporalDerivative (fun s y => a s y j) t (horizontalLinear x) := by
  rw [hw.initialTimeDerivative ha ht, planeTemporalDerivative_component ha]
  fin_cases j <;> simp [triangularLift, planeInclusion, basis]

theorem GlobalPlaneScalarSolution.initialTimeDerivative_vertical {ν : ℝ}
    {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : GlobalPlaneScalarSolution ν a h w)
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    ShearFlows.initialTimeDerivative (triangularVelocity a w) t x 2 =
      planeTimeDerivative ν a h w t (horizontalLinear x) := by
  rw [hw.initialTimeDerivative ha ht]
  simp [triangularLift, planeInclusion, basis, planeTimeDerivative]

theorem CylinderContinuousL2.mono {F : ℝ → Plane × ℝ → ℝ} {S T : Set ℝ}
    (hF : CylinderContinuousL2 F T) (hST : S ⊆ T) : CylinderContinuousL2 F S := by
  obtain ⟨U, hU, hUF⟩ := hF
  exact ⟨U, hU.mono hST, fun t ht => hUF t (hST ht)⟩

theorem CylinderC1L2.mono {F G : ℝ → Plane × ℝ → ℝ} {S T : Set ℝ}
    (hF : CylinderC1L2 F G T) (hST : S ⊆ T) : CylinderC1L2 F G S := by
  obtain ⟨U, V, hU, hV, hUV⟩ := hF
  refine ⟨U, V, hU.mono hST, hV.mono hST, ?_⟩
  intro t ht
  obtain ⟨hu, hv, hd⟩ := hUV t (hST ht)
  exact ⟨hu, hv, hd.mono hST⟩

theorem CylinderCInH2.mono {F : ℝ → Space → ℝ} {S T : Set ℝ}
    (hF : CylinderCInH2 F T) (hST : S ⊆ T) : CylinderCInH2 F S :=
  ⟨hF.1.mono hST, fun j => (hF.2.1 j).mono hST,
    fun j k => (hF.2.2 j k).mono hST⟩

theorem CylinderCInH2.congr_slices {F G : ℝ → Space → ℝ} {S : Set ℝ}
    (hF : CylinderCInH2 F S) (hFG : ∀ t ∈ S, F t = G t) : CylinderCInH2 G S :=
  ⟨hF.1.congr_slices (fun t ht => by rw [hFG t ht]),
    fun j => (hF.2.1 j).congr_slices (fun t ht => by rw [hFG t ht]),
    fun j k => (hF.2.2 j k).congr_slices (fun t ht => by rw [hFG t ht])⟩

theorem cylinderCInH1_zero (S : Set ℝ) : CylinderCInH1 (fun _ _ => 0) S := by
  refine ⟨cylinderContinuousL2_zero S, ?_⟩
  intro j
  have hz : scalarSpatialD j (fun _ : Space => (0 : ℝ)) = fun _ => 0 := by
    funext x
    simp [scalarSpatialD]
  change CylinderContinuousL2 (fun t => cylinderPullback (scalarSpatialD j (fun _ => 0))) S
  rw [hz]
  exact cylinderContinuousL2_zero S

end ForcedComputation.VelocityDetector

end

end OAI
