import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.NativeHausdorffGrowth

namespace OAI

/-!
# Euclidean coordinates for projection disks

An orthonormal basis identifies a finite-dimensional subspace with Euclidean
space. Composing this isometry with orthogonal projection preserves projection
norms and transfers coverage of closed disks into these coordinates.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_projection_disk_coordinates {n d : ℕ}
    (P : Submodule ℝ (Ambient d)) (hdim : Module.finrank ℝ P = n) :
    ∃ T : Ambient d →L[ℝ] Ambient n,
      (∀ x, ‖T x‖ = ‖P.starProjection x‖) ∧
      (∀ x, ‖T x‖ ≤ ‖x‖) ∧
      ∀ (A : Set (Ambient d)) (p : Ambient d) (r : ℝ),
        closedBall (P.orthogonalProjectionOnto p) r ⊆ P.orthogonalProjectionOnto '' A →
          closedBall (T p) r ⊆ T '' A := by
  let b : OrthonormalBasis (Fin n) ℝ P :=
    (stdOrthonormalBasis ℝ P).reindex (finCongr hdim)
  let E : P ≃ₗᵢ[ℝ] Ambient n := b.repr
  let T : Ambient d →L[ℝ] Ambient n :=
    E.toLinearIsometry.toContinuousLinearMap.comp P.orthogonalProjectionOnto
  have hnorm : ∀ x, ‖T x‖ = ‖P.starProjection x‖ := by
    intro x
    change ‖E (P.orthogonalProjectionOnto x)‖ = _
    rw [E.norm_map]
    rfl
  refine ⟨T, hnorm, fun x => (hnorm x).trans_le (P.norm_starProjection_apply_le x), ?_⟩
  intro A p r hcover u hu
  have hu' : E.symm u ∈ closedBall (P.orthogonalProjectionOnto p) r := by
    change dist (E.symm u) (P.orthogonalProjectionOnto p) ≤ r
    rw [← E.dist_map, E.apply_symm_apply]
    exact hu
  obtain ⟨x, hx, heq⟩ := hcover hu'
  refine ⟨x, hx, ?_⟩
  change E (P.orthogonalProjectionOnto x) = u
  rw [heq, E.apply_symm_apply]

end

end RieszRectifiability

end OAI
