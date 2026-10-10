import OAI.Geometry.SurfaceImmersion.Geometry.PreferredNormalAvoidanceGlue
import OAI.Geometry.SurfaceImmersion.Correction.SmoothCoverCutoff

namespace OAI

/-! The global preferred normal is constructed from the two local fields;
its smooth cutoff is obtained from the open cover, not assumed. -/
noncomputable section
open Set Manifold
open scoped ContDiff
namespace ClosedSurfaceR4
open VelocityFrame NormalFrame
variable {M κ : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]

theorem preferredNormal_from_cover {F a b : M → Space} {U V : Set M}
    (hU : IsOpen U) (hV : IsOpen V)
    (ha : ContMDiffOn planeModel spaceModel ∞ a U)
    (hb : ContMDiffOn planeModel spaceModel ∞ b V)
    (ha1 : ∀ p ∈ U, ‖a p‖ = 1) (hb1 : ∀ p ∈ V, ‖b p‖ = 1)
    (haN : ∀ p ∈ U, ∀ v : TangentSpace planeModel p,
      inner ℝ (surfaceDifferential F p v) (a p) = 0)
    (hbN : ∀ p ∈ V, ∀ v : TangentSpace planeModel p,
      inner ℝ (surfaceDifferential F p v) (b p) = 0)
    (hne : ∀ p ∈ U ∩ V, b p ≠ -a p)
    (hcover : U ∪ V = univ)
    (C : κ → Set M) (B : κ → M → Vec)
    (haAvoid : ∀ k p, p ∈ C k → p ∈ U → spaceCoordinates (a p) ≠ -normalize (B k p))
    (hbAvoid : ∀ k p, p ∈ C k → p ∈ V → spaceCoordinates (b p) ≠ -normalize (B k p))
    (hpositive : ∀ k p, p ∈ C k → p ∈ U ∩ V →
      0 < inner ℝ (spaceCoordinates.symm (B k p)) (a p) ∧
      0 < inner ℝ (spaceCoordinates.symm (B k p)) (b p)) :
    ∃ N : PreferredNormal F,
      (∀ p ∈ U \ V, N.vector p = a p) ∧
      (∀ p ∈ V \ U, N.vector p = b p) ∧
      ∀ k p, p ∈ C k → spaceCoordinates (N.vector p) ≠ -normalize (B k p) := by
  obtain ⟨χ,hχ,hχU,hχV,hχ01⟩ := smooth_cover_cutoff hU hV hcover
  obtain ⟨N,hNa,hNb,havoid⟩ := preferredNormal_collar_avoidance hU hV ha hb ha1 hb1 haN hbN hne
    hχ hχU hχV hχ01 C B haAvoid hbAvoid (by
      intro k p hp h0 h1
      apply hpositive k p hp
      constructor
      · exact hχU (subset_tsupport χ (by change χ p ≠ 0; exact h0.ne'))
      · apply hχV
        apply subset_tsupport
        change 1-χ p ≠ 0
        linarith)
  refine ⟨N,?_,?_,havoid⟩
  · intro p hp
    apply hNa
    have hz : 1-χ p = 0 := image_eq_zero_of_notMem_tsupport (f := fun q : M => (1:ℝ)-χ q) (fun h => hp.2 (hχV h))
    linarith
  · intro p hp
    exact hNb p (image_eq_zero_of_notMem_tsupport (fun h => hp.2 (hχU h)))

end ClosedSurfaceR4

end

end OAI
