import OAI.Analysis.CircleDomains.Sobolev.SobolevCapacityBallCover
import OAI.Analysis.CircleDomains.Selection.GraphCylinderCover

namespace OAI

/-! The unit Sobolev capacity estimate supplies a countable graph cover
with a quantitative quadratic cost and uniformly bounded diameters. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma unit_graph_capacity_cover {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    (huL2 : MemLp (fun p => u (euclideanPlaneCoordinates.symm p)) 2 volume)
    {A : Set (ℝ × ℝ)} (hA : A ⊆ closedBall 0 1)
    (hone : ∀ c ∈ A, 1 ≤ u (euclideanPlaneCoordinates.symm c))
    (f : (ℝ × ℝ) → ℝ) (t : ℝ)
    (hband : ∀ x ∈ A, f x ∈ Icc (t-1) (t+1)) :
    ∃ (U : Set (ℝ × ℝ)) (N : U → ℕ)
      (T : (x : U) → Fin (N x) → Set ((ℝ × ℝ) × ℝ)),
      U.Countable ∧ (fun x => (x,f x)) '' A ⊆ ⋃ x : U, ⋃ j, T x j ∧
      (∀ x j, ediam (T x j) ≤ 8) ∧
      (∑' x : U, ∑' j : Fin (N x), ediam (T x j)^2) ≤
        4194304 * (ENNReal.ofReal (∫ p, (u (euclideanPlaneCoordinates.symm p))^2) +
          coordinateSobolevEnergy V univ) := by
  obtain ⟨U,r,hU,hr,hcover,hcost⟩ :=
    locally_sobolev_unit_ball_cover hu hw hLp huL2 hA hone
  obtain ⟨N,T,hcover',hdiam,hcost'⟩ := graph_cover_of_base_balls hU r zero_lt_one
    (by simpa using hr) hcover f t hband
  refine ⟨U,N,T,hU,hcover',?_,?_⟩
  · simpa using hdiam
  · calc
      _ ≤ 32*∑' x : U, ENNReal.ofReal (r x) := by simpa using hcost'
      _ ≤ 32*(131072*(ENNReal.ofReal (∫ p, (u (euclideanPlaneCoordinates.symm p))^2) +
          coordinateSobolevEnergy V univ)) := mul_le_mul' le_rfl hcost
      _ = _ := by rw [← mul_assoc]; norm_num

end CircleDomainRigidity

end

end OAI
