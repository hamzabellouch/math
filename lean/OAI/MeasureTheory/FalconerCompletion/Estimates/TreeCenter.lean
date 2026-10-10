import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Measures.PathIndex

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

section
section
namespace CurrentFalconer.TreeND
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def treeCenter (p : CellPath d) : EuclideanSpace ℝ (Fin d) :=
  ambientGridCenter p.length (fun i => (pathIndex p i : ℤ))

lemma treeCenter_mem (p : CellPath d) : treeCenter p ∈ treeCell p :=
  ambientGridCenter_mem _ _

noncomputable def occupiedCenterCells (ν : Measure (EuclideanSpace ℝ (Fin d)))
    (p : ℕ) (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) : Finset (CellPath d) := by
  classical
  exact (dyadicPaths p).filter fun q => 0 < ν (treeCell q) ∧ treeCenter q ∈ ball x r

lemma treeCenter_ball_card {g : ℕ} (T : Finset (CellPath d)) (hT : T ⊆ dyadicPaths g)
    (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 ≤ r)
    (hdist : ∀ p ∈ T, dist (treeCenter p) x ≤ r) :
    (T.card : ℝ) ≤ (2*(2:ℝ)^g*r+5)^d := by
  classical
  let f : CellPath d → (Fin d → ℤ) := fun p i => pathIndex p i
  have hf : Set.InjOn f T := by
    intro p hp q hq he
    apply pathIndex_injective (((mem_dyadicPaths _ _).mp (hT hp)).trans
      ((mem_dyadicPaths _ _).mp (hT hq)).symm)
    funext i
    have hei : (pathIndex p i : ℤ) = pathIndex q i := congrFun he i
    exact_mod_cast hei
  have hh := ambientGridCenter_ball_card g (T.image f) x hr (fun a ha => by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
    have he : p.length = g := (mem_dyadicPaths _ _).mp (hT hp)
    simpa only [treeCenter,he] using hdist p hp)
  rwa [Finset.card_image_of_injOn hf] at hh

end CurrentFalconer.TreeND
end
end

end OAI
