import OAI.Analysis.CircleDomains.Rigidity.AxialChordGeometry

namespace OAI

/-! The coordinate swap preserves the actual closed disk family. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity

 theorem axialSwap_involutive (i : Fin 2) : Involutive (axialSwap i) := by
  intro z
  fin_cases i <;> apply Complex.ext <;> simp [axialSwap]

 theorem axialSwap_mem_closedBall_iff (i : Fin 2) (z c : ℂ) (r : ℝ) :
    axialSwap i z ∈ closedBall (axialSwap i c) r ↔ z ∈ closedBall c r := by
  simp only [mem_closedBall,axialSwap_dist]

 theorem axialSwap_pairwise_disjoint {κ : Type*} (i : Fin 2) (c : κ → ℂ) (r : κ → ℝ)
    (hd : Pairwise (Disjoint on fun j => closedBall (c j) (r j))) :
    Pairwise (Disjoint on fun j => closedBall (axialSwap i (c j)) (r j)) := by
  intro j k hjk
  apply disjoint_left.mpr
  intro z hz hz'
  have hj : axialSwap i z ∈ closedBall (c j) (r j) := by
    simpa only [axialSwap_involutive i (c j)] using
      (axialSwap_mem_closedBall_iff i z (axialSwap i (c j)) (r j)).mpr hz
  have hk : axialSwap i z ∈ closedBall (c k) (r k) := by
    simpa only [axialSwap_involutive i (c k)] using
      (axialSwap_mem_closedBall_iff i z (axialSwap i (c k)) (r k)).mpr hz'
  exact disjoint_left.mp (hd hjk) hj hk

 theorem horizontal_mem_swapped_disk (i : Fin 2) (x y : ℝ) (c : ℂ) (r : ℝ) :
    (⟨x,y⟩ : ℂ) ∈ closedBall (axialSwap i c) r ↔
      complexCoordinateLine i y x ∈ closedBall c r := by
  rw [← axialSwap_line i y x]
  exact axialSwap_mem_closedBall_iff i _ _ _

end CircleDomainRigidity

end

end OAI
