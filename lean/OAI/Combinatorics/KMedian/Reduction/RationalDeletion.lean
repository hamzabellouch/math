import Mathlib
import OAI.Combinatorics.KMedian.Reduction.DeletionHistory

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

def rationalEligible (I : Instance) (B : ℚ) (U : Finset (Fin I.n)) : Finset (Fin I.n) :=
  U.filter (fun i => rationalCost I (U.erase i)-rationalCost I U ≤ B)

def rationalDeleteStep (I : Instance) (B : ℚ) (U : Finset (Fin I.n)) : Finset (Fin I.n) :=
  if I.k < U.card then
    if h : (rationalEligible I B U).Nonempty then U.erase ((rationalEligible I B U).min' h) else U
  else U

def rationalHistory (I : Instance) (B : ℚ) (T : Finset (Fin I.n)) : ℕ → Finset (Fin I.n)
  | 0 => T
  | t+1 => rationalDeleteStep I B (rationalHistory I B T t)

theorem cast_rationalEligible (I : Instance) (B : ℚ) (U : Finset (Fin I.n)) :
    rationalEligible I B U=eligible I (B:ℝ) U := by
  ext i
  simp only [rationalEligible,eligible,mem_filter,Rat.cast_le]

theorem cast_rationalStep (I : Instance) (B : ℚ) (U : Finset (Fin I.n)) :
    rationalDeleteStep I B U=deleteStep I (B:ℝ) U := by
  simp only [rationalDeleteStep,deleteStep,cast_rationalEligible]

theorem cast_rationalHistory (I : Instance) (B : ℚ) (T : Finset (Fin I.n)) (t : ℕ) :
    rationalHistory I B T t=deletionHistory I (B:ℝ) T t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [rationalHistory,deletionHistory,cast_rationalStep,ih]

def deletionEndpoints (I : Instance) (T : Finset (Fin I.n)) (c : ℕ) : Finset (Finset (Fin I.n)) :=
  (insert 0 (deletionValues I T c)).image (fun r => rationalHistory I r T c)

theorem deletionEndpoints_card (I : Instance) (T : Finset (Fin I.n)) (c : ℕ) :
    (deletionEndpoints I T c).card ≤ (c+1)*(T.card+1)^(c+1)+1 := by
  calc
    _ ≤ (insert 0 (deletionValues I T c)).card := card_image_le
    _ ≤ (deletionValues I T c).card+1 := card_insert_le _ _
    _ ≤ _ := Nat.add_le_add_right (card_deletionValues I T c) 1

theorem ideal_endpoint_mem (I : Instance) (T : Finset (Fin I.n)) (c : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    deletionHistory I B T c ∈ deletionEndpoints I T c := by
  obtain ⟨r,hr,hh⟩ := enumerate_ideal_history I T c hB
  exact mem_image.mpr ⟨r,hr,(cast_rationalHistory I r T c).trans (hh c le_rfl).symm⟩

end MetricKMedian.Reduction
end
end

end OAI
