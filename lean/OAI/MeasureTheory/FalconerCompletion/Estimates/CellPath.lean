import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereMeasure

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

section
section
namespace CurrentFalconer.TreeND
abbrev CellPath (d : ℕ) := List (Fin d → Bool)
variable {d : ℕ}

def dyadicPaths {d : ℕ} : ℕ → Finset (CellPath d)
  | 0 => {[]}
  | n+1 => Finset.univ.biUnion fun a : Fin d → Bool =>
      (dyadicPaths n).image (List.cons a)

@[simp] theorem mem_dyadicPaths (n : ℕ) (p : CellPath d) :
    p ∈ dyadicPaths n ↔ p.length = n := by
  induction n generalizing p with
  | zero => simp [dyadicPaths]
  | succ n ih =>
    cases p with
    | nil => simp [dyadicPaths]
    | cons a p => simp [dyadicPaths, ih]

lemma dyadicPaths_card_le (N : ℕ) : (dyadicPaths (d := d) N).card ≤ (2^d)^N := by
  classical
  induction N with
  | zero => simp [dyadicPaths]
  | succ N ih =>
    calc
      _ ≤ ∑ a ∈ (Finset.univ : Finset (Fin d → Bool)),
        ((dyadicPaths N).image (List.cons a)).card := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ (Finset.univ : Finset (Fin d → Bool)), (2^d)^N :=
        Finset.sum_le_sum (fun _ _ => Finset.card_image_le.trans ih)
      _ = _ := by simp [pow_succ,Nat.mul_comm]

end CurrentFalconer.TreeND
end
end

end OAI
