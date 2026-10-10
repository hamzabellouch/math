import OAI.Combinatorics.LowSpaceSubsetSum.Counting.Model
import Mathlib.Data.Finset.Card

namespace OAI

/-!
# Uniform sign randomization of a fixed solution

The sign mask is uniform among all indexed subsets. Toggling a fixed solution
is a bijection on that exact finite space, so it is also uniform. This is the
distributional step preceding the representation balance event.
-/

namespace LowSpaceSubsetSum

open scoped symmDiff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def toggleEquiv (S : Finset ι) : Finset ι ≃ Finset ι where
  toFun F := S ∆ F
  invFun F := S ∆ F
  left_inv F := symmDiff_symmDiff_cancel_left S F
  right_inv F := symmDiff_symmDiff_cancel_left S F

/-- Exact event counting for a uniformly chosen sign mask. -/
theorem toggle_event_card (S : Finset ι) (A : Finset (Finset ι)) :
    (Finset.univ.filter fun F : Finset ι => S ∆ F ∈ A).card = A.card := by
  classical
  have himage : (Finset.univ.filter fun F : Finset ι => S ∆ F ∈ A).image
      (fun F => S ∆ F) = A := by
    ext D
    constructor
    · intro hD
      obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hD
      exact (Finset.mem_filter.mp hF).2
    · intro hD
      refine Finset.mem_image.mpr ⟨S ∆ D, ?_, symmDiff_symmDiff_cancel_left S D⟩
      simpa using hD
  calc
    _ = ((Finset.univ.filter fun F : Finset ι => S ∆ F ∈ A).image
        (fun F => S ∆ F)).card :=
      (Finset.card_image_of_injective _ (toggleEquiv S).injective).symm
    _ = A.card := congrArg Finset.card himage

/-- The equality is of probabilities, not merely of supports. -/
theorem toggle_event_probability (S : Finset ι) (A : Finset (Finset ι)) :
    ((Finset.univ.filter fun F : Finset ι => S ∆ F ∈ A).card : ℝ) /
      (2 : ℝ) ^ Fintype.card ι = A.card / (2 : ℝ) ^ Fintype.card ι := by
  rw [toggle_event_card]

end LowSpaceSubsetSum

end OAI
