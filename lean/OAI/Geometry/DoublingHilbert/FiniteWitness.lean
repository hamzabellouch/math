import Mathlib
import OAI.Geometry.DoublingHilbert.FiniteCompactness
import OAI.Geometry.DoublingHilbert.Main

namespace OAI

open Set Metric
noncomputable section
namespace CompactBanach

theorem finite_witness (k : ℕ) {A : ℝ} (hA : 1 ≤ A) :
    ∃ s : Finset DoublingHilbert.constructedSet,
      ¬ ∃ f : s → EuclideanSpace ℝ (Fin k), ∃ a : ℝ, 0 < a ∧
        ∀ x y : s, a * dist x y ≤ dist (f x) (f y) ∧
          dist (f x) (f y) ≤ A * a * dist x y := by
  let o : DoublingHilbert.constructedSet :=
    ⟨DoublingHilbert.point 0 0, DoublingHilbert.point_mem _ _ (DoublingHilbert.admissible_zero _)⟩
  apply finite_witness_of_no_embedding o (le_trans zero_le_one hA)
  rintro ⟨f, hf⟩
  apply DoublingHilbert.no_scaled_embedding f (a := 1) zero_lt_one hA
  simpa only [one_mul, mul_one] using hf

                                                                          
                                       
theorem finite_witness_card (k : ℕ) {A : ℝ} (hA : 1 ≤ A) :
    ∃ s : Finset DoublingHilbert.constructedSet, 2 ≤ s.card ∧
      ¬ ∃ f : s → EuclideanSpace ℝ (Fin k), ∃ a : ℝ, 0 < a ∧
        ∀ x y : s, a * dist x y ≤ dist (f x) (f y) ∧
          dist (f x) (f y) ≤ A * a * dist x y := by
  classical
  obtain ⟨s, hs⟩ := finite_witness k hA
  refine ⟨s, ?_, hs⟩
  by_contra! hc
  have hc' : s.card ≤ 1 := by omega
  apply hs
  refine ⟨fun _ => 0, 1, zero_lt_one, fun x y => ?_⟩
  have hxy : x = y := Subtype.ext (Finset.card_le_one.mp hc' x x.property y y.property)
  simp [hxy]

end CompactBanach
end

end OAI
