import OAI.Geometry.NodalSets.Elliptic.RealBallCubeContainmentLemmas
import OAI.Geometry.NodalSets.Elliptic.RealSquareCutoffWeakGradient

namespace OAI

namespace Yau
open Set MeasureTheory
noncomputable section

theorem real_indicator_difference_localize {n : ℕ} (Q : Set (Coord n))
    (u chi : Coord n → ℝ) (i : Fin n) (h : ℝ) (x : Coord n)
    (hx : x ∈ Q) (ht : x+Pi.single i h ∈ Q)
    (hc : chi x=1) (hct : chi (x+Pi.single i h)=1) :
    realDifferenceQuotient i h (Q.indicator u) x =
      realDifferenceQuotient i h (fun y ↦ chi y*u y) x := by
  simp only [realDifferenceQuotient,indicator_of_mem hx,indicator_of_mem ht,hc,hct,one_mul]

theorem real_supported_difference_localize {n : ℕ} (Q : Set (Coord n))
    (u chi eta : Coord n → ℝ) (i : Fin n) (h : ℝ)
    (hend : ∀ x ∈ tsupport eta, x ∈ Q ∧ x+Pi.single i h ∈ Q ∧
      chi x=1 ∧ chi (x+Pi.single i h)=1) :
    (fun x ↦ eta x*realDifferenceQuotient i h (Q.indicator u) x) =
      (fun x ↦ eta x*realDifferenceQuotient i h (fun y ↦ chi y*u y) x) := by
  funext x
  by_cases hx : x ∈ tsupport eta
  · obtain ⟨hxQ,htQ,hc,hct⟩ := hend x hx
    rw [real_indicator_difference_localize Q u chi i h x hxQ htQ hc hct]
  · rw [image_eq_zero_of_notMem_tsupport hx,zero_mul,zero_mul]

theorem real_square_gradient_difference_pairing_localize {n : ℕ} (Q : Set (Coord n))
    (u chi eta q : Coord n → ℝ) (V : Fin n → Coord n → ℝ)
    (i j : Fin n) (h : ℝ)
    (hend : ∀ x ∈ tsupport eta, x ∈ Q ∧ x+Pi.single i h ∈ Q ∧
      chi x=1 ∧ chi (x+Pi.single i h)=1) :
    (fun x ↦ realDifferenceQuotient i h (Q.indicator u) x*realSquareCutoffGradient eta q V j x) =
      (fun x ↦ realDifferenceQuotient i h (fun y ↦ chi y*u y) x*realSquareCutoffGradient eta q V j x) := by
  funext x
  by_cases hx : x ∈ tsupport eta
  · obtain ⟨hxQ,htQ,hc,hct⟩ := hend x hx
    rw [real_indicator_difference_localize Q u chi i h x hxQ htQ hc hct]
  · simp only [realSquareCutoffGradient,image_eq_zero_of_notMem_tsupport hx,
      zero_pow (by decide : (2:ℕ)≠0),zero_mul,mul_zero,add_zero]

end
end Yau

end OAI
