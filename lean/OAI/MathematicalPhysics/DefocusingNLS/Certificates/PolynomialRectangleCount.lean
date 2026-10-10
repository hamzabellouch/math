import OAI.MathematicalPhysics.DefocusingNLS.Certificates.PolynomialAnalyticMultiplicity

namespace OAI

/-! # Finite rectangle counts for the certified simple polynomial roots -/

open Polynomial Set
open scoped Classical

namespace DefocusingNLS

theorem rectangleZeroCount_of_simple_orders (V : ℝ) (f : ℂ → ℂ) (S : Finset ℂ)
    (ho : ∀ z, analyticOrderAt f z = if z ∈ S then 1 else 0) :
    rectangleZeroCount V f = ((S.filter (fun z => z ∈ countingRectangle V)).card : ℕ∞) := by
  classical
  unfold rectangleZeroCount
  rw [tsum_subtype]
  rw [tsum_eq_sum (s := S)]
  · simp only [Set.indicator_apply]
    rw [← Finset.sum_filter]
    calc
      _ = ∑ _z ∈ S.filter (fun z => z ∈ countingRectangle V), (1 : ℕ∞) := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [ho, ite_eq_left (Finset.mem_filter.mp hz).1]
      _ = _ := by simp
  · intro z hz
    rw [Set.indicator_apply]
    split_ifs <;> simp [ho, hz]

theorem rectangleZeroCount_polynomial_translate (p : Polynomial ℂ) (hp : p ≠ 0)
    (hsimple : p.roots.Nodup) (c : ℂ) (V : ℝ) :
    rectangleZeroCount V (fun z => p.eval (z + c)) =
      ((p.roots.toFinset.filter (fun w => w - c ∈ countingRectangle V)).card : ℕ∞) := by
  classical
  let S := p.roots.toFinset.image (fun w => w - c)
  have hS (z : ℂ) : z ∈ S ↔ z + c ∈ p.roots := by
    constructor
    · intro hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      simpa using hw
    · intro hz
      exact Finset.mem_image.mpr ⟨z + c, by simpa using hz, by simp⟩
  have ho (z : ℂ) : analyticOrderAt (fun w => p.eval (w + c)) z =
      if z ∈ S then 1 else 0 := by
    rw [analyticOrderAt_polynomial_translate p hp c z, ← Polynomial.count_roots]
    by_cases hz : z ∈ S
    · rw [ite_eq_left hz, Multiset.count_eq_one_of_mem hsimple ((hS z).mp hz)]
      rfl
    · rw [ite_eq_right hz, Multiset.count_eq_zero.mpr (fun h => hz ((hS z).mpr h))]
      rfl
  rw [rectangleZeroCount_of_simple_orders V _ S ho]
  dsimp [S]
  rw [Finset.filter_image, Finset.card_image_of_injective]
  intro z w hz
  exact sub_left_inj.mp hz

end DefocusingNLS

end OAI
