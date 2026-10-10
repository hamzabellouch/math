import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedPrimeGeometry

namespace OAI

/-! A distinguished prime row is empty outside its forced complementary
norm range. This keeps the later mass sum linear in the output length. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma stoppedDistinguished_row_eq_zero {B ρ a b : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {j j₀ k h : ℕ} (hj : j < geometricBinCount ρ B) {Z Q : ℝ} {early : Bool}
    {c d e : Eisenstein} (hc : primary c) (hd : primary d)
    (hbig : b/geometricBinLower ρ B j < norm (c*d)) (F : Eisenstein → ℂ) :
    (∑ p ∈ stoppedDistinguishedPrimeSet B ρ a b j j₀ k h Z Q early c d e, F p) = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  exact (not_lt_of_ge (stoppedDistinguished_complement_bound hρ hρ₂ hj hc hd hp) hbig).elim

end CubicFirstMoment

end

end OAI
