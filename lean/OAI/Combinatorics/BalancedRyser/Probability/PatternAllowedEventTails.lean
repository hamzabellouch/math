import OAI.Combinatorics.BalancedRyser.Probability.PatternFixedEventAveraging
import OAI.Combinatorics.BalancedRyser.Probability.PatternTailAsymptotics

namespace OAI

open MeasureTheory Filter
open scoped BigOperators Topology

namespace Balanced.PatternModel

universe u v

theorem measureReal_iUnion_inter_le_of_fixed_le
    (P : PatternModel.{u}) {I : Type v} [Fintype I]
    (K : I → Finset P.Color) (S E : I → Set P.Sample)
    (hS : ∀ i, MeasurableSet (S i)) (hE : ∀ i, MeasurableSet (E i))
    (hdepends : ∀ i x y, (∀ c ∈ K i, x c = y c) → (x ∈ S i ↔ y ∈ S i))
    (C : I → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i x, x ∈ S i →
      P.measure.real ((P.fixCoordinates (K i) x) ⁻¹' E i) ≤ C i) :
    P.measure.real (⋃ i, S i ∩ E i) ≤ ∑ i, C i * P.measure.real (S i) := by
  apply (measureReal_iUnion_fintype_le _).trans
  exact Finset.sum_le_sum (fun i _ =>
    P.measureReal_inter_le_of_fixed_measureReal_le (K i) (S i) (E i)
      (hS i) (hE i) (hdepends i) (C i) (hC i) (hbound i))

end Balanced.PatternModel

namespace Balanced.PatternTails

universe u v

theorem polynomial_allowed_union_tail_le
    (P : PatternModel.{u}) {I : Type v} [Fintype I]
    (K : I → Finset P.Color) (S E : I → Set P.Sample)
    (hS : ∀ i, MeasurableSet (S i)) (hE : ∀ i, MeasurableSet (E i))
    (hdepends : ∀ i x y, (∀ c ∈ K i, x c = y c) → (x ∈ S i ↔ y ∈ S i))
    (q : ℝ) (hq : 0 < q) (d k : ℕ) (A C : ℝ) (hC : 0 ≤ C)
    (hcard : (Fintype.card I : ℝ) ≤ A * q ^ d)
    (htail : ∀ i x, x ∈ S i →
      P.measure.real ((P.fixCoordinates (K i) x) ⁻¹' E i) ≤ C / q ^ (d + k)) :
    P.measure.real (⋃ i, S i ∩ E i) ≤ A * C / q ^ k := by
  apply polynomial_union_tail_le P.measure (fun i => S i ∩ E i)
    q hq d k A C hC hcard
  intro i
  have hnonneg : 0 ≤ C / q ^ (d + k) := div_nonneg hC (pow_nonneg hq.le _)
  have h := P.measureReal_inter_le_of_fixed_measureReal_le (K i) (S i) (E i)
    (hS i) (hE i) (hdepends i) _ hnonneg (htail i)
  exact h.trans (mul_le_of_le_one_right hnonneg measureReal_le_one)

theorem polynomial_allowed_union_tendsto_zero
    (P : ℕ → PatternModel.{u}) (I : ℕ → Type v) [∀ n, Fintype (I n)]
    (K : ∀ n, I n → Finset (P n).Color)
    (S E : ∀ n, I n → Set (P n).Sample)
    (hS : ∀ n i, MeasurableSet (S n i)) (hE : ∀ n i, MeasurableSet (E n i))
    (hdepends : ∀ n i x y,
      (∀ c ∈ K n i, x c = y c) → (x ∈ S n i ↔ y ∈ S n i))
    (q : ℕ → ℕ) (hq : Tendsto q atTop atTop)
    (d : ℕ) (A C : ℝ) (hC : 0 ≤ C)
    (hcard : ∀ᶠ n in atTop, (Fintype.card (I n) : ℝ) ≤ A * (q n : ℝ) ^ d)
    (htail : ∀ᶠ n in atTop, ∀ i x, x ∈ S n i →
      (P n).measure.real (((P n).fixCoordinates (K n i) x) ⁻¹' E n i) ≤
        C / (q n : ℝ) ^ (d + 1)) :
    Tendsto (fun n => (P n).measure.real (⋃ i, S n i ∩ E n i)) atTop (𝓝 0) := by
  apply polynomial_union_tendsto_zero (fun n => (P n).measure) I
    (fun n i => S n i ∩ E n i) q hq d A C hC hcard
  filter_upwards [htail] with n hn
  intro i
  have hnonneg : 0 ≤ C / (q n : ℝ) ^ (d + 1) := by positivity
  have h := (P n).measureReal_inter_le_of_fixed_measureReal_le
    (K n i) (S n i) (E n i) (hS n i) (hE n i) (hdepends n i)
    _ hnonneg (hn i)
  exact h.trans (mul_le_of_le_one_right hnonneg measureReal_le_one)

end Balanced.PatternTails

end OAI
