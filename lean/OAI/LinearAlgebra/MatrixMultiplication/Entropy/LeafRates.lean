import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ExactStatisticWords
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexTypeEntropy

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

namespace MatrixMultiplication.LeafRates

open MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology

variable {A U : Type*} [Fintype A] [DecidableEq A] [Fintype U]

theorem log_card_supported (statistic : U → A) (counts b : A → ℕ)
    (hb : ∀ a, 0 < counts a → Fintype.card {u : U // statistic u = a} = b a)
    (hbpos : ∀ a, 0 < b a) :
    Real.log (Fintype.card (ExactStatisticWords.Words statistic counts) : ℝ) =
      Real.log (Nat.multinomial Finset.univ counts : ℝ) +
        ∑ a, (counts a : ℝ) * Real.log (b a : ℝ) := by
  rw [ExactStatisticWords.card_of_supported statistic counts b hb, Nat.cast_mul, Nat.cast_prod]
  have hm : (Nat.multinomial Finset.univ counts : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.multinomial_pos Finset.univ counts))
  have hp : (∏ a, (b a ^ counts a : ℕ) : ℝ) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro a _
    exact_mod_cast (Nat.ne_of_gt (pow_pos (hbpos a) _))
  rw [Real.log_mul hm hp, Real.log_prod (s := Finset.univ)
    (f := fun a => ((b a ^ counts a : ℕ) : ℝ))
    (fun a _ => by exact_mod_cast (Nat.ne_of_gt (pow_pos (hbpos a) (counts a))))]
  simp only [Nat.cast_pow, Real.log_pow]

theorem log_card (statistic : U → A) (counts b : A → ℕ)
    (hb : ∀ a, Fintype.card {u : U // statistic u = a} = b a)
    (hbpos : ∀ a, 0 < b a) :
    Real.log (Fintype.card (ExactStatisticWords.Words statistic counts) : ℝ) =
      Real.log (Nat.multinomial Finset.univ counts : ℝ) +
        ∑ a, (counts a : ℝ) * Real.log (b a : ℝ) :=
  log_card_supported statistic counts b (fun a _ => hb a) hbpos

theorem tendsto_log_card_supported (statistic : U → A) (counts b : A → ℕ)
    (hb : ∀ a, 0 < counts a → Fintype.card {u : U // statistic u = a} = b a)
    (hbpos : ∀ a, 0 < b a) (hD : 0 < ∑ a, counts a) :
    Tendsto (fun t : ℕ =>
      Real.log (Fintype.card (ExactStatisticWords.Words statistic (fun a => t * counts a)) : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
        ∑ a, ((counts a : ℝ) / (∑ a, counts a : ℕ)) * Real.log (b a : ℝ))) := by
  have hl := (tendsto_log_multinomial_mul counts hD).add_const
    (∑ a, ((counts a : ℝ) / (∑ a, counts a : ℕ)) * Real.log (b a : ℝ))
  apply hl.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with t ht
  have hbt : ∀ a, 0 < t * counts a → Fintype.card {u : U // statistic u = a} = b a :=
    fun a ha => hb a (by nlinarith)
  rw [log_card_supported statistic (fun a => t * counts a) b hbt hbpos, add_div]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  have ht' : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  have hDsum : (∑ a, (counts a : ℝ)) ≠ 0 := by
    simpa only [Nat.cast_sum] using hD'
  simp only [Nat.cast_mul]
  field_simp [ht', hD', hDsum]

theorem tendsto_log_card (statistic : U → A) (counts b : A → ℕ)
    (hb : ∀ a, Fintype.card {u : U // statistic u = a} = b a)
    (hbpos : ∀ a, 0 < b a) (hD : 0 < ∑ a, counts a) :
    Tendsto (fun t : ℕ =>
      Real.log (Fintype.card (ExactStatisticWords.Words statistic (fun a => t * counts a)) : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
        ∑ a, ((counts a : ℝ) / (∑ a, counts a : ℕ)) * Real.log (b a : ℝ))) :=
  tendsto_log_card_supported statistic counts b (fun a _ => hb a) hbpos hD

end MatrixMultiplication.LeafRates

end

end OAI
