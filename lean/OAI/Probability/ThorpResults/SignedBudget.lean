import OAI.Probability.ThorpResults.UniformMoments

namespace OAI

noncomputable section
open scoped BigOperators

namespace ThorpNine.Harmonic.Thorp.LowPlanes
open Specht

def signedEntropy (α β : YoungDiagram) : ℝ :=
  (∑ x : Cell α, Real.log ((α.card + β.card : ℕ) / (α.rowLen (row x) : ℝ))) +
  (∑ x : Cell β, Real.log ((α.card + β.card : ℕ) / (β.rowLen (row x) : ℝ)))

def budgetCoefficient (a : ℝ) (d : ℕ) : ℝ :=
  a * (1 - 1 / (2 * Real.sqrt d))

def remainderBudget (κ : ℝ) (d l : ℕ) : ℝ :=
  if l = 0 then 0 else
    max 0 (budgetCoefficient κ d * l * Real.log (2 ^ d : ℝ) -
      l * Real.log ((2 ^ d : ℝ) / l))

def logWeightedMoment (d r : ℕ) (μ : Shapes (2 ^ d)) : EReal :=
  (ENNReal.ofReal (weightedMoment d r μ)).log

lemma row_entropy_nonneg (α : YoungDiagram) (n : ℕ) (hn : α.card ≤ n)
    (x : Cell α) : 0 ≤ Real.log ((n : ℝ) / (α.rowLen (row x) : ℝ)) := by
  have hp : 0 < α.rowLen (row x) :=
    lt_of_le_of_lt (Nat.zero_le _) (YoungDiagram.mem_iff_lt_rowLen.mp x.2)
  have hle : α.rowLen (row x) ≤ n :=
    ((α.rowLen_anti 0 (row x) (Nat.zero_le _)).trans (rowLen_zero_le_card α)).trans hn
  apply Real.log_nonneg
  apply (le_div_iff₀ (by exact_mod_cast hp)).mpr
  simpa using (show (α.rowLen (row x) : ℝ) ≤ n by exact_mod_cast hle)

lemma signedEntropy_nonneg (α β : YoungDiagram) : 0 ≤ signedEntropy α β := by
  apply add_nonneg
  · exact Finset.sum_nonneg (fun x _ => row_entropy_nonneg α _ (Nat.le_add_right _ _) x)
  · exact Finset.sum_nonneg (fun x _ => row_entropy_nonneg β _ (Nat.le_add_left _ _) x)

lemma budgetCoefficient_nonneg {a : ℝ} (ha : 0 ≤ a) {d : ℕ} (hd : 1 ≤ d) :
    0 ≤ budgetCoefficient a d := by
  have hs : 1 ≤ Real.sqrt (d : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hd)
  have hden : 0 < 2 * Real.sqrt (d : ℝ) := by positivity
  have hdiv : 1 / (2 * Real.sqrt (d : ℝ)) ≤ 1 :=
    (div_le_one hden).mpr (by linarith)
  exact mul_nonneg ha (sub_nonneg.mpr hdiv)

lemma remainderBudget_nonneg (κ : ℝ) (d l : ℕ) : 0 ≤ remainderBudget κ d l := by
  unfold remainderBudget
  split_ifs
  · exact le_rfl
  · exact le_max_left _ _

theorem signed_occurrence_moment (η κ : ℝ) (hη : 0 < η) :
    ∃ r : ℕ, 1 ≤ r ∧ ∀ d : ℕ, 1 ≤ d →
      ∀ (μ : Shapes (2 ^ d)) (α β γ : YoungDiagram),
        α.card + β.card + γ.card = 2 ^ d →
        logWeightedMoment d r μ ≤
          ((budgetCoefficient η d * signedEntropy α β +
            remainderBudget κ d γ.card : ℝ) : EReal) := by
  obtain ⟨r, _, hr, h⟩ := uniform_weighted_moment
  refine ⟨r, by omega, ?_⟩
  intro d hd μ α β γ _
  have hz : logWeightedMoment d r μ ≤ 0 := by
    apply ENNReal.log_le_zero_iff.mpr
    exact (ENNReal.ofReal_le_one).mpr (h d μ)
  apply hz.trans
  exact_mod_cast add_nonneg
    (mul_nonneg (budgetCoefficient_nonneg hη.le hd) (signedEntropy_nonneg α β))
    (remainderBudget_nonneg κ d γ.card)

end ThorpNine.Harmonic.Thorp.LowPlanes

end

end OAI
