import OAI.Analysis.Cotype.DampedPolynomial

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem rectangle_mem_rectangularIndices {s : Finset ι} {t : Finset κ}
    (hs : s.Nonempty) (ht : t.Nonempty) (k l : ℕ) :
    rectangle s t ∈ rectangularIndices k l ↔ k = s.card ∧ l = t.card := by
  rw [mem_rectangularIndices]
  constructor
  · rintro ⟨s', t', hk, hl, he⟩
    obtain ⟨rfl, rfl⟩ := rectangle_injective_nonempty hs ht he.symm
    exact ⟨hk.symm, hl.symm⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨s, t, rfl, rfl, rfl⟩

theorem Ckl_eq_sum_univ (f : ((ι × κ) → Bool) → ℝ) (k l : ℕ) :
    Ckl f k l = ∑ P, if P ∈ rectangularIndices k l then fourier f P else 0 := by
  simp [Ckl]

def groupedPolynomial (f : ((ι × κ) → Bool) → ℝ) (a b c : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (Fintype.card ι + 1),
    ∑ l ∈ Finset.range (Fintype.card κ + 1), Ckl f k l * a ^ k * b ^ l * c ^ (k*l)

theorem groupedPolynomial_eq_expectation {f : ((ι × κ) → Bool) → ℝ}
    (hf : IsOdd f) (hr : RankOneSupported f) (a b c : ℝ) :
    groupedPolynomial f a b c = dampedExpectation f a b c := by
  rw [dampedExpectation_fourier]
  unfold groupedPolynomial
  simp_rw [Ckl_eq_sum_univ, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext l; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P _
  by_cases hz : fourier f P = 0
  · simp [hz]
  obtain ⟨s, t, hs, ht, he⟩ := odd_rank_one_support hf hz (hr P hz)
  have hsne : s.Nonempty := Finset.card_pos.mp (by obtain ⟨k, hk⟩ := hs; omega)
  have htne : t.Nonempty := Finset.card_pos.mp (by obtain ⟨k, hk⟩ := ht; omega)
  have hsc : s.card < Fintype.card ι + 1 := Nat.lt_succ_of_le (Finset.card_le_univ s)
  have htc : t.card < Fintype.card κ + 1 := Nat.lt_succ_of_le (Finset.card_le_univ t)
  rw [← he, dampedExpectation_odd_rectangle s t hs ht]
  simp_rw [rectangle_mem_rectangularIndices hsne htne]
  simp [ite_and, hsc, htc, mul_assoc]

theorem groupedPolynomial_bound {f : ((ι × κ) → Bool) → ℝ} {M a b : ℝ}
    (hf : IsOdd f) (hr : RankOneSupported f) (hM : ∀ S, |f S| ≤ M)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    |groupedPolynomial f a b (1/2)| ≤ M := by
  rw [groupedPolynomial_eq_expectation hf hr]
  exact dampedExpectation_bound ha hb (by norm_num) hM

end Cotype

end

end OAI
