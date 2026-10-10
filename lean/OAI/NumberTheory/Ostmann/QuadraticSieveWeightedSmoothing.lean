import OAI.NumberTheory.Ostmann.QuadraticSieveSquarefreeKernel
import OAI.NumberTheory.Ostmann.QuadraticSieveWeight
import OAI.NumberTheory.Ostmann.QuadraticSieveWeightedNorm

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped SchwartzMap

noncomputable def smoothingRows (M K : ℕ) : Finset ℤ := by
  classical
  exact (Finset.Icc 1 (3 * (M : ℤ))).filter
    (fun m => Odd m ∧ K < squarefreeKernel m.natAbs)

@[simp] theorem mem_smoothingRows {M K : ℕ} {m : ℤ} :
    m ∈ smoothingRows M K ↔
      1 ≤ m ∧ m ≤ 3 * (M : ℤ) ∧ Odd m ∧ K < squarefreeKernel m.natAbs := by
  classical
  simp only [smoothingRows, Finset.mem_filter, Finset.mem_Icc]
  tauto

noncomputable def smoothingWeight (M : ℕ) (m : ℤ) : ℝ :=
  sieveBump ((m : ℝ) / (M : ℝ))

theorem smoothingWeight_nonneg (M : ℕ) (m : ℤ) : 0 ≤ smoothingWeight M m :=
  sieveBump_nonneg _

noncomputable def smoothingEnergy (M K : ℕ) (S : Finset ℕ) (a : ℕ → ℂ) : ℝ :=
  weightedNumeratorEnergy (smoothingRows M K) S (smoothingWeight M) a

noncomputable def smoothingNorm (M K : ℕ) (S : Finset ℕ) : ℝ :=
  weightedNumeratorNorm (smoothingRows M K) S (smoothingWeight M)

theorem smoothingNorm_nonneg (M K : ℕ) (S : Finset ℕ) : 0 ≤ smoothingNorm M K S :=
  weightedNumeratorNorm_nonneg _ _ _

theorem smoothingEnergy_le_norm (M K : ℕ) (S : Finset ℕ) (a : ℕ → ℂ) :
    smoothingEnergy M K S a ≤ smoothingNorm M K S * coefficientEnergy S a :=
  weightedNumeratorEnergy_le_norm _ _ _ _

noncomputable def smoothingSummand (M K : ℕ) (S : Finset ℕ) (a : ℕ → ℂ) (m : ℤ) : ℂ :=
  if 0 < m ∧ Odd m ∧ K < squarefreeKernel m.natAbs then
    sieveWeight ((m : ℝ) / (M : ℝ)) *
      ((‖∑ n ∈ S, a n * (jacobiSym m n : ℂ)‖ ^ 2 : ℝ) : ℂ) else 0

theorem smoothingSummand_zero_of_not_mem {M : ℕ} (hM : 0 < M) (K : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) (m : ℤ) (hm : m ∉ smoothingRows M K) :
    smoothingSummand M K S a m = 0 := by
  classical
  unfold smoothingSummand
  by_cases hc : 0 < m ∧ Odd m ∧ K < squarefreeKernel m.natAbs
  · rw [ite_eq_left hc]
    have hout : 3 * (M : ℤ) < m := by
      by_contra h
      exact hm (mem_smoothingRows.mpr ⟨by omega, le_of_not_gt h, hc.2.1, hc.2.2⟩)
    have hMr : (0 : ℝ) < M := by exact_mod_cast hM
    have houtr : 3 * (M : ℝ) < (m : ℝ) := by exact_mod_cast hout
    have hz : sieveWeight ((m : ℝ) / (M : ℝ)) = 0 := by
      apply sieveWeight_zero
      right
      apply (le_div_iff₀ hMr).mpr
      linarith
    rw [hz, zero_mul]
  · simp only [ite_eq_right hc]

theorem summable_smoothingSummand {M : ℕ} (hM : 0 < M) (K : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) : Summable (smoothingSummand M K S a) :=
  summable_of_ne_finset_zero (s := smoothingRows M K)
    (fun m hm => smoothingSummand_zero_of_not_mem hM K S a m hm)

theorem smoothingEnergy_eq_tsum {M : ℕ} (hM : 0 < M) (K : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) :
    (smoothingEnergy M K S a : ℂ) = ∑' m : ℤ, smoothingSummand M K S a m := by
  rw [tsum_eq_sum (s := smoothingRows M K)
    (fun m hm => smoothingSummand_zero_of_not_mem hM K S a m hm)]
  unfold smoothingEnergy weightedNumeratorEnergy
  push_cast
  apply Finset.sum_congr rfl
  intro m hm
  obtain ⟨hm1, hm3, hmo, hmK⟩ := mem_smoothingRows.mp hm
  have hp : 0 < m ∧ Odd m ∧ K < squarefreeKernel m.natAbs := ⟨by omega, hmo, hmK⟩
  simp only [smoothingSummand, ite_eq_left hp, sieveWeight_apply, smoothingWeight, Complex.ofReal_pow]

end Ostmann.QuadraticSieve

end OAI
