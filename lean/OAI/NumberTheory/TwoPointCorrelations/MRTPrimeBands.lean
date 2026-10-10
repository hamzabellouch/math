import OAI.NumberTheory.TwoPointCorrelations.PrimeReciprocalTheorem
import OAI.NumberTheory.TwoPointCorrelations.MRTTypicalFactors

namespace OAI

/-! Prime-band reciprocal masses used in MRT's typical-factorization sieve.
The only classical input here is the already discharged Mertens theorem. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def mrtPrimeBand (P Q : ℝ) : Finset ℕ :=
  sievePrimesUpTo Q \ sievePrimesUpTo P

lemma mrt_sievePrimesUpTo_mono {P Q : ℝ} (hPQ : P ≤ Q) :
    sievePrimesUpTo P ⊆ sievePrimesUpTo Q := by
  intro p hp
  rcases mem_filter.mp hp with ⟨hp, hprime⟩
  exact mem_filter.mpr ⟨mem_Iic.mpr ((mem_Iic.mp hp).trans (Nat.floor_mono hPQ)), hprime⟩

lemma mrtPrimeBand_prime {P Q : ℝ} {p : ℕ} (hp : p ∈ mrtPrimeBand P Q) : p.Prime :=
  sievePrimesUpTo_prime Q p (mem_sdiff.mp hp).1

lemma mrtPrimeBand_bounds {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    {p : ℕ} (hp : p ∈ mrtPrimeBand P Q) : P < p ∧ (p : ℝ) ≤ Q := by
  have hpQ := (mem_sdiff.mp hp).1
  have hpP := (mem_sdiff.mp hp).2
  refine ⟨?_, sievePrimesUpTo_le Q hQ p hpQ⟩
  by_contra hnot
  have hple : (p : ℝ) ≤ P := le_of_not_gt hnot
  exact hpP (mem_filter.mpr ⟨mem_Iic.mpr ((Nat.le_floor_iff hP).mpr hple),
    mrtPrimeBand_prime hp⟩)

lemma mrtPrimeBand_mass {P Q : ℝ} (hPQ : P ≤ Q) :
    (∑ p ∈ mrtPrimeBand P Q, 1 / (p : ℝ)) =
      (∑ p ∈ sievePrimesUpTo Q, 1 / (p : ℝ)) -
        ∑ p ∈ sievePrimesUpTo P, 1 / (p : ℝ) := by
  exact sum_sdiff_eq_sub (f := fun p : ℕ => (1 : ℝ) / p) (mrt_sievePrimesUpTo_mono hPQ)

/-- Uniform bounded-error reciprocal mass for every positive prime band. -/
theorem mrt_prime_band_mertens : ∃ C : ℝ, 0 ≤ C ∧
    ∀ P Q : ℝ, 2 ≤ P → P ≤ Q →
      |(∑ p ∈ mrtPrimeBand P Q, 1 / (p : ℝ)) -
        (Real.log (Real.log Q) - Real.log (Real.log P))| ≤ C := by
  obtain ⟨C, hC⟩ := primeReciprocalInput
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 2 (by norm_num))
  refine ⟨2 * C, by positivity, ?_⟩
  intro P Q hP hPQ
  rw [mrtPrimeBand_mass hPQ]
  have hQ := hP.trans hPQ
  have he : (∑ p ∈ sievePrimesUpTo Q, 1 / (p : ℝ)) -
      (∑ p ∈ sievePrimesUpTo P, 1 / (p : ℝ)) -
      (Real.log (Real.log Q) - Real.log (Real.log P)) =
      ((∑ p ∈ sievePrimesUpTo Q, 1 / (p : ℝ)) - Real.log (Real.log Q)) -
      ((∑ p ∈ sievePrimesUpTo P, 1 / (p : ℝ)) - Real.log (Real.log P)) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith [hC Q hQ, hC P hP])

theorem mrt_prime_band_product : ∃ C : ℝ, 0 < C ∧
    ∀ P Q : ℝ, 2 ≤ P → P ≤ Q →
      Real.exp (-(∑ p ∈ mrtPrimeBand P Q, 1 / (p : ℝ))) ≤
        C * Real.log P / Real.log Q := by
  obtain ⟨C, hC0, hC⟩ := mrt_prime_band_mertens
  refine ⟨Real.exp C, Real.exp_pos C, ?_⟩
  intro P Q hP hPQ
  have hP1 : 1 < P := lt_of_lt_of_le (by norm_num) hP
  have hQ1 : 1 < Q := hP1.trans_le hPQ
  have hm := (abs_le.mp (hC P Q hP hPQ)).1
  calc
    _ ≤ Real.exp (C + Real.log (Real.log P) - Real.log (Real.log Q)) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = _ := by
      rw [Real.exp_sub, Real.exp_add, Real.exp_log (Real.log_pos hP1),
        Real.exp_log (Real.log_pos hQ1)]

end TwoPointCorrelations

end OAI
