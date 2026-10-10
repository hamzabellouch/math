import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorSamplerCells
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorStoredSpace

namespace OAI

/-! # The concrete family-sampler storage under the capacity guard -/

namespace LowSpaceSubsetSum.SeparatorSamplerBounds

open RepresentationSetup

private theorem reserve_le (n g u : ℕ) (hn : n+1 ≤ u) (hg : g ≤ n) (hu : 10000 ≤ u) :
    FixedSizeSampleCells.reserve n g+18 ≤ u^5 := by
  have h3 := Nat.pow_le_pow_left (show n ≤ u by omega) 3
  have hg3 := Nat.pow_le_pow_left (show g+1 ≤ u by omega) 3
  have hu3 : u ≤ u^3 := by
    simpa only [pow_one] using pow_le_pow_right' (by omega : 1 ≤ u) (by decide : 1 ≤ 3)
  have hu4 : u ≤ u^4 := by
    simpa only [pow_one] using pow_le_pow_right' (by omega : 1 ≤ u) (by decide : 1 ≤ 4)
  have h34 : u^3 ≤ u^4 := pow_le_pow_right' (by omega) (by decide)
  have ht : 3*n^3+128 ≤ 4*u^3 := by nlinarith only [h3, hu3, hu]
  have hm := Nat.mul_le_mul (show g+1 ≤ u by omega) ht
  have hm' : (g+1)*(3*n^3+128) ≤ 4*u^4 := by
    convert hm using 1; ring
  have hmajor : 133*u^4 ≤ u^5 := by
    calc
      _ ≤ u*u^4 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  unfold FixedSizeSampleCells.reserve
  nlinarith only [hm', hg3, h34, hu4, hu, hmajor]

theorem four_cells {n g : ℕ} (I : Instance n) (hn : 10000 ≤ n) (hg : g ≤ n)
    (C : ℕ) (hC : 2^g ≤ C) (k m : Fin 4 → ℕ) (hk : ∀ i, k i ≤ g)
    (hm : ∀ i, m i ≤ 11*2^g)
    (s : (SeparatorFamilyExecution.coupling n g 4 k m hk).Seed) :
    (SeparatorSamplerCells.run n g 4 k m hk s).2 ≤ inputScale I^6*(C+1) := by
  have hu : n+1 ≤ inputScale I := by unfold inputScale; omega
  have hu0 : 10000 ≤ inputScale I := by omega
  have hr := reserve_le n g (inputScale I) hu hg hu0
  have hp := Nat.mul_le_mul (Nat.mul_le_mul_left 11 hC) hr
  have hc : 44*inputScale I^5 ≤ inputScale I^6 := by
    calc
      _ ≤ inputScale I*inputScale I^5 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  have hmain := Nat.mul_le_mul_left C hc
  have hbase : 208 ≤ inputScale I^6 := by
    have hpow : inputScale I ≤ inputScale I^6 := by
      simpa only [pow_one] using pow_le_pow_right' (by omega : 1 ≤ inputScale I)
        (by decide : 1 ≤ 6)
    omega
  have h := SeparatorSamplerCells.four_cells n g k m hk hm s
  nlinarith only [h, hp, hmain, hbase]

noncomputable def application {g : ℕ} (S : SeparatorExpectation.RoundedParameters g)
    (n : ℕ) (s : (S.samplerCoupling n).Seed) :=
  SeparatorSamplerCells.run n g 4 S.e S.counts S.size_le s

theorem application_value {g : ℕ} (S : SeparatorExpectation.RoundedParameters g)
    (n : ℕ) (s : (S.samplerCoupling n).Seed) :
    (application S n s).1 = SeparatorFamilyExecution.Application.run S n s := by
  exact SeparatorSamplerCells.run_value n g 4 S.e S.counts S.size_le s

theorem application_cells {n g : ℕ} (I : Instance n)
    (S : SeparatorExpectation.RoundedParameters g) (hn : 10000 ≤ n) (hg : g ≤ n)
    (C : ℕ) (hC : 2^g ≤ C) (s : (S.samplerCoupling n).Seed) :
    (application S n s).2 ≤ inputScale I^6*(C+1) :=
  four_cells I hn hg C hC S.e S.counts S.size_le S.counts_le s

/-- The concrete top blocks obey a stronger table-capacity guard, hence
all four sampled families and their unread seed tails fit the same cap. -/
theorem representation_cells {n : ℕ} (R : RepresentationSetup n)
    (h : R.PrimeHistory) (hn : 10000 ≤ n)
    (s : ((RepresentationSetup.separatorParameters h.1.1.2 (by omega)).samplerCoupling n).Seed) :
    (application (RepresentationSetup.separatorParameters h.1.1.2 (by omega)) n s).2 ≤
      inputScale R.input^6*(compressionDictionaryCapacity n+1) := by
  have hg : 2*blockHalf n 0 ≤ n := by
    simp only [blockHalf, Matrix.cons_val_zero]
    omega
  have hpow : 2^(2*blockHalf n 0) ≤ compressionDictionaryCapacity n := by
    exact (Nat.pow_le_pow_right (by decide)
      (show 2*blockHalf n 0 ≤ 2*(2*blockHalf n 0) by omega)).trans
      (RepresentationSetup.separator_table_rate_le_capacity (n := n))
  exact application_cells R.input _ hn hg _ hpow s

end LowSpaceSubsetSum.SeparatorSamplerBounds

end OAI
