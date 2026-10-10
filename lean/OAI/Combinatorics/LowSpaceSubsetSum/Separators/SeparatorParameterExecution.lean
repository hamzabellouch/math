import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorParameters
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.CountedBinomial
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MeasuredLog2

namespace OAI

/-! # Integer execution of the separator sizes and sample counts

A constant-state power loop and binary-log loop compute the prescribed
sample size. Five multiplicative binomial loops and four integer ceiling
divisions compute the actual family-array lengths.
-/

namespace LowSpaceSubsetSum.SeparatorParameterExecution

open scoped BigOperators

def powerLoop : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, value, work => (value, work + 1)
  | fuel + 1, value, work => powerLoop fuel (value * 3) (work + 3)

theorem powerLoop_formula (fuel value work : ℕ) :
    powerLoop fuel value work = (value * 3 ^ fuel, work + 3 * fuel + 1) := by
  induction fuel generalizing value work with
  | zero => simp [powerLoop]
  | succ fuel ih =>
    simp only [powerLoop, ih, pow_succ]
    congr 1 <;> ring

theorem three_power_bound (m : ℕ) : 3 ^ m ≤ 2 ^ (2 * m) := by
  calc
    3 ^ m ≤ 4 ^ m := Nat.pow_le_pow_left (by decide) m
    _ = 2 ^ (2 * m) := by rw [pow_mul]; rfl

def logBits (m : ℕ) : ℕ × ℕ :=
  let power := powerLoop m 1 0
  let bits := MeasuredLog2.run (2 * m) power.1
  (bits.1, power.2 + bits.2 + 2)

theorem logBits_value (m : ℕ) : (logBits m).1 = SeparatorParameters.logBits m := by
  simp only [logBits, powerLoop_formula, one_mul]
  rw [MeasuredLog2.run_value _ _ (three_power_bound m), Nat.log2_eq_log_two]
  rfl

theorem logBits_work (m : ℕ) : (logBits m).2 ≤ 9 * m + 4 := by
  have h := MeasuredLog2.run_work (2 * m) (3 ^ m)
  simp only [logBits, powerLoop_formula, one_mul, zero_add]
  omega

def sample (g k : ℕ) : ℕ × ℕ :=
  let bits := logBits (4 * g)
  ((8 * g * g - bits.1 * (g - k)) / (16 * g), bits.2 + 12)

theorem sample_value (g k : ℕ) : (sample g k).1 = SeparatorParameters.sampleSize g k := by
  simp only [sample, logBits_value, SeparatorParameters.sampleSize]

theorem sample_work (g k : ℕ) : (sample g k).2 ≤ 36 * g + 16 := by
  have h := logBits_work (4 * g)
  change _ + 12 ≤ _
  omega

def families (g k e : ℕ) : Vector ℕ 4 × ℕ :=
  let numerator := CountedBinomial.run g e
  let denominators := Vector.ofFn (fun i : Fin 4 =>
    CountedBinomial.run (g / 2) (e - balancedBlockCounts 4 k i))
  (Vector.ofFn (fun i : Fin 4 => (10 * numerator.value) ⌈/⌉ denominators[i.val].value),
    8 * numerator.steps + (∑ i : Fin 4, 8 * denominators[i.val].steps + 6) + 10)

theorem families_value (g k e : ℕ) (i : Fin 4) :
    (families g k e).1[i.val] =
      (10 * g.choose e) ⌈/⌉ (g / 2).choose (e - balancedBlockCounts 4 k i) := by
  simp only [families, Vector.getElem_ofFn, CountedBinomial.run_value]

theorem families_work (g k e : ℕ) : (families g k e).2 ≤ 24 * g + 34 := by
  have hn := CountedBinomial.run_steps g e
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) =>
    Nat.mul_le_mul_left 8
      (CountedBinomial.run_steps (g / 2) (e - balancedBlockCounts 4 k i)))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hs
  have hd : 2 * (g / 2) ≤ g := by omega
  change 8 * (CountedBinomial.run g e).steps +
    (∑ i : Fin 4, 8 * (CountedBinomial.run (g / 2) (e - balancedBlockCounts 4 k i)).steps + 6) + 10 ≤ _
  omega

structure Data where
  size : ℕ
  counts : Vector ℕ 4

def run (g k : ℕ) : Data × ℕ :=
  let e := sample g k
  let counts := families g k e.1
  (⟨e.1, counts.1⟩, e.2 + counts.2 + 1)

theorem size_value (g k : ℕ) : (run g k).1.size = SeparatorParameters.sampleSize g k :=
  sample_value g k

theorem counts_value (g k : ℕ) (i : Fin 4) :
    (run g k).1.counts[i.val] = SeparatorParameters.familyCount g k i := by
  simp only [run, sample_value, families_value, SeparatorParameters.familyCount]

theorem work (g k : ℕ) : (run g k).2 ≤ 60 * g + 51 := by
  have he := sample_work g k
  have hc := families_work g k (sample g k).1
  change _ + _ + 1 ≤ _
  omega

theorem rounded_size (g k : ℕ) (hg : 64 ≤ g) (heven : 2 ∣ g)
    (hk : k ≤ g) (hklo : 2 * g ≤ 3 * k) (i : Fin 4) :
    (run g k).1.size = (SeparatorParameters.rounded g k hg heven hk hklo).e i :=
  size_value g k

theorem rounded_counts (g k : ℕ) (hg : 64 ≤ g) (heven : 2 ∣ g)
    (hk : k ≤ g) (hklo : 2 * g ≤ 3 * k) (i : Fin 4) :
    (run g k).1.counts[i.val] = (SeparatorParameters.rounded g k hg heven hk hklo).counts i := by
  rw [counts_value, SeparatorParameters.familyCount_eq g k hg heven hk hklo]

end LowSpaceSubsetSum.SeparatorParameterExecution

end OAI
