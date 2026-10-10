import OAI.NumberTheory.JointDickman.Amplification.GeometricDyadicPartition
import OAI.NumberTheory.JointDickman.Amplification.FiniteTripleExtension

namespace OAI

/-! # Exact support of the amplification integrand in each geometric box -/

namespace JointDickman
open Finset

theorem mem_tensor_interval_of_ratio {n : ℕ} {N : ℝ} (hN : 0 < N)
    (hn : (n : ℝ)/N ∈ Set.Icc (1/2 : ℝ) 4) :
    n ∈ Ioc ⌊(1/4 : ℝ)*N⌋₊ ⌊(17/4 : ℝ)*N⌋₊ := by
  have hlo := (le_div_iff₀ hN).mp hn.1
  have hhi := (div_le_iff₀ hN).mp hn.2
  apply mem_Ioc.mpr
  constructor
  · apply (Nat.floor_lt (show 0 ≤ (1/4 : ℝ)*N by positivity)).mpr
    nlinarith
  · apply (Nat.le_floor_iff (show 0 ≤ (17/4 : ℝ)*N by positivity)).mpr
    nlinarith

theorem amplificationBoxWeight_integer_support (B : ℕ) {T N : ℝ}
    (hT : 0 < T) (hN : 0 < N) (s : ℝ) (a b c : ℕ)
    (hw : amplificationBoxWeight B s (a/N) (b/N) (c/(N/T)) ≠ 0) :
    c ∈ Ioc ⌊(1/4 : ℝ)*(N/T)⌋₊ ⌊(17/4 : ℝ)*(N/T)⌋₊ ∧
    a ∈ Ioc ⌊(1/4 : ℝ)*N⌋₊ ⌊(17/4 : ℝ)*N⌋₊ ∧
    b ∈ Ioc ⌊(1/4 : ℝ)*N⌋₊ ⌊(17/4 : ℝ)*N⌋₊ := by
  obtain ⟨ha,hb,hc⟩ := amplificationSpatialProfile_support (right_ne_zero_of_mul hw)
  exact ⟨mem_tensor_interval_of_ratio (div_pos hN hT) ⟨hc.1,hc.2.trans (by norm_num)⟩,
    mem_tensor_interval_of_ratio hN ha,mem_tensor_interval_of_ratio hN hb⟩

noncomputable def amplificationArithmeticTerm (B j : ℕ) (T : ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (c b a : ℕ) : ℝ :=
  if a = b+j*c then
    signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) a*
    signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) h) b*
    coefficientWeight B c*
    (amplificationBump (Real.log c/B)*amplificationBump (a/(T*c))*amplificationBump (b/(T*c)))
  else 0

noncomputable def amplificationBoxTerm (B j : ℕ) (T N : ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (c b a : ℕ) : ℝ :=
  if a = b+j*c then
    signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) g) a*
    signedSplitProductMass (auxiliaryPrimes B) (subsetSiteTest (auxiliaryPrimes B) h) b*
    coefficientWeight B c*
    amplificationBoxWeight B (Real.log (N/T)/B) (a/N) (b/N) (c/(N/T))
  else 0

theorem amplificationBoxTerm_support (B j : ℕ) {T N : ℝ} (hT : 0 < T) (hN : 0 < N)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (c b a : ℕ)
    (hf : amplificationBoxTerm B j T N g h c b a ≠ 0) :
    c ∈ Ioc ⌊(1/4 : ℝ)*(N/T)⌋₊ ⌊(17/4 : ℝ)*(N/T)⌋₊ ∧
    b ∈ Ioc ⌊(1/4 : ℝ)*N⌋₊ ⌊(17/4 : ℝ)*N⌋₊ ∧
    a ∈ Ioc ⌊(1/4 : ℝ)*N⌋₊ ⌊(17/4 : ℝ)*N⌋₊ := by
  have hw : amplificationBoxWeight B (Real.log (N/T)/B) (a/N) (b/N) (c/(N/T)) ≠ 0 := by
    intro hz
    apply hf
    simp only [amplificationBoxTerm,hz,mul_zero,ite_self]
  obtain ⟨hc,ha,hb⟩ := amplificationBoxWeight_integer_support B hT hN _ a b c hw
  exact ⟨hc,hb,ha⟩

theorem amplificationBoxTerm_eq (B j : ℕ) {T N : ℝ} (hT : 0 < T) (hN : 0 < N)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (c b a : ℕ) :
    amplificationBoxTerm B j T N g h c b a =
      amplificationArithmeticTerm B j T g h c b a*dyadicPartitionWeight (c/(N/T)) := by
  by_cases hc : c = 0
  · simp [amplificationBoxTerm,amplificationArithmeticTerm,hc,coefficientWeight]
  · have hcpos : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero hc
    unfold amplificationBoxTerm amplificationArithmeticTerm
    rw [amplificationBoxWeight_normalized B hT hN hcpos]
    split_ifs <;> ring


theorem amplificationArithmeticTerm_log_support {B : ℕ} (hB : 0 < B) (j : ℕ) (T : ℝ)
    (g h : (auxiliaryPrimes B → Bool) → ℝ) (c b a : ℕ)
    (hf : amplificationArithmeticTerm B j T g h c b a ≠ 0) :
    (B : ℝ) ≤ Real.log c ∧ Real.log c ≤ 2*B := by
  have hne : amplificationBump (Real.log c/B) ≠ 0 := by
    intro hz
    apply hf
    simp [amplificationArithmeticTerm,hz]
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hh := amplificationBump_support hne
  have hlo := (lt_div_iff₀ hBr).mp hh.1
  have hhi := (div_lt_iff₀ hBr).mp hh.2
  constructor <;> nlinarith

end JointDickman

end OAI
