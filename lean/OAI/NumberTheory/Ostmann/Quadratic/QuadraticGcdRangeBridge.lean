import Mathlib.Algebra.Order.Floor.Ring
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGcdCoefficientBridge
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticDivisorMomentBound

namespace OAI

/-! # A genuine dyadic range after removing the common divisor -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

noncomputable def quadraticRangeCoeff (L : ℕ) (v : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n ≤ L then v n else 0

theorem quadratic_gcd_pair_range_extension {L U : ℕ} (hLU : L ≤ U)
    (v w : ℕ → ℂ) (F : ℕ → ℂ) :
    (∑ z ∈ quadraticGcdPairs U 1,
      quadraticRangeCoeff L v z.1 * conj (quadraticRangeCoeff L w z.2) * F (z.1 * z.2)) =
      ∑ z ∈ quadraticGcdPairs L 1, v z.1 * conj (w z.2) * F (z.1 * z.2) := by
  have hsub : quadraticGcdPairs L 1 ⊆ quadraticGcdPairs U 1 := by
    intro z hz
    obtain ⟨hz, hg⟩ := Finset.mem_filter.mp hz
    obtain ⟨hs, ht⟩ := Finset.mem_product.mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨oddSquarefreeRange_mono hLU hs, oddSquarefreeRange_mono hLU ht⟩, hg⟩
  have hz (z : ℕ × ℕ) (hu : z ∈ quadraticGcdPairs U 1) (hl : z ∉ quadraticGcdPairs L 1) :
      quadraticRangeCoeff L v z.1 * conj (quadraticRangeCoeff L w z.2) * F (z.1 * z.2) = 0 := by
    obtain ⟨hu, hg⟩ := Finset.mem_filter.mp hu
    obtain ⟨hs, ht⟩ := Finset.mem_product.mp hu
    by_cases h₁ : z.1 ≤ L
    · have h₂ : ¬ z.2 ≤ L := by
        intro h₂
        apply hl
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hg⟩
        · obtain ⟨hr, ho, hsf⟩ := Finset.mem_filter.mp hs
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, h₁⟩, ho, hsf⟩
        · obtain ⟨hr, ho, hsf⟩ := Finset.mem_filter.mp ht
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, h₂⟩, ho, hsf⟩
      simp [quadraticRangeCoeff, h₂]
    · simp [quadraticRangeCoeff, h₁]
  rw [← Finset.sum_subset hsub hz]
  apply Finset.sum_congr rfl
  intro z hz
  obtain ⟨hz, _⟩ := Finset.mem_filter.mp hz
  obtain ⟨hs, ht⟩ := Finset.mem_product.mp hz
  have h₁ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).2
  have h₂ := (Finset.mem_Icc.mp (Finset.mem_filter.mp ht).1).2
  simp [quadraticRangeCoeff, h₁, h₂]

noncomputable def quadraticGcdBlockSize (R D : ℕ) : ℕ := ⌈(R : ℝ) / D⌉₊

noncomputable def quadraticGcdBlockCoeff (R D : ℕ) (v : ℕ → ℂ) : ℕ → ℂ :=
  quadraticRangeCoeff ((2 * R) / D) (quadraticDivisibilityCoeff D v)

theorem quadratic_gcd_block_range (R D : ℕ) :
    (2 * R) / D ≤ 2 * quadraticGcdBlockSize R D := by
  have h₁ : (((2 * R) / D : ℕ) : ℝ) ≤ (2 * (R : ℝ)) / D := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using (Nat.cast_div_le (m := 2 * R) (n := D) (α := ℝ))
  have h₂ : (R : ℝ) / D ≤ (quadraticGcdBlockSize R D : ℝ) := Nat.le_ceil _
  have hh : (((2 * R) / D : ℕ) : ℝ) ≤ 2 * (quadraticGcdBlockSize R D : ℝ) := by
    rw [mul_div_assoc] at h₁
    linarith
  exact_mod_cast hh

theorem quadratic_gcd_block_lower {R D : ℕ} (hD : 0 < D) (v : ℕ → ℂ)
    (hv : ∀ n < R, v n = 0) {n : ℕ} (hn : n < quadraticGcdBlockSize R D) :
    quadraticGcdBlockCoeff R D v n = 0 := by
  have hnr : (n : ℝ) < (R : ℝ) / D := (Nat.lt_ceil).mp hn
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hmul : D * n < R := by
    have hh := (lt_div_iff₀ hDR).mp hnr
    rw [mul_comm] at hh
    exact_mod_cast hh
  simp [quadraticGcdBlockCoeff, quadraticRangeCoeff, quadraticDivisibilityCoeff, hv _ hmul]

theorem quadratic_gcd_block_reindex {R D : ℕ} (hD : Squarefree D) (ho : Odd D)
    (v w : ℕ → ℂ) (F : ℕ → ℂ) :
    (∑ z ∈ quadraticGcdPairs (2 * R) D,
      v z.1 * conj (w z.2) * F (quadraticPairKernel z.1 z.2)) =
      ∑ z ∈ quadraticGcdPairs (2 * quadraticGcdBlockSize R D) 1,
        quadraticGcdBlockCoeff R D v z.1 * conj (quadraticGcdBlockCoeff R D w z.2) * F (z.1 * z.2) := by
  rw [quadratic_gcd_coefficient_reindex hD ho]
  exact (quadratic_gcd_pair_range_extension (quadratic_gcd_block_range R D)
    (quadraticDivisibilityCoeff D v) (quadraticDivisibilityCoeff D w) F).symm

theorem quadratic_range_energy {L U : ℕ} (hLU : L ≤ U) (v : ℕ → ℂ) :
    quadraticSieveEnergy U (quadraticRangeCoeff L v) = quadraticSieveEnergy L v := by
  unfold quadraticSieveEnergy
  have he : (∑ n ∈ oddSquarefreeRange L, ‖quadraticRangeCoeff L v n‖ ^ 2) =
      ∑ n ∈ oddSquarefreeRange U, ‖quadraticRangeCoeff L v n‖ ^ 2 := by
    apply Finset.sum_subset (oddSquarefreeRange_mono hLU)
    intro n hn hnL
    have hnl : ¬ n ≤ L := by
      intro hh
      apply hnL
      obtain ⟨hr, ho, hsf⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, hh⟩, ho, hsf⟩
    simp [quadraticRangeCoeff, hnl]
  rw [← he]
  apply Finset.sum_congr rfl
  intro n hn
  simp [quadraticRangeCoeff, (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2]

theorem quadratic_gcd_block_energy {R D : ℕ} (hD : Squarefree D) (ho : Odd D)
    (v : ℕ → ℂ) :
    quadraticSieveEnergy (2 * quadraticGcdBlockSize R D) (quadraticGcdBlockCoeff R D v) ≤
      quadraticSieveEnergy (2 * R) v := by
  unfold quadraticGcdBlockCoeff
  rw [quadratic_range_energy (quadratic_gcd_block_range R D)]
  exact quadratic_gcd_coefficient_energy hD ho v

theorem quadraticGcdBlockSize_pos {R D : ℕ} (hR : 0 < R) (hD : 0 < D) :
    0 < quadraticGcdBlockSize R D := by
  apply Nat.ceil_pos.mpr
  exact div_pos (by exact_mod_cast hR) (by exact_mod_cast hD)

theorem quadraticGcdBlockSize_le {R D : ℕ} (hD : 0 < D) :
    quadraticGcdBlockSize R D ≤ R := by
  apply Nat.ceil_le.mpr
  exact div_le_self (Nat.cast_nonneg _) (by exact_mod_cast hD)

theorem quadraticGcdBlockSize_comparable {R D : ℕ} (hD : 0 < D) (hDR : D ≤ R) :
    (R : ℝ) / D ≤ quadraticGcdBlockSize R D ∧
      (quadraticGcdBlockSize R D : ℝ) ≤ 2 * ((R : ℝ) / D) := by
  have hpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hbase : 1 ≤ (R : ℝ) / D := (le_div_iff₀ hpos).mpr (by simpa only [one_mul] using (show (D : ℝ) ≤ R by exact_mod_cast hDR))
  constructor
  · exact Nat.le_ceil _
  · have hh := Nat.ceil_lt_add_one (show 0 ≤ (R : ℝ) / D by positivity)
    change (quadraticGcdBlockSize R D : ℝ) < (R : ℝ) / D + 1 at hh
    linarith

theorem quadratic_gcd_block_divisor_moment (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ R D : ℕ, Squarefree D → Odd D → ∀ v : ℕ → ℂ,
      quadraticDivisorMoment (2 * quadraticGcdBlockSize R D) (quadraticGcdBlockCoeff R D v) ≤
        C * (2 * (R : ℝ)) ^ ε * quadraticSieveEnergy (2 * R) v := by
  obtain ⟨C, hC, hc⟩ := quadratic_divisor_moment_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro R D hD ho v
  apply (hc _ _).trans
  have hsize : (2 * quadraticGcdBlockSize R D : ℝ) ≤ 2 * R := by
    exact_mod_cast Nat.mul_le_mul_left 2 (quadraticGcdBlockSize_le (Nat.pos_of_ne_zero hD.ne_zero))
  have hpow := Real.rpow_le_rpow (by positivity) hsize hε.le
  have henergy := quadratic_gcd_block_energy (R := R) hD ho v
  have hn : 0 ≤ quadraticSieveEnergy (2 * quadraticGcdBlockSize R D) (quadraticGcdBlockCoeff R D v) :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hpow hC.le) henergy hn (by positivity)

end Ostmann

end OAI
