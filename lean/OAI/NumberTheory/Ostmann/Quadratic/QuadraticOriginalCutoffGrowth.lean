import OAI.NumberTheory.Ostmann.Quadratic.QuadraticWholeLowGrowth
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticWholeHighGrowth
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticWholeMiddleGrowth
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticRoundedCorrectionGeometry

namespace OAI

/-! # The complete bounds apply to the literal rounded Poisson cutoffs -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_second_lower_le_upper {X J : ℝ} (hX : 0 ≤ X) (hJ : 1 ≤ J) :
    quadraticSecondLower X J ≤ quadraticSecondUpper X J := by
  have hlo : quadraticSecondLower X J ≤ X := by
    unfold quadraticSecondLower
    exact div_le_self hX (by linarith)
  have hhi : X ≤ quadraticSecondUpper X J := by
    unfold quadraticSecondUpper
    nlinarith [mul_le_mul_of_nonneg_left hJ hX]
  exact hlo.trans hhi

theorem quadratic_original_low_cut {M H N J : ℝ} {e B b d : ℕ}
    (hM : 0 < M) (hH : 0 < H) (hHN : H ≤ N) (he : 0 < e) (hB : 0 < B) (hJ : 1 ≤ J)
    (hb : B ≤ b) (hb' : b ≤ 2 * B)
    (hcut : (d : ℝ) ≤ quadraticSecondUpper (quadraticCorrectionBase M H e b) J) :
    (d : ℝ) ≤ 2 * quadraticCorrectionBase M N e B * J := by
  have hhi := (quadratic_correction_cutoff_band hM hH he hB hJ hb hb').2.2.2
  have hmono := quadratic_correction_base_mono hM hH hHN he hB
  exact (hcut.trans hhi).trans (by gcongr)

theorem quadratic_original_lower_cut {M H N J : ℝ} {e B b d : ℕ}
    (hM : 0 < M) (hH : 0 < H) (hN : 0 < N) (hNH : N ≤ 2 * H)
    (he : 0 < e) (hB : 0 < B) (hJ : 1 ≤ J) (hb : B ≤ b) (hb' : b ≤ 2 * B)
    (hcut : quadraticSecondLower (quadraticCorrectionBase M H e b) J < (d : ℝ)) :
    quadraticCorrectionBase M N e B / (4 * (2 * J)) ≤ (d : ℝ) := by
  have hlo := (quadratic_correction_cutoff_band hM hH he hB hJ hb hb').1
  have hdouble := quadratic_correction_base_double hM hH hN hNH he hB
  calc
    _ ≤ (2 * quadraticCorrectionBase M H e B) / (4 * (2 * J)) := by gcongr
    _ = quadraticCorrectionBase M H e B / (4 * J) := by ring
    _ ≤ quadraticSecondLower (quadraticCorrectionBase M H e b) J := hlo
    _ ≤ d := hcut.le

theorem quadratic_whole_original_low_growth {C ε ξ M H J : ℝ} (hC : 0 ≤ C)
    {e B N Q : ℕ} (hM : 0 < M) (hH : 0 < H) (hHN : H ≤ N)
    (he : 0 < e) (hB : 0 < B) (hN : 0 < N) (hQ : 1 ≤ Q) (hJ : 1 ≤ J)
    (R : ℕ → ℕ → Prop) (v w : ℕ → ℂ)
    (hv : ∀ n < N, v n = 0) (hw : ∀ n < N, w n = 0)
    (hmat : ∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) :
    ‖((M / e : ℝ) : ℂ) * quadraticLowCorrectionTotal B N Q
        (fun d b => R d b ∧ (d : ℝ) ≤ quadraticSecondUpper (quadraticCorrectionBase M H e b) J) v w‖ ≤
      ((Nat.log 2 Q + 2 : ℕ) : ℝ) *
        (96 * J * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
          quadraticCorrectionGrowthScale C ε ξ M e B N v w) := by
  apply quadratic_whole_low_growth hC hM he hB hN hQ hJ _ v w hv hw _ hmat
  intro d _ b hb hbB hp
  exact quadratic_original_low_cut hM hH hHN he hB hJ hbB
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).2 hp.2

theorem quadratic_whole_original_high_growth {C ε ξ M H J : ℝ} (hC : 0 ≤ C)
    {e B N Q : ℕ} (hM : 0 < M) (hH : 0 < H) (hNH : (N : ℝ) ≤ 2 * H)
    (he : 0 < e) (hB : 0 < B) (hN : 0 < N) (hQ : 1 ≤ Q) (hJ : 1 ≤ J)
    (R : ℕ → ℕ → Prop) (v w : ℕ → ℂ)
    (hmat : ∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) :
    ‖((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) * quadraticHighCorrectionTotal B N Q
        (fun d b => R d b ∧ quadraticSecondUpper (quadraticCorrectionBase M H e b) J < (d : ℝ)) v w‖ ≤
      ((Nat.log 2 Q + 2 : ℕ) : ℝ) *
        (384 * (2 * J) * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
          quadraticCorrectionGrowthScale C ε ξ M e B N v w) := by
  apply quadratic_whole_high_growth hC hM he hB hN hQ (by linarith : 1 ≤ 2 * J) _ v w _ hmat
  intro d _ b hb hbB hp
  have hX : 0 ≤ quadraticCorrectionBase M H e b := Real.sqrt_nonneg _
  apply quadratic_original_lower_cut hM hH (by exact_mod_cast hN) hNH he hB hJ hbB
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).2
  exact (quadratic_second_lower_le_upper hX hJ).trans_lt hp.2

end Ostmann

end OAI
