import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace Problem336.SchauderTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma measure_abs_gt_le_fourth_moment (Z : Ω → ℝ) (hZ : AEMeasurable Z P)
    (C : ℝ≥0∞) (hC : ∫⁻ ω, ‖Z ω‖ₑ ^ (4 : ℕ) ∂P ≤ C)
    (b : ℝ) (hb : 0 < b) :
    P {ω | b < |Z ω|} ≤ C / (ENNReal.ofReal b) ^ (4 : ℕ) := by
  calc
    P {ω | b < |Z ω|} ≤ P {ω | (ENNReal.ofReal b) ^ (4 : ℕ) ≤ ‖Z ω‖ₑ ^ (4 : ℕ)} := by
      apply measure_mono
      intro ω hω
      change (ENNReal.ofReal b) ^ (4 : ℕ) ≤ ‖Z ω‖ₑ ^ (4 : ℕ)
      apply pow_le_pow_left₀ (by positivity)
      simpa [Real.enorm_eq_ofReal_abs] using ENNReal.ofReal_le_ofReal hω.le
    _ ≤ (∫⁻ ω, ‖Z ω‖ₑ ^ (4 : ℕ) ∂P) / (ENNReal.ofReal b) ^ (4 : ℕ) := by
      apply meas_ge_le_lintegral_div
      · fun_prop
      · exact pow_ne_zero _ (ENNReal.ofReal_ne_zero_iff.mpr hb)
      · finiteness
    _ ≤ C / (ENNReal.ofReal b) ^ (4 : ℕ) := by gcongr

lemma fourth_threshold_identity (C : ℝ≥0∞) (n : ℕ) :
    C / (ENNReal.ofReal ((4 / 3 : ℝ) ^ n)) ^ (4 : ℕ) =
      C * ENNReal.ofReal (81 / 256 : ℝ) ^ n := by
  rw [ENNReal.ofReal_pow (by norm_num), ← pow_mul, Nat.mul_comm n 4, pow_mul,
    div_eq_mul_inv, ENNReal.inv_pow]
  have hb : ((ENNReal.ofReal (4 / 3 : ℝ)) ^ (4 : ℕ))⁻¹ =
      ENNReal.ofReal (81 / 256 : ℝ) := by
    rw [← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_inv_of_pos (by positivity)]
    norm_num
  rw [hb]

lemma measure_bad_block_le (Z : (n : ℕ) → Fin (2 ^ n) → Ω → ℝ)
    (hZ : ∀ n k, AEMeasurable (Z n k) P) (C : ℝ≥0∞)
    (hC : ∀ n k, ∫⁻ ω, ‖Z n k ω‖ₑ ^ (4 : ℕ) ∂P ≤ C) (n : ℕ) :
    P {ω | ∃ k : Fin (2 ^ n), (4 / 3 : ℝ) ^ n < |Z n k ω|} ≤
      C * ENNReal.ofReal (81 / 128 : ℝ) ^ n := by
  classical
  calc
    P {ω | ∃ k : Fin (2 ^ n), (4 / 3 : ℝ) ^ n < |Z n k ω|} ≤
        ∑ k : Fin (2 ^ n), P {ω | (4 / 3 : ℝ) ^ n < |Z n k ω|} := by
      rw [show {ω | ∃ k : Fin (2 ^ n), (4 / 3 : ℝ) ^ n < |Z n k ω|} =
        ⋃ k : Fin (2 ^ n), {ω | (4 / 3 : ℝ) ^ n < |Z n k ω|} by ext ω; simp]
      exact measure_iUnion_fintype_le P _
    _ ≤ ∑ _k : Fin (2 ^ n), C * ENNReal.ofReal (81 / 256 : ℝ) ^ n := by
      apply Finset.sum_le_sum
      intro k _
      rw [← fourth_threshold_identity]
      exact measure_abs_gt_le_fourth_moment (Z n k) (hZ n k) C (hC n k) _
        (pow_pos (by norm_num) n)
    _ = C * ENNReal.ofReal (81 / 128 : ℝ) ^ n := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_pow, Nat.cast_ofNat]
      rw [mul_left_comm, ← mul_pow]
      have hr : (2 : ℝ≥0∞) * ENNReal.ofReal (81 / 256 : ℝ) =
          ENNReal.ofReal (81 / 128 : ℝ) := by
        calc
          (2 : ℝ≥0∞) * ENNReal.ofReal (81 / 256 : ℝ) =
              ENNReal.ofReal ((2 : ℝ) * (81 / 256)) := by
            simp only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
          _ = _ := by norm_num
      rw [hr]

theorem ae_eventually_dyadic_bound
    (Z : (n : ℕ) → Fin (2 ^ n) → Ω → ℝ)
    (hZ : ∀ n k, AEMeasurable (Z n k) P) (C : ℝ≥0∞) (hCfin : C < ∞)
    (hC : ∀ n k, ∫⁻ ω, ‖Z n k ω‖ₑ ^ (4 : ℕ) ∂P ≤ C) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ k : Fin (2 ^ n), |Z n k ω| ≤ (4 / 3 : ℝ) ^ n := by
  have hs : (∑' n, P {ω | ∃ k : Fin (2 ^ n), (4 / 3 : ℝ) ^ n < |Z n k ω|}) ≠ ∞ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (ENNReal.tsum_le_tsum (measure_bad_block_le Z hZ C hC))
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_lt_top hCfin (tsum_geometric_lt_top.mpr (ENNReal.ofReal_lt_one.mpr (by norm_num)))
  filter_upwards [ae_eventually_notMem hs] with ω hω
  filter_upwards [hω] with n hn
  simpa only [Set.mem_ofPred_eq, not_exists, not_lt] using hn

theorem ae_eventually_gaussian_dyadic_bound
    (Z : (n : ℕ) → Fin (2 ^ n) → Ω → ℝ)
    (hZ : ∀ n k, HasLaw (Z n k) (gaussianReal 0 1) P) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ k : Fin (2 ^ n), |Z n k ω| ≤ (4 / 3 : ℝ) ^ n := by
  let C : ℝ≥0∞ := ∫⁻ x : ℝ, ‖x‖ₑ ^ (4 : ℕ) ∂gaussianReal 0 1
  have hCfin : C < ∞ := by
    have hm := memLp_id_gaussianReal (μ := 0) (v := 1) (4 : ℝ≥0)
    have ht := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := (4 : ℝ≥0∞)) (by norm_num) (by norm_num) hm
    simpa [C] using ht
  apply ae_eventually_dyadic_bound Z (fun n k => (hZ n k).aemeasurable) C hCfin
  intro n k
  exact ((hZ n k).lintegral_comp (f := fun x : ℝ => ‖x‖ₑ ^ (4 : ℕ)) (by fun_prop)).le

def incrementRatio : ℝ := (4 / 3) / Real.sqrt 2

lemma incrementRatio_nonneg : 0 ≤ incrementRatio := by
  unfold incrementRatio
  positivity

lemma incrementRatio_lt_one : incrementRatio < 1 := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [incrementRatio, div_lt_one hs]
  nlinarith

lemma summable_incrementRatio : Summable (fun n : ℕ => incrementRatio ^ n) :=
  summable_geometric_of_lt_one incrementRatio_nonneg incrementRatio_lt_one

theorem ae_eventually_gaussian_increment_bound
    (D : (n : ℕ) → Fin (2 ^ n) → Ω → ℝ)
    (hD : ∀ n k, HasLaw (D n k) (gaussianReal 0 ((2 : ℝ≥0)⁻¹ ^ n)) P) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ k : Fin (2 ^ n), |D n k ω| ≤ incrementRatio ^ n := by
  let Z : (n : ℕ) → Fin (2 ^ n) → Ω → ℝ :=
    fun n k ω => (Real.sqrt 2) ^ n * D n k ω
  have hZ (n : ℕ) (k : Fin (2 ^ n)) : HasLaw (Z n k) (gaussianReal 0 1) P := by
    have hv : (NNReal.mk (((Real.sqrt 2) ^ n) ^ 2) (sq_nonneg _)) *
        ((2 : ℝ≥0)⁻¹ ^ n) = 1 := by
      apply NNReal.coe_injective
      simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_pow,
        NNReal.coe_inv, NNReal.coe_ofNat, NNReal.coe_one]
      rw [← pow_mul, Nat.mul_comm n 2, pow_mul, Real.sq_sqrt (by norm_num), ← mul_pow]
      norm_num
    have h := gaussianReal_const_mul (hD n k) ((Real.sqrt 2) ^ n)
    rw [mul_zero, hv] at h
    exact h
  filter_upwards [ae_eventually_gaussian_dyadic_bound Z hZ] with ω hω
  filter_upwards [hω] with n hn
  intro k
  have hk := hn k
  have hs : 0 < (Real.sqrt 2) ^ n := pow_pos (Real.sqrt_pos.2 (by norm_num)) _
  rw [incrementRatio, div_pow]
  apply (le_div_iff₀ hs).2
  simpa [Z, abs_mul, abs_of_pos hs, mul_comm] using hk

theorem ae_all_eventually_gaussian_increment_bound {I : Type*} [Countable I]
    (D : I → (n : ℕ) → Fin (2 ^ n) → Ω → ℝ)
    (hD : ∀ i n k, HasLaw (D i n k) (gaussianReal 0 ((2 : ℝ≥0)⁻¹ ^ n)) P) :
    ∀ᵐ ω ∂P, ∀ i, ∀ᶠ n in atTop, ∀ k : Fin (2 ^ n),
      |D i n k ω| ≤ incrementRatio ^ n := by
  apply ae_all_iff.mpr
  intro i
  exact ae_eventually_gaussian_increment_bound (D i) (hD i)

end Problem336.SchauderTail

end

end OAI
