import OAI.NumberTheory.JointDickman.Analysis.MellinAngularEnergy

namespace OAI

/-! # The bounded floor discrepancy between real and integer dyadic cutoffs -/
namespace JointDickman
open Finset MeasureTheory

lemma mellinPolynomial_consecutive (a : ℕ → ℂ) {K L N : ℕ}
    (hKL : K ≤ L) (hLN : L ≤ N) (t : ℝ) :
    mellinPolynomial (Ioc K N) a t =
      mellinPolynomial (Ioc K L) a t + mellinPolynomial (Ioc L N) a t := by
  simp only [mellinPolynomial_eq_angular]
  exact angularMellinPolynomial_consecutive a hKL hLN _

lemma norm_mellinPolynomial_interval_le (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    {K L : ℕ} (hK : 0 < K) (_hKL : K ≤ L) (t : ℝ) :
    ‖mellinPolynomial (Ioc K L) a t‖ ≤ (L - K : ℕ) / (K : ℝ) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  unfold mellinPolynomial
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _n ∈ Ioc K L, 1 / (K : ℝ) := by
      apply sum_le_sum
      intro n hn
      have hKn : K ≤ n := (mem_Ioc.mp hn).1.le
      have hnr : (0 : ℝ) < n := hKr.trans_le (by exact_mod_cast hKn)
      rw [norm_mul, norm_additivePhase, mul_one, norm_div, Complex.norm_natCast]
      exact (div_le_div_of_nonneg_right (ha n) hnr.le).trans
        (one_div_le_one_div_of_le hKr (by exact_mod_cast hKn))
    _ = _ := by simp [Nat.card_Ioc, div_eq_mul_inv]

lemma nat_floor_four_bounds {X : ℝ} (hX : 0 ≤ X) :
    4 * ⌊X⌋₊ ≤ ⌊4 * X⌋₊ ∧ ⌊4 * X⌋₊ ≤ 4 * ⌊X⌋₊ + 3 := by
  have hlo := Nat.floor_le hX
  have hhi := Nat.lt_floor_add_one X
  constructor
  · apply Nat.le_floor
    push_cast
    linarith
  · have hh : ⌊4 * X⌋₊ < 4 * ⌊X⌋₊ + 4 := by
      apply (Nat.floor_lt (by positivity : (0 : ℝ) ≤ 4 * X)).mpr
      push_cast
      linarith
    omega

/-- The three possible extra floor-endpoint terms contribute only `O(T/N²)`
to the spectral energy. -/
theorem mellinPolynomial_real_cutoff_energy (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    {X A B : ℝ} (hX : 1 ≤ X)
    (hbound : ∀ T : ℝ, 1 ≤ T →
      (∫ t in -T..T, ‖mellinPolynomial (Ioc ⌊X⌋₊ (4 * ⌊X⌋₊)) a t‖ ^ 2) ≤ A + B * T) :
    ∀ T : ℝ, 1 ≤ T →
      (∫ t in -T..T, ‖mellinPolynomial (Ioc ⌊X⌋₊ ⌊4 * X⌋₊) a t‖ ^ 2) ≤
        2 * A + (2 * B + 3 / (⌊X⌋₊ : ℝ) ^ 2) * T := by
  let N := ⌊X⌋₊
  have hN : 0 < N := by
    change 0 < ⌊X⌋₊
    exact Nat.floor_pos.mpr hX
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hlo, hhi⟩ := nat_floor_four_bounds (show 0 ≤ X by linarith)
  have htail (t : ℝ) : ‖mellinPolynomial (Ioc (4 * N) ⌊4 * X⌋₊) a t‖ ≤ 3 / (4 * (N : ℝ)) := by
    have hh := norm_mellinPolynomial_interval_le a ha
      (show 0 < 4 * N by omega) hlo t
    have hdiff : ⌊4 * X⌋₊ - 4 * N ≤ 3 := by omega
    have hdiff' : ((⌊4 * X⌋₊ - 4 * N : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hdiff
    apply hh.trans
    push_cast
    exact div_le_div_of_nonneg_right hdiff' (by positivity)
  intro T hT
  have hpoint (t : ℝ) : ‖mellinPolynomial (Ioc N ⌊4 * X⌋₊) a t‖ ^ 2 ≤
      2 * ‖mellinPolynomial (Ioc N (4 * N)) a t‖ ^ 2 + 2 * (3 / (4 * (N : ℝ))) ^ 2 := by
    rw [mellinPolynomial_consecutive a (by omega : N ≤ 4 * N) hlo]
    have hh := norm_add_le (mellinPolynomial (Ioc N (4 * N)) a t)
      (mellinPolynomial (Ioc (4 * N) ⌊4 * X⌋₊) a t)
    have hb := htail t
    have hn := norm_nonneg (mellinPolynomial (Ioc N (4 * N)) a t)
    have ht := norm_nonneg (mellinPolynomial (Ioc (4 * N) ⌊4 * X⌋₊) a t)
    have hs := norm_nonneg (mellinPolynomial (Ioc N (4 * N)) a t +
      mellinPolynomial (Ioc (4 * N) ⌊4 * X⌋₊) a t)
    have he : 0 ≤ 3 / (4 * (N : ℝ)) := by positivity
    nlinarith [sq_nonneg (‖mellinPolynomial (Ioc N (4 * N)) a t‖ - 3 / (4 * (N : ℝ)))]
  have hI (L U : ℕ) : IntervalIntegrable
      (fun t => ‖mellinPolynomial (Ioc L U) a t‖ ^ 2) volume (-T) T :=
    ((continuous_mellinPolynomial _ _).norm.pow 2).intervalIntegrable _ _
  have hi := intervalIntegral.integral_mono (by linarith : -T ≤ T) (hI _ _)
    (((hI _ _).const_mul 2).add intervalIntegrable_const) hpoint
  rw [intervalIntegral.integral_add ((hI _ _).const_mul 2) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hi
  simp only [smul_eq_mul] at hi
  have herr : (T - -T) * (2 * (3 / (4 * (N : ℝ))) ^ 2) ≤ 3 / (N : ℝ) ^ 2 * T := by
    field_simp
    nlinarith
  have hb := hbound T hT
  change (∫ t in -T..T, ‖mellinPolynomial (Ioc N (4 * N)) a t‖ ^ 2) ≤ A + B * T at hb
  change (∫ t in -T..T, ‖mellinPolynomial (Ioc N ⌊4 * X⌋₊) a t‖ ^ 2) ≤ _
  nlinarith

end JointDickman

end OAI
