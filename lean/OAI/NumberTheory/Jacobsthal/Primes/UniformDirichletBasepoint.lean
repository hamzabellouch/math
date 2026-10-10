import StrongPNT.Erdos970.PNT5_Strong
import OAI.NumberTheory.Jacobsthal.Siegel.Main

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.MeasureTheory _root_.Set _root_.Finset _root_.Complex
open scoped Topology
namespace Erdos970Dependency.SiegelWalfisz
open WeightedTorusJets

theorem norm_LFunction_modulus_height {eta : ℝ} (heta : 0 < eta) (heta_half : eta ≤ 1 / 2)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {s : ℂ} (hre : 1 - eta ≤ s.re) :
    ‖DirichletCharacter.LFunction chi s‖ ≤ (1 / eta + 2) * ‖s‖ * (q : ℝ) ^ eta := by
  have hs : 0 < s.re := by linarith
  have hq1 : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hint := integrableOn_min_mul_rpow (Nat.cast_nonneg q)
    (by linarith : -s.re - 1 < -1)
  have hI : ‖∫ t : ℝ in Ioi 1,
      (∑ k ∈ Icc 1 ⌊t⌋₊, chi (k : ZMod q)) * (t : ℂ) ^ (-(s + 1))‖ ≤
      ∫ t : ℝ in Ioi 1, min t (q : ℝ) * t ^ (-s.re - 1) := by
    apply norm_integral_le_of_norm_le hint
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have he : (-(s + 1)).re = -s.re - 1 := by simp; ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (norm_sum_character_Icc_le_min chi hchi ht0.le)
      (Real.rpow_nonneg ht0.le _)
  have hbound := hI.trans (integral_min_mul_rpow_le hq1 heta heta_half hre)
  rw [LFunction_eq_partial_sum_integral_of_re_pos chi hchi hs, norm_mul]
  calc
    ‖s‖ * _ ≤ ‖s‖ * ((q : ℝ) ^ eta * (1 / eta + 2)) :=
      mul_le_mul_of_nonneg_left hbound (norm_nonneg s)
    _ = _ := by ring

theorem norm_LFunction_height_envelope {eta : ℝ} (heta : 0 < eta) (heta_half : eta ≤ 1 / 2)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {s : ℂ} (hre : 1 - eta ≤ s.re) {H : ℝ} (hH : ‖s‖ ≤ H) :
    ‖DirichletCharacter.LFunction chi s‖ ≤ (1 / eta + 2) * H * (q : ℝ) ^ eta := by
  apply (norm_LFunction_modulus_height heta heta_half chi hchi hre).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hH (by positivity)) (Real.rpow_nonneg (Nat.cast_nonneg q) eta)

theorem norm_LFunction_half_strip {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖DirichletCharacter.LFunction chi s‖ ≤ 4 * ‖s‖ * (q : ℝ) ^ (1 / 2 : ℝ) := by
  have h := norm_LFunction_modulus_height (eta := (1 / 2 : ℝ)) (s := s)
    (by norm_num) (by norm_num) chi hchi (by linarith)
  norm_num at h
  exact h

end Erdos970Dependency.SiegelWalfisz

end

section

open _root_.Complex
namespace Erdos970Dependency.SiegelWalfisz

theorem LFunction_ne_zero_right {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) : DirichletCharacter.LFunction chi s ≠ 0 := by
  rw [DirichletCharacter.LFunction_eq_LSeries chi hs]
  exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re chi hs

theorem uniform_log_derivative_right :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q) (s : ℂ),
      1 < s.re → ‖deriv (DirichletCharacter.LFunction chi) s / DirichletCharacter.LFunction chi s‖ ≤
        (s.re - 1)⁻¹ + C := by
  obtain ⟨C, hC, hbound⟩ := _root_.Erdos970.strongPnt_triv_bound_zeta
  refine ⟨C, hC, ?_⟩
  intro q _ chi s hs
  have hz := hbound s.re 0 hs
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hz
  exact (WeightedTorusJets.norm_logDeriv_LFunction_le_neg_logDeriv_zeta chi hs).trans
    ((Complex.re_le_norm _).trans hz)

noncomputable def perronPoint (v t : ℝ) : ℂ :=
  ((1 + (Real.log v)⁻¹ : ℝ) : ℂ) + (t : ℂ) * Complex.I

@[simp] theorem perronPoint_re (v t : ℝ) : (perronPoint v t).re = 1 + (Real.log v)⁻¹ := by
  simp [perronPoint]

theorem perronPoint_re_gt_one {v : ℝ} (hv : 1 < v) (t : ℝ) : 1 < (perronPoint v t).re := by
  rw [perronPoint_re]
  have h := inv_pos.mpr (Real.log_pos hv)
  linarith

theorem LFunction_ne_zero_perron_line {v : ℝ} (hv : 1 < v) {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    DirichletCharacter.LFunction chi (perronPoint v t) ≠ 0 :=
  LFunction_ne_zero_right chi (perronPoint_re_gt_one hv t)

theorem uniform_log_derivative_perron_line :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : ℝ), 1 < v → ∀ (q : ℕ) [NeZero q]
      (chi : DirichletCharacter ℂ q) (t : ℝ),
      ‖deriv (DirichletCharacter.LFunction chi) (perronPoint v t) /
        DirichletCharacter.LFunction chi (perronPoint v t)‖ ≤ Real.log v + C := by
  obtain ⟨C, hC, hbound⟩ := uniform_log_derivative_right
  refine ⟨C, hC, ?_⟩
  intro v hv q _ chi t
  have h := hbound q chi (perronPoint v t) (perronPoint_re_gt_one hv t)
  simpa only [perronPoint_re, add_sub_cancel_left, inv_inv] using h

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open scoped BigOperators

noncomputable def absoluteZetaTwo : ℝ := ∑' n : ℕ, ‖LSeries.term (fun _ => 1) (2 : ℂ) n‖

lemma absoluteZetaTwo_summable :
    Summable (fun n : ℕ => ‖LSeries.term (fun _ => 1) (2 : ℂ) n‖) := by
  apply Summable.norm
  exact LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (by intro n hn; simp) (by norm_num)

lemma one_le_absoluteZetaTwo : 1 ≤ absoluteZetaTwo := by
  have h := absoluteZetaTwo_summable.le_tsum 1 (fun n _ => norm_nonneg (LSeries.term (fun _ => 1) (2 : ℂ) n))
  simpa [LSeries.term, absoluteZetaTwo] using h

lemma norm_LSeries_le_absoluteZetaTwo (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    {s : ℂ} (hs : 2 ≤ s.re) : ‖LSeries f s‖ ≤ absoluteZetaTwo := by
  have hsum : LSeriesSummable f s :=
    LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => hf n) (by linarith)
  apply (norm_tsum_le_tsum_norm hsum.norm).trans
  apply Summable.tsum_le_tsum _ hsum.norm absoluteZetaTwo_summable
  intro n
  exact (LSeries.norm_term_le s (show ‖f n‖ ≤ ‖(1 : ℂ)‖ by simpa using hf n)).trans
    (LSeries.norm_term_le_of_re_le_re (fun _ => (1 : ℂ)) (by simpa using hs) n)

lemma norm_LFunction_le_absoluteZetaTwo {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖DirichletCharacter.LFunction chi s‖ ≤ absoluteZetaTwo := by
  rw [DirichletCharacter.LFunction_eq_LSeries chi (by linarith)]
  exact norm_LSeries_le_absoluteZetaTwo _ (fun n => chi.norm_le_one n) hs

lemma norm_inv_LFunction_le_absoluteZetaTwo {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖(DirichletCharacter.LFunction chi s)⁻¹‖ ≤ absoluteZetaTwo := by
  let f : ℕ → ℂ := fun n => chi n * (ArithmeticFunction.moebius n : ℂ)
  have hf (n : ℕ) : ‖f n‖ ≤ 1 := by
    have hm : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast, ← Int.cast_abs]
      exact_mod_cast (show |ArithmeticFunction.moebius n| ≤ 1 from ArithmeticFunction.abs_moebius_le_one)
    change ‖chi n * (ArithmeticFunction.moebius n : ℂ)‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (chi.norm_le_one n) (norm_nonneg _)).trans (by simpa using hm)
  have hs1 : 1 < s.re := by linarith
  have hp : DirichletCharacter.LFunction chi s * LSeries f s = 1 := by
    rw [DirichletCharacter.LFunction_eq_LSeries chi hs1]
    exact DirichletCharacter.LSeries.mul_mu_eq_one chi hs1
  have hn := LFunction_ne_zero_right chi hs1
  have hinv : (DirichletCharacter.LFunction chi s)⁻¹ = LSeries f s := by
    apply mul_left_cancel₀ hn
    rw [mul_inv_cancel₀ hn, hp]
  rw [hinv]
  exact norm_LSeries_le_absoluteZetaTwo f hf hs

theorem uniform_basepoint_bounds :
    ∃ B : ℝ, 0 < B ∧ ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q) (s : ℂ),
      2 ≤ s.re → B⁻¹ ≤ ‖DirichletCharacter.LFunction chi s‖ ∧
        ‖DirichletCharacter.LFunction chi s‖ ≤ B := by
  have hB : 0 < absoluteZetaTwo := lt_of_lt_of_le zero_lt_one one_le_absoluteZetaTwo
  refine ⟨absoluteZetaTwo, hB, ?_⟩
  intro q _ chi s hs
  refine ⟨?_, norm_LFunction_le_absoluteZetaTwo chi hs⟩
  have hn := norm_pos_iff.mpr (LFunction_ne_zero_right chi (by linarith : 1 < s.re))
  have h := mul_le_mul_of_nonneg_right (norm_inv_LFunction_le_absoluteZetaTwo chi hs) hn.le
  rw [norm_inv, inv_mul_cancel₀ hn.ne'] at h
  rw [← one_div]
  exact (div_le_iff₀ hB).mpr (by nlinarith)

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
