import OAI.NumberTheory.DirichletL.GaussianTheta
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Function.LocallyIntegrable

namespace OAI

noncomputable section

open scoped BigOperators Classical Topology
open Filter Asymptotics

namespace SevenEighths.ThetaRegularity

abbrev O := ActualEisensteinCubic.O

open ActualEisensteinCubic ConcreteTraceCRT GaussianTheta

theorem norm_gaussian (a : ℝ) (z : ℂ) :
    ‖gaussian a z‖ = Real.exp (-Real.pi * a * ‖z‖ ^ 2) := by
  simp [gaussian, Complex.norm_exp, pow_two, Complex.mul_re, Complex.mul_im]

theorem lattice_gap (z : O) (hz : z ≠ 0) : 1 ≤ ‖eisEmbedding z‖ ^ 2 := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {z}) ≠ 0 by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hz)

theorem gaussian_le_inverse_square (a : ℝ) (ha : 0 ≤ a) (z : ℂ) :
    ‖gaussian a z‖ ≤ ((1 + a * ‖z‖ ^ 2) ^ 2)⁻¹ := by
  let x := a * ‖z‖ ^ 2
  have hx : 0 ≤ x := mul_nonneg ha (sq_nonneg _)
  have h1 : 1 + x ≤ Real.exp x := by simpa [add_comm] using Real.add_one_le_exp x
  have hs : (1 + x) ^ 2 ≤ Real.exp (Real.pi * x) := calc
    _ ≤ (Real.exp x) ^ 2 := by gcongr
    _ = Real.exp (2 * x) := by rw [pow_two, ← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right Real.two_le_pi hx)
  rw [norm_gaussian]
  have hexp : -Real.pi * a * ‖z‖ ^ 2 = -(Real.pi * x) := by dsimp [x]; ring
  rw [hexp]
  rw [Real.exp_neg]
  exact (inv_le_inv₀ (Real.exp_pos _) (by positivity)).mpr hs

variable (c : O) [NeZero c]

local instance residueFinite : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span (NeZero.ne c)
local instance residueFintype : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _

def decayRate : ℝ := Real.pi * parameter c 1

theorem decayRate_pos : 0 < decayRate c :=
  mul_pos Real.pi_pos (parameter_pos c 1 one_pos)

omit [NeZero c] in
theorem parameter_eq (t : ℝ) : parameter c t = parameter c 1 * t := by
  unfold parameter
  ring

omit [NeZero c] in
theorem norm_gaussian_parameter (t : ℝ) (z : ℂ) :
    ‖gaussian (parameter c t) z‖ = Real.exp (-decayRate c * t * ‖z‖ ^ 2) := by
  rw [norm_gaussian, parameter_eq]
  congr 1
  unfold decayRate
  ring

theorem coefficient_norm_le_one (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (r : O ⧸ Ideal.span {c}) : ‖χ r‖ ≤ 1 := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    have hu : ‖χ (u : O ⧸ Ideal.span {c})‖ = 1 := by
      simpa only [MulChar.coe_equivToUnitHom] using
        Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)
    exact hu.le
  · rw [MulChar.map_nonunit χ hr, norm_zero]
    norm_num

theorem term_norm_le (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) (z : O) :
    ‖χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
      gaussian (parameter c t) (eisEmbedding z)‖ ≤
        Real.exp (-decayRate c * t * ‖eisEmbedding z‖ ^ 2) := by
  rw [norm_mul, norm_gaussian_parameter]
  exact mul_le_of_le_one_left (Real.exp_nonneg _) (coefficient_norm_le_one c χ _)

theorem continuousOn_theta_above (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (δ : ℝ) (hδ : 0 < δ) : ContinuousOn (theta c χ) (Set.Ioi δ) := by
  apply continuousOn_tsum (u := fun z : O => ‖gaussian (parameter c δ) (eisEmbedding z)‖)
  · intro z
    unfold gaussian parameter
    fun_prop
  · exact (gaussian_summable _ (parameter_pos c δ hδ)).norm
  · intro z t ht
    apply (term_norm_le c χ t z).trans
    rw [norm_gaussian_parameter]
    apply Real.exp_le_exp.mpr
    have hn : 0 ≤ decayRate c * ‖eisEmbedding z‖ ^ 2 :=
      mul_nonneg (decayRate_pos c).le (sq_nonneg _)
    have htd : δ < t := ht
    nlinarith

theorem continuousAt_theta (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (t : ℝ) (ht : 0 < t) : ContinuousAt (theta c χ) t := by
  have h := continuousOn_theta_above c χ (t / 2) (half_pos ht)
  exact h.continuousAt (isOpen_Ioi.mem_nhds (show t / 2 < t by linarith))

theorem continuousOn_theta (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) :
    ContinuousOn (theta c χ) (Set.Ioi 0) :=
  fun t ht => (continuousAt_theta c χ t ht).continuousWithinAt

theorem theta_locallyIntegrableOn (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) :
    MeasureTheory.LocallyIntegrableOn (theta c χ) (Set.Ioi 0) :=
  (continuousOn_theta c χ).locallyIntegrableOn measurableSet_Ioi

def tailConstant : ℝ := ∑' z : O, ‖gaussian (parameter c (1 / 2)) (eisEmbedding z)‖

omit [NeZero c] in
theorem tailConstant_nonneg : 0 ≤ tailConstant c := tsum_nonneg (fun _z => norm_nonneg _)

theorem tailConstant_le_cauchy :
    tailConstant c ≤ 4 * (1 + Real.pi / Real.sqrt (parameter c (1 / 2))) ^ 2 := by
  have ha := parameter_pos c (1 / 2) (by norm_num)
  apply le_trans (Summable.tsum_le_tsum
    (fun z : O => gaussian_le_inverse_square _ ha.le (eisEmbedding z))
    (gaussian_summable _ ha).norm
    (EisensteinSchwartzPoisson.scaled_eisenstein_cauchy_summable _ ha))
  exact EisensteinSchwartzPoisson.scaled_eisenstein_cauchy_bound _ ha

theorem tailConstant_le_linear :
    tailConstant c ≤ 8 * (1 + Real.pi ^ 2 * Real.sqrt 3 * ‖eisEmbedding c‖) := by
  have ha := parameter_pos c (1 / 2) (by norm_num)
  have hs : (Real.pi / Real.sqrt (parameter c (1 / 2))) ^ 2 =
      Real.pi ^ 2 * Real.sqrt 3 * ‖eisEmbedding c‖ := by
    rw [div_pow, Real.sq_sqrt ha.le]
    simp only [parameter]
    norm_num
    field_simp
  have h := tailConstant_le_cauchy c
  have hsq := sq_nonneg (1 - Real.pi / Real.sqrt (parameter c (1 / 2)))
  nlinarith

theorem tail_eq_tsum (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) (ht : 0 < t) :
    theta c χ t - constantTerm c χ = ∑' z : O, if z = 0 then 0 else
      χ (Ideal.Quotient.mk (Ideal.span {c}) z) * gaussian (parameter c t) (eisEmbedding z) := by
  have h := (theta_summable c χ t ht).tsum_eq_add_tsum_ite (0 : O)
  rw [theta_zero_term c χ t] at h
  exact sub_eq_iff_eq_add.mpr (by simpa only [theta, add_comm] using h)

theorem tail_term_bound (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (t : ℝ) (ht : 1 ≤ t) (z : O) :
    ‖if z = 0 then (0 : ℂ) else
      χ (Ideal.Quotient.mk (Ideal.span {c}) z) * gaussian (parameter c t) (eisEmbedding z)‖ ≤
      Real.exp (-decayRate c * t / 2) *
        ‖gaussian (parameter c (1 / 2)) (eisEmbedding z)‖ := by
  by_cases hz : z = 0
  · simp only [ite_eq_left hz, norm_zero]
    positivity
  · rw [ite_eq_right hz]
    apply (term_norm_le c χ t z).trans
    rw [norm_gaussian_parameter, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hn := lattice_gap z hz
    have hβ := decayRate_pos c
    have hprod : 0 ≤ (t - 1) * (‖eisEmbedding z‖ ^ 2 - 1) :=
      mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hn)
    have hineq : t / 2 + ‖eisEmbedding z‖ ^ 2 / 2 ≤ t * ‖eisEmbedding z‖ ^ 2 := by
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hineq hβ.le]

theorem theta_tail_bound (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) (ht : 1 ≤ t) :
    ‖theta c χ t - constantTerm c χ‖ ≤
      tailConstant c * Real.exp (-decayRate c * t / 2) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  rw [tail_eq_tsum c χ t ht0]
  have hsum := (gaussian_summable _ (parameter_pos c (1 / 2) (by norm_num))).norm
  have hmajor := hsum.mul_left (Real.exp (-decayRate c * t / 2))
  have hnorm := Summable.of_nonneg_of_le (fun z => norm_nonneg _)
    (tail_term_bound c χ t ht) hmajor
  apply (norm_tsum_le_tsum_norm hnorm).trans
  have h := Summable.tsum_le_tsum (tail_term_bound c χ t ht) hnorm hmajor
  simpa only [tsum_mul_left, tailConstant, mul_comm] using h

theorem theta_tail_bound_conductor (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (t : ℝ) (ht : 1 ≤ t) :
    ‖theta c χ t - constantTerm c χ‖ ≤
      8 * (1 + Real.pi ^ 2 * Real.sqrt 3 * ‖eisEmbedding c‖) *
        Real.exp (-decayRate c * t / 2) :=
  (theta_tail_bound c χ t ht).trans
    (mul_le_mul_of_nonneg_right (tailConstant_le_linear c) (Real.exp_nonneg _))

theorem theta_tail_isBigO_exp (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) :
    (fun t : ℝ => theta c χ t - constantTerm c χ) =O[atTop]
      (fun t : ℝ => Real.exp (-(decayRate c / 2) * t)) := by
  apply isBigO_iff.mpr
  refine ⟨tailConstant c, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have he : -(decayRate c / 2) * t = -decayRate c * t / 2 := by ring
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), he] using theta_tail_bound c χ t ht

theorem theta_tail_isBigO_rpow (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (r : ℝ) :
    (fun t : ℝ => theta c χ t - constantTerm c χ) =O[atTop] (fun t : ℝ => t ^ r) :=
  (theta_tail_isBigO_exp c χ).trans
    (isLittleO_exp_neg_mul_rpow_atTop (half_pos (decayRate_pos c)) r).isBigO

end SevenEighths.ThetaRegularity

end

end OAI
