import OAI.Probability.PosteriorReplicas.Gaussian.GaussianGramMoment

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

section
variable {X : Type*} [MeasurableSpace X]

lemma truncated_inverse_moment (μ : Measure X) {f : X → ℝ} (hf : Measurable f)
    (hn : ∀ x, 0 ≤ f x) (k : ℕ) (C : ℝ≥0∞)
    (htube : ∀ r : ℝ, 0 < r → r ≤ 1 → μ {x | f x ≤ r} ≤ C*ENNReal.ofReal (r^(k+1)))
    {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    (∫⁻ x in {x | f x ≤ h}, ENNReal.ofReal ((f x)⁻¹^k) ∂μ) ≤
      C * ENNReal.ofReal h * (1+(2:ℝ≥0∞)^(k+1)) := by
  let ρ := μ.restrict {x | f x ≤ h}
  have hb : ∀ r : ℝ, 0 < r → r ≤ 1 →
      ρ {x | f x/h ≤ r} ≤ (C*ENNReal.ofReal (h^(k+1)))*ENNReal.ofReal (r^(k+1)) := by
    intro r hr hr1
    calc
      _ ≤ μ {x | f x ≤ h*r} := by
        rw [Measure.restrict_apply (measurableSet_le (hf.div_const h) measurable_const)]
        apply measure_mono
        intro x hx
        have := (div_le_iff₀ hh).mp hx.1
        change f x ≤ h*r
        simpa only [mul_comm r h] using this
      _ ≤ C*ENNReal.ofReal ((h*r)^(k+1)) :=
        htube _ (mul_pos hh hr) ((mul_le_of_le_one_left hr.le hh1).trans hr1)
      _ = _ := by rw [mul_pow, ENNReal.ofReal_mul (by positivity), mul_assoc]
  have hi := PosteriorRegression.inverse_moment_of_tube_bound ρ (fun x => f x/h) k
    (hf.div_const h) (fun x => div_nonneg (hn x) hh.le) (C*ENNReal.ofReal (h^(k+1))) hb
  have hm : ρ univ ≤ C*ENNReal.ofReal (h^(k+1)) := by
    simpa only [ρ, Measure.restrict_apply_univ] using htube h hh hh1
  have he (x : X) : ENNReal.ofReal ((f x)⁻¹^k) =
      ENNReal.ofReal (h⁻¹^k)*ENNReal.ofReal ((f x/h)⁻¹^k) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [← mul_pow, inv_div, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hh.ne', one_mul]
  calc
    _ = ENNReal.ofReal (h⁻¹^k) * (∫⁻ x, ENNReal.ofReal ((f x/h)⁻¹^k) ∂ρ) := by
      simp_rw [he]
      rw [lintegral_const_mul _ (by fun_prop)]
    _ ≤ ENNReal.ofReal (h⁻¹^k) *
        (C*ENNReal.ofReal (h^(k+1)) + (C*ENNReal.ofReal (h^(k+1)))*2^(k+1)) := by
      exact mul_le_mul' le_rfl (hi.trans (add_le_add hm le_rfl))
    _ = _ := by
      rw [← mul_one_add, ← mul_assoc, ← mul_assoc, mul_comm _ C, mul_assoc C,
        ← ENNReal.ofReal_mul (by positivity)]
      have hc : h⁻¹^k*h^(k+1) = h := by
        rw [pow_succ, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hh.ne', one_pow, one_mul]
      rw [hc]
end

lemma inverse_pow_finite_dyadic_majorant {X : Type*} (f : X → ℝ) (k J : ℕ)
    (hf : ∀ x, 0 ≤ f x) (x : X) :
    ENNReal.ofReal ((f x)⁻¹^k) ≤ 1 +
      (∑ j ∈ Finset.range J, ({x | f x ≤ (1/2:ℝ)^j}).indicator
        (fun _ => ENNReal.ofReal ((2:ℝ)^(k*(j+1)))) x) +
      ({x | f x ≤ (1/2:ℝ)^J}).indicator (fun x => ENNReal.ofReal ((f x)⁻¹^k)) x := by
  classical
  by_cases hsmall : f x ≤ (1/2:ℝ)^J
  · rw [indicator_of_mem (show x ∈ {x | f x ≤ (1/2:ℝ)^J} from hsmall)]
    exact le_add_left le_rfl
  have hp : 0 < f x := lt_trans (by positivity : 0 < (1/2:ℝ)^J) (lt_of_not_ge hsmall)
  rw [indicator_of_notMem (show x ∉ {x | f x ≤ (1/2:ℝ)^J} from hsmall), add_zero]
  by_cases hlarge : 1 ≤ f x
  · apply le_add_of_le_left
    apply le_trans (ENNReal.ofReal_le_ofReal (pow_le_one₀ (inv_nonneg.mpr (hf x))
      (inv_le_one_of_one_le₀ hlarge)))
    simp
  obtain ⟨j,hlo,hhi⟩ := exists_nat_pow_near_of_lt_one hp (le_of_not_ge hlarge)
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1)
  have hj : j < J := by
    by_contra hnot
    have hle := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 1)
      (le_of_not_gt hnot)
    exact hsmall (hhi.trans hle)
  have hpow : ENNReal.ofReal ((f x)⁻¹^k) ≤ ENNReal.ofReal ((2:ℝ)^(k*(j+1))) := by
    have hinv := (inv_le_inv₀ hp (pow_pos (by norm_num : (0:ℝ) < 1/2) _)).mpr hlo.le
    have hinv' : (f x)⁻¹ ≤ (2:ℝ)^(j+1) := by simpa using hinv
    apply ENNReal.ofReal_le_ofReal
    simpa only [← pow_mul, Nat.mul_comm] using pow_le_pow_left₀ (by positivity) hinv' k
  calc
    _ ≤ ENNReal.ofReal ((2:ℝ)^(k*(j+1))) := hpow
    _ = ({x | f x ≤ (1/2:ℝ)^j}).indicator
        (fun _ => ENNReal.ofReal ((2:ℝ)^(k*(j+1)))) x := by
      rw [indicator_of_mem (show x ∈ {x | f x ≤ (1/2:ℝ)^j} from hhi)]
    _ ≤ ∑ j ∈ Finset.range J, ({x | f x ≤ (1/2:ℝ)^j}).indicator
        (fun _ => ENNReal.ofReal ((2:ℝ)^(k*(j+1)))) x :=
      Finset.single_le_sum (f := fun j => ({x | f x ≤ (1/2:ℝ)^j}).indicator
        (fun _ => ENNReal.ofReal ((2:ℝ)^(k*(j+1)))) x)
        (fun i _ => bot_le) (Finset.mem_range.mpr hj)
    _ ≤ _ := le_add_left le_rfl

lemma inverse_moment_finite_bins {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ} (hf : Measurable f)
    (hn : ∀ x, 0 ≤ f x) (k J : ℕ) (C : ℝ≥0∞)
    (htube : ∀ r : ℝ, 0 < r → r ≤ 1 → μ {x | f x ≤ r} ≤ C*ENNReal.ofReal (r^(k+1)))
    (hcut : C*ENNReal.ofReal ((1/2:ℝ)^J)*(1+(2:ℝ≥0∞)^(k+1)) ≤ 1) :
    (∫⁻ x, ENNReal.ofReal ((f x)⁻¹^k) ∂μ) ≤
      2 + ∑ j ∈ Finset.range J, ENNReal.ofReal ((2:ℝ)^(k*(j+1))) * μ {x | f x ≤ (1/2:ℝ)^j} := by
  have hmeas (j : ℕ) : MeasurableSet {x | f x ≤ (1/2:ℝ)^j} := measurableSet_le hf measurable_const
  have hsum : Measurable (fun x => ∑ j ∈ Finset.range J, ({x | f x ≤ (1/2:ℝ)^j}).indicator
      (fun _ => ENNReal.ofReal ((2:ℝ)^(k*(j+1)))) x) :=
    Finset.measurable_sum _ (fun j _ => measurable_const.indicator (hmeas j))
  have hadd : Measurable (fun x => 1 + ∑ j ∈ Finset.range J, ({x | f x ≤ (1/2:ℝ)^j}).indicator
      (fun _ => ENNReal.ofReal ((2:ℝ)^(k*(j+1)))) x) := measurable_const.add hsum
  have htail := (truncated_inverse_moment μ hf hn k C htube
    (h := (1/2:ℝ)^J) (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))).trans hcut
  calc
    _ ≤ ∫⁻ x, 1 + (∑ j ∈ Finset.range J, ({x | f x ≤ (1/2:ℝ)^j}).indicator
        (fun _ => ENNReal.ofReal ((2:ℝ)^(k*(j+1)))) x) +
        ({x | f x ≤ (1/2:ℝ)^J}).indicator (fun x => ENNReal.ofReal ((f x)⁻¹^k)) x ∂μ :=
      lintegral_mono (inverse_pow_finite_dyadic_majorant f k J hn)
    _ = 1 + (∑ j ∈ Finset.range J, ENNReal.ofReal ((2:ℝ)^(k*(j+1))) * μ {x | f x ≤ (1/2:ℝ)^j}) +
        ∫⁻ x in {x | f x ≤ (1/2:ℝ)^J}, ENNReal.ofReal ((f x)⁻¹^k) ∂μ := by
      rw [lintegral_add_aux hadd
        ((by fun_prop : Measurable (fun x => ENNReal.ofReal ((f x)⁻¹^k))).indicator (hmeas J)),
        lintegral_add_left measurable_const,
        lintegral_const, measure_univ, mul_one,
      lintegral_finsetSum _ (fun j _ => measurable_const.indicator (hmeas j)),
        lintegral_indicator (hmeas J)]
      congr 2
      apply Finset.sum_congr rfl
      intro j _
      rw [lintegral_indicator (hmeas j), lintegral_const, Measure.restrict_apply_univ]
    _ ≤ _ := by
      calc
        _ ≤ 1 + (∑ j ∈ Finset.range J, ENNReal.ofReal ((2:ℝ)^(k*(j+1))) * μ {x | f x ≤ (1/2:ℝ)^j}) + 1 :=
          add_le_add le_rfl htail
        _ = _ := by ring

end PosteriorReplicas
end

end OAI
