import Mathlib
import OAI.Probability.LogConcave.Analysis.SymmetricGradientDerivative
import OAI.Probability.LogConcave.Sampling.Primitive

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
namespace LogConcaveSampling
open scoped RealInnerProductSpace NNReal

theorem primitivePotential_mode_bounds {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    {z₀ : Point d} (hz : z₀ = -r • gradient F (x + r • z₀)) (v : Point d) :
    primitivePotential F x r z₀ + (1 - (lam : ℝ) * r ^ 2) * ‖v‖ ^ 2 / 2 ≤
      primitivePotential F x r (z₀ + v) ∧
    primitivePotential F x r (z₀ + v) ≤
      primitivePotential F x r z₀ + (1 + (lam : ℝ) * r ^ 2) * ‖v‖ ^ 2 / 2 := by
  have hb := quadratic_remainder_of_gradient_lipschitz hF.smooth hF.gradient_lipschitz
    (x + r • z₀) (r • v)
  rw [abs_le] at hb
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr] at hb
  have hlin : inner ℝ z₀ v + inner ℝ (r • v) (gradient F (x + r • z₀)) = 0 := by
    conv_lhs => arg 1; rw [hz]
    simp only [real_inner_smul_left]
    rw [real_inner_comm]
    ring
  dsimp only [primitivePotential]
  rw [norm_add_sq_real, smul_add, ← add_assoc]
  constructor <;> nlinarith [hb.1, hb.2]

theorem Primitive.exists_unique_mode {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam : ℝ) * r ^ 2 < 1) :
    ∃ z₀ : Point d, z₀ = -r • gradient F (x + r • z₀) ∧
      (∀ z : Point d, primitivePotential F x r z₀ ≤ primitivePotential F x r z) ∧
      (∀ z : Point d, primitivePotential F x r z ≤ primitivePotential F x r z₀ → z = z₀) := by
  obtain ⟨z₀, hz, _, _, _⟩ := exists_mode_with_iteration_bound hF.gradient_lipschitz x hr hl
  refine ⟨z₀, hz, ?_, ?_⟩
  · intro z
    have hb := (primitivePotential_mode_bounds hF x hr hz (z - z₀)).1
    rw [add_sub_cancel] at hb
    have hn : 0 ≤ (1 - (lam : ℝ) * r ^ 2) * ‖z - z₀‖ ^ 2 / 2 := by positivity
    linarith
  · intro z hzmin
    have hb := (primitivePotential_mode_bounds hF x hr hz (z - z₀)).1
    rw [add_sub_cancel] at hb
    have hnorm : ‖z - z₀‖ = 0 := by
      have hp : 0 < 1 - (lam : ℝ) * r ^ 2 := by linarith
      have hmul : (1 - (lam : ℝ) * r ^ 2) * ‖z - z₀‖ ^ 2 ≤ 0 := by linarith
      rcases eq_or_lt_of_le (norm_nonneg (z - z₀)) with hn | hn
      · exact hn.symm
      · have hpos := mul_pos hp (sq_pos_of_pos hn)
        linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

end LogConcaveSampling

namespace LogConcaveSampling
open scoped RealInnerProductSpace NNReal

theorem Primitive.continuous_potential {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) (r : ℝ) :
    Continuous (primitivePotential F x r) := by
  exact (continuous_norm.pow 2 |>.div_const 2).add
    (hF.smooth.continuous.comp (continuous_const.add (continuous_id.const_smul r)))

theorem Primitive.integrable_exp_neg_potential {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam : ℝ) * r ^ 2 < 1) :
    Integrable (fun z => Real.exp (-primitivePotential F x r z)) := by
  obtain ⟨z₀, hz, _, _⟩ := hF.exists_unique_mode x hr hl
  let a := (1 - (lam : ℝ) * r ^ 2) / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hi := (integrable_gaussian_envelope d ha).comp_sub_right z₀
  apply (hi.const_mul (Real.exp (-primitivePotential F x r z₀))).mono'
    ((Real.continuous_exp.comp (hF.continuous_potential x r).neg).aestronglyMeasurable)
  filter_upwards [] with z
  change |Real.exp (-primitivePotential F x r z)| ≤ _
  rw [abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  have hb := (primitivePotential_mode_bounds hF x hr hz (z - z₀)).1
  rw [add_sub_cancel] at hb
  apply Real.exp_le_exp.mpr
  dsimp [a]
  linarith

end LogConcaveSampling

namespace LogConcaveSampling
open scoped RealInnerProductSpace

lemma polynomial_gaussian_absorb {b x : ℝ} (hb : 0 < b) (_hx : 0 ≤ x) :
    x * Real.exp (-b*x) ≤ (2/b) * Real.exp (-(b/2)*x) := by
  have he : (b/2)*x ≤ Real.exp ((b/2)*x) := by
    linarith [Real.add_one_le_exp ((b/2)*x)]
  have he' := mul_le_mul_of_nonneg_right he (Real.exp_pos (-b*x)).le
  rw [← Real.exp_add] at he'
  have hexp : (b/2)*x + -b*x = -(b/2)*x := by ring
  rw [hexp] at he'
  have hbp : 0 < b/2 := by positivity
  have hh : (x * Real.exp (-b*x)) * (b/2) ≤ Real.exp (-(b/2)*x) := by nlinarith only [he']
  have hh' := (le_div_iff₀ hbp).mpr hh
  calc
    _ ≤ Real.exp (-(b/2)*x) / (b/2) := hh'
    _ = _ := by field_simp

lemma integrable_sq_norm_gaussian (d : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : Point d => ‖x‖^2 * Real.exp (-b * ‖x‖^2)) := by
  apply ((integrable_gaussian_envelope d (b := b/2) (by positivity)).const_mul (2/b)).mono'
    ((continuous_norm.pow 2).mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_norm.pow 2)))).aestronglyMeasurable
  filter_upwards [] with x
  change |‖x‖^2 * Real.exp (-b * ‖x‖^2)| ≤ _
  rw [abs_of_nonneg (by positivity)]
  exact polynomial_gaussian_absorb hb (sq_nonneg _)

theorem radial_integration_by_parts {d : ℕ} {H : Point d → ℝ} {m K : ℝ}
    (hH : ContDiff ℝ 1 H) (hm : 0 < m) (hK : 0 ≤ K)
    (htail : ∀ x, m * ‖x‖^2 / 2 ≤ H x)
    (hgrad : ∀ x, ‖gradient H x‖ ≤ K * ‖x‖) :
    Integrable (fun x => inner ℝ (gradient H x) x * Real.exp (-H x)) ∧
      (∫ x, inner ℝ (gradient H x) x * Real.exp (-H x)) =
        (d : ℝ) * ∫ x, Real.exp (-H x) := by
  let F : ℝ → Point d → ℝ := fun a x => Real.exp (-H (a • x))
  let F' : ℝ → Point d → ℝ := fun a x =>
    -(inner ℝ (gradient H (a • x)) x) * Real.exp (-H (a • x))
  have hgc : Continuous (gradient H) :=
    (InnerProductSpace.toDual ℝ (Point d)).symm.continuous.comp
      (hH.continuous_fderiv (by norm_num))
  have hdiff : ∀ (x : Point d) (a : ℝ), HasDerivAt (fun a => F a x) (F' a x) a := by
    intro x a
    have hh := ((hH.differentiable (by norm_num) (a • x)).hasFDerivAt).comp_hasDerivAt a
      ((hasDerivAt_id a).smul_const x)
    have hh' : HasDerivAt (fun a => H (a • x)) (inner ℝ (gradient H (a • x)) x) a := by
      convert! hh using 1
      change inner ℝ (gradient H (a • x)) x = fderiv ℝ H (a • x) ((1 : ℝ) • x)
      rw [one_smul,inner_gradient_left]
    convert! hh'.neg.exp using 1; simp only [F',mul_comm,Pi.neg_apply]
  have hbase : Integrable (F 1) := by
    simp only [F,one_smul]
    apply (integrable_gaussian_envelope d (b := m/2) (by positivity)).mono'
      ((Real.continuous_exp.comp hH.continuous.neg).aestronglyMeasurable)
    filter_upwards [] with x
    change |Real.exp (-H x)| ≤ _
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    linarith [htail x]
  have hbnd : ∀ (x : Point d) (a : ℝ), a ∈ Set.Ioo (1/2 : ℝ) 2 →
      ‖F' a x‖ ≤ (2*K) * (‖x‖^2 * Real.exp (-(m/8) * ‖x‖^2)) := by
    intro x a ha
    have hap : 0 ≤ a := by linarith [ha.1]
    have hga : ‖gradient H (a • x)‖ ≤ 2*K*‖x‖ := by
      calc
        _ ≤ K * ‖a • x‖ := hgrad _
        _ = K * (a*‖x‖) := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hap]
        _ ≤ 2*K*‖x‖ := by
          calc
            _ ≤ K * (2*‖x‖) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ha.2.le (norm_nonneg x)) hK
            _ = _ := by ring
    have hinner : |inner ℝ (gradient H (a • x)) x| ≤ 2*K*‖x‖^2 := by
      calc
        _ ≤ ‖gradient H (a • x)‖ * ‖x‖ := abs_real_inner_le_norm _ _
        _ ≤ (2*K*‖x‖)*‖x‖ := mul_le_mul_of_nonneg_right hga (norm_nonneg x)
        _ = _ := by ring
    have htail' : (m/8)*‖x‖^2 ≤ H (a • x) := by
      have ht := htail (a • x)
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hap,mul_pow] at ht
      have ha2 : (1/4 : ℝ) ≤ a^2 := by nlinarith [ha.1]
      have hh := mul_le_mul_of_nonneg_left ha2 (show 0 ≤ m*‖x‖^2 by positivity)
      nlinarith
    dsimp [F']
    rw [abs_mul,abs_neg,abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (2*K*‖x‖^2) * Real.exp (-H (a • x)) := mul_le_mul_of_nonneg_right hinner (by positivity)
      _ ≤ (2*K*‖x‖^2) * Real.exp (-(m/8)*‖x‖^2) := by
        gcongr
        linarith
      _ = _ := by ring
  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure (Point d))) (F := F) (F' := F')
    (bound := fun x => (2*K) * (‖x‖^2 * Real.exp (-(m/8)*‖x‖^2)))
    (x₀ := (1 : ℝ)) (s := Set.Ioo (1/2 : ℝ) 2)
    (Ioo_mem_nhds (by norm_num) (by norm_num))
    (Filter.Eventually.of_forall fun a =>
      ((Real.continuous_exp.comp (hH.continuous.comp (continuous_id.const_smul a)).neg)).aestronglyMeasurable)
    hbase
    (by
      have hh : Continuous (fun x => -(inner ℝ (gradient H x) x) * Real.exp (-H x)) :=
        (hgc.inner continuous_id).neg.mul (Real.continuous_exp.comp hH.continuous.neg)
      convert! hh.aestronglyMeasurable using 1
      simp only [F',one_smul])
    (Filter.Eventually.of_forall hbnd)
    ((integrable_sq_norm_gaussian d (b := m/8) (by positivity)).const_mul (2*K))
    (Filter.Eventually.of_forall fun x a _ => hdiff x a)
  have hidentity : (fun a : ℝ => ∫ x, F a x) =ᶠ[𝓝 1]
      (fun a => (a^d)⁻¹ * ∫ x, Real.exp (-H x)) := by
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with a ha
    simpa [F,finrank_euclideanSpace_fin] using
      (Measure.integral_comp_smul_of_nonneg (volume : Measure (Point d))
        (fun x => Real.exp (-H x)) a (hR := ha.le))
  have halgebra : HasDerivAt (fun a : ℝ => (a^d)⁻¹ * ∫ x, Real.exp (-H x))
      (-(d : ℝ) * ∫ x, Real.exp (-H x)) 1 := by
    convert! (((hasDerivAt_id (1 : ℝ)).pow d).inv (by simp)).mul_const (∫ x, Real.exp (-H x)) using 1; simp
  have heq := hparam.2.unique (halgebra.congr_of_eventuallyEq hidentity)
  have hi : Integrable (fun x => inner ℝ (gradient H x) x * Real.exp (-H x)) := by
    simpa [F',neg_mul] using hparam.1.neg
  refine ⟨hi, ?_⟩
  have heq' : -(∫ x, inner ℝ (gradient H x) x * Real.exp (-H x)) =
      -((d : ℝ) * ∫ x, Real.exp (-H x)) := by
    simpa only [F',one_smul,neg_mul,integral_neg] using heq
  exact neg_inj.mp heq'

end LogConcaveSampling

namespace LogConcaveSampling
open scoped RealInnerProductSpace

lemma partition_toReal {d : ℕ} {H : Point d → ℝ}
    (hi : Integrable (fun x => Real.exp (-H x))) :
    (partition H).toReal = ∫ x, Real.exp (-H x) := by
  exact (integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => (Real.exp_pos (-H x)).le)
    hi.aestronglyMeasurable).symm

lemma integral_gibbs {d : ℕ} {H : Point d → ℝ} (hc : Continuous H)
    (hi : Integrable (fun x => Real.exp (-H x))) (f : Point d → ℝ) :
    (∫ x, f x ∂gibbs H) = (∫ x, Real.exp (-H x) * f x) / ∫ x, Real.exp (-H x) := by
  rw [gibbs,integral_smul_measure,ENNReal.toReal_inv,partition_toReal hi]
  have hden : Measurable (gibbsDensity H) :=
    (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp hc.neg)).measurable
  rw [integral_withDensity_eq_integral_toReal_smul hden
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) f]
  simp only [gibbsDensity,ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul]
  ring

lemma integrable_gibbs_of_weighted {d : ℕ} {H f : Point d → ℝ} (hc : Continuous H)
    (hi : Integrable (fun x => Real.exp (-H x)))
    (hf : Integrable (fun x => Real.exp (-H x) * f x)) : Integrable f (gibbs H) := by
  have hp : partition H ≠ ⊤ := (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (Real.exp_pos (-H x)).le)).2 hi
  have hpos : 0 < partition H := by
    have hmeasure : Measurable (gibbsDensity H) :=
      (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp hc.neg)).measurable
    rw [partition,lintegral_pos_iff_support hmeasure]
    have hh : Function.support (gibbsDensity H) = Set.univ := by
      ext x
      simp [Function.mem_support,gibbsDensity,not_le_of_gt (Real.exp_pos (-H x))]
    rw [hh]
    exact isOpen_univ.measure_pos volume Set.univ_nonempty
  have hw : Integrable f (volume.withDensity (gibbsDensity H)) := by
    have hden : Measurable (gibbsDensity H) :=
      (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp hc.neg)).measurable
    rw [integrable_withDensity_iff_integrable_smul' hden
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simpa only [gibbsDensity,ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul] using hf
  exact hw.smul_measure (by simpa using hpos.ne')

theorem Admissible.radial_gradient_lower {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) (x : Point d) : ‖x‖^2 ≤ inner ℝ (gradient V x) x := by
  let g : ℝ → ℝ := fun t => inner ℝ x (gradient V (t • x))
  let h : ℝ → ℝ := fun t => inner ℝ x (fderiv ℝ (gradient V) (t • x) x)
  have hdg := hV.contDiff_gradient.differentiable (by norm_num)
  have hg : ∀ t, HasDerivAt g (h t) t := by
    intro t
    have hh := (hdg (t • x)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const x)
    simpa [g,h,Function.comp_def] using (hasDerivAt_const t x).inner ℝ hh
  have hderiv : ∀ t, HasDerivAt (fun t => g t - ‖x‖^2*t) (h t-‖x‖^2) t := by
    intro t
    convert! (hg t).sub ((hasDerivAt_id t).const_mul (‖x‖^2)) using 1
    simp
  have hmono : Monotone (fun t => g t-‖x‖^2*t) :=
    monotone_of_hasDerivAt_nonneg hderiv (fun t => sub_nonneg.mpr (hV.hessian_bounds (t • x) x).1)
  have hh := hmono (show (0 : ℝ) ≤ 1 by norm_num)
  simp only [g,zero_smul,one_smul,hV.gradient_zero,inner_zero_right,mul_zero,sub_zero,mul_one] at hh
  rw [real_inner_comm] at hh
  linarith only [hh]

theorem Admissible.second_moment_bound {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) :
    Integrable (fun x => ‖x‖^2) (gibbs V) ∧ (∫ x, ‖x‖^2 ∂gibbs V) ≤ d := by
  have hi := radial_integration_by_parts (hV.smooth.of_le (by norm_num))
    (m := 1) (K := 2) (by norm_num) (by norm_num)
    (fun x => by simpa using (hV.quadratic_bounds x).1) hV.gradient_norm_le
  have hisq : Integrable (fun x => Real.exp (-V x) * ‖x‖^2) := by
    apply (integrable_sq_norm_gaussian d (b := 1/2) (by norm_num)).mono'
      ((Real.continuous_exp.comp hV.smooth.continuous.neg).mul (continuous_norm.pow 2)).aestronglyMeasurable
    filter_upwards [] with x
    change |Real.exp (-V x) * ‖x‖^2| ≤ _
    rw [abs_of_nonneg (by positivity)]
    calc
      _ ≤ Real.exp (-(1/2)*‖x‖^2) * ‖x‖^2 := by
        gcongr
        linarith [(hV.quadratic_bounds x).1]
      _ = _ := by ring
  have hnum : (∫ x, Real.exp (-V x) * ‖x‖^2) ≤ (d : ℝ) * ∫ x, Real.exp (-V x) := by
    rw [← hi.2]
    apply integral_mono hisq hi.1
    intro x
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right
      (hV.radial_gradient_lower x) (Real.exp_pos (-V x)).le
  have hZ : 0 < ∫ x, Real.exp (-V x) := by
    rw [← partition_toReal hV.integrable_exp_neg]
    exact ENNReal.toReal_pos hV.partition_pos.ne' hV.partition_ne_top
  refine ⟨integrable_gibbs_of_weighted hV.smooth.continuous hV.integrable_exp_neg hisq, ?_⟩
  rw [integral_gibbs hV.smooth.continuous hV.integrable_exp_neg]
  exact (div_le_iff₀ hZ).mpr hnum

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
