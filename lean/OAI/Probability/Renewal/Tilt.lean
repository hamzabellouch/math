import OAI.Probability.Renewal.SumLaw

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace HoneycombLocal

def tilt (p : PMF ℕ) (u : ℝ) (hu : 0 ≤ u) : PMF ℕ :=
  letI := isProbabilityMeasure_tilted (integrable_laplace p hu)
  (p.toMeasure.tilted (fun j => -u * (j : ℝ))).toPMF

lemma tilt_toMeasure (p : PMF ℕ) (u : ℝ) (hu : 0 ≤ u) :
    (tilt p u hu).toMeasure = p.toMeasure.tilted (fun j => -u * (j : ℝ)) := by
  let := isProbabilityMeasure_tilted (integrable_laplace p hu)
  exact Measure.toPMF_toMeasure _

lemma tilt_apply (p : PMF ℕ) (u : ℝ) (hu : 0 ≤ u) (j : ℕ) :
    tilt p u hu j = ENNReal.ofReal (Real.exp (-u * (j : ℝ)) / laplace p u) * p j := by
  change p.toMeasure.tilted (fun j => -u * (j : ℝ)) {j} = _
  rw [Measure.tilted, withDensity_apply _ (measurableSet_singleton _), lintegral_singleton]
  rw [p.toMeasure_apply_singleton _ (measurableSet_singleton _)]
  rfl

lemma tilt_apply_real (p : PMF ℕ) (u : ℝ) (hu : 0 ≤ u) (j : ℕ) :
    (tilt p u hu j).toReal = Real.exp (-u * (j : ℝ)) / laplace p u * (p j).toReal := by
  rw [tilt_apply, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity [laplace_pos p hu])]

lemma integral_tilt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : PMF ℕ) (u : ℝ) (hu : 0 ≤ u) (F : ℕ → E) :
    (∫ j, F j ∂(tilt p u hu).toMeasure) =
      (laplace p u)⁻¹ • ∫ j, Real.exp (-u * (j : ℝ)) • F j ∂p.toMeasure := by
  rw [tilt_toMeasure, integral_tilted]
  simp_rw [div_eq_inv_mul, mul_smul]
  rw [integral_smul]
  rfl

lemma integrable_tilt_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : PMF ℕ) (u : ℝ) (hu : 0 ≤ u) (F : ℕ → E) :
    Integrable F (tilt p u hu).toMeasure ↔
      Integrable (fun j : ℕ => Real.exp (-u * (j : ℝ)) • F j) p.toMeasure := by
  rw [tilt_toMeasure]
  exact integrable_tilted_iff (integrable_laplace p hu) F

lemma measureReal_tilt (p : PMF ℕ) (u : ℝ) (hu : 0 ≤ u) (s : Set ℕ) :
    (tilt p u hu).toMeasure.real s =
      (∫ j in s, Real.exp (-u * (j : ℝ)) ∂p.toMeasure) / laplace p u := by
  rw [Measure.real, tilt_toMeasure, tilted_apply_eq_ofReal_integral]
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun _ => by positivity [laplace_pos p hu]))]
  rw [integral_div]; rfl

lemma measureReal_tilt_lower (p : PMF ℕ) (u : ℝ) (hu : 0 ≤ u) (s : Set ℕ) (x : ℝ)
    (hs : ∀ j ∈ s, (j : ℝ) ≤ x) :
    Real.exp (-u * x) * p.toMeasure.real s ≤ (tilt p u hu).toMeasure.real s := by
  rw [measureReal_tilt]
  have hpos := laplace_pos p hu
  apply (le_div_iff₀ hpos).mpr
  calc
    (Real.exp (-u * x) * p.toMeasure.real s) * laplace p u ≤
        Real.exp (-u * x) * p.toMeasure.real s := by
      exact mul_le_of_le_one_right (by positivity) (laplace_le_one p hu)
    _ = ∫ _ in s, Real.exp (-u * x) ∂p.toMeasure := by simp [mul_comm]
    _ ≤ ∫ j in s, Real.exp (-u * (j : ℝ)) ∂p.toMeasure := by
      apply setIntegral_mono_on (integrable_const _) (integrable_laplace p hu).integrableOn
        MeasurableSet.of_discrete
      intro j hj
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left (hs j hj) (neg_nonpos.mpr hu)

lemma tilt_char_difference (p : PMF ℕ) (u : ℝ) (hu : 0 ≤ u) (t : ℝ) :
    ‖latticeChar (tilt p u hu) t - latticeChar p t‖ ≤
      2 * (1 - laplace p u) / laplace p u := by
  let F : ℕ → ℂ := fun j => Complex.exp (((j : ℝ) * t : ℝ) * Complex.I)
  have hF : ∀ j, ‖F j‖ = 1 := by intro j; simp only [F, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im]; simp
  have hIF : Integrable F p.toMeasure := integrable_lattice_exp p t
  have hEF : Integrable (fun j : ℕ => Real.exp (-u * (j : ℝ)) • F j) p.toMeasure := by
    refine Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable 1 ?_
    filter_upwards [] with j
    rw [norm_smul, hF, mul_one, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) j])
  have hd : ‖(∫ j, Real.exp (-u * (j : ℝ)) • F j ∂p.toMeasure) - latticeChar p t‖ ≤
      1 - laplace p u := by
    change ‖(∫ j, Real.exp (-u * (j : ℝ)) • F j ∂p.toMeasure) - (∫ j, F j ∂p.toMeasure)‖ ≤ _
    rw [← integral_sub hEF hIF]
    calc
      ‖∫ j, Real.exp (-u * (j : ℝ)) • F j - F j ∂p.toMeasure‖ ≤
          ∫ j, ‖Real.exp (-u * (j : ℝ)) • F j - F j‖ ∂p.toMeasure := norm_integral_le_integral_norm _
      _ = 1 - laplace p u := by
        rw [← deficit_integral p hu]
        apply integral_congr_ae
        filter_upwards [] with j
        have hid : Real.exp (-u * (j : ℝ)) • F j - F j = (Real.exp (-u * (j : ℝ)) - 1) • F j := by simp [sub_smul]
        rw [hid, norm_smul, hF, mul_one, Real.norm_eq_abs,
          abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_one_iff.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) j])))]
        ring
  change ‖(∫ j, F j ∂(tilt p u hu).toMeasure) - latticeChar p t‖ ≤ _
  rw [integral_tilt]
  have hz := laplace_pos p hu
  have hz1 := laplace_le_one p hu
  let z := laplace p u
  have hid : z⁻¹ • (∫ j, Real.exp (-u * (j : ℝ)) • F j ∂p.toMeasure) - latticeChar p t =
      z⁻¹ • ((∫ j, Real.exp (-u * (j : ℝ)) • F j ∂p.toMeasure) - latticeChar p t) +
      (z⁻¹ - 1) • latticeChar p t := by simp [smul_sub, sub_smul]
  rw [hid]
  calc
    _ ≤ ‖z⁻¹ • ((∫ j, Real.exp (-u * (j : ℝ)) • F j ∂p.toMeasure) - latticeChar p t)‖ +
        ‖(z⁻¹ - 1) • latticeChar p t‖ := norm_add_le _ _
    _ ≤ z⁻¹ * (1 - z) + (z⁻¹ - 1) * 1 := by
      simp only [norm_smul, Real.norm_eq_abs]
      rw [abs_of_pos (inv_pos.mpr hz), abs_of_nonneg (sub_nonneg.mpr ((one_le_inv₀ hz).mpr hz1))]
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hz.le)
      · exact mul_le_mul_of_nonneg_left (norm_latticeChar_le_one p t)
          (sub_nonneg.mpr ((one_le_inv₀ hz).mpr hz1))
    _ = 2 * (1 - laplace p u) / laplace p u := by dsimp [z]; field_simp; ring

end HoneycombLocal

end

end OAI
