import OAI.NumberTheory.DirichletL.Hecke.PrincipalStrip

namespace OAI

noncomputable section
open scoped Classical Topology
open Set
namespace SevenEighths.HeckeLogarithmicInput
open HeckeFamily

def regular (η : Character) (s : ℂ) : ℂ :=
  if η.residue = 1 then HeckePrincipalStrip.sourceNormalized η s else LFunction η s

theorem regular_eq_nonprincipal (η : Character) (hη : η.residue ≠ 1) :
    regular η = LFunction η := by funext s; simp [regular, hη]

theorem regular_differentiableAt (η : Character) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (regular η) s := by
  have hplus : s+1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at he
    linarith
  by_cases hη : η.residue = 1
  · have he : regular η = HeckePrincipalStrip.sourceNormalized η := by
      funext z; simp [regular, hη]
    rw [he]
    exact (HeckeOrigin.poleRemoved_entire η s).div (differentiableAt_id.add_const 1) hplus
  · rw [regular_eq_nonprincipal η hη]
    exact LFunction_entire_nonprincipal η hη s

theorem regular_ne_zero (η : Character) {s : ℂ}
    (hs : HeckeZeroSupremum.beta < s.re) : regular η s ≠ 0 := by
  have hs0 : 0 < s.re := by linarith [HeckeZeroSupremum.half_le_beta]
  have h0 : s ≠ 0 := by intro h; simp [h] at hs0
  have hplus : s+1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at he
    linarith
  by_cases hη : η.residue = 1
  · simp only [regular, ite_eq_left hη, HeckePrincipalStrip.sourceNormalized]
    apply div_ne_zero _ hplus
    by_cases h1 : s = 1
    · subst s; exact HeckeOrigin.poleRemoved_one_ne_zero η hη
    · rw [HeckeOrigin.poleRemoved_eq η h0 h1]
      exact mul_ne_zero (sub_ne_zero.mpr h1)
        (HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt η hs (Or.inl h1))
  · rw [regular_eq_nonprincipal η hη]
    exact HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt η hs (Or.inr hη)

theorem regular_inverse_differentiableAt (η : Character) {s : ℂ}
    (hs : HeckeZeroSupremum.beta < s.re) :
    DifferentiableAt ℂ (fun z => (regular η z)⁻¹) s :=
  (regular_differentiableAt η (by linarith [HeckeZeroSupremum.half_le_beta])).inv
    (regular_ne_zero η hs)

theorem principal_regular_factor_bound {s : ℂ} (hs : 0 ≤ s.re) :
    ‖s-1‖ ≤ ‖s+1‖ := by
  have he : ‖s+1‖^2 - ‖s-1‖^2 = 4*s.re := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  nlinarith [norm_nonneg (s-1), norm_nonneg (s+1)]

theorem regular_norm_le (η : Character) {σ : ℝ} (hσ : 1 < σ)
    {s : ℂ} (hs : σ ≤ s.re) : ‖regular η s‖ ≤ HeckeReciprocalBound.bound σ := by
  by_cases hη : η.residue = 1
  · have h0 : s ≠ 0 := by intro h; simp [h] at hs; linarith
    have h1 : s ≠ 1 := by intro h; simp [h] at hs; linarith
    have hp : 0 < ‖s+1‖ := by
      have hr := Complex.re_le_norm (s+1)
      simp only [Complex.add_re, Complex.one_re] at hr
      linarith
    simp only [regular, ite_eq_left hη, HeckePrincipalStrip.sourceNormalized,
      HeckeOrigin.poleRemoved_eq η h0 h1, norm_div, norm_mul]
    apply le_trans _ (HeckeStripActual.LFunction_norm_le η hσ hs)
    apply (div_le_iff₀ hp).mpr
    nlinarith [principal_regular_factor_bound (s := s) (by linarith), norm_nonneg (LFunction η s)]
  · rw [regular_eq_nonprincipal η hη]
    exact HeckeStripActual.LFunction_norm_le η hσ hs

theorem regular_inverse_norm_le (η : Character) {s : ℂ} (hs : (3/2 : ℝ) ≤ s.re) :
    ‖(regular η s)⁻¹‖ ≤ 5 * HeckeReciprocalBound.bound (3/2) := by
  have h0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have h1 : s ≠ 1 := by intro h; norm_num [h] at hs
  have hL := HeckeReciprocalBound.reciprocal_norm_le η (by norm_num : (1 : ℝ)<3/2) hs
  rw [HeckeReciprocal.reciprocal_eq_inv η h0 h1] at hL
  have hB : 0 ≤ HeckeReciprocalBound.bound (3/2) := tsum_nonneg (fun _ => norm_nonneg _)
  by_cases hη : η.residue = 1
  · have hlow : (1/2 : ℝ) ≤ ‖s-1‖ := by
      have hr := Complex.re_le_norm (s-1)
      simp only [Complex.sub_re, Complex.one_re] at hr
      linarith
    have hratio : ‖s+1‖ / ‖s-1‖ ≤ 5 := by
      apply (div_le_iff₀ (by linarith : 0 < ‖s-1‖)).mpr
      have hr := norm_add_le (s-1) (2 : ℂ)
      norm_num only [Complex.norm_ofNat] at hr
      rw [show s-1+2=s+1 by ring] at hr
      linarith
    simp only [regular, ite_eq_left hη, HeckePrincipalStrip.sourceNormalized,
      HeckeOrigin.poleRemoved_eq η h0 h1, inv_div, norm_div, norm_mul]
    calc
      _ = (‖s+1‖ / ‖s-1‖) * ‖(LFunction η s)⁻¹‖ := by rw [norm_inv]; ring
      _ ≤ _ := mul_le_mul hratio hL (norm_nonneg _) (by norm_num)
  · rw [regular_eq_nonprincipal η hη]
    linarith

def uniformConstant : ℝ :=
  108*((1+HeckeStrip.leftConstant)*HeckeReciprocalBound.bound (11/10))

theorem uniformConstant_nonneg : 0 ≤ uniformConstant := by
  have hc := HeckeStrip.leftConstant_pos
  have hD : 0 ≤ HeckeReciprocalBound.bound (11/10) := tsum_nonneg (fun _ => norm_nonneg _)
  unfold uniformConstant
  positivity

theorem modulus_norm_ge_one (η : Character) : 1 ≤ (η.modulus.absNorm : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)

theorem regular_strip_bound (η : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals η.residue) (z : ℂ)
    (hz : z ∈ HeckeStrip.closedStrip) :
    ‖regular η z‖ ≤ uniformConstant * (η.modulus.absNorm : ℝ)^(3/5 : ℝ) *
      (3+|z.im|)^2 := by
  by_cases hη : η.residue = 1
  · simpa only [regular, ite_eq_left hη, uniformConstant] using
      HeckePrincipalStrip.uniform_source_normalized_strip_bound η hp z hz
  · rw [regular_eq_nonprincipal η hη]
    apply (HeckePresentation.uniform_strip_bound η hp hη z hz).trans
    have hc := HeckeStrip.leftConstant_pos
    have hD : 0 ≤ HeckeReciprocalBound.bound (11/10) := tsum_nonneg (fun _ => norm_nonneg _)
    unfold uniformConstant
    gcongr ; norm_num

theorem regular_right_growth (η : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals η.residue) {z : ℂ}
    (hz : -(1/10 : ℝ) ≤ z.re) :
    ‖regular η z‖ ≤ uniformConstant * (η.modulus.absNorm : ℝ)^(3/5 : ℝ) *
      (3+|z.im|)^2 := by
  by_cases hright : z.re ≤ 11/10
  · exact regular_strip_bound η hp z ⟨hz, hright⟩
  · apply (regular_norm_le η (by norm_num : (1 : ℝ)<11/10) (le_of_not_ge hright)).trans
    have hD : 0 ≤ HeckeReciprocalBound.bound (11/10) := tsum_nonneg (fun _ => norm_nonneg _)
    have hc := HeckeStrip.leftConstant_pos
    have hC : HeckeReciprocalBound.bound (11/10) ≤ uniformConstant := by
      unfold uniformConstant; nlinarith
    have hQ : 1 ≤ (η.modulus.absNorm : ℝ)^(3/5 : ℝ) :=
      Real.one_le_rpow (modulus_norm_ge_one η) (by norm_num)
    have hT : 1 ≤ (3+|z.im|)^2 := by nlinarith [abs_nonneg z.im]
    exact hC.trans ((le_mul_of_one_le_right uniformConstant_nonneg hQ).trans
      (le_mul_of_one_le_right (mul_nonneg uniformConstant_nonneg (by linarith : 0 ≤ (η.modulus.absNorm : ℝ)^(3/5 : ℝ))) hT))

theorem regular_ne_zero_on_disk (η : Character) (a e t : ℝ)
    (ha : HeckeZeroSupremum.beta ≤ a) (he : 0 < e) {z : ℂ}
    (hz : z ∈ Metric.ball ((2 : ℂ)+t*Complex.I) (2-a-2*e)) :
    regular η z ≠ 0 := by
  apply regular_ne_zero η
  have hn : ‖z-((2 : ℂ)+t*Complex.I)‖ < 2-a-2*e := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have hr := Complex.abs_re_le_norm (z-((2 : ℂ)+t*Complex.I))
  have hrl := neg_abs_le (z-((2 : ℂ)+t*Complex.I)).re
  norm_num [Complex.sub_re, Complex.add_re, Complex.mul_re] at hr hrl
  linarith

theorem reciprocal_norm_le_regular_inverse (η : Character) {s : ℂ}
    (hs : HeckeZeroSupremum.beta < s.re) :
    ‖HeckeReciprocal.reciprocal η s‖ ≤ ‖(regular η s)⁻¹‖ := by
  have hs0 : 0 < s.re := by linarith [HeckeZeroSupremum.half_le_beta]
  have h0 : s ≠ 0 := by intro h; simp [h] at hs0
  by_cases hη : η.residue = 1
  · by_cases h1 : s = 1
    · subst s
      rw [HeckeReciprocal.reciprocal_principal_one η hη, norm_zero]
      exact norm_nonneg _
    have hp : s+1 ≠ 0 := by
      intro h
      have he := congrArg Complex.re h
      simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at he
      linarith
    have hL := HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt η hs (Or.inl h1)
    have he : HeckeReciprocal.reciprocal η s =
        ((s-1)/(s+1))*(regular η s)⁻¹ := by
      rw [HeckeReciprocal.reciprocal_eq_inv η h0 h1]
      simp only [regular, ite_eq_left hη, HeckePrincipalStrip.sourceNormalized,
        HeckeOrigin.poleRemoved_eq η h0 h1]
      field_simp
    rw [he, norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    rw [norm_div]
    exact (div_le_one (norm_pos_iff.mpr hp)).mpr (principal_regular_factor_bound hs0.le)
  · simp only [HeckeReciprocal.reciprocal, regular, ite_eq_right hη, le_refl]

theorem regular_disk_growth (η : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals η.residue) (a e t : ℝ)
    (ha : (1/2 : ℝ) ≤ a) (he : 0 ≤ e) {z : ℂ}
    (hz : z ∈ Metric.closedBall ((2 : ℂ)+t*Complex.I) (2-a-2*e)) :
    ‖regular η z‖ ≤ (4*uniformConstant) * (η.modulus.absNorm : ℝ)^(3/5 : ℝ) *
      (3+|t|)^2 := by
  have hn : ‖z-((2 : ℂ)+t*Complex.I)‖ ≤ 2-a-2*e := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have hr := Complex.abs_re_le_norm (z-((2 : ℂ)+t*Complex.I))
  have hi := Complex.abs_im_le_norm (z-((2 : ℂ)+t*Complex.I))
  norm_num [Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.sub_im, Complex.add_im, Complex.mul_im] at hr hi
  have hzre : -(1/10 : ℝ) ≤ z.re := by
    have hh := neg_abs_le (z.re-2)
    linarith
  have hheight : 3+|z.im| ≤ 2*(3+|t|) := by
    have hab := abs_add_le (z.im-t) t
    rw [sub_add_cancel] at hab
    linarith [abs_nonneg t]
  apply (regular_right_growth η hp hzre).trans
  have hsq : (3+|z.im|)^2 ≤ 4*(3+|t|)^2 := by
    have h := (sq_le_sq₀ (by positivity : 0 ≤ 3+|z.im|)
      (by positivity : 0 ≤ 2*(3+|t|))).mpr hheight
    nlinarith
  calc
    _ ≤ uniformConstant*(η.modulus.absNorm : ℝ)^(3/5 : ℝ)*(4*(3+|t|)^2) :=
      mul_le_mul_of_nonneg_left hsq (mul_nonneg uniformConstant_nonneg (Real.rpow_nonneg (by positivity) _))
    _ = _ := by ring

end SevenEighths.HeckeLogarithmicInput

end

end OAI
