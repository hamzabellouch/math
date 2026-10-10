import Mathlib
import OAI.Analysis.FreeWords.SpectralClip

namespace OAI

noncomputable section

namespace KKUltraTrace

open scoped ComplexOrder InnerProductSpace

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem gnsVector_norm_sq (τ : A →ₚ[ℂ] ℂ) (a : A) :
    ‖gnsVector τ a‖^2 = (τ (star a*a)).re := by
  rw [@norm_sq_eq_re_inner ℂ, gnsVector_inner]
  rfl

theorem gnsVector_star_norm (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ x y : A, τ (x*y) = τ (y*x)) (a : A) :
    ‖gnsVector τ (star a)‖ = ‖gnsVector τ a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [gnsVector_norm_sq, gnsVector_norm_sq, star_star, htr]

theorem gnsVector_mul_norm_left (τ : A →ₚ[ℂ] ℂ) (a b : A) :
    ‖gnsVector τ (a*b)‖ ≤ ‖a‖*‖gnsVector τ b‖ := by
  rw [← gnsStarAlgHom_vector]
  exact ((τ.gnsStarAlgHom a).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le _ _) (norm_nonneg _))

theorem gnsVector_mul_norm_right (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ x y : A, τ (x*y) = τ (y*x)) (a b : A) :
    ‖gnsVector τ (a*b)‖ ≤ ‖b‖*‖gnsVector τ a‖ := by
  rw [← gnsVector_star_norm τ htr (a*b), star_mul]
  simpa only [norm_star, gnsVector_star_norm τ htr] using
    gnsVector_mul_norm_left τ (star b) (star a)

theorem clipWeight_excess_support {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    b^2 * (1-clipWeight b t)^2 ≤ t * (1-clipWeight b t)^2 := by
  by_cases hs : Real.sqrt t ≤ b
  · simp only [clipWeight, clipFunction, max_eq_left hs, div_self (ne_of_gt hb), sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, le_refl]
  · have hb2 : b^2 ≤ t := by nlinarith [Real.sq_sqrt ht, Real.sqrt_nonneg t, lt_of_not_ge hs]
    exact mul_le_mul_of_nonneg_right hb2 (sq_nonneg _)

def clipRemainderWeight (b : ℝ) (a : A) : A := cfc (fun t => 1-clipWeight b t) (star a*a)

theorem spectralClip_sub {b : ℝ} (hb : 0 < b) (a : A) :
    a-spectralClip b a = a*clipRemainderWeight b a := by
  rw [clipRemainderWeight, cfc_sub (fun _ : ℝ => 1) (clipWeight b) _ continuousOn_const
    (continuous_clipWeight hb).continuousOn, cfc_const (1:ℝ) _ (IsSelfAdjoint.of_nonneg (star_mul_self_nonneg _)),
    map_one, mul_sub, mul_one, spectralClip_eq hb]

theorem norm_clipRemainderWeight_le {b : ℝ} (hb : 0 < b) (a : A) :
    ‖clipRemainderWeight b a‖ ≤ 1 := by
  apply norm_cfc_le zero_le_one
  intro t ht
  have hw := clipWeight_bounds hb (spectrum_nonneg_of_nonneg (star_mul_self_nonneg a) ht)
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1-clipWeight b t)]
  linarith

theorem clipRemainder_norm_lower (τ : A →ₚ[ℂ] ℂ) {b : ℝ} (hb : 0 < b) (a : A) :
    b * ‖gnsVector τ (clipRemainderWeight b a)‖ ≤ ‖gnsVector τ (a-spectralClip b a)‖ := by
  let q := clipRemainderWeight b a
  have hs : IsSelfAdjoint (star a*a) := IsSelfAdjoint.of_nonneg (star_mul_self_nonneg _)
  have hq : star q*q = cfc (fun t => (1-clipWeight b t)^2) (star a*a) := by
    dsimp [q, clipRemainderWeight]
    rw [IsSelfAdjoint.cfc.star_eq, ← pow_two]
    exact (cfc_pow (fun t => 1-clipWeight b t) 2 (star a*a)
      (continuous_const.sub (continuous_clipWeight hb)).continuousOn hs).symm
  have horder : b^2 • (star q*q) ≤ star (a-spectralClip b a)*(a-spectralClip b a) := by
    rw [hq, spectralClip_error_square hb, ← cfc_smul (b^2) (fun t => (1-clipWeight b t)^2) (star a*a)
      ((continuous_const.sub (continuous_clipWeight hb)).pow 2).continuousOn]
    apply (cfc_le_iff _ _ _
      (((continuous_const.sub (continuous_clipWeight hb)).pow 2).const_mul (b^2)).continuousOn
      (continuous_id.mul ((continuous_const.sub (continuous_clipWeight hb)).pow 2)).continuousOn).mpr
    intro t ht
    exact clipWeight_excess_support hb (spectrum_nonneg_of_nonneg (star_mul_self_nonneg a) ht)
  have hre := (τ.monotone' horder).1
  change (τ (b^2 • (star q*q))).re ≤ (τ (star (a-spectralClip b a)*(a-spectralClip b a))).re at hre
  have heq : (τ (b^2 • (star q*q))).re = b^2 * (τ (star q*q)).re := by
    simp [← Complex.coe_smul, -Complex.ofReal_pow]
  rw [heq, ← gnsVector_norm_sq, ← gnsVector_norm_sq] at hre
  change b*‖gnsVector τ q‖ ≤ _
  nlinarith [norm_nonneg (gnsVector τ q), norm_nonneg (gnsVector τ (a-spectralClip b a))]

theorem tracial_clip_approximation (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ x y : A, τ (x*y) = τ (y*x)) {b : ℝ} (hb : 0 < b)
    (a x : A) (hx : 2*‖x‖ ≤ b) :
    ‖gnsVector τ (spectralClip b a-x)‖ ≤ 3*‖gnsVector τ (a-x)‖ := by
  let q := clipRemainderWeight b a
  have hq : ‖q‖ ≤ 1 := norm_clipRemainderWeight_le hb a
  have hlow : b*‖gnsVector τ q‖ ≤ ‖gnsVector τ (a-spectralClip b a)‖ :=
    clipRemainder_norm_lower τ hb a
  have hupp : ‖gnsVector τ (a-spectralClip b a)‖ ≤
      ‖gnsVector τ (a-x)‖+‖x‖*‖gnsVector τ q‖ := by
    rw [spectralClip_sub hb]
    have he : a*q = (a-x)*q+x*q := by noncomm_ring
    rw [he, map_add]
    exact (norm_add_le _ _).trans (add_le_add
      ((gnsVector_mul_norm_right τ htr (a-x) q).trans
        (by nlinarith [norm_nonneg (gnsVector τ (a-x))]))
      (gnsVector_mul_norm_left τ x q))
  have herr : ‖gnsVector τ (a-spectralClip b a)‖ ≤ 2*‖gnsVector τ (a-x)‖ := by
    nlinarith [mul_le_mul_of_nonneg_right hx (norm_nonneg (gnsVector τ q))]
  have he : spectralClip b a-x = -(a-spectralClip b a)+(a-x) := by abel
  rw [he, map_add, map_neg]
  have hn := norm_add_le (-gnsVector τ (a-spectralClip b a)) (gnsVector τ (a-x))
  rw [norm_neg] at hn
  linarith

end

end KKUltraTrace
end

end OAI
