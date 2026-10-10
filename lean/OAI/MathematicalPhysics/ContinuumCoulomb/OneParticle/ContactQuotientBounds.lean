import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.HoppingBox

namespace OAI

/-! Stability of the actual contact quotient. A fixed natural guard for
the fixed positive normalization integral suffices for all inputs. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarHoppingNumerator_abs_le_four (d : ℝ) : |planarHoppingNumerator d| ≤ 4 := by
  rw [planarHoppingNumerator_box]
  have hpoint (a b : ℝ) :
      ‖planarHoppingIntegrand d (planarPairEquiv.symm (a, b))‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (planarHoppingIntegrand_nonnegative d _)]
    exact (mul_le_of_le_one_left (planarResolventMode_positive _).le
      (planarForcing_le_one _)).trans (planarResolventMode_le_one _)
  have hinner (a : ℝ) :
      ‖∫ b in (-1 : ℝ)..1, planarHoppingIntegrand d (planarPairEquiv.symm (a, b))‖ ≤ 2 := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun b => planarHoppingIntegrand d (planarPairEquiv.symm (a, b)))
      (a := (-1 : ℝ)) (b := 1) (C := 1) (fun b _ => hpoint a b)
    norm_num at h ⊢
    exact h
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun a => ∫ b in (-1 : ℝ)..1,
      planarHoppingIntegrand d (planarPairEquiv.symm (a, b)))
    (a := (-1 : ℝ)) (b := 1) (C := 2) (fun a _ => hinner a)
  norm_num at h ⊢
  exact h

def contactNormalizationGuard : ℕ :=
  ⌈2 / (∫ r, planarResolventMode r ^ 2)⌉₊ + 1

theorem contactNormalizationGuard_positive : 0 < contactNormalizationGuard := by
  unfold contactNormalizationGuard
  omega

theorem contactNormalizationGuard_bound :
    2 ≤ (contactNormalizationGuard : ℝ) * (∫ r, planarResolventMode r ^ 2) := by
  have hp := planarResolventMode_square_integral_positive
  have hceil := Nat.le_ceil (2 / (∫ r, planarResolventMode r ^ 2))
  have hg : 2 / (∫ r, planarResolventMode r ^ 2) ≤ (contactNormalizationGuard : ℝ) := by
    unfold contactNormalizationGuard
    push_cast
    linarith
  exact (div_le_iff₀ hp).mp hg

theorem contact_quotient_error {C a a' b b' ε : ℝ}
    (hC : 1 ≤ C) (ha : 0 < a) (hguard : 2 ≤ C * a)
    (hε : 0 ≤ ε) (hsmall : C * ε ≤ 1)
    (hb : |b| ≤ 4) (hea : |a' - a| ≤ ε) (heb : |b' - b| ≤ ε) :
    |b' / (2 * a') - b / (2 * a)| ≤ 3 * C ^ 2 * ε := by
  have hC0 : 0 < C := by linarith
  have hlinear := mul_le_mul_of_nonneg_left (abs_le.mp hea).1 hC0.le
  have hga' : 1 ≤ C * a' := by nlinarith
  have ha' : 0 < a' := by
    by_contra hn
    have hn' := le_of_not_gt hn
    have hh := mul_nonpos_of_nonneg_of_nonpos hC0.le hn'
    linarith
  have hia : a⁻¹ ≤ C := (inv_le_iff_one_le_mul₀ ha).mpr (by linarith)
  have hia' : a'⁻¹ ≤ C := (inv_le_iff_one_le_mul₀ ha').mpr hga'
  have heq : b' / (2 * a') - b / (2 * a) =
      ((b' - b) * a'⁻¹ + b * (a - a') * a'⁻¹ * a⁻¹) / 2 := by
    field_simp [ha.ne', ha'.ne']
    ring
  have hfirst : |(b' - b) * a'⁻¹| ≤ ε * C := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr ha')]
    exact mul_le_mul heb hia' (inv_nonneg.mpr ha'.le) hε
  have hsecond : |b * (a - a') * a'⁻¹ * a⁻¹| ≤ 4 * ε * C ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr ha),
      abs_of_pos (inv_pos.mpr ha'), abs_sub_comm a a']
    calc
      _ ≤ 4 * ε * C * C := by gcongr
      _ = _ := by ring
  rw [heq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have htotal := (abs_add_le ((b' - b) * a'⁻¹) (b * (a - a') * a'⁻¹ * a⁻¹)).trans
    (add_le_add hfirst hsecond)
  have hCC : C ≤ C ^ 2 := by nlinarith
  have hmon := mul_le_mul_of_nonneg_left hCC hε
  apply (div_le_div_of_nonneg_right htotal (by norm_num)).trans
  nlinarith [mul_nonneg (sq_nonneg C) hε]

end ContinuumCoulomb

end

end OAI
