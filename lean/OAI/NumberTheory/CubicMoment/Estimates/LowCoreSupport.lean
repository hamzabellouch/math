import OAI.NumberTheory.CubicMoment.Estimates.RoughNoncubeLowHeight

namespace OAI

/-! The concrete finite low-conductor frequency support: a small
nonzero core times a bounded cube, with precisely the cubes removed. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def lowNoncubeSupport (V J : ℝ) : Finset Eisenstein :=
  (((nonzeroNormBall V).product (nonzeroNormBall J)).image
    (fun z => z.1*z.2^3)).filter (fun h => ¬∃ j : Eisenstein, j^3 = h)

lemma mem_lowNoncubeSupport {V J : ℝ} {h : Eisenstein} (hh : h ∈ lowNoncubeSupport V J) :
    (¬∃ a : Eisenstein, a^3 = h) ∧ ∃ v j : Eisenstein,
      v ≠ 0 ∧ j ≠ 0 ∧ norm v ≤ V ∧ norm j ≤ J ∧ h = v*j^3 := by
  obtain ⟨hi,hn⟩ := Finset.mem_filter.mp hh
  obtain ⟨⟨v,j⟩,hm,he⟩ := Finset.mem_image.mp hi
  have hv := mem_nonzeroNormBall.mp (Finset.mem_product.mp hm).1
  have hj := mem_nonzeroNormBall.mp (Finset.mem_product.mp hm).2
  exact ⟨hn,v,j,hv.2,hj.2,hv.1,hj.1,he.symm⟩

lemma lowNoncubeSupport_card {V J : ℝ} (hV : 0 ≤ V) (hJ : 0 ≤ J) :
    ((lowNoncubeSupport V J).card:ℝ) ≤ 324*V*J := by
  have hc : (lowNoncubeSupport V J).card ≤
      ((nonzeroNormBall V).product (nonzeroNormBall J)).card :=
    (Finset.card_filter_le _ _).trans (Finset.card_image_le)
  have hb : (((nonzeroNormBall V).product (nonzeroNormBall J)).card:ℝ) =
      ((nonzeroNormBall V).card:ℝ)*((nonzeroNormBall J).card:ℝ) := by
    exact_mod_cast Finset.card_product (nonzeroNormBall V) (nonzeroNormBall J)
  calc
    _ ≤ (((nonzeroNormBall V).product (nonzeroNormBall J)).card:ℝ) := Nat.cast_le.mpr hc
    _ = _ := hb
    _ ≤ (18*V)*(18*J) := mul_le_mul (nonzeroNormBall_card_le hV) (nonzeroNormBall_card_le hJ)
      (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

lemma low_core_log_quotient {z : ℝ} (hz : 1 ≤ z) (a k : ℕ) :
    z^a/(z^(a+k+1))^2 ≤ 1/z^k := by
  have hzp : 0 < z := zero_lt_one.trans_le hz
  apply (div_le_div_iff₀ (pow_pos (pow_pos hzp _) 2) (pow_pos hzp _)).mpr
  rw [one_mul,← pow_add,← pow_mul]
  exact pow_le_pow_right₀ hz (by omega)

lemma low_core_mass_bound {M C J L z : ℝ} {n a k : ℕ}
    (hJ : 0 ≤ J) (hz : 1 ≤ z)
    (hn : (n:ℝ) ≤ 324*z^a*J)
    (hM : M ≤ (n:ℝ)*(C*L/z^(a+k+1))^2) :
    M ≤ (324*C^2)*J*L^2/z^k := by
  have hquot := low_core_log_quotient hz a k
  calc
    M ≤ (324*z^a*J)*(C*L/z^(a+k+1))^2 := hM.trans
      (mul_le_mul_of_nonneg_right hn (sq_nonneg _))
    _ = (324*C^2)*J*L^2*(z^a/(z^(a+k+1))^2) := by rw [div_pow]; ring
    _ ≤ (324*C^2)*J*L^2*(1/z^k) := mul_le_mul_of_nonneg_left hquot
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg C)) hJ) (sq_nonneg L))
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
