import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace OAI

/-! A contraction which preserves a given direction preserves the
pairing with that direction. Applied to the normalized finite-cover trace. -/
noncomputable section
namespace CubicFirstMoment

private lemma affine_nonneg_slope_zero (A B : ℝ) (h : ∀ t : ℝ, 0≤A+2*t*B) : B=0 := by
  by_contra hb
  have ht := h (-(A+1)/(2*B))
  have he : A+2*(-(A+1)/(2*B))*B= -1 := by field_simp [hb]; ring
  rw [he] at ht
  norm_num at ht

lemma cubicTheta_inner_of_norm_shear
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (a u : E) (b v : F) (hn : ‖u‖=‖v‖)
    (h : ∀ c : ℂ, ‖a+c • u‖≤‖b+c • v‖) :
    inner ℂ a u=inner ℂ b v := by
  have hre (u' : E) (v' : F) (he : ‖u'‖=‖v'‖)
      (hh : ∀ c : ℂ, ‖a+c • u'‖≤‖b+c • v'‖) :
      (inner ℂ a u').re=(inner ℂ b v').re := by
    have hs : ∀ t : ℝ, 0≤(‖b‖^2-‖a‖^2)+
        2*t*((inner ℂ b v').re-(inner ℂ a u').re) := by
      intro t
      have ht := mul_self_le_mul_self (_root_.norm_nonneg _) (hh (t:ℂ))
      rw [←pow_two,←pow_two,norm_add_sq (𝕜:=ℂ),norm_add_sq (𝕜:=ℂ),
        inner_smul_right,inner_smul_right,norm_smul,norm_smul,he] at ht
      change ‖a‖^2+2*((t:ℂ)*inner ℂ a u').re+(‖(t:ℂ)‖*‖v'‖)^2≤
        ‖b‖^2+2*((t:ℂ)*inner ℂ b v').re+(‖(t:ℂ)‖*‖v'‖)^2 at ht
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at ht
      nlinarith
    have hz := affine_nonneg_slope_zero (‖b‖^2-‖a‖^2)
      ((inner ℂ b v').re-(inner ℂ a u').re) hs
    linarith
  have hreal := hre u v hn h
  have himag := hre (Complex.I • u) (Complex.I • v)
    (by simp only [norm_smul,hn]) (by
      intro c
      simpa only [smul_smul] using h (c*Complex.I))
  simp only [inner_smul_right,Complex.mul_re,Complex.I_re,Complex.I_im,
    zero_mul,one_mul,zero_sub] at himag
  exact Complex.ext hreal (by linarith)

end CubicFirstMoment

end

end OAI
