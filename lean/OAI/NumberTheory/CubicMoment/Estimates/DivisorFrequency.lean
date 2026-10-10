import OAI.NumberTheory.CubicMoment.Estimates.CubePoisson

namespace OAI

/-! The effective frequency after a square-divisor restriction is d*h.
This identity retains vanishing when the divisor meets a conductor. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicSymbol_square_eq_star {b : Eisenstein} (hb : primary b) (d : Eisenstein) :
    cubicSymbol b (d^2) = star (cubicSymbol b d) := by
  rw [cubicSymbol_pow_upper hb]
  by_cases hc : IsCoprime b d
  · have hm : cubicSymbol b d*star (cubicSymbol b d) = 1 := by
      have h := Complex.mul_conj' (cubicSymbol b d)
      simpa only [starRingEnd_apply,norm_cubicSymbol_of_isCoprime hb hc,
        Complex.ofReal_one,one_pow] using h
    have hz : cubicSymbol b d ≠ 0 := by
      intro hz
      rw [hz,zero_mul] at hm
      norm_num at hm
    apply mul_left_cancel₀ hz
    calc
      cubicSymbol b d*(cubicSymbol b d)^2 = (cubicSymbol b d)^3 := by ring
      _ = 1 := cubicSymbol_cube_of_isCoprime hb d hc
      _ = _ := hm.symm
  · rw [cubicSymbol_eq_zero_of_not_isCoprime hb hc]
    simp

lemma divisor_mixed_frequency {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (d h : Eisenstein) :
    mixedSymbol b a (d^2)*(star (cubicSymbol b h)*cubicSymbol a h) =
      star (cubicSymbol b (d*h))*cubicSymbol a (d*h) := by
  simp only [mixedSymbol,cubicSymbol_square_eq_star ha,cubicSymbol_square_eq_star hb,
    cubicSymbol_mul_upper ha,cubicSymbol_mul_upper hb,star_mul,star_star]
  ring

lemma divisor_gram_radial {a b d : Eisenstein} (ha : primary a) (hb : primary b)
    (hd : d ≠ 0) (W : ℝ → ℂ) {A : ℝ} (hA : 0 ≤ A) (h : Eisenstein) :
    mixedSymbol b a (d^2)*gramDualTerm b a W (A/(norm d)^2) h =
      (star (cubicSymbol b (d*h))*cubicSymbol a (d*h))*
        (Real.fourierChar (tracePair (h:ℂ) (1/(3*traceLambda))):ℂ)*
        radialDualProfile W (A*norm (d*h)/(27*(norm d)^3*norm (b*a))) := by
  rw [gramDualTerm_radial b a W (div_nonneg hA (sq_nonneg _))]
  have he : A/(norm d)^2*norm h/(27*norm (b*a)) =
      A*norm (d*h)/(27*(norm d)^3*norm (b*a)) := by
    simp only [norm_mul_eq]
    have hn : norm d ≠ 0 := (norm_pos_of_ne_zero hd).ne'
    have hab0 : norm (b*a) ≠ 0 := (norm_pos_of_ne_zero
      (mul_ne_zero (primary_ne_zero hb) (primary_ne_zero ha))).ne'
    field_simp
  rw [he]
  calc
    _ = (mixedSymbol b a (d^2)*(star (cubicSymbol b h)*cubicSymbol a h))*
        (Real.fourierChar (tracePair (h:ℂ) (1/(3*traceLambda))):ℂ)*
        radialDualProfile W (A*norm (d*h)/(27*(norm d)^3*norm (b*a))) := by ring
    _ = _ := by rw [divisor_mixed_frequency ha hb]

end CubicFirstMoment

end

end OAI
