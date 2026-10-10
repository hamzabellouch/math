import OAI.NumberTheory.CubicMoment.Estimates.CubeLattice
import OAI.NumberTheory.CubicGram.CubeExtraction

namespace OAI

/-!
# The actual principal frequencies in the dispersion Poisson formula

At `h = d²*j³`, the additive phase is one and the character factors
are precisely the coprimality indicator. The radial argument loses its
`d` scale exactly, before any lattice estimate is applied.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicSymbol_cube_value {b : Eisenstein} (hb : primary b) (j : Eisenstein) :
    cubicSymbol b (j^3) = if IsCoprime b j then 1 else 0 := by
  rw [cubicSymbol_pow_upper hb]
  by_cases hj : IsCoprime b j
  · rw [ite_eq_left hj,cubicSymbol_cube_of_isCoprime hb j hj]
  · rw [ite_eq_right hj,cubicSymbol_eq_zero_of_not_isCoprime hb hj]
    simp

lemma cube_character_phase {b d : Eisenstein} (hb : primary b)
    (hbd : IsCoprime b d) (j : Eisenstein) :
    cubicSymbol b (d^2)*star (cubicSymbol b (d^2*j^3)) =
      if IsCoprime b j then 1 else 0 := by
  have hu : cubicSymbol b (d^2)*star (cubicSymbol b (d^2)) = 1 := by
    have hh := Complex.mul_conj' (cubicSymbol b (d^2))
    simpa only [starRingEnd_apply,norm_cubicSymbol_of_isCoprime hb hbd.pow_right,
      Complex.ofReal_one,one_pow] using hh
  rw [cubicSymbol_mul_upper hb,star_mul,cubicSymbol_cube_value hb]
  calc
    _ = (cubicSymbol b (d^2)*star (cubicSymbol b (d^2))) *
        star (if IsCoprime b j then (1:ℂ) else 0) := by ring
    _ = _ := by rw [hu,one_mul]; split_ifs <;> simp

lemma cube_mixed_character_phase {a b d : Eisenstein} (ha : primary a) (hb : primary b)
    (had : IsCoprime a d) (hbd : IsCoprime b d) (j : Eisenstein) :
    mixedSymbol b a (d^2)*
      (star (cubicSymbol b (d^2*j^3))*cubicSymbol a (d^2*j^3)) =
        if IsCoprime a j ∧ IsCoprime b j then 1 else 0 := by
  calc
    _ = (cubicSymbol b (d^2)*star (cubicSymbol b (d^2*j^3))) *
        star (cubicSymbol a (d^2)*star (cubicSymbol a (d^2*j^3))) := by
      simp only [mixedSymbol,star_mul,star_star]
      ring
    _ = _ := by
      rw [cube_character_phase hb hbd,cube_character_phase ha had]
      by_cases haj : IsCoprime a j <;> by_cases hbj : IsCoprime b j <;> simp [haj,hbj]

/-- This is the literal principal-frequency summand of the sieved
Poisson expansion. It retains the exclusion of common prime factors. -/
theorem cube_gramDualTerm {a b d : Eisenstein}
    (ha : primary a) (hb : primary b) (hd : primary d)
    (had : IsCoprime a d) (hbd : IsCoprime b d)
    (W : ℝ → ℂ) {A : ℝ} (hA : 0 ≤ A) (j : Eisenstein) :
    mixedSymbol b a (d^2)*gramDualTerm b a W (A/(norm d)^2) (d^2*j^3) =
      if IsCoprime a j ∧ IsCoprime b j then
        radialDualProfile W (A*(norm j)^3/(27*norm (b*a))) else 0 := by
  have hdn : norm d ≠ 0 := ne_of_gt (norm_pos_of_ne_zero (primary_ne_zero hd))
  have hscale : 0 ≤ A/(norm d)^2 := div_nonneg hA (sq_nonneg _)
  rw [gramDualTerm_radial b a W hscale,squarefree_cube_frequency_phase hd,
    mul_one,← mul_assoc,cube_mixed_character_phase ha hb had hbd]
  have he : A/(norm d)^2*norm (d^2*j^3)/(27*norm (b*a)) =
      A*(norm j)^3/(27*norm (b*a)) := by
    rw [norm_mul_eq,eisenstein_norm_pow,eisenstein_norm_pow]
    field_simp
  rw [he]
  split_ifs <;> simp

end CubicFirstMoment

end

end OAI
