import OAI.NumberTheory.Ostmann.Supply.ProjectionCrossBound
import OAI.NumberTheory.Ostmann.Supply.UniformProjection

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [NeZero p]
local notation "H" => EuclideanSpace ℂ (ZMod p)

theorem inner_centered_projected (S : Finset (ZMod p)) (f : H) (v : centeredSpace S) :
    inner ℂ f (v:H) = inner ℂ (centeredProjection S f) (v:H) := by
  change _ = inner ℂ ((centeredSpace S).starProjection f) (v:H)
  rw [Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr v.property]

theorem projection_row_le (S : Finset (ZMod p)) {ε : ℝ}
    (hpos : 0 < density S) (hlt : density S < 1)
    (hε : 0 ≤ ε) (hg : gamma S ≤ ε^2) (v : centeredSpace Sᶜ) :
    ‖inner ℂ (uniformVector S) (spectralProjection (largeSpectrum S) (v:H))‖ ≤
      (uniformCoefficient S*(ε*Real.sqrt p))*‖v‖ := by
  have hi : inner ℂ (uniformVector S) (spectralProjection (largeSpectrum S) (v:H)) =
      inner ℂ (spectralProjection (largeSpectrum S) (uniformVector S)) (v:H) :=
    ((frequencySpace (largeSpectrum S)).inner_starProjection_left_eq_right _ _).symm
  rw [hi,inner_centered_projected Sᶜ]
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
    (centered_projection_uniform_le S Sᶜ hpos hlt
      (centeredProjection_compl_normalizedVector S) hε hg) (norm_nonneg _))

theorem projection_column_le (S : Finset (ZMod p)) {ε : ℝ}
    (hpos : 0 < density S) (hlt : density S < 1)
    (hε : 0 ≤ ε) (hg : gamma S ≤ ε^2) :
    ‖centeredProjection S (spectralProjection (largeSpectrum S) (uniformVector Sᶜ))‖ ≤
      uniformCoefficient Sᶜ*(ε*Real.sqrt p) :=
  centered_projection_uniform_compl_le S S hpos hlt
    (centeredProjection_normalizedVector S) hε hg

theorem projection_lower_le (S : Finset (ZMod p)) (v : centeredSpace Sᶜ) :
    ‖centeredProjection S (spectralProjection (largeSpectrum S) (v:H))‖ ≤
      (1/2:ℝ)*‖v‖ := by
  have hn := centeredProjection_cross_norm_le_half S Sᶜ (Finset.disjoint_left.mpr (fun x hx hxc => (Finset.mem_compl.mp hxc) hx))
    (frequencySpace (largeSpectrum S))
  have hv : centeredProjection Sᶜ (v:H) = (v:H) :=
    Submodule.starProjection_eq_self_iff.mpr v.property
  have hb := (centeredProjection S ∘L spectralProjection (largeSpectrum S) ∘L
    centeredProjection Sᶜ).le_opNorm (v:H)
  simp only [ContinuousLinearMap.comp_apply,hv] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

end Ostmann.Supply

end

end OAI
