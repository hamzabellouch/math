import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingNormalizedProfile

namespace OAI

/-!
# A uniform positive displacement at one of two annular returns

The normalized profile is the actual matrix profile. Consequently the
two-scale cancellation estimate gives a positive lower bound independent
of the return matrix, while the scale bound controls every intervening
shearing parameter.
-/

noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem rootShearSize_two_scales_lower {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (hk : 0 < rootShearingKappa i j g) (r s ρ : ℝ)
    (hρ : 0 < ρ) (hρone : ρ ≤ 1)
    (hrlo : ρ ≤ |rootShearingKappa i j g * r|)
    (hrhi : |rootShearingKappa i j g * r| ≤ 1)
    (hslo : 16 / ρ ≤ |rootShearingKappa i j g * s|) :
    ρ / (16 * (n : ℝ)) ≤ rootShearSize hij g r ∨
    ρ / (16 * (n : ℝ)) ≤ rootShearSize hij g s := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast Fin.pos i
  have h := shearing_profile_two_scales
    ((g.val j j - g.val i i) / rootShearingKappa i j g)
    (g.val j i / (rootShearingKappa i j g) ^ 2)
    (rootShearingOffDiagonalSize i j g / rootShearingKappa i j g)
    (rootShearingKappa i j g * r) (rootShearingKappa i j g * s) ρ
    (rootShearing_normalized_profile_identity i j g hk) hρ hρone hrlo hrhi hslo
  have hbound (u : ℝ) := rootShearing_normalized_profile_le_size hij g hk u
  rcases h with h | h
  · left
    have hle := h.trans (hbound r)
    apply (div_le_iff₀ (by positivity : 0 < 16 * (n : ℝ))).mpr
    nlinarith
  · right
    have hle := h.trans (hbound s)
    apply (div_le_iff₀ (by positivity : 0 < 16 * (n : ℝ))).mpr
    nlinarith

theorem rootShearSize_bound_on_symmetric_interval {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (hsmall : rootShearingKappa i j g ≤ 1)
    (t C : ℝ) (ht : |t| * rootShearingKappa i j g ≤ C) :
    ∀ u : ℝ, |u| ≤ |t| →
      rootShearSize hij g u ≤ (n : ℝ) * n * (2 * C + C ^ 2) := by
  intro u hu
  apply rootShearSize_bound_of_scale hij g hsmall u C
  exact (mul_le_mul_of_nonneg_right hu (rootShearingKappa_nonneg i j g)).trans ht

end DukePrimeDegree

end

end OAI
