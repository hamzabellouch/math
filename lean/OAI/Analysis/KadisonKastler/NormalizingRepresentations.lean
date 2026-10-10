import OAI.Analysis.KadisonKastler.BoundaryIntertwiner
import OAI.Analysis.KadisonKastler.AmenableEmbedding
import OAI.Analysis.KadisonKastler.Algebra

namespace OAI

/-! # Transporting normalization between nearby representations

This is the final change of position in modular alignment. The exact
normalizing representation is conjugated to the given representation
using the actual averaged intertwiner and its polar unitary.
-/

namespace KadisonKastler

open scoped CStarAlgebra BoundedContinuousFunction

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {G : Type*} [Group G]

/-- An intertwiner transports a normalizing action to the conjugated algebra. -/
theorem conjugates_self_of_intertwined_representation
    (P : VonNeumannAlgebra H) (U z : G →* unitary (H →L[ℂ] H))
    (hz : ∀ g, Conjugates (z g) P P) (w : unitary (H →L[ℂ] H))
    (hw : ∀ g, (w : H →L[ℂ] H) * (U g : H →L[ℂ] H) =
      (z g : H →L[ℂ] H) * (w : H →L[ℂ] H)) (g : G) :
    Conjugates (U g) (unitaryConjugateAlgebra (star w) P)
      (unitaryConjugateAlgebra (star w) P) := by
  have he : star w * z g * w = U g := by
    apply Subtype.ext
    change star (w : H →L[ℂ] H) * (z g : H →L[ℂ] H) * (w : H →L[ℂ] H) = _
    rw [mul_assoc, ← hw, ← mul_assoc, Unitary.star_mul_self_of_mem w.property, one_mul]
  have hq := conjugates_unitaryConjugateAlgebra (star w) P
  have hq' : Conjugates w (unitaryConjugateAlgebra (star w) P) P := by
    simpa only [star_star] using hq.symm
  simpa only [← mul_assoc, he] using (hq'.trans (hz g)).trans hq

variable [TopologicalSpace G] [DiscreteTopology G]

local instance normalizingFunctionCStar : CStarAlgebra (G →ᵇ (H →L[ℂ] H)) where

/-- A translation-invariant bimodule mean gives the single small change of
position. No regularity is required of the normalizing representation. -/
theorem exists_near_conjugated_normalizing_action
    (P : VonNeumannAlgebra H) (U z : G →* unitary (H →L[ℂ] H))
    (hz : ∀ g, Conjugates (z g) P P)
    (m : BimoduleMean (boundaryConstant (G := G) (B := H →L[ℂ] H)))
    (hm : ∀ g f, m.toCLM (boundaryTranslate (1 : G →* ((H →L[ℂ] H) ≃⋆ₐ[ℂ]
      (H →L[ℂ] H))) g f) = m.toCLM f)
    {d : ℝ} (hd : d < 1)
    (hclose : ∀ g, ‖(z g : H →L[ℂ] H) - (U g : H →L[ℂ] H)‖ ≤ d) :
    ∃ q : unitary (H →L[ℂ] H), ‖(q : H →L[ℂ] H) - 1‖ ≤ 2 * d ∧
      ∀ g, Conjugates (U g) (unitaryConjugateAlgebra q P)
        (unitaryConjugateAlgebra q P) := by
  let α : G →* ((H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H)) := 1
  let S := boundedUnitaryFamily z
  have hS (g k : G) : S.val g * α g (S.val k) = S.val (g * k) := by
    change (z g : H →L[ℂ] H) * (z k : H →L[ℂ] H) = (z (g * k) : H →L[ℂ] H)
    rw [map_mul, Submonoid.coe_mul]
  obtain ⟨w, hw, hn⟩ := exists_unitary_boundary_intertwiner α m
    (by intro g f; exact hm g f) S hS U (by intro g t; rfl) hd hclose
  refine ⟨star w, ?_, ?_⟩
  · have he : ‖(star w : H →L[ℂ] H) - 1‖ = ‖(w : H →L[ℂ] H) - 1‖ := by
      simpa only [Unitary.coe_star, star_sub, star_one] using
        norm_star ((w : H →L[ℂ] H) - 1)
    exact he ▸ hn
  · intro g
    apply conjugates_self_of_intertwined_representation P U z hz w
    intro k
    exact hw k

end

end KadisonKastler

end OAI
