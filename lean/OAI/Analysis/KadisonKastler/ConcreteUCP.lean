import OAI.Analysis.KadisonKastler.UCP
import OAI.Analysis.KadisonKastler.PairedRepresentations

namespace OAI

/-!
# The UCP criterion for concrete von Neumann algebras

The ordinary Kadison--Kastler gap supplies precisely the reverse unit-ball
approximation used in the UCP range argument.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _

local instance (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

/-- The faithful inclusion of a concrete von Neumann algebra into its
ambient bounded operators. -/
abbrev algebraInclusion (M : VonNeumannAlgebra H) :
    Algebra M →⋆ₐ[ℂ] (H →L[ℂ] H) := M.toStarSubalgebra.subtype

theorem reverse_gap_of_kkDistance_lt {M N : VonNeumannAlgebra H} {g : ℝ}
    (hgap : kkDistance M N < g) :
    ∀ y : Algebra N, ‖y‖ ≤ 1 → ∀ r : ℝ, g < r →
      ∃ x : Algebra M, ‖x‖ ≤ 1 ∧
        ‖algebraInclusion N y - algebraInclusion M x‖ < r := by
  intro y hy r hr
  have hdist : kkDistance N M < r := by rw [kkDistance_comm]; exact hgap.trans hr
  obtain ⟨x, hx, hxy⟩ := exists_unitBall_approx
    (M := N) (N := M) (x := (y : H →L[ℂ] H)) ⟨y.property, hy⟩ hdist
  exact ⟨⟨x, hx.1⟩, hx.2, hxy⟩

/-- An intertwining star-algebra equivalence gives equality of the
concrete algebras after unitary conjugation. -/
theorem conjugates_of_starEquiv {M N : VonNeumannAlgebra H}
    (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N) (u : unitary (H →L[ℂ] H))
    (hθ : ∀ x : Algebra M,
      (u : H →L[ℂ] H) * algebraInclusion M x * star (u : H →L[ℂ] H) =
        algebraInclusion N (θ x)) :
    Conjugates u M N := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    rw [show unitaryConj u x = algebraInclusion N (θ ⟨x, hx⟩) from hθ ⟨x, hx⟩]
    exact (θ ⟨x, hx⟩).property
  · intro y hy
    obtain ⟨x, hx⟩ := θ.surjective ⟨y, hy⟩
    change θ x = ⟨y, hy⟩ at hx
    refine ⟨(x : H →L[ℂ] H), x.property, ?_⟩
    change (u : H →L[ℂ] H) * algebraInclusion M x * star (u : H →L[ℂ] H) = y
    rw [hθ, hx]
    rfl

/-- The concrete-algebra isomorphism part of the UCP criterion, with the
ordinary metric used only for the reverse gap. -/
theorem concrete_ucp_starEquiv_of_published {M N : VonNeumannAlgebra H}
    (hPublished : PublishedMultiplicationCorrection M)
    (φ : Algebra M →CP Algebra N) (hφ : φ 1 = 1)
    {e g : ℝ} (he : 0 ≤ e) (he₁ : e < 1 / 1000) (hge : g + e < 1)
    (hclose : CompletelyBoundedBy
      ((algebraInclusion N).toAlgHom.toLinearMap.comp φ.toLinearMap -
        (algebraInclusion M).toAlgHom.toLinearMap) e)
    (hgap : kkDistance M N < g) :
    ∃ θ : Algebra M ≃⋆ₐ[ℂ] Algebra N,
      CompletelyBoundedBy
        ((algebraInclusion N).toAlgHom.toLinearMap.comp θ.toAlgEquiv.toLinearMap -
          (algebraInclusion M).toAlgHom.toLinearMap) (32 * e) := by
  exact ucp_starEquiv_of_published M hPublished φ hφ
    (algebraInclusion M) (algebraInclusion N) Subtype.val_injective Subtype.val_injective
    he he₁ hge hclose (reverse_gap_of_kkDistance_lt hgap)

/-- The unitary-conjugacy conclusion of the UCP criterion for concrete
algebras. Both published inputs are explicit, while positivity,
surjectivity, correction estimates, and polar implementation are proved. -/
theorem concrete_ucp_unitary_of_published {M N : VonNeumannAlgebra H}
    (hCorrection : PublishedMultiplicationCorrection M)
    (hCommutant : PublishedBlockCommutantApproximation (Algebra M) H)
    (φ : Algebra M →CP Algebra N) (hφ : φ 1 = 1)
    {e g : ℝ} (he : 0 ≤ e) (he₁ : e < 1 / 1000) (hge : g + e < 1)
    (hclose : CompletelyBoundedBy
      ((algebraInclusion N).toAlgHom.toLinearMap.comp φ.toLinearMap -
        (algebraInclusion M).toAlgHom.toLinearMap) e)
    (hgap : kkDistance M N < g) :
    ∃ u : unitary (H →L[ℂ] H),
      Conjugates u M N ∧ ‖(u : H →L[ℂ] H) - 1‖ ≤ 128 * e := by
  obtain ⟨θ, hθ⟩ := concrete_ucp_starEquiv_of_published hCorrection φ hφ
    he he₁ hge hclose hgap
  let θrep : Algebra M →⋆ₐ[ℂ] (H →L[ℂ] H) :=
    (algebraInclusion N).comp θ.toStarAlgHom
  have hrep : θrep.toAlgHom.toLinearMap =
      (algebraInclusion N).toAlgHom.toLinearMap.comp θ.toAlgEquiv.toLinearMap := by
    ext x
    rfl
  have hreverse : CompletelyBoundedBy
      ((algebraInclusion M).toAlgHom.toLinearMap - θrep.toAlgHom.toLinearMap)
      (32 * e) := by
    intro p q X
    have h := hθ p q X
    rw [matrix_map_sub] at h
    rw [hrep, matrix_map_sub]
    simpa only [norm_sub_rev] using h
  obtain ⟨u, hu, hnorm⟩ := close_representations_of_published hCommutant
    (algebraInclusion M) θrep (by positivity) (by linarith) hreverse
  refine ⟨u, conjugates_of_starEquiv θ u hu, ?_⟩
  linarith

end

end KadisonKastler

end OAI
