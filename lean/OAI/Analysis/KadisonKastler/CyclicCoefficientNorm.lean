import OAI.Analysis.BoundedHochschild.NormalVectors
import OAI.Analysis.KadisonSimilarity.Derivation.CyclicDecomposition

namespace OAI

/-! # Norm-attaining coefficient models have cyclic sign vectors

Equality in the coefficient norm estimate places the left vector in the
closed orbit of the right vector. For a commuting sign operator, this
makes that cyclic space invariant under the sign.
-/

namespace KadisonKastler

noncomputable section

open KadisonSimilarity HochschildNormalPart
open scoped InnerProductSpace

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem coefficient_norm_eq_mem_orbitClosure
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ η : H)
    (hn : ‖η‖ = ‖ξ‖) (hf : ‖coefficient π η ξ‖ = ‖ξ‖ ^ 2) :
    η ∈ orbitClosure π.range ξ := by
  let K := orbitClosure π.range ξ
  have hcoeff : coefficient π (K.toSubmodule.starProjection η) ξ = coefficient π η ξ := by
    ext a
    change inner ℂ (K.toSubmodule.starProjection η) (π a ξ) = inner ℂ η (π a ξ)
    rw [K.toSubmodule.inner_starProjection_left_eq_right]
    congr 1
    apply K.toSubmodule.starProjection_eq_self_iff.mpr
    exact (LinearMap.range (orbitLinearMap π.range ξ)).le_topologicalClosure
      ⟨π.rangeRestrict a, rfl⟩
  apply (K.toSubmodule.mem_iff_norm_starProjection η).mpr
  by_cases hz : ‖ξ‖ = 0
  · have hη : η = 0 := norm_eq_zero.mp (hn.trans hz)
    simp [hη]
  · have hp := coefficient_norm π (K.toSubmodule.starProjection η) ξ
    rw [hcoeff, hf, sq] at hp
    have hle : ‖ξ‖ ≤ ‖K.toSubmodule.starProjection η‖ :=
      (mul_le_mul_iff_left₀ (lt_of_le_of_ne (norm_nonneg ξ) (Ne.symm hz))).mp hp
    apply le_antisymm (K.toSubmodule.norm_starProjection_apply_le η)
    rw [hn]
    exact hle

theorem commuting_operator_preserves_orbitClosure
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (S : H →L[ℂ] H)
    (hS : ∀ a, Commute S (π a)) (hξ : S ξ ∈ orbitClosure π.range ξ) :
    ∀ x ∈ orbitClosure π.range ξ, S x ∈ orbitClosure π.range ξ := by
  let K := orbitClosure π.range ξ
  have hle : K.toSubmodule ≤ K.toSubmodule.comap S.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro x ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := a.property
      change π b = a.val at hb
      change S (a.val ξ) ∈ K
      rw [← hb]
      have he := congrArg (fun T : H →L[ℂ] H => T ξ) (hS b).eq
      change S (π b ξ) = π b (S ξ) at he
      rw [he]
      exact orbitClosure_invariant π.range ξ (π.rangeRestrict b) _ hξ
    · exact K.isClosed.preimage S.continuous
  exact fun x hx => hle hx

end

end KadisonKastler

end OAI
