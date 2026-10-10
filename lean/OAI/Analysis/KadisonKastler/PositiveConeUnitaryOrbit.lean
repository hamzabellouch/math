import OAI.Analysis.KadisonKastler.PositiveConeOrbitUniqueness

namespace OAI

/-! # Uniqueness on every commutant-unitary orbit in the positive cone

The quadratic action of `1 - J u J` and acuteness prove uniqueness
without assuming that either vector is the reference vector.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance positiveUnitaryOrbitRealInner : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

theorem positiveCone_unitary_orbit_unique
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ = ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    {η : H} (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (u : unitary (H →L[ℂ] H)) (hu : (u : H →L[ℂ] H) ∈ M.commutant)
    (hζ : (u : H →L[ℂ] H) η ∈ modularPositiveCone (M := M) J ξ) :
    (u : H →L[ℂ] H) η = η := by
  let ζ := (u : H →L[ℂ] H) η
  let q := conjugationUnitary J hJ u
  have hqM : (q : H →L[ℂ] H) ∈ M := hleft ⟨u,hu⟩
  have hηJ := modularPositiveCone_fixed J hright ξ hξ hη
  have hζJ := modularPositiveCone_fixed J hright ξ hξ hζ
  have hqη : (q : H →L[ℂ] H) η = ζ := by
    change J ((u : H →L[ℂ] H) (J η)) = ζ
    rw [hηJ]
    exact hζJ
  let a : Algebra M := 1 - ⟨q,hqM⟩
  have hrighta : conjugationOperator J a.val = 1 - (u : H →L[ℂ] H) := by
    change conjugationOperator J (1 - conjugationOperator J u) = _
    rw [conjugationOperator_sub,conjugationOperator_one J hJ,conjugationOperator_twice J hJ]
  have haη : modularQuadratic J a η = η - ζ - ζ + (q : H →L[ℂ] H) ζ := by
    change (1 - (q : H →L[ℂ] H)) (conjugationOperator J a.val η) = _
    rw [hrighta,sub_apply,one_apply_eq_self]
    change (1 - (q : H →L[ℂ] H)) (η-ζ) = _
    simp only [sub_apply,one_apply_eq_self,map_sub,hqη]
    abel
  have hinner : inner ℝ ζ ((q : H →L[ℂ] H) ζ) = inner ℝ ζ η := by
    have he := Unitary.inner_map_map q η ζ
    rw [hqη] at he
    exact (congrArg Complex.re he).trans (real_inner_comm ζ η)
  have hp := modularPositiveCone_acute J hJ hright ξ hpos hζ
    (modularQuadratic_preserves_positiveCone J hJ hright ξ a hη)
  rw [haη,inner_add_right,inner_sub_right,inner_sub_right,
    real_inner_self_eq_norm_sq,hinner] at hp
  change 0 ≤ inner ℝ ζ η - ‖ζ‖ ^ 2 - ‖ζ‖ ^ 2 + inner ℝ ζ η at hp
  have hn : ‖ζ‖ = ‖η‖ := Unitary.norm_map u η
  rw [hn] at hp
  have he := norm_sub_sq_real ζ η
  have hsq : ‖ζ-η‖ ^ 2 ≤ 0 := by
    rw [he,hn]
    nlinarith only [hp]
  have hz : ‖ζ-η‖ = 0 := by nlinarith only [hsq,sq_nonneg ‖ζ-η‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

end

end KadisonKastler

end OAI
