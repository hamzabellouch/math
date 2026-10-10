import OAI.Analysis.KadisonKastler.TomitaPolarConjugation

namespace OAI

/-! # The state vector in the Tomita graph

Projection of `(Ω,0)` onto the unscaled graph is exactly half of `(Ω,JΩ)`.
This elementary identity identifies the state vector for the polar construction.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

theorem tomita_state_coefficient (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (a : Algebra M) :
    inner ℂ (J Ω) (J (star a.val Ω)) = inner ℂ Ω (a.val Ω) := by
  rw [conjugateIsometry_inner]
  change (starRingEnd ℂ) (inner ℂ Ω (star a.val Ω)) = _
  rw [inner_conj_symm, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]

theorem rescaledGraphProjection_state (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) :
    rescaledGraphProjection M J Ω 1 (Generator.tupleSingle 0 Ω) =
      (1 / 2 : ℂ) • rescaledGraphVector J Ω 1 1 := by
  let P := rescaledGraphSubspace M J Ω 1
  apply P.eq_starProjection_of_mem_of_inner_eq_zero
  · exact P.smul_mem _ (rescaledGraphVector_mem M J Ω 1 1)
  · intro v hv
    have hc : IsClosed {w : TomitaGraphHilbert H |
        inner ℂ (Generator.tupleSingle 0 Ω -
          (1 / 2 : ℂ) • rescaledGraphVector J Ω 1 1) w = 0} :=
      isClosed_eq (continuous_const.inner continuous_id) continuous_const
    apply closure_minimal (s := Set.range (rescaledGraphMap M J Ω 1)) ?_ hc hv
    rintro _ ⟨a, rfl⟩
    change inner ℂ (Generator.tupleSingle 0 Ω -
      (1 / 2 : ℂ) • rescaledGraphVector J Ω 1 1) (rescaledGraphVector J Ω 1 a.val) = 0
    simp only [inner_sub_left, inner_smul_left, PiLp.inner_apply, Fin.sum_univ_two,
      Generator.tupleSingle_apply, Pi.single_apply, Fin.isValue, ↓reduceIte,
      rescaledGraphVector_zero,
      rescaledGraphVector_one, one_smul, star_one, one_apply_eq_self]
    rw [tomita_state_coefficient J Ω a]
    have hhalf : (starRingEnd ℂ) (1 / 2) = (1 / 2 : ℂ) := by
      change star (1 / 2 : ℂ) = _
      simp
    simp only [show (1 : Fin 2) ≠ 0 from by decide, ite_false,
      inner_zero_left, add_zero, hhalf]
    ring

theorem graphResolvent_state (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) :
    graphResolvent M J Ω 1 Ω = (1 / 2 : ℂ) • Ω := by
  have h := congrArg (fun v : TomitaGraphHilbert H => v 0)
    (rescaledGraphProjection_state (M := M) J Ω)
  change graphResolvent M J Ω 1 Ω = (1 / 2 : ℂ) • Ω at h
  exact h

end

end KadisonKastler

end OAI
