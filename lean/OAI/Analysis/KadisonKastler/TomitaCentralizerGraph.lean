import OAI.Analysis.KadisonKastler.TomitaVectorFixed

namespace OAI

/-! # Centralizer vectors in the closed Tomita graph -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

private theorem vectorState_star (Ω : H) (T : H →L[ℂ] H) :
    star (inner ℂ Ω (T Ω)) = inner ℂ Ω (star T Ω) := by
  change (starRingEnd ℂ) (inner ℂ Ω (T Ω)) = _
  rw [inner_conj_symm, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

theorem vectorState_centralizer_star (Ω : H) (r : Algebra M)
    (hr : ∀ a : Algebra M,
      inner ℂ Ω ((r.val * a.val) Ω) = inner ℂ Ω ((a.val * r.val) Ω)) :
    ∀ a : Algebra M,
      inner ℂ Ω ((star r.val * a.val) Ω) = inner ℂ Ω ((a.val * star r.val) Ω) := by
  intro a
  have h := congrArg star (hr (star a))
  change star (inner ℂ Ω ((r.val * star a.val) Ω)) =
    star (inner ℂ Ω ((star a.val * r.val) Ω)) at h
  rw [vectorState_star, vectorState_star, star_mul, star_mul, star_star] at h
  exact h.symm

theorem tomita_centralizer_coefficient (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (r : Algebra M)
    (hr : ∀ a : Algebra M,
      inner ℂ Ω ((r.val * a.val) Ω) = inner ℂ Ω ((a.val * r.val) Ω)) (a : Algebra M) :
    inner ℂ (J (star r.val Ω)) (J (star a.val Ω)) = inner ℂ (r.val Ω) (a.val Ω) := by
  rw [conjugateIsometry_inner]
  change (starRingEnd ℂ) (inner ℂ (star r.val Ω) (star a.val Ω)) = _
  rw [inner_conj_symm]
  calc
    inner ℂ (star a.val Ω) (star r.val Ω) =
        inner ℂ Ω ((a.val * star r.val) Ω) := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
      rfl
    _ = inner ℂ Ω ((star r.val * a.val) Ω) := (vectorState_centralizer_star Ω r hr a).symm
    _ = inner ℂ (r.val Ω) (a.val Ω) := by
      change inner ℂ Ω (star r.val (a.val Ω)) = _
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

/-- The graph resolvent acts as one half on every vector-state centralizer vector. -/
theorem rescaledGraphProjection_centralizer (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (r : Algebra M)
    (hr : ∀ a : Algebra M,
      inner ℂ Ω ((r.val * a.val) Ω) = inner ℂ Ω ((a.val * r.val) Ω)) :
    rescaledGraphProjection M J Ω 1 (Generator.tupleSingle 0 (r.val Ω)) =
      (1 / 2 : ℂ) • rescaledGraphVector J Ω 1 r.val := by
  let P := rescaledGraphSubspace M J Ω 1
  apply P.eq_starProjection_of_mem_of_inner_eq_zero
  · exact P.smul_mem _ (rescaledGraphVector_mem M J Ω 1 r)
  · intro v hv
    have hc : IsClosed {w : TomitaGraphHilbert H |
        inner ℂ (Generator.tupleSingle 0 (r.val Ω) -
          (1 / 2 : ℂ) • rescaledGraphVector J Ω 1 r.val) w = 0} :=
      isClosed_eq (continuous_const.inner continuous_id) continuous_const
    apply closure_minimal (s := Set.range (rescaledGraphMap M J Ω 1)) ?_ hc hv
    rintro _ ⟨a, rfl⟩
    change inner ℂ (Generator.tupleSingle 0 (r.val Ω) -
      (1 / 2 : ℂ) • rescaledGraphVector J Ω 1 r.val) (rescaledGraphVector J Ω 1 a.val) = 0
    simp only [inner_sub_left, inner_smul_left, PiLp.inner_apply, Fin.sum_univ_two,
      Generator.tupleSingle_apply, Pi.single_apply, Fin.isValue, ↓reduceIte,
      rescaledGraphVector_zero, rescaledGraphVector_one, one_smul]
    rw [tomita_centralizer_coefficient J Ω r hr a]
    have hhalf : (starRingEnd ℂ) (1 / 2) = (1 / 2 : ℂ) := by
      change star (1 / 2 : ℂ) = _
      simp
    simp only [show (1 : Fin 2) ≠ 0 from by decide, ite_false,
      inner_zero_left, add_zero, hhalf]
    ring

theorem graphResolvent_centralizer (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (r : Algebra M)
    (hr : ∀ a : Algebra M,
      inner ℂ Ω ((r.val * a.val) Ω) = inner ℂ Ω ((a.val * r.val) Ω)) :
    graphResolvent M J Ω 1 (r.val Ω) = (1 / 2 : ℂ) • r.val Ω := by
  have h := congrArg (fun v : TomitaGraphHilbert H => v 0)
    (rescaledGraphProjection_centralizer J Ω r hr)
  exact h

end

end KadisonKastler

end OAI
