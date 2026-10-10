import OAI.Analysis.KadisonKastler.PreparedPairState

namespace OAI

/-! # Central vectors and the relative commutant

The central-vector space used in Haagerup's construction is a closed
complex subspace. A one-dimensional central-vector space detects an
irreducible inclusion once its generating vector is separating.
-/

namespace KadisonKastler

open UltrapowerBridge

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {N P M : VonNeumannAlgebra H}

/-- Vectors on which left and conjugate-right multiplication agree. -/
def centralVectorSpace (N : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) : Submodule ℂ H where
  carrier := {ξ | ∀ a : Algebra N, a.val ξ = conjugationOperator J (star a).val ξ}
  zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero, implies_true]
  add_mem' := by
    intro ξ η hξ hη a
    simp only [map_add, hξ a, hη a]
  smul_mem' := by
    intro c ξ hξ a
    simp only [map_smul, hξ a]

@[simp] theorem mem_centralVectorSpace (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) :
    ξ ∈ centralVectorSpace N J ↔
      ∀ a : Algebra N, a.val ξ = conjugationOperator J (star a).val ξ := Iff.rfl

theorem centralVectorSpace_isClosed (N : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) :
    IsClosed (centralVectorSpace N J : Set H) := by
  change IsClosed {ξ | ∀ a : Algebra N, a.val ξ = conjugationOperator J (star a).val ξ}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter (fun a => isClosed_eq a.val.continuous
    (conjugationOperator J (star a).val).continuous)

instance centralVectorSpace_complete (N : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) :
    CompleteSpace (centralVectorSpace N J) :=
  (centralVectorSpace_isClosed N J).completeSpace_coe

theorem centralVectorSpace_antitone (hNP : N ≤ P) (J : H ≃ₗᵢ⋆[ℂ] H) :
    centralVectorSpace P J ≤ centralVectorSpace N J := by
  intro ξ hξ a
  exact hξ (StarSubalgebra.inclusion hNP a)

/-- The relative commutant acts on central vectors. -/
theorem centralVectorSpace_invariant (J : H ≃ₗᵢ⋆[ℂ] H)
    (hright : ∀ a : Algebra N, conjugationOperator J (star a).val ∈ M.commutant)
    (T : H →L[ℂ] H) (hT : T ∈ M)
    (hcomm : ∀ a : Algebra N, a.val * T = T * a.val)
    {ξ : H} (hξ : ξ ∈ centralVectorSpace N J) : T ξ ∈ centralVectorSpace N J := by
  intro a
  calc
    a.val (T ξ) = T (a.val ξ) := congrArg (fun S : H →L[ℂ] H => S ξ) (hcomm a)
    _ = T (conjugationOperator J (star a).val ξ) := congrArg T (hξ a)
    _ = conjugationOperator J (star a).val (T ξ) :=
      congrArg (fun S : H →L[ℂ] H => S ξ)
        (VonNeumannAlgebra.mem_commutant_iff.mp (hright a) T hT)

/-- A separating central vector spanning all central vectors forces irreducibility. -/
theorem scalar_relative_commutant_of_centralVectorSpace
    (J : H ≃ₗᵢ⋆[ℂ] H)
    (hright : ∀ a : Algebra N, conjugationOperator J (star a).val ∈ M.commutant)
    (ξ : H) (hξ : ξ ∈ centralVectorSpace N J)
    (hline : centralVectorSpace N J ≤ Submodule.span ℂ {ξ})
    (hsep : Function.Injective (fun a : Algebra M => a.val ξ))
    (T : H →L[ℂ] H) (hT : T ∈ M)
    (hcomm : ∀ a : Algebra N, a.val * T = T * a.val) :
    ∃ z : ℂ, T = z • (1 : H →L[ℂ] H) := by
  obtain ⟨z,hz⟩ := Submodule.mem_span_singleton.mp
    (hline (centralVectorSpace_invariant J hright T hT hcomm hξ))
  refine ⟨z, ?_⟩
  have ha : (⟨T,hT⟩ : Algebra M) = z • (1 : Algebra M) := by
    apply hsep
    change T ξ = z • ξ
    exact hz.symm
  exact congrArg Subtype.val ha

theorem centralVectorSpace_conjugate (N : VonNeumannAlgebra H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    {ξ : H} (hξ : ξ ∈ centralVectorSpace N J) : J ξ ∈ centralVectorSpace N J := by
  intro a
  have h := congrArg J (hξ (star a))
  change J ((star a).val ξ) = J (J ((star (star a)).val (J ξ))) at h
  rw [star_star,hJ] at h
  change a.val (J ξ) = J ((star a).val (J (J ξ)))
  rw [hJ]
  exact h.symm

end

end KadisonKastler

end OAI
