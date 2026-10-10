import OAI.Analysis.KadisonKastler.StateCentralSequenceAlgebra

namespace OAI

/-! # Equivalence of state and vector asymptotic centralizers

Four-unitary decomposition in the state-central sequence C-star algebra
extends the quantitative unitary result to every bounded sequence.
-/

namespace KadisonKastler

open Filter
open scoped Topology BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance stateCentralizerEquivalenceRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

private def stateSequenceVectorDefect (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) (n : ℕ) :
    stateCentralSequenceAlgebra (M := M) ξ →ₗ[ℂ] H where
  toFun x := centralVectorDefect J ξ (x.val n).val
  map_add' _ _ := by simp only [AddMemClass.coe_add,BoundedContinuousFunction.add_apply,
    AddMemClass.coe_add,map_add]
  map_smul' _ _ := by simp only [SetLike.val_smul,BoundedContinuousFunction.smul_apply,
    SetLike.val_smul,map_smul,RingHom.id_apply]

theorem StateAsymptoticallyCentral.vector
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (hcyc : DenseRange (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    {x : BoundedSequence (Algebra M)} (hx : StateAsymptoticallyCentral ξ x) :
    AsymptoticallyCentral J ξ x := by
  let y : stateCentralSequenceAlgebra (M := M) ξ := ⟨x,hx⟩
  obtain ⟨u,c,hy,_⟩ := CStarAlgebra.exists_sum_four_unitary y
  let T := stateSequenceVectorDefect (M := M) J ξ
  have he (n : ℕ) : T n y=∑ i : Fin 4, c i • T n (u i).val := by
    rw [hy,map_sum]
    simp only [map_smul]
  have ht (i : Fin 4) : Tendsto (fun n => T n (u i).val) atTop (𝓝 0) := by
    let v (n : ℕ) : unitary (Algebra M) := ⟨(u i).val.val n,by
      constructor
      · exact congrArg (fun z : stateCentralSequenceAlgebra (M := M) ξ => z.val n)
          (u i).property.1
      · exact congrArg (fun z : stateCentralSequenceAlgebra (M := M) ξ => z.val n)
          (u i).property.2⟩
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact (unitary_centrality_iff_state_commutator J hJ hright hleft ξ hξ hcyc hpos v).mpr
      (u i).val.property
  have hs (i : Fin 4) : Tendsto (fun n => c i • T n (u i).val) atTop (𝓝 0) := by
    simpa only [smul_zero] using (ht i).const_smul (c i)
  have hall := tendsto_finsetSum Finset.univ (fun i _ => hs i)
  have hvec : Tendsto (fun n => T n y) atTop (𝓝 0) := by
    simpa only [← he,Finset.sum_const_zero] using hall
  change Tendsto (fun n => ‖T n y‖) atTop (𝓝 0)
  simpa only [norm_zero] using hvec.norm

theorem asymptoticallyCentral_iff_state
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (hcyc : DenseRange (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (x : BoundedSequence (Algebra M)) :
    AsymptoticallyCentral J ξ x ↔ StateAsymptoticallyCentral ξ x :=
  ⟨fun hx => hx.state_commutator hJ hright hξ,
    fun hx => hx.vector J hJ hright hleft ξ hξ hcyc hpos⟩

theorem vectorBicentralizerMember_iff_state_sequences
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (hcyc : DenseRange (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ)) (a : Algebra M) :
    vectorBicentralizerMember J ξ a ↔
      ∀ x : BoundedSequence (Algebra M), StateAsymptoticallyCentral ξ x →
        ∀ η : H, Tendsto (fun n => (a*(x n)-(x n)*a).val η) atTop (𝓝 0) := by
  simp only [vectorBicentralizerMember,
    asymptoticallyCentral_iff_state J hJ hright hleft ξ hξ hcyc hpos]

end

end KadisonKastler

end OAI
