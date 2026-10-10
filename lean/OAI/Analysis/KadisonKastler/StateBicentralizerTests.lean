import OAI.Analysis.KadisonKastler.StateCentralizerEquivalence

namespace OAI

/-! # State-sequence bicentralizers and their unitary tests

This formulation applies to a separating vector even when its algebra
orbit is a proper subspace of the represented Hilbert space.
-/

namespace KadisonKastler

open Filter
open scoped Topology BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def stateBicentralizerMember (ξ : H) (a : Algebra M) : Prop :=
  ∀ x : BoundedSequence (Algebra M), StateAsymptoticallyCentral ξ x →
    ∀ η : H, Tendsto (fun n => (a*(x n)-(x n)*a).val η) atTop (𝓝 0)

private def stateCommutatorEvaluation (ξ : H) (a : Algebra M) (η : H) (n : ℕ) :
    stateCentralSequenceAlgebra (M := M) ξ →ₗ[ℂ] H where
  toFun x := (a*(x.val n)-(x.val n)*a).val η
  map_add' x y := by
    change a.val ((x.val n).val η+(y.val n).val η)-
      ((x.val n).val (a.val η)+(y.val n).val (a.val η)) =
      (a.val ((x.val n).val η)-(x.val n).val (a.val η))+
        (a.val ((y.val n).val η)-(y.val n).val (a.val η))
    rw [map_add]
    abel
  map_smul' c x := by
    change (a*(c • (x.val n))-(c • (x.val n))*a).val η = _
    simp only [mul_smul_comm,smul_mul_assoc,← smul_sub,SetLike.val_smul,smul_apply,RingHom.id_apply]

theorem stateBicentralizerMember_iff_unitary_tests (ξ : H) (a : Algebra M) :
    stateBicentralizerMember ξ a ↔
      ∀ u : ℕ → unitary (Algebra M),
        Tendsto (fun n => ‖vectorStateCommutator ξ (u n).val‖) atTop (𝓝 0) →
        ∀ η : H, Tendsto (fun n => (a*(u n).val-(u n).val*a).val η) atTop (𝓝 0) := by
  constructor
  · intro ha u hu η
    let x : BoundedSequence (Algebra M) :=
      BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun n => (u n).val) 1
        (fun n => norm_unitary_le_one (u n))
    exact ha x hu η
  · intro ha x hx η
    let y : stateCentralSequenceAlgebra (M := M) ξ := ⟨x,hx⟩
    obtain ⟨u,c,hy,_⟩ := CStarAlgebra.exists_sum_four_unitary y
    let T := stateCommutatorEvaluation ξ a η
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
      exact ha v (u i).val.property η
    have hs (i : Fin 4) : Tendsto (fun n => c i • T n (u i).val) atTop (𝓝 0) := by
      simpa only [smul_zero] using (ht i).const_smul (c i)
    have hall := tendsto_finsetSum Finset.univ (fun i _ => hs i)
    change Tendsto (fun n => T n y) atTop (𝓝 0)
    simpa only [← he,Finset.sum_const_zero] using hall

end

end KadisonKastler

end OAI
