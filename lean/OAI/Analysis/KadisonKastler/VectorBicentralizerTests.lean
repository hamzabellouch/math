import OAI.Analysis.KadisonKastler.CentralDefectStateBound
import Mathlib.Analysis.CStarAlgebra.Unitary.Span

namespace OAI

/-! # Unitary tests for the vector form of the bicentralizer

The closed asymptotic sequence algebra is a C-star algebra. Its four-unitary
decomposition shows that testing all its bounded sequences is equivalent
to testing its unitaries. This does not assert triviality of the bicentralizer.
-/

namespace KadisonKastler

open Filter
open scoped Topology BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
  (ξ : H) (hξ : J ξ = ξ)

instance centralSequenceAlgebra_complete :
    CompleteSpace (centralSequenceAlgebra J hJ hright ξ hξ) :=
  (centralSequenceAlgebra_isClosed J hJ hright ξ hξ).completeSpace_coe

instance centralSequenceAlgebra_cstar :
    CStarAlgebra (centralSequenceAlgebra J hJ hright ξ hξ) where

def vectorBicentralizerMember (a : Algebra M) : Prop :=
  ∀ x : BoundedSequence (Algebra M), AsymptoticallyCentral J ξ x →
    ∀ η : H, Tendsto (fun n => (a*(x n)-(x n)*a).val η) atTop (𝓝 0)

private def commutatorSequenceEvaluation (a : Algebra M) (η : H) (n : ℕ) :
    centralSequenceAlgebra J hJ hright ξ hξ →ₗ[ℂ] H where
  toFun x := (a*(x.val n)-(x.val n)*a).val η
  map_add' x y := by
    change a.val ((x.val n).val η + (y.val n).val η) -
        ((x.val n).val (a.val η) + (y.val n).val (a.val η)) =
      (a.val ((x.val n).val η) - (x.val n).val (a.val η)) +
        (a.val ((y.val n).val η) - (y.val n).val (a.val η))
    rw [map_add]
    abel
  map_smul' c x := by
    change (a*(c • (x.val n))-(c • (x.val n))*a).val η = _
    simp only [mul_smul_comm,smul_mul_assoc,← smul_sub,SetLike.val_smul,smul_apply,RingHom.id_apply]

theorem vectorBicentralizerMember_iff_unitary (a : Algebra M) :
    vectorBicentralizerMember J ξ a ↔
      ∀ u : unitary (centralSequenceAlgebra J hJ hright ξ hξ), ∀ η : H,
        Tendsto (fun n => (a*(u.val.val n)-(u.val.val n)*a).val η) atTop (𝓝 0) := by
  constructor
  · intro h u η
    exact h u.val.val u.val.property η
  · intro h x hx η
    let y : centralSequenceAlgebra J hJ hright ξ hξ := ⟨x,hx⟩
    obtain ⟨u,c,hy,_⟩ := CStarAlgebra.exists_sum_four_unitary y
    let T := commutatorSequenceEvaluation J hJ hright ξ hξ a η
    have he (n : ℕ) : T n y = ∑ i : Fin 4, c i • T n (u i).val := by
      rw [hy,map_sum]
      simp only [map_smul]
    have ht (i : Fin 4) : Tendsto (fun n => c i • T n (u i).val) atTop (𝓝 0) := by
      have hi : Tendsto (fun n => T n (u i).val) atTop (𝓝 0) := h (u i) η
      simpa only [smul_zero] using hi.const_smul (c i)
    have hall := tendsto_finsetSum Finset.univ (fun i _ => ht i)
    change Tendsto (fun n => T n y) atTop (𝓝 0)
    simpa only [← he,Finset.sum_const_zero] using hall

end

end KadisonKastler

end OAI
