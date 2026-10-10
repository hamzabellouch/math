import OAI.Analysis.Pureness.States.RegularizedStateQuotientTrace
import OAI.Analysis.Pureness.Cuntz.MatrixTraceCorrespondence
import OAI.Analysis.Pureness.States.FiniteStateComparison

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (hsimple : TopologicallySimple A) (hA : IsNuclear.{u,0} A)
include hsimple hA

theorem tracialState_of_finite_dimension_state
    (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y) :
    Nonempty (TracialState A) := by
  obtain ⟨τ⟩ := regularizedStateCauchyQuotient_has_tracialState hsimple y hy f hA
  exact ⟨(τ.comap (regularizedStateCauchyEmbedding hsimple y hy f 0)).comap
    (scalarMatrixHom (ι := Fin 1))⟩

theorem finite_dimension_states_empty_of_no_trace
    (htrace : ¬ Nonempty (TracialState A))
    (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) : IsEmpty (StateSpace y) :=
  ⟨fun f => htrace (tracialState_of_finite_dimension_state hsimple hA y hy f)⟩

theorem finiteComparison_of_nuclear_no_trace
    (hAU : ∀ (u v : CuntzClass (MatrixLimit A)) (k : ℕ), 1 ≤ k →
      (k+1) • u ≤ k • v → u ≤ v)
    (htrace : ¬ Nonempty (TracialState A))
    (L : ℕ) (M N : Positive (FinMatrix A L)) (hN : N.1 ≠ 0) :
    CuntzSubequiv M.1 N.1 := by
  apply finiteComparison_of_states hsimple hAU L M N hN
  intro f
  have hy : finitePositiveClass L N ≠ 0 :=
    fun h => hN ((finitePositiveClass_eq_zero_iff L N).mp h)
  exact (finite_dimension_states_empty_of_no_trace hsimple hA htrace _ hy).false f |>.elim
end CuntzPureness

end

end OAI
