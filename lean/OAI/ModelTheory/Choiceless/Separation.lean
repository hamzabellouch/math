import OAI.ModelTheory.Choiceless.QueryMachine

namespace OAI

namespace CPTSeparation

theorem main :
    (∀ (A B : Type) [Fintype A] [Fintype B] (S : Input A) (T : Input B),
      S.Iso T → (S.query ↔ T.query)) ∧
    OrdinaryPolynomialTime ∧
    ¬ FullCPT.EvaluationDefinable (fun {_} [_] I => I.query) := by
  refine ⟨?_, ?_, FullCPT.query_not_evaluationDefinable⟩
  · intro A B _ _ S T e
    exact Input.query_invariant e
  · refine ⟨QueryMachine.answer, QueryMachine.polynomialAlgorithm, ?_, ?_⟩
    · intro k
      change Finite QueryMachine.Letter
      infer_instance
    · intro A _ N e S
      let iso : S.Iso (S.ordered e) :=
        { toEquiv := e
          rel_eq := by intro r x y; simp [Input.ordered] }
      exact (QueryMachine.answer_correct ⟨N,S.ordered e⟩).trans
        (Input.query_invariant iso).symm

end CPTSeparation

end OAI
