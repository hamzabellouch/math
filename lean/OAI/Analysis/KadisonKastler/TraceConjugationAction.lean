import OAI.Analysis.KadisonKastler.CountableTraceGroup

namespace OAI

/-! # The trace conjugation representation of the countable group -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

/-- Conjugation by a unitary, acting on the canonical trace Hilbert space. -/
def concreteTraceConjugationUnitary
    (hM : Generator.IsII1Factor M.toStarSubalgebra) (u : unitary (Algebra M)) :
    unitary (ConcreteTraceHilbert hM →L[ℂ] ConcreteTraceHilbert hM) :=
  concreteTraceLeftUnitary hM u * concreteTraceRightUnitary hM (star u)

@[simp] theorem concreteTraceConjugationUnitary_embedding
    (hM : Generator.IsII1Factor M.toStarSubalgebra) (u : unitary (Algebra M))
    (a : Algebra M) :
    (concreteTraceConjugationUnitary hM u :
      ConcreteTraceHilbert hM →L[ℂ] ConcreteTraceHilbert hM)
        (concreteTraceEmbedding hM a) =
      concreteTraceEmbedding hM ((u : Algebra M) * a * star (u : Algebra M)) := by
  change concreteTraceLeftAction hM u
    (concreteTraceRightAction hM (star (u : Algebra M)) (concreteTraceEmbedding hM a)) = _
  rw [concreteTraceRightAction_embedding, concreteTraceLeftAction_embedding, mul_assoc]

/-- The multiplication law follows on the dense bounded algebra vectors. -/
def concreteTraceConjugationAction
    (hM : Generator.IsII1Factor M.toStarSubalgebra) :
    unitary (Algebra M) →*
      unitary (ConcreteTraceHilbert hM →L[ℂ] ConcreteTraceHilbert hM) where
  toFun := concreteTraceConjugationUnitary hM
  map_one' := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    have he : ∀ x : ConcreteTraceHilbert hM,
        (concreteTraceConjugationUnitary hM 1 :
          ConcreteTraceHilbert hM →L[ℂ] ConcreteTraceHilbert hM) x = x := by
      apply isClosed_property (concreteTraceEmbedding_denseRange hM)
        (isClosed_eq (by fun_prop) continuous_id)
      intro a
      simp only [concreteTraceConjugationUnitary_embedding, OneMemClass.coe_one,
        star_one, one_mul, mul_one, id_eq]
    exact he
  map_mul' u v := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    have he : ∀ x : ConcreteTraceHilbert hM,
        (concreteTraceConjugationUnitary hM (u * v) :
          ConcreteTraceHilbert hM →L[ℂ] ConcreteTraceHilbert hM) x =
        (concreteTraceConjugationUnitary hM u :
          ConcreteTraceHilbert hM →L[ℂ] ConcreteTraceHilbert hM)
          ((concreteTraceConjugationUnitary hM v :
            ConcreteTraceHilbert hM →L[ℂ] ConcreteTraceHilbert hM) x) := by
      apply isClosed_property (concreteTraceEmbedding_denseRange hM)
        (isClosed_eq (by fun_prop) (by fun_prop))
      intro a
      simp only [concreteTraceConjugationUnitary_embedding, Submonoid.coe_mul,
        star_mul, mul_assoc]
    exact he

variable [TopologicalSpace.SeparableSpace H]

/-- A countable trace-dense group gives an actual unitary representation
whose fixed vectors are precisely the scalar trace vectors. -/
theorem exists_countable_trace_conjugation_representation
    (hM : Generator.IsII1Factor M.toStarSubalgebra) :
    ∃ G : Subgroup (unitary (Algebra M)),
      (G : Set (unitary (Algebra M))).Countable ∧
      ∃ σ : G →* unitary (ConcreteTraceHilbert hM →L[ℂ] ConcreteTraceHilbert hM),
        (∀ g, σ g = concreteTraceConjugationUnitary hM g.val) ∧
        (∀ v : ConcreteTraceHilbert hM,
          (∀ g, (σ g : ConcreteTraceHilbert hM →L[ℂ] ConcreteTraceHilbert hM) v = v) →
          ∃ z : ℂ, v = z • concreteTraceEmbedding hM 1) := by
  obtain ⟨G, hGc, hGdense⟩ := exists_countable_traceDense_unitary_subgroup
    (concreteFactorTrace hM) (concreteFactorTrace_finiteVector hM)
  let σ := (concreteTraceConjugationAction hM).comp G.subtype
  refine ⟨G, hGc, σ, fun _ => rfl, ?_⟩
  intro v hv
  exact concreteTrace_scalar_of_traceDense_invariant hM (fun g : G => g.val)
    hGdense v hv

end

end KadisonKastler

end OAI
