import OAI.Analysis.FactorGeneration.RelativeGeneration
import OAI.Analysis.RelativeGeneration.ConditionalMembership
import OAI.Analysis.RelativeGeneration.DistanceSections

namespace OAI

noncomputable section

open scoped Topology

namespace Generator.Tracial

open UltrapowerBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hNM : N ≤ M)

def relativeDistance (ξ : H) (unitary : TraceUnitary τ) : ℝ :=
  Metric.infDist ξ (relativeTraceSpace (N := N) τ unitary : Set H)

include hNM in
theorem relativeDistance_sublevel_open (ξ : H) (ε : ℝ) :
    IsOpen {unitary : TraceUnitary τ | relativeDistance (N := N) τ ξ unitary < ε} :=
  RelativeCompletion.isOpen_infDist_lt_dense_sections
    (fun unitary => (relativeTraceSpace (N := N) τ unitary : Set H))
    (RelativePolynomial.sectionVector τ hNM) (polynomialVector_mem τ hNM)
    (RelativePolynomial.continuous_sectionVector τ hNM)
    (polynomialVector_dense τ hNM)
    (fun unitary => ⟨0, (relativeTraceSpace (N := N) τ unitary).zero_mem⟩) ξ ε

include hNM in
theorem relativeGenerated_eq_iff_dense_distances
    (η : ℕ → traceCyclicSpace τ) (hη : DenseRange η) (unitary : TraceUnitary τ) :
    relativeGenerated (N := N) τ unitary = M ↔
      ∀ index level : ℕ,
        relativeDistance (N := N) τ (η index).val unitary < 1 / (level + 1 : ℝ) := by
  constructor
  · intro heq index level
    have hmem : (η index).val ∈ relativeTraceSpace (N := N) τ unitary := by
      change (η index).val ∈
        vectorOrbitClosure (relativeGenerated (N := N) τ unitary).toStarSubalgebra τ.vector
      rw [heq]
      exact (η index).property
    change Metric.infDist _ _ < _
    rw [Metric.infDist_zero_of_mem hmem]
    positivity
  · intro hdist
    let traceSpace := relativeTraceSpace (N := N) τ unitary
    have hclosed : IsClosed (traceSpace : Set H) := Submodule.isClosed_topologicalClosure _
    have hmem (index : ℕ) : (η index).val ∈ traceSpace := by
      apply (hclosed.mem_iff_infDist_zero ⟨0, traceSpace.zero_mem⟩).mpr
      apply le_antisymm _ Metric.infDist_nonneg
      by_contra hpos
      obtain ⟨level, hlevel⟩ := exists_nat_one_div_lt (lt_of_not_ge hpos)
      exact (not_lt_of_ge (hdist index level).le) hlevel
    have hall (ξ : traceCyclicSpace τ) : ξ.val ∈ traceSpace := by
      have hpreimage : IsClosed {ξ : traceCyclicSpace τ | ξ.val ∈ traceSpace} :=
        hclosed.preimage continuous_subtype_val
      exact closure_minimal (by rintro _ ⟨index, rfl⟩; exact hmem index) hpreimage (hη ξ)
    apply le_antisymm (relativeGenerated_le τ hNM unitary)
    intro element helement
    exact mem_subalgebra_of_baseVector_mem τ (relativeGenerated_le τ hNM unitary)
      ⟨element, helement⟩
      (hall ⟨baseVector τ ⟨element, helement⟩,
        Submodule.le_topologicalClosure _ ⟨⟨element, helement⟩, rfl⟩⟩)

include hNM in
theorem relativeGeneratingLocus_eq_iInter
    (η : ℕ → traceCyclicSpace τ) (hη : DenseRange η) :
    {unitary : TraceUnitary τ | relativeGenerated (N := N) τ unitary = M} =
      ⋂ index : ℕ, ⋂ level : ℕ,
        {unitary | relativeDistance (N := N) τ (η index).val unitary <
          1 / (level + 1 : ℝ)} := by
  ext unitary
  simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  exact relativeGenerated_eq_iff_dense_distances τ hNM η hη unitary

include hNM in
theorem relativeGeneratingLocus_isGδ
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) :
    IsGδ {unitary : TraceUnitary τ | relativeGenerated (N := N) τ unitary = M} := by
  let := traceCyclicSpace_separable τ hsep
  obtain ⟨η, hη⟩ := TopologicalSpace.exists_dense_seq (traceCyclicSpace τ)
  rw [relativeGeneratingLocus_eq_iInter τ hNM η hη]
  exact IsGδ.iInter fun index => IsGδ.iInter_of_isOpen fun level =>
    relativeDistance_sublevel_open τ hNM (η index).val (1 / (level + 1 : ℝ))

end Generator.Tracial

end

end OAI
