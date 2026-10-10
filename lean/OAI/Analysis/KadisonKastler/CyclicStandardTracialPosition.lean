import OAI.Analysis.KadisonKastler.TracialVectorExistence
import OAI.Analysis.KadisonKastler.StandardTracialPosition
import OAI.Analysis.KadisonKastler.FaithfulCyclicConstruction

namespace OAI

/-! # Standard tracial vectors on the faithful cyclic corner

A normal cyclic representation transports the cyclic trace vector
into the given cyclic separating representation of the same algebra.
-/

namespace KadisonKastler

noncomputable section

open Generator.Tracial UltrapowerBridge

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem exists_standardTracialPosition_of_cyclic_separating
    {M : VonNeumannAlgebra H} (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (Ω : H) (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) : Nonempty (StandardTracialPosition M) := by
  let hf := traceHilbert_factor hM
  let hu := traceHilbert_nonzero hM
  let K := TraceFreeHilbert hf hM.diffuse hM.finite hu
  let P := traceFreeHilbertClosure hf hM.diffuse hM.finite hu
  let τ := traceFreeHilbertClosureTrace hf hM.diffuse hM.finite hu
  let e := traceFreeHilbertEquiv hf hM.diffuse hM.finite hu
  let : TopologicalSpace.SeparableSpace K := concreteTraceHilbert_separable hM
  have hc : DenseRange (algebraVectorMap P τ.vector) :=
    traceFreeHilbertClosureTrace_cyclic hf hM.diffuse hM.finite hu
  have hs : Function.Injective (algebraVectorMap P τ.vector) := by
    intro a b hab
    apply sub_eq_zero.mp
    apply τ.separating
    change a.val τ.vector - b.val τ.vector = 0
    exact sub_eq_zero.mpr hab
  obtain ⟨W, hW⟩ := exists_spatial_of_normal_cyclic_separating e
    (traceFreeHilbertEquiv_boundedWeakNormal hM) Ω τ.vector hcyc hc hsep hs
  refine ⟨{
    trace := concreteFactorTrace hM
    vector := W.symm τ.vector
    trace_eq := ?_
    cyclic := spatialVectorTransport_cyclic e W hW τ.vector hc }⟩
  intro a
  calc
    (concreteFactorTrace hM).toLinearMap a = τ.trace (e a) :=
      (traceFreeHilbertClosureTrace_copy hf hM.diffuse hM.finite hu a).symm
    _ = inner ℂ (W.symm τ.vector) (a.val (W.symm τ.vector)) :=
      (spatialVectorTransport_state e W hW τ.vector a).symm

theorem exists_faithfulCyclic_standardTracialPosition [Nontrivial H]
    (M : VonNeumannAlgebra H) (hM : Generator.IsII1Factor M.toStarSubalgebra) :
    Nonempty (StandardTracialPosition (faithfulCyclicAlgebra M)) := by
  have hF : Generator.IsII1Factor (faithfulCyclicAlgebra M).toStarSubalgebra :=
    Generator.isII1Factor_of_starAlgEquiv (faithfulCyclicEquiv M) hM
      (vonNeumann_wotClosed (faithfulCyclicAlgebra M))
  exact exists_standardTracialPosition_of_cyclic_separating hF (faithfulCyclicVector M)
    (faithfulCyclicAlgebra_separating M) (by
      apply (faithfulCyclicHom_cyclic M).mono
      rintro _ ⟨a, rfl⟩
      exact ⟨faithfulCyclicEquiv M a, rfl⟩)

end

end KadisonKastler

end OAI
