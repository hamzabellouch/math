import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixNormalizedLeaves

namespace OAI

/-! # Actual group-valued leaf measures for the remaining subgroups -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

def remainingGroupLeafMeasure (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hfinal : c.finalEntries = allPositiveRoots n) (ν : Measure c.Time) :
    Measure (positiveRootGeneratedGroup (allPositiveRoots n \ P)) :=
  ν.map (c.remainingWordHomeomorph hP hfinal)

lemma remainingGroupLeafMeasure_locallyFinite (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n)
    (ν : Measure c.Time) [IsLocallyFiniteMeasure ν] :
    IsLocallyFiniteMeasure (c.remainingGroupLeafMeasure hP hfinal ν) := by
  let E := c.remainingWordHomeomorph hP hfinal
  constructor
  intro u
  obtain ⟨V,hu,hV,hfin⟩ := Measure.exists_isOpen_measure_lt_top ν (E.symm u)
  refine ⟨E '' V,(E.isOpenMap _ hV).mem_nhds ⟨E.symm u,hu,E.apply_symm_apply u⟩,?_⟩
  change ν.map E (E '' V) < ⊤
  rw [Measure.map_apply E.measurable (E.isOpenMap _ hV).measurableSet,
    E.injective.preimage_image]
  exact hfin

lemma remainingGroupLeafMeasure_apply (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n)
    (ν : Measure c.Time) {S : Set c.Time} (hS : MeasurableSet S) :
    c.remainingGroupLeafMeasure hP hfinal ν (c.remainingWordHomeomorph hP hfinal '' S) = ν S := by
  let E := c.remainingWordHomeomorph hP hfinal
  rw [remainingGroupLeafMeasure,Measure.map_apply E.measurable
    (E.measurableEmbedding.measurableSet_image.mpr hS),E.injective.preimage_image]

lemma remainingGroupLeafMeasure_restrict (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hfinal : c.finalEntries = allPositiveRoots n)
    (ν : Measure c.Time) {S : Set c.Time} (hS : MeasurableSet S) :
    (c.remainingGroupLeafMeasure hP hfinal ν).restrict (c.remainingWordHomeomorph hP hfinal '' S) =
      (ν.restrict S).map (c.remainingWordHomeomorph hP hfinal) := by
  let E := c.remainingWordHomeomorph hP hfinal
  rw [remainingGroupLeafMeasure,Measure.restrict_map E.measurable
    (E.measurableEmbedding.measurableSet_image.mpr hS),E.injective.preimage_image]

end EliminationChain
namespace RootPrefixBox
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    {Pfx : RootPrefixCoordinates n P T} {c : EliminationChain P D}
    {hP : InitialRootPattern P} {hfinal : c.finalEntries = allPositiveRoots n} {g : G n}

theorem ae_exists_groupLeafMeasure (A : RootPrefixBox Pfx c hP hfinal g) (R : ℝ)
    (hAR : A.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) :
    ∀ᵐ s ∂(A.coordinateMeasure μ).fst,
      ∃ ν : Measure (positiveRootGeneratedGroup (allPositiveRoots n \ P)),
        IsLocallyFiniteMeasure ν ∧ ν (c.remainingWordHomeomorph hP hfinal '' A.time) = 1 ∧
        ν.restrict (c.remainingWordHomeomorph hP hfinal '' A.time) =
          (A.conditionalKernel μ s).map (c.remainingWordHomeomorph hP hfinal) := by
  filter_upwards [A.ae_exists_prefixLeafMeasure R hAR μ hfree] with s hs
  obtain ⟨η,hloc,hmass,hres,_⟩ := hs
  let : IsLocallyFiniteMeasure η := hloc
  refine ⟨c.remainingGroupLeafMeasure hP hfinal η,
    c.remainingGroupLeafMeasure_locallyFinite hP hfinal η,?_,?_⟩
  · rw [c.remainingGroupLeafMeasure_apply hP hfinal η A.time_open.measurableSet]
    exact hmass
  · rw [c.remainingGroupLeafMeasure_restrict hP hfinal η A.time_open.measurableSet,hres]

end RootPrefixBox
end DukePrimeDegree

end

end OAI
