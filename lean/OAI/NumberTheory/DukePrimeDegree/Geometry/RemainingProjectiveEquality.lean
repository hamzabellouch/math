import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixBasedMeasure

namespace OAI

/-! # Recovering a prefix conditional from its based group measure -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}

lemma centeredRemainingMeasure_unit_lt_top (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries = allPositiveRoots n)
    (ν : Measure c.Time) [IsLocallyFiniteMeasure ν] (t : c.Time) :
    c.centeredRemainingMeasure hP hf ν t (c.cube 1) < ∞ := by
  let : IsLocallyFiniteMeasure (c.centeredRemainingMeasure hP hf ν t) :=
    c.centeredRemainingMeasure_locallyFinite hP hf ν t
  exact (measure_mono (c.cube_subset_closedCube 1)).trans_lt
    (c.closedCube_compact 1).measure_lt_top

lemma uncenter_basedRemainingGroupMeasure (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries = allPositiveRoots n)
    (ν : Measure c.Time) (t : c.Time) :
    ((c.remainingGroupLeafMeasure hP hf (c.basedRemainingMeasure hP hf ν t)).map
        (Homeomorph.mulLeft (c.remainingWordHomeomorph hP hf t))).map
        (c.remainingWordHomeomorph hP hf).symm =
      (c.centeredRemainingMeasure hP hf ν t (c.cube 1))⁻¹ • ν := by
  let W := c.remainingWordHomeomorph hP hf
  let E := c.remainingRebase hP hf t
  change (((anchorNormalize (ν.map E) (c.cube 1)).map W).map
    (Homeomorph.mulLeft (W t))).map W.symm = _
  rw [anchorNormalize,Measure.map_smul _ W.measurable.aemeasurable,
    Measure.map_smul _ (Homeomorph.mulLeft (W t)).measurable.aemeasurable,
    Measure.map_smul _ W.symm.measurable.aemeasurable]
  congr 1
  rw [Measure.map_map W.measurable E.measurable,
    Measure.map_map (Homeomorph.mulLeft (W t)).measurable (W.measurable.comp E.measurable),
    Measure.map_map W.symm.measurable
      ((Homeomorph.mulLeft (W t)).measurable.comp (W.measurable.comp E.measurable))]
  have he : W.symm ∘ Homeomorph.mulLeft (W t) ∘ W ∘ E = id := by
    funext u
    change W.symm (W t * W (E u)) = u
    rw [c.remainingRebase_word hP hf,mul_inv_cancel_left,W.symm_apply_apply]
  rw [he,Measure.map_id]

theorem anchorNormalize_of_basedRemainingGroupMeasure (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries = allPositiveRoots n)
    (ν : Measure c.Time) [IsLocallyFiniteMeasure ν] (t : c.Time) (ht : t ∈ ν.support)
    (J : Set c.Time) :
    anchorNormalize
      (((c.remainingGroupLeafMeasure hP hf (c.basedRemainingMeasure hP hf ν t)).map
        (Homeomorph.mulLeft (c.remainingWordHomeomorph hP hf t))).map
        (c.remainingWordHomeomorph hP hf).symm) J = anchorNormalize ν J := by
  rw [c.uncenter_basedRemainingGroupMeasure]
  exact anchorNormalize_smul ν J _
    (ENNReal.inv_ne_zero.mpr (c.centeredRemainingMeasure_unit_lt_top hP hf ν t).ne)
    (ENNReal.inv_ne_top.mpr (c.centeredRemainingMeasure_unit_pos hP hf ν t ht).ne')

theorem uncenter_basedRemainingGroupMeasure_mass (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries = allPositiveRoots n)
    (ν : Measure c.Time) [IsLocallyFiniteMeasure ν] (t : c.Time) (ht : t ∈ ν.support)
    (J : Set c.Time) (hJ : ν J = 1) :
    let η := ((c.remainingGroupLeafMeasure hP hf (c.basedRemainingMeasure hP hf ν t)).map
      (Homeomorph.mulLeft (c.remainingWordHomeomorph hP hf t))).map
      (c.remainingWordHomeomorph hP hf).symm
    η J ≠ 0 ∧ η J ≠ ∞ := by
  dsimp only
  rw [c.uncenter_basedRemainingGroupMeasure,Measure.smul_apply,smul_eq_mul,hJ,mul_one]
  exact ⟨ENNReal.inv_ne_zero.mpr (c.centeredRemainingMeasure_unit_lt_top hP hf ν t).ne,
    ENNReal.inv_ne_top.mpr (c.centeredRemainingMeasure_unit_pos hP hf ν t ht).ne'⟩

end EliminationChain
namespace RootPrefixBox
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    {Pfx : RootPrefixCoordinates n P T} {c : EliminationChain P D}
    {hP : InitialRootPattern P} {hf : c.finalEntries = allPositiveRoots n} {g : G n}

theorem conditional_of_based_group_measure
    (A : RootPrefixBox Pfx c hP hf g) (R : ℝ) (hAR : A.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) :
    ∀ᵐ z ∂A.coordinateMeasure μ,
      ∀ η : Measure (positiveRootGeneratedGroup (allPositiveRoots n \ P)),
        c.remainingGroupLeafMeasure hP hf (A.basedLeaf R μ z) = η →
        A.conditionalKernel μ z.1 =
          (anchorNormalize ((η.map (Homeomorph.mulLeft
            (c.remainingWordHomeomorph hP hf z.2))).map
              (c.remainingWordHomeomorph hP hf).symm) A.time).restrict A.time := by
  have hs := ae_of_ae_map measurable_fst.aemeasurable (A.ae_leafMeasure_spec R hAR μ hfree)
  filter_upwards [hs,A.ae_mem_leafMeasure_support R hAR μ hfree] with z hz ht
  intro η hη
  let : IsLocallyFiniteMeasure (A.leafMeasure R μ z.1) := hz.1
  rw [←hη]
  have he := c.anchorNormalize_of_basedRemainingGroupMeasure hP hf
    (A.leafMeasure R μ z.1) z.2 ht A.time
  change A.conditionalKernel μ z.1 = _
  rw [basedLeaf,he]
  simpa only [anchorNormalize,hz.2.1,inv_one,one_smul] using hz.2.2.1.symm

theorem based_group_measure_uncenter_mass
    (A : RootPrefixBox Pfx c hP hf g) (R : ℝ) (hAR : A.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1) :
    ∀ᵐ z ∂A.coordinateMeasure μ,
      ∀ η : Measure (positiveRootGeneratedGroup (allPositiveRoots n \ P)),
        c.remainingGroupLeafMeasure hP hf (A.basedLeaf R μ z) = η →
        let ν := (η.map (Homeomorph.mulLeft (c.remainingWordHomeomorph hP hf z.2))).map
          (c.remainingWordHomeomorph hP hf).symm
        ν A.time ≠ 0 ∧ ν A.time ≠ ∞ := by
  have hs := ae_of_ae_map measurable_fst.aemeasurable (A.ae_leafMeasure_spec R hAR μ hfree)
  filter_upwards [hs,A.ae_mem_leafMeasure_support R hAR μ hfree] with z hz ht
  intro η hη
  let : IsLocallyFiniteMeasure (A.leafMeasure R μ z.1) := hz.1
  rw [←hη]
  exact c.uncenter_basedRemainingGroupMeasure_mass hP hf
    (A.leafMeasure R μ z.1) z.2 ht A.time hz.2.1

end RootPrefixBox
end DukePrimeDegree

end

end OAI
