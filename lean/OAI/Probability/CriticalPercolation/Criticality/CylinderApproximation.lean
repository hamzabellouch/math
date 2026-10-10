import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.BlockIndependence

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical symmDiff ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

def finiteCoordinateEvents : Set (Set (Set E)) :=
  {A | ∃ S : Finset E, MeasurableSet[blockSigma (S : Set E)] A}

lemma finiteCoordinateEvents_ring : IsSetRing (finiteCoordinateEvents (E := E)) where
  empty_mem := ⟨∅,@MeasurableSet.empty (Set E) (blockSigma ((∅ : Finset E) : Set E))⟩
  union_mem := by
    rintro A B ⟨S,hS⟩ ⟨T,hT⟩
    refine ⟨S ∪ T,?_⟩
    exact @MeasurableSet.union (Set E) (blockSigma ((S ∪ T : Finset E) : Set E)) _ _
      (blockSigma_mono (by simp) _ hS) (blockSigma_mono (by simp) _ hT)
  sdiff_mem := by
    rintro A B ⟨S,hS⟩ ⟨T,hT⟩
    refine ⟨S ∪ T,?_⟩
    exact @MeasurableSet.diff (Set E) (blockSigma ((S ∪ T : Finset E) : Set E)) _ _
      (blockSigma_mono (by simp) _ hS) (blockSigma_mono (by simp) _ hT)

lemma generateFrom_finiteCoordinateEvents :
    MeasurableSpace.generateFrom (finiteCoordinateEvents (E := E)) =
      (Set.instMeasurableSpace : MeasurableSpace (Set E)) := by
  apply le_antisymm
  · exact MeasurableSpace.generateFrom_le fun A ⟨S,hS⟩ => blockSigma_le _ _ hS
  · change (⨆ e : E, coordinateSigma e) ≤ _
    refine iSup_le fun e => ?_
    intro A hA
    apply MeasurableSpace.measurableSet_generateFrom
    refine ⟨{e},?_⟩
    exact (le_iSup_of_le e (le_iSup_of_le (Finset.mem_singleton_self e) le_rfl) :
      coordinateSigma e ≤ blockSigma (({e} : Finset E) : Set E)) _ hA

lemma exists_finiteCoordinate_approx (q : E → unitInterval)
    {A : Set (Set E)} (hA : MeasurableSet A) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (S : Finset E) (B : Set (Set E)), MeasurableSet[blockSigma (S : Set E)] B ∧
      law q (B ∆ A) < ε := by
  obtain ⟨B,⟨S,hB⟩,h⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    finiteCoordinateEvents_ring (μ := law q)
    (show ∃ D : Set (Set (Set E)), D.Countable ∧ D ⊆ finiteCoordinateEvents ∧
        law q (⋃₀ D)ᶜ = 0 from
      ⟨{Set.univ},by simp,by rintro A rfl; exact ⟨∅,@MeasurableSet.univ (Set E) (blockSigma ((∅ : Finset E) : Set E))⟩,by simp⟩)
    generateFrom_finiteCoordinateEvents.symm hA hε
  exact ⟨S,B,hB,h⟩

lemma measurable_image_equiv_blocks (e : E ≃ E) (S : Set E) :
    @Measurable (Set E) (Set E) (blockSigma (e.symm '' S)) (blockSigma S)
      (fun ω => e '' ω) := by
  apply measurable_iff_comap_le.mpr
  simp only [blockSigma, MeasurableSpace.comap_iSup]
  refine iSup₂_le fun x hx => ?_
  have hm : @Measurable (Set E) Prop (coordinateSigma (e.symm x)) inferInstance
      (fun ω => x ∈ e '' ω) := by
    have hh : (fun ω : Set E => x ∈ e '' ω) = (fun ω => e.symm x ∈ ω) := by
      funext ω
      exact propext (by simp)
    rw [hh]
    exact measurable_iff_comap_le.mpr le_rfl
  have hc := hm.comap_le
  rw [coordinateSigma,MeasurableSpace.comap_comp]
  change MeasurableSpace.comap (fun ω : Set E => x ∈ e '' ω) inferInstance ≤ _
  exact hc.trans (le_iSup_of_le (e.symm x) (le_iSup_of_le ⟨x,hx,rfl⟩ le_rfl))

end CriticalPercolation.BernoulliProduct
end
end

end OAI
