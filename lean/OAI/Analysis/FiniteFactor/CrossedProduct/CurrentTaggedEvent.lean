import OAI.Analysis.FiniteFactor.Coupling.TaggedAdmissibility
import OAI.Analysis.FiniteFactor.FiniteSingleTag
import OAI.Analysis.FiniteFactor.TagExponentialLower
import OAI.Analysis.FiniteFactor.CrossedProduct.ProjectionEvent

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter CouplingParameters
open scoped ENNReal
noncomputable section

def sourceCurrentTaggedEvent (j : ℕ) : Set SourceBiasedSample :=
  sourceTaggedEvent j ∩ {ω | ∀ i : Fin (sourceBlockSize j),
    ω ⟨j,i⟩ ∈ (stagedCouplingParameters j j).currentBoundary}

theorem sourceCurrentTaggedEvent_measurable (j : ℕ) : MeasurableSet (sourceCurrentTaggedEvent j) := by
  apply (sourceTaggedEvent_measurable j).inter
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => ((stagedCouplingParameters j j).currentBoundary_measurable).preimage
    (measurable_pi_apply (⟨j,i⟩ : SourceCoordinate))

/-- The actual current tagged block has mass at least exp(-82). This is a
finite independent exactly-one-tag calculation under sourceBiasedLaw j. -/
theorem sourceCurrentTaggedEvent_mass (j : ℕ) :
    ENNReal.ofReal (Real.exp (-82)) ≤ (sourceBiasedLaw j) (sourceCurrentTaggedEvent j) := by
  let F := sourceBlockCoordinates j
  let p := stagedCouplingParameters j j
  let μ := fun i : SourceCoordinate => (stagedCouplingParameters j i.1).labelledCoupling
  let T := fun _ : SourceCoordinate => p.currentTag
  let A := fun _ : SourceCoordinate => p.currentNonTag
  have hTm (i : SourceCoordinate) (hi : i ∈ F) : μ i (T i) = ENNReal.ofReal (1/(sourceBlockSize j : ℝ)) := by
    have his := mem_sourceBlockCoordinates hi
    change (stagedCouplingParameters j i.1).labelledCoupling p.currentTag = _
    rw [his,currentTag_mass]
    simp [stagedCouplingParameters,tagMass]
  have hAm (i : SourceCoordinate) (hi : i ∈ F) :
      ENNReal.ofReal (1-41/(sourceBlockSize j : ℝ)) ≤ μ i (A i) := by
    have his := mem_sourceBlockCoordinates hi
    change _ ≤ (stagedCouplingParameters j i.1).labelledCoupling p.currentNonTag
    rw [his]
    exact p.currentNonTag_mass_lower
  have hh := finite_single_tag_lower μ F T A
    (fun _ _ => p.currentTag_measurable) (fun _ _ => p.currentNonTag_measurable)
    (fun _ _ => p.currentTag_disjoint) (ENNReal.ofReal (1/(sourceBlockSize j : ℝ)))
    (ENNReal.ofReal (1-41/(sourceBlockSize j : ℝ))) (fun i hi => (hTm i hi).symm.le) hAm
  have hsub : (⋃ i ∈ F, singleTagCylinder F T A i) ⊆ sourceCurrentTaggedEvent j := by
    intro ω hω
    simp only [Set.mem_iUnion] at hω
    obtain ⟨i,hi,hc⟩ := hω
    have his := mem_sourceBlockCoordinates hi
    rcases i with ⟨s,i⟩
    change s = j at his
    subst s
    have ht : ω ⟨j,i⟩ ∈ p.currentTag := by simpa [T] using hc ⟨j,i⟩ hi
    refine ⟨⟨i,ht.1⟩,?_⟩
    intro u
    have hu : (⟨j,u⟩ : SourceCoordinate) ∈ F := by
      exact Finset.mem_map.mpr ⟨u,Finset.mem_univ _,rfl⟩
    have hcu := hc ⟨j,u⟩ hu
    by_cases h : (⟨j,u⟩ : SourceCoordinate) = ⟨j,i⟩
    · have ht : ω ⟨j,u⟩ ∈ p.currentTag := by simpa only [ite_eq_left h] using hcu
      exact ht.2
    · have ha : ω ⟨j,u⟩ ∈ p.currentNonTag := by simpa only [ite_eq_right h] using hcu
      exact ha.2
  have hmt : (sourceBlockSize j : ℝ≥0∞)*ENNReal.ofReal (1/(sourceBlockSize j : ℝ)) = 1 := by
    calc
      _ = ENNReal.ofReal ((sourceBlockSize j : ℝ)*(1/(sourceBlockSize j : ℝ))) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        simp
      _ = 1 := by rw [mul_one_div_cancel (sourceBlockSize_pos j).ne']; simp
  have hbase : 0 ≤ 1-41/(sourceBlockSize j : ℝ) := by
    apply sub_nonneg.mpr
    apply (div_le_one (sourceBlockSize_pos j)).mpr
    have hm : (100 : ℝ) ≤ sourceBlockSize j := by exact_mod_cast (sourceStage j).m_ge_100
    linarith
  change (F.card : ℝ≥0∞)*ENNReal.ofReal (1/(sourceBlockSize j : ℝ))*
    (ENNReal.ofReal (1-41/(sourceBlockSize j : ℝ)))^(F.card-1) ≤ _ at hh
  rw [show F.card = sourceBlockSize j from sourceBlockCoordinates_card j,hmt,one_mul,
    ← ENNReal.ofReal_pow hbase] at hh
  have hn := ENNReal.ofReal_le_ofReal (tag_probability_exponential_lower (sourceBlockSize j)
    (sourceStage j).m_ge_100)
  exact hn.trans (hh.trans (measure_mono hsub))

end
end FiniteFactor

end OAI
