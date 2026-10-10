import OAI.Analysis.FiniteFactor.CrossedProduct.CouplingBudget
import OAI.Analysis.FiniteFactor.BiasedPairs.RealIdentity
import OAI.Analysis.FiniteFactor.CrossedProduct.Attenuation

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter CouplingParameters
open scoped ENNReal
noncomputable section

/-- A deterministic source phase assignment, chosen from the fixed angles. -/
structure SourcePhaseAssignment (θ : SourceCoordinate → ℝ) (j : ℕ) (k : ℤ) where
  block : ℕ
  width : Fin 2
  indices : Finset SourceCoordinate
  later : j ≤ block
  first_later : width = 0 → j < block
  subset : indices ⊆ sourceBlockCoordinates block
  card_lower : (sourceBlockSize block : ℝ)/20 ≤ (indices.card : ℝ)
  threshold : ∀ i ∈ indices,
    1-Int.fract ((k : ℝ)*θ i) ∈ Set.Icc (sourceWidth block width) (1-sourceWidth block width)

def sourceChosenAssignment (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (j : ℕ) (hphase : SourceSecondPhasesFrom θ j) (k : ℤ)
    (hk : sourcePhaseLower j ≤ |(k : ℝ)|) : SourcePhaseAssignment θ j k := by
  have hex : Nonempty (SourcePhaseAssignment θ j k) := by
    obtain ⟨s,w,I,hjs,hw,hI,hcard,hu⟩ := exists_source_qualifying_assignment θ hθ j hphase k hk
    exact ⟨⟨s,w,I,hjs,hw,hI,hcard,hu⟩⟩
  exact Classical.choice hex

namespace SourcePhaseAssignment
variable {θ : SourceCoordinate → ℝ} {j : ℕ} {k : ℤ}

def badEvent (a : SourcePhaseAssignment θ j k) (b : Bool) : Set SourceBiasedSample :=
  (fun ω => (sourceBiasedEndpoint (fun _ => b) ω,
    sourceBiasedEndpoint (fun _ => !b) ω)) ⁻¹'
    badHalfEvent (fun _ => b) (fun i => 1-Int.fract ((k : ℝ)*θ i)) a.indices a.indices.card

theorem badEvent_measurable (a : SourcePhaseAssignment θ j k) (b : Bool) :
    MeasurableSet (a.badEvent b) :=
  (badHalfEvent_measurable ..).preimage
    ((sourceBiasedEndpoint_measurable _).prodMk (sourceBiasedEndpoint_measurable _))

/-- Both conditional estimates use the actual full-vector posterior and the
constructed numerical budget. The assignment has no sample argument. -/
theorem badEvent_condExp (a : SourcePhaseAssignment θ j k) (b : Bool) :
    ∀ᵐ ω ∂sourceBiasedLaw j,
      (sourceBiasedLaw j)[(a.badEvent b).indicator (fun _ => (1 : ℝ)) |
        (inferInstance : MeasurableSpace (SourceCoordinate → ℝ)).comap
          (sourceBiasedEndpoint (fun _ => b))] ω ≤ Real.exp (-(sourceStage j).L/400) := by
  have hi (i : SourceCoordinate) (h : i ∈ a.indices) : i.1 = a.block :=
    mem_sourceBlockCoordinates (a.subset h)
  have hh := badHalf_condExp_bound (fun i : SourceCoordinate => stagedCouplingParameters j i.1)
    (fun _ => b) (fun _ => a.width) (fun i => 1-Int.fract ((k : ℝ)*θ i)) a.indices
    a.indices.card (sourceBlockSize a.block) ((stagedCouplingParameters j a.block).rho a.width)
    (sourceStage j).L
    (fun i h => by simpa only [stagedCouplingParameters,hi i h,Set.mem_Icc] using a.threshold i h)
    (fun i h => by rw [hi i h])
    ((stagedCouplingParameters j a.block).rho_nonneg a.width)
    a.card_lower (staged_rho_budget j a.block a.later a.width a.first_later)
  have he : (a.badEvent b).indicator (fun _ => (1 : ℝ)) =
      fun ω => (badHalfEvent (fun _ => b) (fun i => 1-Int.fract ((k : ℝ)*θ i))
        a.indices a.indices.card).indicator (fun _ => (1 : ℝ))
        (sourceBiasedEndpoint (fun _ => b) ω,sourceBiasedEndpoint (fun _ => !b) ω) := by
    funext ω
    by_cases h : (sourceBiasedEndpoint (fun _ => b) ω,sourceBiasedEndpoint (fun _ => !b) ω) ∈
        badHalfEvent (fun _ => b) (fun i => 1-Int.fract ((k : ℝ)*θ i)) a.indices a.indices.card
    · have hp : ω ∈ a.badEvent b := h
      rw [Set.indicator_of_mem hp,Set.indicator_of_mem h]
    · have hp : ω ∉ a.badEvent b := h
      rw [Set.indicator_of_notMem hp,Set.indicator_of_notMem h]
  rw [he]
  exact hh

/-- At an assigned index, failure of both oriented bad events forces an
actual floor crossing, hence the original uncapped ratio is attenuated. -/
theorem attenuation_or_bad (hθ : SourceAngles θ) (a : SourcePhaseAssignment θ j k) :
    ∀ᵐ ω ∂sourceBiasedLaw j,
      sourceCocycle θ sourceLogWeight k (sourceBiasedEndpoint (fun _ => true) ω) /
        sourceCocycle θ sourceLogWeight k (sourceBiasedEndpoint (fun _ => false) ω) ≤
          Real.exp (-(sourceStage j).L) ∨ ω ∈ a.badEvent false ∨ ω ∈ a.badEvent true := by
  have hcube := vectorEndpoint_unitCube (fun i : SourceCoordinate => stagedCouplingParameters j i.1)
  have hx := ae_of_ae_map (sourceBiasedEndpoint_measurable (fun _ => false)).aemeasurable
    (hcube (fun _ => false))
  have hy := ae_of_ae_map (sourceBiasedEndpoint_measurable (fun _ => true)).aemeasurable
    (hcube (fun _ => true))
  filter_upwards [hx,hy,sourceBiasedLaw_ordered j,
    sourceBiasedEndpoint_ae j (fun _ => false) (ae_finiteFloorSupport θ hθ.summable),
    sourceBiasedEndpoint_ae j (fun _ => true) (ae_finiteFloorSupport θ hθ.summable)]
    with ω hxc hyc hxy hfx hfy
  let x := sourceBiasedEndpoint (fun _ => false) ω
  let y := sourceBiasedEndpoint (fun _ => true) ω
  let u := fun i => 1-Int.fract ((k : ℝ)*θ i)
  by_cases hc : ∃ i ∈ a.indices, x i < u i ∧ u i ≤ y i
  · obtain ⟨i,hi,hcross⟩ := hc
    apply Or.inl
    have hatt := sourceCocycle_crossing_attenuation θ sourceLogWeight sourceLogWeight_nonneg
      hfx hfy hxy k i (hxc i) (hyc i) hcross
    apply hatt.trans
    apply Real.exp_le_exp.mpr
    have his := mem_sourceBlockCoordinates (a.subset hi)
    change -(sourceStage i.1).C ≤ -(sourceStage j).L
    rw [his]
    exact neg_le_neg (staged_drop_budget j a.block a.later)
  · have hn : ∀ i ∈ a.indices, ¬(x i < u i ∧ u i ≤ y i) := by
      intro i hi hc'; exact hc ⟨i,hi,hc'⟩
    by_cases hcount : (a.indices.card : ℝ)/2 ≤
        ((eligibleIndices (fun _ => false) x u a.indices).card : ℝ)
    · apply Or.inr ∘ Or.inl
      refine ⟨hcount,?_⟩
      intro i hh
      exact hn i i.2 hh
    · apply Or.inr ∘ Or.inr
      exact second_bad_half_in_reverse x y u a.indices (fun i _ => hxy i) hn (lt_of_not_ge hcount)

end SourcePhaseAssignment
end
end FiniteFactor

end OAI
