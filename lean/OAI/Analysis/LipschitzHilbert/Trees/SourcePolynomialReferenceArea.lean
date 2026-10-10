import OAI.Analysis.LipschitzHilbert.Trees.SourcePolynomialGoodPathArea
import OAI.Analysis.LipschitzHilbert.Trees.SourceSelectedReferenceData

namespace OAI

/-! The reference-event construction with a polynomially growing top-weight
scale. The same finite union controls the original selected prefixes and
retains its weighted integral, not only the area of the removed set. -/
noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal BigOperators
namespace LipschitzHilbert

theorem eventually_polynomial_selected_reference_prefix_area
    (D eventPower weightPower : ℝ) (hD : 2 < D) :
    ∀ᶠ L : ℝ in atTop, ∀ (K : ℝ), 1 ≤ K → K ≤ L^weightPower →
    ∀ (ι σ : Type*) (tops : Finset ι) (T : ι → SlopeBox)
      (events : ι → Finset σ) (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : ι → σ → PhysicalReferenceData N κ Label Item)
      (Q : ∀ t i, Finset (P t i).family.PacketIndex)
      (A e s r : ℝ) (base : Set (ℝ×ℝ)),
      MeasurableSet base → (∀ t ∈ tops, ((events t).card:ℝ) ≤ L^eventPower) →
      (∀ t ∈ tops, ∀ᵐ y : ℝ ∂volume, ∀ k : ℤ, ∀ i ∈ events t,
        (volume.restrict (sourceLineTile (T t).length k))
          {x | (x,y+(T t).slope*x) ∈ ((P t i).restrictPackets (Q t i)).bad L A e s r} ≤
        ENNReal.ofReal (Real.exp (-12*L))*
          (volume.restrict (sourceLineTile (T t).length k)) univ) →
      let bad := fun t => ⋃ i ∈ events t, ((P t i).restrictPackets (Q t i)).bad L A e s r
      let weight := fun t => (T t).weight K D
      let good := sourceGoodPathSet base tops weight bad L
      Integrable (sourceBadPathMass tops weight bad) (volume.prod volume) ∧
      (∫ z, sourceBadPathMass tops weight bad z ∂volume.prod volume) ≤
        (∑ t ∈ tops, (T t).length*(T t).width)*Real.exp (-10*L) ∧
      MeasurableSet good ∧ good ⊆ base ∧
      (volume.prod volume) (base \ good) ≤ ENNReal.ofReal
        ((∑ t ∈ tops, (T t).length*(T t).width)*Real.exp (-9*L)) ∧
      ∀ t, ∀ z ∉ bad t, ∀ i ∈ events t,
        z ∉ ((P t i).restrictPackets (Q t i)).bad L A e s r ∧
        ∀ (stop : Fin N → ℕ), Antitone stop → ∀ H : ℕ,
          finiteCubicVariation (fun k => (P t i).family.selectedPhysicalPrefix
            (P t i).alternate (P t i).alternate_bound (P t i).slope (P t i).selector
            (P t i).direction (P t i).test (P t i).packetTop L A (Q t i) stop z (min k H))
            (2*H) ≤ (L^r)^3 := by
  filter_upwards [eventually_source_polynomial_good_path_area D eventPower weightPower hD]
    with L harea
  intro K hK hKL ι σ tops T events N κ Label Item _ _ P Q A e s r base hbase hcard htail
    bad weight good
  have hbad (t : ι) : MeasurableSet (bad t) :=
    MeasurableSet.biUnion (Finset.countable_toSet (events t))
      (fun i _ => ((P t i).restrictPackets (Q t i)).bad_measurable L A e s r)
  have ha := harea K hK hKL ι σ tops T events
    (fun t i => ((P t i).restrictPackets (Q t i)).bad L A e s r)
    bad base hbase (fun t _ => hbad t) (fun _ _ => Subset.rfl) hcard htail
  refine ⟨ha.1,ha.2.1,ha.2.2.1,ha.2.2.2.1,ha.2.2.2.2,?_⟩
  intro t z hz i hi
  have hzi : z ∉ ((P t i).restrictPackets (Q t i)).bad L A e s r := by
    intro hmem
    exact hz (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,hmem⟩⟩)
  exact ⟨hzi,fun stop hstop H =>
    (P t i).selectedPrefix_good_bound (Q t i) L A e s r stop hstop z hzi H⟩

end LipschitzHilbert

end

end OAI
