import OAI.Analysis.LipschitzHilbert.Trees.SourcePhysicalGoodPath

namespace OAI

/-! Selected residual packet families have event-dependent spatial item
fibers. The weighted good-path argument only uses their measurable
physical bad events, so the exact same area estimate applies without
identifying these different finite item types. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal BigOperators
namespace LipschitzHilbert

theorem eventually_selected_physical_reference_good_path_area (K D a : ℝ)
    (hK : 1 ≤ K) (hD : 2 < D) :
    ∀ᶠ L : ℝ in atTop, ∀ (ι σ : Type*) (tops : Finset ι) (T : ι → SlopeBox)
      (events : ι → Finset σ) (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ι → σ → ∀ j, Label j → Type)
      [Fintype κ] [∀ t i j l, Fintype (Item t i j l)]
      (P : ∀ t i, PhysicalReferenceData N κ Label (Item t i))
      (A e s r : ℝ) (base : Set (ℝ×ℝ)),
      MeasurableSet base → (∀ t ∈ tops, ((events t).card:ℝ) ≤ L^a) →
      (∀ t ∈ tops, ∀ᵐ y : ℝ ∂volume, ∀ k : ℤ, ∀ i ∈ events t,
        (volume.restrict (sourceLineTile (T t).length k))
          {x | (x,y+(T t).slope*x) ∈ (P t i).bad L A e s r} ≤
        ENNReal.ofReal (Real.exp (-12*L))*
          (volume.restrict (sourceLineTile (T t).length k)) univ) →
      let bad := fun t => ⋃ i ∈ events t, (P t i).bad L A e s r
      let good := sourceGoodPathSet base tops (fun t => (T t).weight K D) bad L
      MeasurableSet good ∧ good ⊆ base ∧
      (volume.prod volume) (base \ good) ≤ ENNReal.ofReal
        ((∑ t ∈ tops, (T t).length*(T t).width)*Real.exp (-9*L)) ∧
      ∀ z ∈ good, ∀ t, z ∉ bad t → ∀ i ∈ events t,
        (P t i).family.physicalAngularError (P t i).slope (P t i).angle
          (P t i).selector (P t i).direction (P t i).test z < L^e ∧
        (P t i).family.physicalMainSquareOnPlane (P t i).slope (P t i).angle
          (P t i).selector (P t i).direction (P t i).test z < L^s ∧
        (P t i).family.physicalMaskedVariation (P t i).alternate (P t i).alternate_bound
          (P t i).slope (P t i).selector (P t i).direction (P t i).test (P t i).packetTop
          L A (z.2-(P t i).slope*z.1) z.1 < L^r := by
  filter_upwards [eventually_source_good_path_area K D a hK hD] with L harea
  intro ι σ tops T events N κ Label Item _ _ P A e s r base hbase hcard htail
  let bad := fun t => ⋃ i ∈ events t, (P t i).bad L A e s r
  have hbad (t : ι) : MeasurableSet (bad t) :=
    MeasurableSet.biUnion (Finset.countable_toSet (events t))
      (fun i _ => (P t i).bad_measurable L A e s r)
  have ha := harea ι σ tops T events (fun t i => (P t i).bad L A e s r) bad base
    hbase (fun t _ => hbad t) (fun _ _ => Subset.rfl) hcard htail
  refine ⟨ha.1,ha.2.1,ha.2.2,?_⟩
  intro z _hz t ht i hi
  apply (P t i).good_bounds L A e s r z
  intro hmem
  exact ht (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,hmem⟩⟩)

end LipschitzHilbert

end

end OAI
