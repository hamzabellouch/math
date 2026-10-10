import OAI.Analysis.LipschitzHilbert.Trees.SourceSelectedGoodPathArea
import OAI.Analysis.LipschitzHilbert.Trees.SourceSelectedGoodEvent

namespace OAI

/-! A selected reference family retains the original physical packets,
coefficients and top masks. Its spatial item type depends on the selected
finite subset, while its good event directly controls the original
selected stopping prefixes and all unary runs. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal BigOperators
namespace LipschitzHilbert
namespace PhysicalReferenceData

variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PhysicalReferenceData N κ Label Item)

def restrictPackets (Q : Finset P.family.PacketIndex) :
    PhysicalReferenceData N κ Label (P.family.RestrictedPacketItem Q) where
  family := P.family.restrictPackets Q
  alternate := P.family.restrictedAlternate P.alternate Q
  alternate_bound := P.family.restrictedAlternate_bound P.alternate P.alternate_bound Q
  slope := P.slope
  angle := P.angle
  selector := P.selector
  direction := P.direction
  test := P.test
  packetTop := fun j l u => P.packetTop j l u.val

theorem restrictPackets_bad (Q : Finset P.family.PacketIndex) (L A e s r : ℝ) :
    (P.restrictPackets Q).bad L A e s r =
      (P.family.restrictPackets Q).physicalReferenceBad
        (P.family.restrictedAlternate P.alternate Q)
        (P.family.restrictedAlternate_bound P.alternate P.alternate_bound Q)
        P.slope P.angle P.selector P.direction P.test
        (fun j l u => P.packetTop j l u.val) L A e s r := rfl

theorem selectedPrefix_good_bound (Q : Finset P.family.PacketIndex) (L A e s r : ℝ)
    (stop : Fin N → ℕ) (hstop : Antitone stop) (z : ℝ×ℝ)
    (hz : z ∉ (P.restrictPackets Q).bad L A e s r) (H : ℕ) :
    finiteCubicVariation (fun k => P.family.selectedPhysicalPrefix P.alternate P.alternate_bound
      P.slope P.selector P.direction P.test P.packetTop L A Q stop z (min k H)) (2*H) ≤
        (L^r)^3 :=
  P.family.selectedPhysicalPrefix_good_event_bound P.alternate P.alternate_bound
    P.slope P.angle P.selector P.direction P.test P.packetTop L A e s r Q stop hstop z hz H

theorem selectedPrefix_unary_good_bound (Q : Finset P.family.PacketIndex) (L A e s r : ℝ)
    (stop : Fin N → ℕ) (hstop : Antitone stop) (z : ℝ×ℝ)
    (hz : z ∉ (P.restrictPackets Q).bad L A e s r)
    {unary : ℕ → Prop} {n : ℕ → ℝ} {start finish : ℕ}
    (R : UnaryRunPartition unary start finish)
    (S : ∀ run : R.runs, UnarySegmentPartition n run.val.1 run.val.2)
    (level : ℕ → ℕ) (hlevel : StrictMono level) (H : ℕ) (hend : level finish ≤ H) :
    (∑ i : UnaryRunSegment R S,
      intervalOscillation (P.family.selectedPhysicalPrefix P.alternate P.alternate_bound
        P.slope P.selector P.direction P.test P.packetTop L A Q stop z)
        H (level i.2.val.1) (level i.2.val.2)^3) ≤ (L^r)^3 :=
  P.family.selectedPhysicalPrefix_unary_good_event_bound P.alternate P.alternate_bound
    P.slope P.angle P.selector P.direction P.test P.packetTop L A e s r Q stop hstop z hz
    R S level hlevel H hend

end PhysicalReferenceData

theorem eventually_selected_reference_prefix_area (K D a : ℝ) (hK : 1 ≤ K) (hD : 2 < D) :
    ∀ᶠ L : ℝ in atTop, ∀ (ι σ : Type*) (tops : Finset ι) (T : ι → SlopeBox)
      (events : ι → Finset σ) (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : ι → σ → PhysicalReferenceData N κ Label Item)
      (Q : ∀ t i, Finset (P t i).family.PacketIndex)
      (A e s r : ℝ) (base : Set (ℝ×ℝ)),
      MeasurableSet base → (∀ t ∈ tops, ((events t).card:ℝ) ≤ L^a) →
      (∀ t ∈ tops, ∀ᵐ y : ℝ ∂volume, ∀ k : ℤ, ∀ i ∈ events t,
        (volume.restrict (sourceLineTile (T t).length k))
          {x | (x,y+(T t).slope*x) ∈ ((P t i).restrictPackets (Q t i)).bad L A e s r} ≤
        ENNReal.ofReal (Real.exp (-12*L))*
          (volume.restrict (sourceLineTile (T t).length k)) univ) →
      let bad := fun t => ⋃ i ∈ events t, ((P t i).restrictPackets (Q t i)).bad L A e s r
      let good := sourceGoodPathSet base tops (fun t => (T t).weight K D) bad L
      MeasurableSet good ∧ good ⊆ base ∧
      (volume.prod volume) (base \ good) ≤ ENNReal.ofReal
        ((∑ t ∈ tops, (T t).length*(T t).width)*Real.exp (-9*L)) ∧
      ∀ z ∈ good, ∀ t, z ∉ bad t → ∀ i ∈ events t,
        ∀ (stop : Fin N → ℕ), Antitone stop → ∀ H : ℕ,
          finiteCubicVariation (fun k => (P t i).family.selectedPhysicalPrefix
            (P t i).alternate (P t i).alternate_bound (P t i).slope (P t i).selector
            (P t i).direction (P t i).test (P t i).packetTop L A (Q t i) stop z (min k H))
            (2*H) ≤ (L^r)^3 := by
  filter_upwards [eventually_selected_physical_reference_good_path_area K D a hK hD]
    with L harea
  intro ι σ tops T events N κ Label Item _ _ P Q A e s r base hbase hcard htail
  let selected := fun t i => (P t i).restrictPackets (Q t i)
  have ha := harea ι σ tops T events N κ Label
    (fun t i => (P t i).family.RestrictedPacketItem (Q t i)) selected
    A e s r base hbase hcard htail
  refine ⟨ha.1,ha.2.1,ha.2.2.1,?_⟩
  intro z _hz t ht i hi stop hstop H
  apply (P t i).selectedPrefix_good_bound (Q t i) L A e s r stop hstop z _ H
  intro hmem
  exact ht (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,hmem⟩⟩)

end LipschitzHilbert

end

end OAI
