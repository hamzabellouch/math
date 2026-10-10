import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledGoodEvents
import OAI.Analysis.LipschitzHilbert.Trees.SourceGoodPathArea

namespace OAI

/-! The weighted good-path construction for actual physical reference
packets. A reference bundle only packages the original formulas; it has
no probabilistic or path estimate as a field. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal
namespace LipschitzHilbert

structure PhysicalReferenceData (N : ℕ) (κ : Type) (Label : Fin N → Type)
    (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)] where
  family : SourceLabeledLattice N κ Label Item
  alternate : ∀ j (l : family.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ
  alternate_bound : ∀ j l u k,
    planarProfileConstant (alternate j l u k) (2*family.order) ≤ family.profileBound
  slope : ℝ
  angle : ℝ
  selector : ∀ j, family.labels j → κ → ℝ → ℂ
  direction : ℝ×ℝ → ℝ
  test : ℝ×ℝ → EuclideanSpace ℂ κ
  packetTop : ∀ j (l : family.labels j), Item j l → SlopeBox

namespace PhysicalReferenceData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PhysicalReferenceData N κ Label Item)

def bad (L A e s r : ℝ) : Set (ℝ×ℝ) :=
  P.family.physicalReferenceBad P.alternate P.alternate_bound P.slope P.angle P.selector
    P.direction P.test P.packetTop L A e s r

theorem bad_measurable (L A e s r : ℝ) : MeasurableSet (P.bad L A e s r) :=
  P.family.physicalReferenceBad_measurable P.alternate P.alternate_bound P.slope P.angle
    P.selector P.direction P.test P.packetTop L A e s r

theorem good_bounds (L A e s r : ℝ) (z : ℝ×ℝ) (hz : z ∉ P.bad L A e s r) :
    P.family.physicalAngularError P.slope P.angle P.selector P.direction P.test z < L^e ∧
    P.family.physicalMainSquareOnPlane P.slope P.angle P.selector P.direction P.test z < L^s ∧
    P.family.physicalMaskedVariation P.alternate P.alternate_bound P.slope P.selector
      P.direction P.test P.packetTop L A (z.2-P.slope*z.1) z.1 < L^r :=
  P.family.physicalReferenceBad_compl_bounds P.alternate P.alternate_bound P.slope P.angle
    P.selector P.direction P.test P.packetTop L A e s r z hz

end PhysicalReferenceData

/-- All shifts of each actual physical reference family enter one
weighted good set. Its removed area depends on total top area, while a
good path satisfies the three original quantitative reference bounds. -/
theorem eventually_physical_reference_good_path_area (K D a : ℝ)
    (hK : 1 ≤ K) (hD : 2 < D) :
    ∀ᶠ L : ℝ in atTop, ∀ (ι σ : Type*) (tops : Finset ι) (T : ι → SlopeBox)
      (events : ι → Finset σ) (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : ι → σ → PhysicalReferenceData N κ Label Item)
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
    MeasurableSet.biUnion (Finset.countable_toSet (events t)) (fun i _ => (P t i).bad_measurable L A e s r)
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
