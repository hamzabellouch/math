import OAI.Analysis.LipschitzHilbert.Trees.SourceSharpDensityForest
import OAI.Analysis.LipschitzHilbert.Trees.SourceDensityRadius
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataDensity

namespace OAI

/-! The ordinary density selection, retaining its sharp witness radius
and original angular cells. Empty packet sets require no dummy keeper. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem densityTile_length (P : PacketLatticeData N κ Label Item) (oldSlope : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (q : P.PacketIndex) :
    P.topLength/DyadicLineGrid.scale (P.densityTile oldSlope cell q).level = P.length q.1 := by
  simp only [densityTile,DyadicLineGrid.scale,zpow_natCast,PacketLatticeData.length]

structure OrdinaryDensityForest (P : PacketLatticeData N κ Label Item)
    (packets : Finset P.PacketIndex) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (w tau eta : ℝ) (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) where
  keepers : Finset packets
  top : keepers → SlopeBox
  assigned : packets → keepers
  witness : keepers → Set (ℝ×ℝ)
  measurable : ∀ i, MeasurableSet (witness i)
  disjoint : Pairwise fun i j => Disjoint (witness i) (witness j)
  inside : ∀ i z, z ∈ witness i → z ∈ E ∧
    z ∈ densitySpatialBox (top i) (densityRadius eta) ∧
    |u z-(top i).slope| ≤ w/(top i).length
  mass : ∀ i, (eta/2)*(top i).area ≤ (volume.prod volume).real (witness i)
  width : ∀ i, (top i).width = P.width
  short : ∀ i, (top i).length ≤ tau
  area : (∑ i, (top i).area) ≤ 2*(volume.prod volume).real E/eta
  length_le : ∀ q : packets, P.length q.val.1 ≤ (top (assigned q)).length
  center : ∀ q : packets,
    (P.actualX q.val.1 q.val.2.1 q.val.2.2,P.actualZ q.val.1 q.val.2.1 q.val.2.2) ∈
      densitySpatialBox (top (assigned q)) (5*densityRadius eta)
  direction : ∀ q : packets, (top (assigned q)).slope ∈
    scaledAngularCell (w/P.topLength) grid q.val.1.val (cell q.val.1 q.val.2.1)

theorem exists_ordinary_density_forest (P : PacketLatticeData N κ Label Item)
    (packets : Finset P.PacketIndex) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (w tau eta : ℝ) (hw : 0<w) (hW : w≤P.width) (heta : 0<eta)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (hE : MeasurableSet E)
    (hEfin : (volume.prod volume) E≠∞) (hu : Measurable u)
    (hdensity : ∀ q∈packets, eta<P.ordinaryDensity 0 cell grid w tau E u q) :
    Nonempty (OrdinaryDensityForest P packets cell grid w tau eta E u) := by
  classical
  obtain ⟨test,keepers,assigned,hmeas,hdisj,harea,hmass,hinside,hassign⟩ :=
    exists_sharp_high_density_forest packets (P.densityTile 0 cell)
      P.topLength w P.width tau (densityRadius eta) eta grid P.topLength_pos hw hW
      (densityRadius_ge_one eta) heta E u hE hEfin hu (densityRadius_tail heta) hdensity
  refine ⟨{
    keepers := keepers
    top := fun i => (test i.val).top
    assigned := assigned
    witness := fun i => densityTest E u (test i.val).top
      (scaledAngularCell (w/P.topLength) grid (test i.val).level (test i.val).cell)
      (densityRadius eta)
    measurable := fun i => hmeas i.val i.property
    disjoint := ?_
    inside := fun i z hz => hinside i.val i.property z hz
    mass := fun i => hmass i.val i.property
    width := fun i => (test i.val).width_eq
    short := fun i => (test i.val).length_le
    area := ?_
    length_le := ?_
    center := ?_
    direction := fun q => (hassign q).2.2 }⟩
  · intro i j hij
    exact hdisj i.property j.property (fun h => hij (Subtype.ext h))
  · rw [Finset.sum_coe_sort keepers (fun j => (test j).top.area)]
    exact harea
  · intro q
    simpa only [P.densityTile_length] using (hassign q).1
  · intro q
    simpa only [densityTile,zero_mul,add_zero] using (hassign q).2.1

end LipschitzHilbert.PacketLatticeData

end

end OAI
