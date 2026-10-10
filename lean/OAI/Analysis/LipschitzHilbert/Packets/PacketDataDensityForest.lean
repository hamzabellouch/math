import OAI.Analysis.LipschitzHilbert.Packets.PacketDataDensityGeometry
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataReferenceConditions
import OAI.Analysis.LipschitzHilbert.Geometry.PacketDataReferenceSelection
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataOrdinaryDensityForest
import OAI.Analysis.LipschitzHilbert.Trees.SourceHighDensityForest

namespace OAI

/-! The ordinary density produces the literal top assignment and witnesses
needed for packet concentration. No disjoint-witness premise is imposed. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

structure PacketDensityForest (P : PacketLatticeData N κ Label Item)
    (packets : Finset P.PacketIndex) (oldSlope L a cone w tau : ℝ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) where
  keepers : Finset packets
  top : keepers → SlopeBox
  assigned : P.PacketIndex → keepers
  witness : keepers → Set (ℝ×ℝ)
  measurable : ∀ i, MeasurableSet (witness i)
  disjoint : Pairwise fun i j => Disjoint (witness i) (witness j)
  subset : ∀ i, witness i ⊆ E
  finite : ∀ i, (volume.prod volume) (witness i) ≠ ∞
  mass : ∀ i, ENNReal.ofReal (L^(-(a+2))*(top i).length*(top i).width) ≤
    (volume.prod volume) (witness i)
  radius : ∀ i z, z ∈ witness i → (top i).radius z ≤ L^(a+2)
  precision : ∀ i z, z ∈ witness i → |u z-(top i).slope| ≤ w/(top i).length
  close : ∀ i z, z ∈ witness i →
    |u z-(top i).slope| ≤ (top i).width/(12*(top i).length)
  width : ∀ i, (top i).width = P.width
  short : ∀ i, (top i).length ≤ tau
  seed_short : ∀ i, P.length i.val.val.1 ≤ (top i).length
  area : (∑ i, (top i).area) ≤ 2*L^a*(volume.prod volume).real E
  area_pos : 0 < ∑ i, (top i).area
  reference : ∀ q ∈ packets,
    P.referenceCondition oldSlope (top (assigned q)).slope
      (top (assigned q)).length cone w q.1 q.2.1
  horizontal : ∀ q ∈ packets,
    |P.actualX q.1 q.2.1 q.2.2-(top (assigned q)).x|+P.length q.1 ≤
      L^(a+3)*(top (assigned q)).length
  transverse : ∀ q ∈ packets,
    |P.actualZ q.1 q.2.1 q.2.2+(oldSlope-(top (assigned q)).slope)*
      P.actualX q.1 q.2.1 q.2.2-
      ((top (assigned q)).y-(top (assigned q)).slope*(top (assigned q)).x)|+P.width ≤
        L^(a+3)*(top (assigned q)).width

theorem PacketDensityForest.area_budget
    {P : PacketLatticeData N κ Label Item} {packets : Finset P.PacketIndex}
    {oldSlope L a cone w tau : ℝ} {E : Set (ℝ×ℝ)} {u : ℝ×ℝ → ℝ}
    (forest : PacketDensityForest P packets oldSlope L a cone w tau E u)
    (hL : 2 ≤ L) (ratio Fmass : ℝ) (hF : 0 ≤ Fmass)
    (hEF : (volume.prod volume).real E ≤ ratio^2*Fmass) :
    (∑ i, (forest.top i).area) ≤ L^(a+1)*ratio^2*Fmass := by
  have hLp : 0 < L := by linarith
  calc
    _ ≤ 2*L^a*(volume.prod volume).real E := forest.area
    _ ≤ 2*L^a*(ratio^2*Fmass) := mul_le_mul_of_nonneg_left hEF (by positivity)
    _ ≤ (L*L^a)*(ratio^2*Fmass) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hLp.le _))
        (mul_nonneg (sq_nonneg _) hF)
    _ = _ := by rw [Real.rpow_add hLp,Real.rpow_one]; ring

theorem exists_packet_density_forest_in_cells (a : ℝ) (ha : 0 ≤ a) :
    ∃ L0 : ℝ, 2 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (packets : Finset P.PacketIndex),
      packets.Nonempty →
    ∀ (oldSlope : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
      (cone w tau : ℝ), 1 ≤ cone → 0 < w → 12*w ≤ P.width →
    ∀ (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ), MeasurableSet E →
      (volume.prod volume) E ≠ ∞ → Measurable u →
      (∀ q ∈ packets, L^(-a) < P.ordinaryDensity oldSlope cell grid w tau E u q) →
      (∀ q ∈ packets, oldSlope+P.rowSlope q.1 q.2.1 ∈
        scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) →
      ∃ forest : PacketDensityForest P packets oldSlope L a cone w tau E u,
        (∀ i, (forest.top i).slope ∈ scaledAngularCell (w/P.topLength) grid
          i.val.val.1.val (cell i.val.val.1 i.val.val.2.1)) ∧
        (∀ q ∈ packets, (forest.top (forest.assigned q)).slope ∈
          scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) := by
  classical
  obtain ⟨L0,hL0,hforest⟩ := exists_high_density_forest a ha
  refine ⟨L0,hL0,?_⟩
  intro L hL N κ Label Item _ _ P packets hpackets oldSlope cell grid cone w tau hcone hw hW E u hE hEfin hu hdensity hcell
  obtain ⟨test,keepers,choose,hmeas,hdisj,harea,hmass,hinside,hassign⟩ :=
    hforest L hL P.PacketIndex packets (P.densityTile oldSlope cell)
      P.topLength w P.width tau grid P.topLength_pos hw hW E u hE hEfin hu hdensity
  obtain ⟨q0,hq0⟩ := hpackets
  let assigned : P.PacketIndex → keepers := fun q =>
    if hq : q ∈ packets then choose ⟨q,hq⟩ else choose ⟨q0,hq0⟩
  let T : keepers → SlopeBox := fun i => (test i.val).top
  let W : keepers → Set (ℝ×ℝ) := fun i => densityTest E u (T i)
    (scaledAngularCell (w/P.topLength) grid (test i.val).level (test i.val).cell) (L^(a/100+1))
  have hassigned (q : P.PacketIndex) (hq : q ∈ packets) :
      assigned q = choose ⟨q,hq⟩ := dite_eq_left hq
  have hshort (q : P.PacketIndex) (hq : q ∈ packets) :
      P.length q.1 ≤ (T (assigned q)).length := by
    rw [hassigned q hq]
    simpa only [T,P.densityTile_length] using (hassign ⟨q,hq⟩).1
  have hrad (q : P.PacketIndex) (hq : q ∈ packets) :
      (T (assigned q)).radius
        (P.actualX q.1 q.2.1 q.2.2,
          P.actualZ q.1 q.2.1 q.2.2+oldSlope*P.actualX q.1 q.2.1 q.2.2) ≤ L^(a+2) := by
    rw [hassigned q hq]
    exact (hassign ⟨q,hq⟩).2.1
  have hgeometry := P.assigned_packet_geometry_of_density packets assigned T oldSlope L (a+2)
    (hL0.trans hL) (by linarith) hshort
    (fun q _ => (test (assigned q).val).width_eq.ge) hrad
  have hfinite (i : keepers) : (volume.prod volume) (W i) ≠ ∞ :=
    measure_ne_top_of_subset (fun _ hz => (hinside i.val i.property _ hz).1) hEfin
  refine ⟨{
    keepers := keepers
    top := T
    assigned := assigned
    witness := W
    measurable := fun i => hmeas i.val i.property
    disjoint := ?_
    subset := fun i z hz => (hinside i.val i.property z hz).1
    finite := hfinite
    mass := ?_
    radius := fun i z hz => (hinside i.val i.property z hz).2.1
    precision := fun i z hz => (hinside i.val i.property z hz).2.2.1
    close := fun i z hz => (hinside i.val i.property z hz).2.2.2
    width := fun i => (test i.val).width_eq
    short := fun i => (test i.val).length_le
    seed_short := fun i => by
      simpa only [P.densityTile_length] using (test i.val).tile_length_le
    area := ?_
    area_pos := ?_
    reference := ?_
    horizontal := ?_
    transverse := ?_ },?_,?_⟩
  · intro i j hij
    exact hdisj i.property j.property (fun h => hij (Subtype.ext h))
  · intro i
    have h := ENNReal.ofReal_le_ofReal (hmass i.val i.property)
    rw [Measure.real,ENNReal.ofReal_toReal (hfinite i)] at h
    simpa only [SlopeBox.area,mul_assoc] using h
  · change (∑ i : keepers, (fun j => (test j).top.area) i.val) ≤ _
    rw [Finset.sum_coe_sort keepers (fun j => (test j).top.area)]
    exact harea
  · exact Finset.sum_pos (fun i _ => (T i).area_pos) (Finset.univ_nonempty_iff.mpr
      ⟨choose ⟨q0,hq0⟩⟩)
  · intro q hq
    apply P.reference_bounds_of_density_cell oldSlope cell grid w cone hw hcone q _ (hshort q hq)
      (hcell q hq)
    rw [hassigned q hq]
    exact (hassign ⟨q,hq⟩).2.2
  · simpa only [show a+2+1=a+3 by ring] using hgeometry.1
  · simpa only [show a+2+1=a+3 by ring] using hgeometry.2
  · intro i
    exact (test i.val).slope_mem_tile
  · intro q hq
    change (T (assigned q)).slope ∈
      scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)
    rw [hassigned q hq]
    exact (hassign ⟨q,hq⟩).2.2

theorem exists_packet_density_forest (a : ℝ) (ha : 0 ≤ a) :
    ∃ L0 : ℝ, 2 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (packets : Finset P.PacketIndex),
      packets.Nonempty →
    ∀ (oldSlope : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
      (cone w tau : ℝ), 1 ≤ cone → 0 < w → 12*w ≤ P.width →
    ∀ (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ), MeasurableSet E →
      (volume.prod volume) E ≠ ∞ → Measurable u →
      (∀ q ∈ packets, L^(-a) < P.ordinaryDensity oldSlope cell grid w tau E u q) →
      (∀ q ∈ packets, oldSlope+P.rowSlope q.1 q.2.1 ∈
        scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) →
      Nonempty (PacketDensityForest P packets oldSlope L a cone w tau E u) := by
  obtain ⟨L0,hL0,hforest⟩ := exists_packet_density_forest_in_cells a ha
  refine ⟨L0,hL0,?_⟩
  intro L hL N κ Label Item _ _ P packets hp oldSlope cell grid cone w tau hc hw hW E u hE hEfin hu hd hang
  obtain ⟨forest,_,_⟩ := hforest L hL N κ Label Item P packets hp oldSlope cell grid cone w tau hc hw hW
    E u hE hEfin hu hd hang
  exact ⟨forest⟩

end LipschitzHilbert.PacketLatticeData

end

end OAI
