import OAI.Analysis.LipschitzHilbert.Trees.SourceParentResidualReference
import OAI.Analysis.LipschitzHilbert.Trees.SourceSelectedResidualSquare

namespace OAI

/-! The square-reference event is taken on the literal parent cone and
in the path-top reference direction. Its good event controls the original
short residuals without an equality of reference slopes. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable

theorem eventually_physical_parent_short_square (q D : ℝ) (hq : 0 ≤ q) (hD : 0 ≤ D) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item), 6 ≤ P.order → P.absoluteConstant ≤ L^q →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t pathSlope R C F w a : ℝ) (hw : 0 < w)
      (hcone : 0 ≤ C+(SourceParameters.branching L)^3) (hF : 0 ≤ F)
      (hwide : (C+(SourceParameters.branching L)^3)*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
      (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖ ≤ 1) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
    ∀ (τ : Type*) (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
      (T : τ → SlopeBox) (A s : ℝ),
      (grid.branching:ℝ) = SourceParameters.step L →
    ∀ (_hK : 0 < SourceParameters.blockCount L) (shift : Fin (SourceParameters.blockCount L)),
      (∀ j : Fin N, grid.eligible (grid.rootWidth/(SourceParameters.branching L)^2)
        (w/P.length j) 0) → (∀ top ∈ tops, 0 ≤ precision top) →
    let cut := grid.rootWidth/(SourceParameters.branching L)^2
    let stop := fun j : Fin N => grid.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
    let weight := fun top z => (T top).weight (L^(A+2)) D z
    ∀ (phase : ℕ → ℂ), (∀ k, 0 ≤ (phase k).re) →
    ∀ (alpha : ℝ), 0 ≤ alpha → alpha ≤ 1 →
    ∀ (z : ℝ×ℝ) (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ),
      (∀ u ∈ packets, assigned u ∈ tops) →
      (∀ u ∈ packets, grid.eligible cut (precision (assigned u)) (stop u.1)) →
      (∀ u ∈ packets, |t+P.rowSlope u.1 u.2.1-slope (assigned u)| ≤ C*(w/P.length u.1)) →
    let cone := C+(SourceParameters.branching L)^3
    let S := sourceReferencePackets packets (fun u => P.length u.1)
      (fun u => t+P.rowSlope u.1 u.2.1) R pathSlope cone w
    let Q := P.referenceFamily t pathSlope R cone w F hw hcone hF hwide hfrequency
    let orig := P.referenceOriginalLabel t pathSlope R cone w
    let selected := (Finset.univ : Finset Q.PacketIndex).filter
      (fun u => (⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S)
    z ∉ (Q.restrictPackets selected).physicalReferenceBad
      (Q.restrictedAlternate (fun j l => alt j (orig j l)) selected)
      (Q.restrictedAlternate_bound (fun j l => alt j (orig j l))
        (fun j l => hAlt j (orig j l)) selected)
      pathSlope a (fun j l => b j (orig j l)) v f
      (fun j l u => T (assigned ⟨j,⟨orig j l,u.val⟩⟩)) L A (q+8) (2*q+9) s →
    ∀ count : ℕ,
    let value := P.physicalMaskedValue alt hAlt t b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z
    (∑ j : Fin count, ‖grid.packetResidual (packets.filter (fun u => P.length u.1 ≤ R))
      (fun u => slope (assigned u)) (fun u => stop u.1)
      (grid.sourcePacketBase tops slope precision cut weight assigned (fun u => stop u.1) value alpha z)
      (grid.sourceTransition tops slope precision cut weight (SourceParameters.blockCount L)
        (grid.sourceBoundaryGap L) phase z)
      (ShiftedBlocks.endpoint shift j.val) (ShiftedBlocks.endpoint shift (j.val+1))
      (grid.index (ShiftedBlocks.endpoint shift j.val) pathSlope)‖^2) ≤ (L^(3*q+12))^2 := by
  filter_upwards [eventually_selected_physical_shifted_residual_square q D hq hD] with L hbound
  intro N κ Label Item _ _ P horder hP alt hAlt t pathSlope R C F w a hw hcone hF
    hwide hfrequency b hb hb1 v hv f hf hf1 τ grid tops slope precision T A s hbranch hK shift
    hzero hp cut stop weight phase hz alpha ha ha1 z packets assigned hassigned he hangle
    cone S Q orig selected hgood count value
  let own := fun u : Q.PacketIndex => assigned ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩
  let altQ := fun j (l : Q.labels j) => alt j (orig j l)
  have hAltQ := fun j (l : Q.labels j) => hAlt j (orig j l)
  have hS (u : P.PacketIndex) (hu : u ∈ S) :
      P.referenceCondition t pathSlope R cone w u.1 u.2.1 := by
    obtain ⟨_,hlen,hangle⟩ := Finset.mem_filter.mp hu
    exact ⟨hlen,by simpa only [mul_div_assoc] using hangle⟩
  have hmap (u : Q.PacketIndex) (hu : u ∈ selected) :
      (⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ packets :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hu).2).1
  have hs := hbound N κ Label Item Q horder hP altQ hAltQ pathSlope a
    (fun j l => b j (orig j l)) (fun j l => hb j (orig j l)) (fun j l => hb1 j (orig j l))
    v hv f hf hf1 τ grid tops slope precision T A s w hw hbranch hK shift
    hzero hp phase hz alpha ha ha1 z selected own
    (fun u hu => hassigned _ (hmap u hu)) (fun u hu => he _ (hmap u hu)) count pathSlope hgood
  have heq (j : Fin count) :
      grid.packetResidual selected (fun u => slope (own u)) (fun u => stop u.1)
        (grid.sourcePacketBase tops slope precision cut weight own (fun u => stop u.1)
          (Q.physicalMaskedValue altQ hAltQ pathSlope (fun j l => b j (orig j l)) v f
            (fun j l u => T (own ⟨j,⟨l,u⟩⟩)) L A z) alpha z)
        (grid.sourceTransition tops slope precision cut weight (SourceParameters.blockCount L)
          (grid.sourceBoundaryGap L) phase z)
        (ShiftedBlocks.endpoint shift j.val) (ShiftedBlocks.endpoint shift (j.val+1))
        (grid.index (ShiftedBlocks.endpoint shift j.val) pathSlope) =
      grid.packetResidual (packets.filter (fun u => P.length u.1 ≤ R))
        (fun u => slope (assigned u)) (fun u => stop u.1)
        (grid.sourcePacketBase tops slope precision cut weight assigned (fun u => stop u.1) value alpha z)
        (grid.sourceTransition tops slope precision cut weight (SourceParameters.blockCount L)
          (grid.sourceBoundaryGap L) phase z)
        (ShiftedBlocks.endpoint shift j.val) (ShiftedBlocks.endpoint shift (j.val+1))
        (grid.index (ShiftedBlocks.endpoint shift j.val) pathSlope) := by
    rw [P.referenceFamily_physicalSourceResidual_selected t pathSlope R cone w F
      hw hcone hF hwide hfrequency S hS alt hAlt b v f grid tops slope precision cut weight
      assigned stop T L A alpha z]
    exact P.short_parent_residual_eq grid packets assigned slope t R C
      (SourceParameters.branching L) w hw (SourceParameters.branching_pos L) hzero hangle
      _ _ _ _ pathSlope (grid.source_shifted_width_bounds L hbranch hK shift j.val).2
  convert hs using 1
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun x : EuclideanSpace ℂ κ => ‖x‖^2) (heq j).symm

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
