import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceSelectedVariation
import OAI.Analysis.LipschitzHilbert.Trees.SourceResidualGeometry

namespace OAI

/-! The deterministic residual collection of an actual shifted source
path lies in its short reference cone. Its reference good event therefore
controls the original physical prefix used by every active unary segment. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem shifted_residual_referenceCondition (P : SourceLabeledLattice N κ Label Item)
    (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
    (oldSlope w B R C : ℝ) (hw : 0 < w) (hB : 0 < B) (hR : 0 < R)
    {K : ℕ} (hK : 0 < K) (shift : Fin K) (top : τ)
    (hprecision : precision top = w/R)
    (hzero : ∀ u ∈ packets, grid.eligible (grid.rootWidth/B^2) (w/P.length u.1) 0)
    (hangle : ∀ u ∈ packets,
      |oldSlope+P.rowSlope u.1 u.2.1-slope (assigned u)| ≤ C*(w/P.length u.1)) :
    let cut := grid.rootWidth/B^2
    let stop := fun j => grid.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
    let count := grid.firstIneligibleShiftedBlock cut (w/R) (div_pos hw hR) hK shift
    ∀ u ∈ grid.fixedPathResidualPackets tops slope precision cut packets assigned
      (fun u => stop u.1) (ShiftedBlocks.endpoint shift) (count-1) (slope top),
      P.referenceCondition oldSlope (slope top) R (C+B^2) w u.1 u.2.1 := by
  dsimp only
  intro u hu
  have hg := grid.shifted_residual_collection_geometry tops slope precision packets assigned
    (fun u => P.length u.1) (fun u => oldSlope+P.rowSlope u.1 u.2.1)
    (fun u => P.length_pos u.1) hw hB hR hK shift top hprecision hzero hangle u hu
  exact ⟨hg.2.1.le,by simpa only [mul_div_assoc] using hg.2.2⟩

theorem shifted_residual_reference_variation (P : SourceLabeledLattice N κ Label Item)
    (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
    (oldSlope w B R C F : ℝ) (hw : 0 < w) (hB : 0 < B) (hR : 0 < R)
    (hcone : 0 ≤ C+B^2) (hF : 0 ≤ F) (hwide : (C+B^2)*w ≤ P.width)
    (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
    {K : ℕ} (hK : 0 < K) (shift : Fin K) (top : τ)
    (hprecision : precision top = w/R)
    (hzero : ∀ u ∈ packets, grid.eligible (grid.rootWidth/B^2) (w/P.length u.1) 0)
    (hangle : ∀ u ∈ packets,
      |oldSlope+P.rowSlope u.1 u.2.1-slope (assigned u)| ≤ C*(w/P.length u.1))
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A a e s r : ℝ) (z : ℝ×ℝ) :
    let cut := grid.rootWidth/B^2
    let stop := fun j => grid.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j))
    let count := grid.firstIneligibleShiftedBlock cut (w/R) (div_pos hw hR) hK shift
    let S := grid.fixedPathResidualPackets tops slope precision cut packets assigned
      (fun u => stop u.1) (ShiftedBlocks.endpoint shift) (count-1) (slope top)
    let Q := P.referenceFamily oldSlope (slope top) R (C+B^2) w F
      hw hcone hF hwide hfrequency
    let orig := P.referenceOriginalLabel oldSlope (slope top) R (C+B^2) w
    let selected := (Finset.univ : Finset Q.PacketIndex).filter
      (fun u => (⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S)
    z ∉ (Q.restrictPackets selected).physicalReferenceBad
      (Q.restrictedAlternate (fun j l => alt j (orig j l)) selected)
      (Q.restrictedAlternate_bound (fun j l => alt j (orig j l))
        (fun j l => hAlt j (orig j l)) selected)
      (slope top) a (fun j l => b j (orig j l)) v f (fun j l u => T j (orig j l) u.val)
      L A e s r →
    ∀ H, finiteCubicVariation
      (fun k => P.selectedPhysicalPrefix alt hAlt oldSlope b v f T L A S stop z (min k H))
      (2*H) ≤ (L^r)^3 := by
  dsimp only
  intro hgood H
  apply P.referenceFamily_selected_good_bound oldSlope (slope top) R (C+B^2) w F
    hw hcone hF hwide hfrequency alt hAlt b v f T L A _
    (P.shifted_residual_referenceCondition grid tops slope precision packets assigned
      oldSlope w B R C hw hB hR hK shift top hprecision hzero hangle)
    _ (grid.source_length_stopping_antitone _ hw P.length P.length_pos P.length_antitone)
    a e s r z hgood H

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
