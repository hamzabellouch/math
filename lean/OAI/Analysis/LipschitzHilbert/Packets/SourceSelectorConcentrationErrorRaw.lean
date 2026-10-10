import OAI.Analysis.LipschitzHilbert.Packets.SourceSelectorConcentrationErrorSynthesis
import OAI.Analysis.LipschitzHilbert.Trees.SourceSlottedConcentration
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledRawEnvelope

namespace OAI

/-! High-order carrier-free decay and the actual top geometry survive
snapping the translated labeled lattice. These are the raw hypotheses
used in the weighted angular-error concentration theorem. -/

noncomputable section
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem raw_absolute_snapped_order (i : Fin 3) (j : Fin N) (l : P.labels j)
    (u : Item j l) (k : κ) (y x : ℝ) :
    ‖P.raw i j l u k y x‖ ≤ P.absoluteConstant*
      (lineEnvelope (P.length j*(P.snappedSite j l u).1) (P.length j) P.order x*
        lineEnvelope (P.width*(P.snappedSite j l u).2) P.width P.order y) := by
  have hs := snappedLatticeSite_envelope (P.originX j l) (P.originZ j l) (P.length j)
    P.width (P.rowSlope j l) x y (P.length_pos j) P.width_pos (P.site j l u) P.order P.order
  have hA : 0 ≤ (2^P.order*P.profileBound)*P.ratioBound^2 := by
    have := P.profileBound_pos
    positivity
  have h := (P.raw_absolute_envelope i j l u k y x).trans
    (mul_le_mul_of_nonneg_left hs hA)
  have hp : (3:ℝ)^P.order*3^P.order = 3^(2*P.order) := by
    rw [← pow_add]
    congr 1
    omega
  simpa only [absoluteConstant,snappedSite,hp,mul_assoc] using h

theorem raw_absolute_snapped_decay (m : ℕ) (hm : m ≤ P.order)
    (i : Fin 3) (j : Fin N) (l : P.labels j) (u : Item j l) (k : κ) (y x : ℝ) :
    ‖P.raw i j l u k y x‖ ≤ P.absoluteConstant*
      (lineEnvelope (P.length j*(P.snappedSite j l u).1) (P.length j) m x*
        lineEnvelope (P.width*(P.snappedSite j l u).2) P.width m y) := by
  apply (P.raw_absolute_snapped_order i j l u k y x).trans
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul (lineEnvelope_antitone _ _ _ hm) (lineEnvelope_antitone _ _ _ hm)
      (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)) P.absoluteConstant_pos.le

theorem snapped_top_horizontal {T : SlopeBox} {K : ℝ} {D : ℕ}
    (G : SourceLabeledTopGeometry P T K D) (j : Fin N) (l : P.labels j) (u : Item j l) :
    |P.length j*(P.snappedSite j l u).1-T.x| ≤ K*T.length := by
  have hs := snappedLatticeSite_horizontal (P.originX j l) (P.originZ j l)
    (P.length j) P.width (P.rowSlope j l) (P.length_pos j) (P.site j l u)
  change |P.actualX j l u-P.length j*(P.snappedSite j l u).1| ≤ P.length j at hs
  have ht := abs_sub_le (P.length j*(P.snappedSite j l u).1) (P.actualX j l u) T.x
  rw [abs_sub_comm (P.actualX j l u)] at hs
  have hg := G.centerX_le j l u
  linarith

theorem snapped_top_vertical {T : SlopeBox} {K : ℝ} {D : ℕ}
    (G : SourceLabeledTopGeometry P T K D) (j : Fin N) (l : P.labels j) (u : Item j l) :
    |P.width*(P.snappedSite j l u).2-(T.y-T.slope*T.x)| ≤ K*T.width := by
  have hs := snappedLatticeSite_vertical (P.originX j l) (P.originZ j l)
    (P.length j) P.width (P.rowSlope j l) P.width_pos (P.site j l u)
  change |P.actualZ j l u-P.width*(P.snappedSite j l u).2| ≤ P.width at hs
  have ht := abs_sub_le (P.width*(P.snappedSite j l u).2) (P.actualZ j l u) (T.y-T.slope*T.x)
  rw [abs_sub_comm (P.actualZ j l u)] at hs
  have hg := G.centerZ_le j l u
  linarith

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
