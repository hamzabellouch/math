import OAI.Analysis.LipschitzHilbert.Trees.SourceDensityRebase
import OAI.Analysis.LipschitzHilbert.Packets.SourcePacketDensity
import OAI.Analysis.LipschitzHilbert.Trees.SourceScaleRestriction

namespace OAI

/-! Dyadic scale restriction preserves every actual packet density.
The alternating angular grid is rebased with its required sign. -/
noncomputable section
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

@[simp] theorem dropScales_actualX (first : Fin N) (j : Fin (N-first.val))
    (l : (P.dropScales first).labels j) (u : Item (dropIndex first j) l) :
    (P.dropScales first).actualX j l u=P.actualX (dropIndex first j) l u := by
  simp only [actualX,dropScales_length]
  rfl

@[simp] theorem dropScales_actualZ (first : Fin N) (j : Fin (N-first.val))
    (l : (P.dropScales first).labels j) (u : Item (dropIndex first j) l) :
    (P.dropScales first).actualZ j l u=P.actualZ (dropIndex first j) l u := by
  simp only [actualZ,dropScales_length]
  rfl

theorem dropScales_densityTile (first : Fin N) (t : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (j : Fin (N-first.val))
    (l : (P.dropScales first).labels j) (u : Item (dropIndex first j) l) :
    (P.dropScales first).densityTile t (fun j l => cell (dropIndex first j) l) ⟨j,⟨l,u⟩⟩=
      (P.densityTile t cell ⟨dropIndex first j,⟨l,u⟩⟩).rebase first.val := by
  simp only [densityTile,OrdinaryDensityTile.rebase,dropScales_actualX,dropScales_actualZ]
  congr 1
  simp only [dropIndex,Nat.cast_add]
  omega

theorem dropScales_ordinaryDensity (first : Fin N) (t w tau : ℝ) (hw : 0<w)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (E : Set (ℝ×ℝ)) (v : ℝ×ℝ → ℝ) (j : Fin (N-first.val))
    (l : (P.dropScales first).labels j) (u : Item (dropIndex first j) l) :
    (P.dropScales first).ordinaryDensity t (fun j l => cell (dropIndex first j) l)
      (((first.val:ℤ).negOnePow : ℤ)*grid) w tau E v ⟨j,⟨l,u⟩⟩=
      P.ordinaryDensity t cell grid w tau E v ⟨dropIndex first j,⟨l,u⟩⟩ := by
  unfold ordinaryDensity
  rw [P.dropScales_densityTile]
  have he : (P.dropScales first).topLength=P.topLength/DyadicLineGrid.scale first.val := by
    simp only [dropScales,length,DyadicLineGrid.scale,zpow_natCast]
  change ((P.densityTile t cell ⟨dropIndex first j,⟨l,u⟩⟩).rebase first.val).density
    (P.dropScales first).topLength w P.width tau _ E v = _
  rw [he]
  exact OrdinaryDensityTile.density_rebase _ P.topLength w P.width tau first.val grid
    P.topLength_pos hw E v

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
