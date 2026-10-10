import OAI.Analysis.LipschitzHilbert.Trees.SourceDensityScaledForest
import OAI.Analysis.LipschitzHilbert.Trees.SourceScaleRestriction

namespace OAI

/-! Dropping dyadic packet scales rebases the same angular grid. The
alternating shift changes the grid sign at odd starting levels. -/
noncomputable section
open Set
namespace LipschitzHilbert
open DyadicLineGrid

theorem scaledAngularCell_eq_Ico (unit : ℝ) (hunit : 0<unit) (q k j : ℤ) :
    scaledAngularCell unit q k j=Ico (unit*left q k j) (unit*left q k (j+1)) := by
  ext s
  change (left q k j≤s/unit ∧ s/unit<left q k (j+1)) ↔ _
  rw [le_div_iff₀ hunit,div_lt_iff₀ hunit]
  simp only [mul_comm,mem_Ico]

theorem angular_shift_rebase (q h k : ℤ) :
    shift ((h.negOnePow : ℤ)*q) k=shift q (h+k) := by
  simp only [shift,Int.negOnePow_add,Units.val_mul,Int.cast_mul]
  ring

theorem angular_left_rebase (q h k j : ℤ) :
    scale h*left ((h.negOnePow : ℤ)*q) k j=left q (h+k) j := by
  unfold left
  rw [angular_shift_rebase]
  simp only [scale,zpow_add₀ (by norm_num : (2:ℝ)≠0)]
  ring

theorem scaledAngularCell_rebase (unit : ℝ) (hunit : 0<unit) (q h k j : ℤ) :
    scaledAngularCell (unit*scale h) ((h.negOnePow : ℤ)*q) k j=
      scaledAngularCell unit q (h+k) j := by
  rw [scaledAngularCell_eq_Ico _ (mul_pos hunit (scale_pos h)),
    scaledAngularCell_eq_Ico _ hunit]
  congr 1 <;> rw [mul_assoc,angular_left_rebase]

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem dropScales_angularCell (first : Fin N) (w : ℝ) (hw : 0<w)
    (q : ℤ) (j : Fin (N-first.val)) (cell : ℤ) :
    scaledAngularCell (w/(P.dropScales first).topLength)
      (((first.val:ℤ).negOnePow : ℤ)*q) j.val cell=
    scaledAngularCell (w/P.topLength) q (dropIndex first j).val cell := by
  have he : w/(P.dropScales first).topLength=(w/P.topLength)*DyadicLineGrid.scale first.val := by
    change w/(P.topLength/(2:ℝ)^first.val)=(w/P.topLength)*DyadicLineGrid.scale first.val
    simp only [DyadicLineGrid.scale,zpow_natCast]
    field_simp
  rw [he,scaledAngularCell_rebase _ (div_pos hw P.topLength_pos)]
  simp only [dropIndex,Nat.cast_add]

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
