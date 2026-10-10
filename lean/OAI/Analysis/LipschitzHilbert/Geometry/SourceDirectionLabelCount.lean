import OAI.Analysis.LipschitzHilbert.Geometry.SourceDirectionLatticeCount

namespace OAI

/-! Local angular multiplicity supplies the per-scale packing constant.
There is no dependence on the total number of available labels. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem direction_label_count (j : Fin N)
    (items : ∀ l : P.labels j, Finset (Item j l))
    (t w K R : ℝ) (hw : 0<w) (hwW : w≤P.width) (hK : 0≤K) (hR : 0≤R)
    (M Q : ℕ) (hQ : R≤Q)
    (hmultiplicity : SourceSlopeLabels.LocalMultiplicity Finset.univ
      (P.rowSlope j) (w/P.length j) M)
    (hnear : ∀ l, (items l).Nonempty → |P.rowSlope j l-t|≤R*(w/P.length j))
    (z : ℝ×ℝ)
    (hbox : ∀ l u, u∈items l → z∈densitySpatialBox (P.directionBox t ⟨j,⟨l,u⟩⟩) K) :
    (∑ l : P.labels j, ((items l).card:ℝ))≤
      (((2*Q+1)*M:ℕ):ℝ)*(((1+K^2)*(1+(K*(1+R))^2))*(4*Real.pi)^2) := by
  classical
  let active := SourceSlopeLabels.window Finset.univ (P.rowSlope j) t (w/P.length j) R
  let C := ((1+K^2)*(1+(K*(1+R))^2))*(4*Real.pi)^2
  have hC : 0≤C := by dsimp [C]; positivity
  have hcard : active.card≤(2*Q+1)*M :=
    SourceSlopeLabels.window_card_le Finset.univ (P.rowSlope j)
      (div_pos hw (P.length_pos j)) hmultiplicity hQ
  have hsum : (∑ l : P.labels j, ((items l).card:ℝ))=
      ∑ l∈active, ((items l).card:ℝ) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ active)
    intro l _ hl
    have he : items l=∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hn
      exact hl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hnear l hn⟩)
    simp only [he,Finset.card_empty,Nat.cast_zero]
  rw [hsum]
  have hlocal (l : P.labels j) (hl : l∈active) : ((items l).card:ℝ)≤C := by
    apply P.direction_lattice_count j l (items l) t K R hK ?_ z (hbox l)
    have hn := (Finset.mem_filter.mp hl).2
    have hb : |t-P.rowSlope j l| * P.length j≤R*w := by
      calc
        _ ≤ (R*(w/P.length j))*P.length j :=
          mul_le_mul_of_nonneg_right (by simpa only [abs_sub_comm] using hn) (P.length_pos j).le
        _ = _ := by field_simp [(P.length_pos j).ne']
    exact hb.trans (mul_le_mul_of_nonneg_left hwW hR)
  calc
    _ ≤ ∑ _l∈active, C := Finset.sum_le_sum hlocal
    _ = (active.card:ℝ)*C := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hC

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
