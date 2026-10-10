import OAI.Analysis.LipschitzHilbert.Packets.SourceFrozenDensitySum
import OAI.Analysis.LipschitzHilbert.Trees.SourceTreeCellGluing
import OAI.Analysis.LipschitzHilbert.Trees.SourceCellPolynomial

namespace OAI

/-! Integrating the ordinary-tree error over the actual density masks.
Order 53 leaves at least six decay powers after the density loss 203. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
open SourceWhitney

private theorem error_cell_integral {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (b W D eta : ℝ) (hW : 0<W) (hD : 0≤D)
    (p : (ℤ×ℤ)×ℤ) (A : Set (ℝ×ℝ)) (hA : MeasurableSet A)
    (F : ℝ×ℝ → V) (hF : AEStronglyMeasurable F (volume.prod volume))
    (hbound : ∀ z, polynomialWeight b (2*W) 53 z.2^2*‖F z‖≤D)
    (hmass : (volume.prod volume).real (partitionCell b W p∩A)≤
      32*(2:ℝ)^203*eta*(1+|(p.2:ℝ)|)^203*DyadicLineGrid.scale p.1.1*W) :
    IntegrableOn (A.indicator F) (partitionCell b W p) (volume.prod volume) ∧
    (∫ z in partitionCell b W p, ‖A.indicator F z‖ ∂volume.prod volume)≤
      (32^106*D*(32*(2:ℝ)^203*eta))*
        ((DyadicLineGrid.scale p.1.1*W)/(1+|(p.2:ℝ)|)^6) := by
  let w := 1+|(p.2:ℝ)|
  have hw1 : 1≤w := by dsimp [w]; linarith [abs_nonneg (p.2:ℝ)]
  have hw : 0<w := lt_of_lt_of_le (by norm_num) hw1
  have hpt (z : ℝ×ℝ) (hz : z∈partitionCell b W p) :
      ‖F z‖≤32^106*D/w^209 := by
    have hp := transverse_cell_polynomial_weight b W (p.2:ℝ) z.2 53 hW
      (transverseCell_bound b W p.2 hz.2)
    have hs := pow_le_pow_left₀ (by positivity : 0≤(1+|(p.2:ℝ)|)^(2*53)) hp 2
    simp only [mul_pow,←pow_mul] at hs
    change w^212≤32^106*polynomialWeight b (2*W) 53 z.2^2 at hs
    have hl : w^209≤32^106*polynomialWeight b (2*W) 53 z.2^2 :=
      (pow_le_pow_right₀ hw1 (by omega : 209≤212)).trans hs
    apply (le_div_iff₀ (pow_pos hw 209)).mpr
    calc
      _ ≤ (32^106*polynomialWeight b (2*W) 53 z.2^2)*‖F z‖ := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right hl (norm_nonneg (F z))
      _ = 32^106*(polynomialWeight b (2*W) 53 z.2^2*‖F z‖) := by rw [mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hbound z) (pow_nonneg (by norm_num) 106)
  have h := masked_cell_norm_integral (volume.prod volume) (partitionCell b W p) A
    (partitionCell_measurable b W p) hA (partitionCell_finite b W p) F hF
    (32^106*D/w^209) hpt
  refine ⟨h.1,h.2.trans ?_⟩
  apply (mul_le_mul_of_nonneg_left hmass
    (div_nonneg (mul_nonneg (pow_nonneg (by norm_num) 106) hD) (pow_nonneg hw.le 209))).trans_eq
  change (32^106*D/w^209)*(32*2^203*eta*w^203*DyadicLineGrid.scale p.1.1*W)=_
  have he : w^209=w^203*w^6 := by rw [←pow_add]
  rw [he]
  field_simp
  ring

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

/-- A pointwise transverse error estimate integrates with the actual
cell masks at a cost independent of the number of scales and cells. -/
theorem tree_error_integrable_bound (hne : Nonempty P.PacketIndex)
    (F : P.DensityWhitneyCell → ℝ×ℝ → EuclideanSpace ℂ κ)
    (hF : ∀ i, AEStronglyMeasurable (F i) (volume.prod volume))
    (a b D eta : ℝ) (hD : 0≤D) (heta : 0≤eta)
    (hcenter : ∀ q : P.PacketIndex, |P.actualX q.1 q.2.1 q.2.2-a|≤P.topLength/2)
    (hbound : ∀ i z, polynomialWeight b (2*P.width) 53 z.2^2*‖F i z‖≤D)
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E) (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (Omega : P.DensityWhitneyCell → Set ℝ) (hOmega : ∀ i, MeasurableSet (Omega i))
    (hEmpty : ∀ i, ¬P.HasLongPacket i → Omega i=∅)
    (hmass : ∀ i n, (volume.prod volume).real
      (partitionCell b P.width (i.val,n)∩(E∩u ⁻¹' Omega i))≤
      32*(2:ℝ)^203*eta*(1+|(n:ℝ)|)^203*DyadicLineGrid.scale i.val.1*P.width) :
    let G := paste (Finset.univ : Finset P.PacketIndex)
      (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1)
      (by obtain ⟨q⟩ := hne; exact ⟨q,Finset.mem_univ q⟩)
      (fun q _ => P.length_pos q.1)
      (fun i => (E∩u ⁻¹' Omega i).indicator (F i))
    Integrable G (volume.prod volume) ∧ (∫ z, ‖G z‖ ∂volume.prod volume)≤
      (32^106*D*(32*(2:ℝ)^203*eta))*(9*P.topLength*P.width*transverseTailConstant) := by
  classical
  let mask := fun i => E∩u ⁻¹' Omega i
  let J := fun (i : P.DensityWhitneyCell) (n : ℤ) =>
    ∫ z in partitionCell b P.width (i.val,n), ‖(mask i).indicator (F i) z‖ ∂volume.prod volume
  let C := 32^106*D*(32*(2:ℝ)^203*eta)
  have hC : 0≤C := mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) 106) hD)
    (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) 203)) heta)
  have hlocal (i : P.DensityWhitneyCell) (n : ℤ) := error_cell_integral b P.width D eta
    P.width_pos hD (i.val,n) (mask i) (hE.inter ((hOmega i).preimage hu))
    (F i) (hF i) (hbound i) (hmass i n)
  apply product_paste_integrable_bound (Finset.univ : Finset P.PacketIndex)
    (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1)
    (by obtain ⟨q⟩ := hne; exact ⟨q,Finset.mem_univ q⟩)
    (fun q _ => P.length_pos q.1) b P.width P.width_pos
    (fun i => (mask i).indicator (F i)) (fun i => (hlocal i.1 i.2).1)
  intro S T
  let SL := S.filter P.HasLongPacket
  have hzero (i : P.DensityWhitneyCell) (hi : ¬P.HasLongPacket i) (n : ℤ) : J i n=0 := by
    dsimp only [J,mask]
    rw [hEmpty i hi,preimage_empty,inter_empty]
    simp only [indicator_empty,norm_zero,integral_zero]
  have heq : (∑ p∈S×ˢT, J p.1 p.2)=(∑ p∈SL×ˢT, J p.1 p.2) := by
    simp only [Finset.sum_product,SL,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : P.HasLongPacket i
    · simp only [hi,ite_true]
    · simp only [hi,ite_false]
      exact Finset.sum_eq_zero (fun n _ => hzero i hi n)
  change (∑ p∈S×ˢT, J p.1 p.2)≤_
  rw [heq]
  have hbudget := finite_whitney_transverse_budget (Finset.univ : Finset P.PacketIndex)
    (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1)
    a P.topLength P.width P.topLength_pos.le P.width_pos.le (fun q _ => hcenter q)
    (SL.image Subtype.val) T
    (by intro p hp; obtain ⟨i,_hi,rfl⟩ := Finset.mem_image.mp hp; exact i.property)
    (by intro p hp; obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
        exact P.long_cell_scale_le_top i (Finset.mem_filter.mp hi).2)
  rw [Finset.sum_product,Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)] at hbudget
  calc
    _ ≤ ∑ p∈SL×ˢT, C*((DyadicLineGrid.scale p.1.val.1*P.width)/(1+|(p.2:ℝ)|)^6) :=
      Finset.sum_le_sum (fun p _ => (hlocal p.1 p.2).2)
    _ = C*∑ i∈SL, ∑ n∈T, (DyadicLineGrid.scale i.val.1*P.width)/(1+|(n:ℝ)|)^6 := by
      rw [Finset.sum_product,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hbudget hC

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
