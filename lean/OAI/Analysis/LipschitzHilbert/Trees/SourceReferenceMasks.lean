import OAI.Analysis.LipschitzHilbert.Trees.SourceLongCellMask
import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceCoordinates

namespace OAI

/-! Reference-direction masks obtained from the original angular grid.
Only the direction variable is translated; no dyadic cell is reassigned. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem exists_reference_long_cell_mask
    (t b w : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid k j : ℤ) (tau : ℝ)
    (htime : P.topLength≤tau)
    (hWhitney : Whitney (Finset.univ : Finset P.PacketIndex)
      (fun a => P.actualX a.1 a.2.1 a.2.2) (fun a => P.length a.1) k j)
    (hY : ∀ a : P.PacketIndex, |P.actualZ a.1 a.2.1 a.2.2-b|≤P.width/2)
    (hreference : ∀ a : P.PacketIndex, t∈
      scaledAngularCell (w/P.topLength) grid a.1.val (cell a.1 a.2.1))
    (hlong : ∃ a : P.PacketIndex, 32*DyadicLineGrid.scale k<P.length a.1)
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E) (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (eta : ℝ) (heta : 0≤eta)
    (hdensity : ∀ a, P.ordinaryDensity t cell grid w tau E u a≤eta) :
    ∃ Omega : Set ℝ, MeasurableSet Omega ∧
      (∀ a : P.PacketIndex, 32*DyadicLineGrid.scale k<P.length a.1 →
        (fun s : ℝ => s+t) ⁻¹' scaledAngularCell (w/P.topLength) grid a.1.val (cell a.1 a.2.1)⊆Omega) ∧
      (∀ n : ℤ, (volume.prod volume).real
        (partitionCell b P.width ((k,j),n)∩((slopeShear t) ⁻¹' E∩
          (fun z => u (slopeShear t z)-t) ⁻¹' Omega))≤
        32*(2:ℝ)^203*eta*(1+|(n:ℝ)|)^203*DyadicLineGrid.scale k*P.width) := by
  obtain ⟨a,test,_hx,_hy,_ht,_hl,_hu,hcontains,hmass⟩ :=
    P.source_whitney_cell_density t b cell grid k j w tau htime hWhitney hY
      hreference hlong E hE u hu eta heta hdensity
  let Omega := scaledAngularCell (w/P.topLength) grid test.level test.cell
  let O := (fun s : ℝ => s+t) ⁻¹' Omega
  refine ⟨O,(scaledAngularCell_measurable _ _ _ _).preimage (measurable_id.add_const t),?_,?_⟩
  · intro q hq s hs
    exact hcontains q hq hs
  · intro n
    have hm := hmass n
    dsimp only at hm
    let A := E∩u ⁻¹' Omega∩treeCell t b P.width k j n
    have hfin : (volume.prod volume) A≠∞ := by
      have h := (integrableOn_const_iff (C:=(1:ℝ))).mp hm.1
      simpa only [enorm_one,one_ne_zero,false_or,lt_top_iff_ne_top] using h
    have hfin' : (volume.prod volume) ((slopeShear t) ⁻¹' A)≠∞ := by
      rw [(slopeShear_measurePreserving t).measure_preimage_equiv]
      exact hfin
    apply (measureReal_mono (s₂ := (slopeShear t) ⁻¹' A) ?_ hfin').trans
    · have he : (volume.prod volume).real ((slopeShear t) ⁻¹' A)=
          (volume.prod volume).real A := by
        exact congrArg ENNReal.toReal ((slopeShear_measurePreserving t).measure_preimage_equiv A)
      rw [he]
      exact hm.2
    · intro z hz
      refine ⟨⟨hz.2.1,?_⟩,?_⟩
      · have hs := hz.2.2
        change u (slopeShear t z)-t+t∈Omega at hs
        change u (slopeShear t z)∈Omega
        simpa only [sub_add_cancel] using hs
      · have hcell := partitionCell_subset_treeCell b P.width ((k,j),n) hz.1
        exact (Set.ext_iff.mp (treeCell_slopeShear t b P.width k j n) z).mpr hcell



/-- Choose the density masks on the entire actual Whitney partition.
Cells without long packets receive the empty mask. -/
theorem exists_reference_whitney_masks
    (t b w : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) (tau : ℝ)
    (htime : P.topLength≤tau)
    (hY : ∀ a : P.PacketIndex, |P.actualZ a.1 a.2.1 a.2.2-b|≤P.width/2)
    (hreference : ∀ a : P.PacketIndex, t∈
      scaledAngularCell (w/P.topLength) grid a.1.val (cell a.1 a.2.1))
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E) (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (eta : ℝ) (heta : 0≤eta)
    (hdensity : ∀ a, P.ordinaryDensity t cell grid w tau E u a≤eta) :
    ∃ Omega : P.DensityWhitneyCell → Set ℝ,
      (∀ i, MeasurableSet (Omega i)) ∧
      (∀ i, ¬P.HasLongPacket i → Omega i=∅) ∧
      (∀ i (a : P.PacketIndex), 32*DyadicLineGrid.scale i.val.1<P.length a.1 →
        (fun s : ℝ => s+t) ⁻¹' scaledAngularCell (w/P.topLength) grid a.1.val (cell a.1 a.2.1)⊆Omega i) ∧
      (∀ i n, (volume.prod volume).real
        (partitionCell b P.width (i.val,n)∩((slopeShear t) ⁻¹' E∩
          (fun z => u (slopeShear t z)-t) ⁻¹' Omega i))≤
        32*(2:ℝ)^203*eta*(1+|(n:ℝ)|)^203*DyadicLineGrid.scale i.val.1*P.width) := by
  classical
  let Long := {i : P.DensityWhitneyCell // P.HasLongPacket i}
  have hex (i : Long) := P.exists_reference_long_cell_mask t b w cell grid i.val.val.1 i.val.val.2 tau
    htime i.val.property hY hreference i.property E hE u hu eta heta hdensity
  choose O hO hcontains hmass using hex
  let Omega := fun i : P.DensityWhitneyCell => if hi : P.HasLongPacket i then O ⟨i,hi⟩ else ∅
  refine ⟨Omega,?_,?_,?_,?_⟩
  · intro i
    by_cases hi : P.HasLongPacket i
    · simpa only [Omega,dite_eq_left hi] using hO ⟨i,hi⟩
    · simp only [Omega,dite_eq_right hi,MeasurableSet.empty]
  · intro i hi
    exact dite_eq_right hi
  · intro i a ha
    have hi : P.HasLongPacket i := ⟨a,ha⟩
    simpa only [Omega,dite_eq_left hi] using hcontains ⟨i,hi⟩ a ha
  · intro i n
    by_cases hi : P.HasLongPacket i
    · simpa only [Omega,dite_eq_left hi] using hmass ⟨i,hi⟩ n
    · have hzero : Omega i=∅ := dite_eq_right hi
      rw [hzero,preimage_empty,inter_empty,inter_empty,measureReal_empty]
      exact mul_nonneg (mul_nonneg (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) 203)) heta) (by positivity)) (DyadicLineGrid.scale_pos _).le)
        P.width_pos.le


end LipschitzHilbert.SourceLabeledLattice

end

end OAI
