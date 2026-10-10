import OAI.Analysis.LipschitzHilbert.Phase.SourceAngularTreeSplit

namespace OAI

/-! The exact short/frozen/error identity with an independent angular
cutoff, and the corresponding integrated selector error. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable

theorem longOriginalLocal_mask_of_support
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (Omega : P.DensityWhitneyCell → Set ℝ)
    (hsupport : ∀ i (q : P.PacketIndex), 32*DyadicLineGrid.scale i.val.1<P.length q.1 →
      ∀ k s, selector q.1 q.2.1 k s≠0 → s∈Omega i)
    (E : Set (ℝ×ℝ)) (i : P.DensityWhitneyCell) (z : ℝ×ℝ) :
    E.indicator (P.longOriginalLocal c selector u i) z=
      (E∩u ⁻¹' Omega i).indicator (P.longOriginalLocal c selector u i) z := by
  classical
  by_cases hz : z∈E
  · by_cases hu : u z∈Omega i
    · simp only [indicator_of_mem hz,indicator_of_mem (show z∈E∩u ⁻¹' Omega i from ⟨hz,hu⟩)]
    · rw [indicator_of_mem hz,indicator_of_notMem (show z∉E∩u ⁻¹' Omega i from fun h => hu h.2)]
      rw [P.longOriginalLocal_eq_sum]
      apply Finset.sum_eq_zero
      intro q _
      by_cases hq : 32*DyadicLineGrid.scale i.val.1<P.length q.1
      · simp only [ite_eq_left hq]
        have hb (k : κ) : selector q.1 q.2.1 k (u z)=0 := by
          by_contra hk
          exact hu (hsupport i q hq k (u z) hk)
        simp only [ordinaryPacketValue,hb,mul_zero,zero_mul]
        rfl
      · exact ite_eq_right hq
  · rw [indicator_of_notMem hz,indicator_of_notMem (show z∉E∩u ⁻¹' Omega i from fun h => hz h.1)]


theorem masked_ordinary_tree_split_identity (w : ℝ) (hne : Nonempty P.PacketIndex)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (Omega : P.DensityWhitneyCell → Set ℝ)
    (hsupport : ∀ i (q : P.PacketIndex), 32*DyadicLineGrid.scale i.val.1<P.length q.1 →
      ∀ k s, selector q.1 q.2.1 k s≠0 → s∈Omega i)
    (E : Set (ℝ×ℝ)) :
    E.indicator (fun z => P.physicalTreeSelectorValue 0 c (fun j l k => selector j l k (u z)) z)=
      fun z => E.indicator
        (P.shortTreeValue hne 0 32 (fun q => c q.1 q.2.1 q.2.2) selector u) z+
        P.frozenTreeValueAtWidth w hne (P.frozenSelectorCoefficient c selector) E u Omega z+
        P.longErrorTreeValueAtWidth w hne c selector E u Omega z := by
  classical
  funext z
  let i : P.DensityWhitneyCell := indexAt (Finset.univ : Finset P.PacketIndex)
    (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1)
    (P.packet_univ_nonempty hne) (fun q _ => P.length_pos q.1) z.1
  have hs := P.ordinaryTreeLocal_split c selector u i z
  have hm := P.longOriginalLocal_mask_of_support c selector u Omega hsupport E i z
  simp only [Set.indicator_apply,shortTreeValue,frozenTreeValueAtWidth,frozenWhitneyLocalAtWidth,
    longErrorTreeValueAtWidth,paste]
  change (if z∈E then P.physicalTreeSelectorValue 0 c (fun j l k => selector j l k (u z)) z else 0)=
    (if z∈E then P.shortLocalValue 0 32 (fun q => c q.1 q.2.1 q.2.2) selector u i z else 0)+
    (if z∈E∩u ⁻¹' Omega i then P.frozenLongValue 0 (DyadicLineGrid.scale i.val.1) w
      (u z) (P.frozenSelectorCoefficient c selector) z else 0)+
    (if z∈E∩u ⁻¹' Omega i then P.longErrorLocalAtWidth w c selector u i z else 0)
  by_cases hz : z∈E
  · by_cases hu : u z∈Omega i
    · have ha : z∈E∩u ⁻¹' Omega i := ⟨hz,hu⟩
      simp only [ite_eq_left hz,ite_eq_left ha,longErrorLocalAtWidth]
      rw [hs]
      abel
    · have ha : z∉E∩u ⁻¹' Omega i := fun h => hu h.2
      simp only [indicator_of_mem hz,indicator_of_notMem ha] at hm
      simp only [ite_eq_left hz,ite_eq_right ha,add_zero]
      rw [hs,hm,add_zero]
  · have ha : z∉E∩u ⁻¹' Omega i := fun h => hz h.1
    simp only [ite_eq_right hz,ite_eq_right ha,zero_add]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
