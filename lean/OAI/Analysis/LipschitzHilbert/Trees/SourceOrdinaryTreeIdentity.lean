import OAI.Analysis.LipschitzHilbert.Trees.SourceLongErrorGlobal
import OAI.Analysis.LipschitzHilbert.Packets.SourceFrozenTreeGlobal

namespace OAI

/-! The original selected tree is exactly its short part, the frozen
long part, and the long selector error, all on one Whitney partition. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem ordinary_tree_split_identity (hne : Nonempty P.PacketIndex)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (hsupport : ∀ j l k s, selector j l k s≠0 →
      s∈scaledAngularCell (P.width/P.topLength) grid j.val (cell j l))
    (Omega : P.DensityWhitneyCell → Set ℝ)
    (hcontains : ∀ i (q : P.PacketIndex), 32*DyadicLineGrid.scale i.val.1<P.length q.1 →
      scaledAngularCell (P.width/P.topLength) grid q.1.val (cell q.1 q.2.1)⊆Omega i)
    (E : Set (ℝ×ℝ)) :
    E.indicator (fun z => P.physicalTreeSelectorValue 0 c (fun j l k => selector j l k (u z)) z)=
      fun z => E.indicator
        (P.shortTreeValue hne 0 32 (fun q => c q.1 q.2.1 q.2.2) selector u) z+
        P.frozenTreeValue hne (P.frozenSelectorCoefficient c selector) E u Omega z+
        P.longErrorTreeValue hne c selector E u Omega z := by
  classical
  funext z
  let i : P.DensityWhitneyCell := indexAt (Finset.univ : Finset P.PacketIndex)
    (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1)
    (P.packet_univ_nonempty hne) (fun q _ => P.length_pos q.1) z.1
  have hs := P.ordinaryTreeLocal_split c selector u i z
  have hm := P.longOriginalLocal_mask c selector u cell grid hsupport Omega hcontains E i z
  simp only [Set.indicator_apply,shortTreeValue,frozenTreeValue,frozenWhitneyLocal,
    longErrorTreeValue,paste]
  change (if z∈E then P.physicalTreeSelectorValue 0 c (fun j l k => selector j l k (u z)) z else 0)=
    (if z∈E then P.shortLocalValue 0 32 (fun q => c q.1 q.2.1 q.2.2) selector u i z else 0)+
    (if z∈E∩u ⁻¹' Omega i then P.frozenLongValue 0 (DyadicLineGrid.scale i.val.1) P.width
      (u z) (P.frozenSelectorCoefficient c selector) z else 0)+
    (if z∈E∩u ⁻¹' Omega i then P.longErrorLocal c selector u i z else 0)
  by_cases hz : z∈E
  · by_cases hu : u z∈Omega i
    · have ha : z∈E∩u ⁻¹' Omega i := ⟨hz,hu⟩
      simp only [ite_eq_left hz,ite_eq_left ha,longErrorLocal]
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
