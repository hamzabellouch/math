import OAI.Analysis.LipschitzHilbert.Trees.SourceOrdinarySizeTest

namespace OAI

/-! The actual finite signed size-selection loop. Test directions are
chosen near the extremum; all tiles in the enlarged top are deleted. -/
noncomputable section
open Set
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable Classical.decEq

def sizeDeletePackets (w A : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (R : Finset P.PacketIndex) (T : SlopeBox) : Finset P.PacketIndex :=
  R.filter fun q => P.length q.1≤T.length ∧
    (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈densitySpatialBox T A ∧
    T.slope∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)

theorem sizeTestPackets_subset_delete (negative : Bool) (w cb A : ℝ) (hA : 1/2≤A)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) (R : Finset P.PacketIndex) (T : SlopeBox) :
    P.sizeTestPackets negative w cb cell grid R T⊆P.sizeDeletePackets w A cell grid R T := by
  intro q hq
  obtain ⟨hR,hlen,hpos,hang,_hsign⟩ := Finset.mem_filter.mp hq
  apply Finset.mem_filter.mpr
  refine ⟨hR,hlen,?_,hang⟩
  exact ⟨hpos.1.trans (mul_le_mul_of_nonneg_right hA T.length_pos.le),
    hpos.2.trans (mul_le_mul_of_nonneg_right hA T.width_pos.le)⟩

inductive SizeStoppingRun (negative : Bool) (w cb tau sigma epsilon A : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) :
    Finset P.PacketIndex → List SlopeBox → Finset P.PacketIndex → Prop
  | stop (R : Finset P.PacketIndex)
      (hgood : ∀ T, ¬P.sizeTestFails negative w cb tau sigma cell grid c R T) :
      SizeStoppingRun negative w cb tau sigma epsilon A cell grid c R [] R
  | step (R : Finset P.PacketIndex) (T : SlopeBox) (tops : List SlopeBox)
      (remaining : Finset P.PacketIndex)
      (hfail : P.sizeTestFails negative w cb tau sigma cell grid c R T)
      (hfirst : ∀ U, P.sizeTestFails negative w cb tau sigma cell grid c R U →
        sizeDirection negative T.slope<sizeDirection negative U.slope+epsilon)
      (htail : SizeStoppingRun negative w cb tau sigma epsilon A cell grid c
        (R\P.sizeDeletePackets w A cell grid R T) tops remaining) :
      SizeStoppingRun negative w cb tau sigma epsilon A cell grid c R (T::tops) remaining

theorem exists_size_stopping_run (negative : Bool) (w cb tau sigma epsilon A : ℝ)
    (hw : 0≤w) (hcb : 0≤cb) (hepsilon : 0<epsilon) (hA : 1/2≤A)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (initial : Finset P.PacketIndex) :
    ∃ tops remaining, P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c
      initial tops remaining := by
  induction initial using Finset.strongInductionOn with
  | _ R ih =>
    by_cases hex : ∃ T, P.sizeTestFails negative w cb tau sigma cell grid c R T
    · obtain ⟨T,hT,hfirst⟩ := P.exists_near_first_size_test negative w cb tau sigma epsilon
        hw hcb hepsilon cell grid c R hex
      obtain ⟨q,hq⟩ := P.failing_size_test_nonempty negative w cb tau sigma cell grid c R T hT
      have hqD := P.sizeTestPackets_subset_delete negative w cb A hA cell grid R T hq
      have hqR : q∈R := (Finset.mem_filter.mp hq).1
      have hstrict : R\P.sizeDeletePackets w A cell grid R T⊂R := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨Finset.sdiff_subset,?_⟩
        intro heq
        have hmem : q∈R\P.sizeDeletePackets w A cell grid R T := heq.symm ▸ hqR
        exact (Finset.mem_sdiff.mp hmem).2 hqD
      obtain ⟨tops,remaining,hrun⟩ := ih _ hstrict
      exact ⟨T::tops,remaining,SizeStoppingRun.step R T tops remaining hT hfirst hrun⟩
    · exact ⟨[],R,SizeStoppingRun.stop R (not_exists.mp hex)⟩

namespace SizeStoppingRun
variable {P} {negative : Bool} {w cb tau sigma epsilon A : ℝ}
  {cell : ∀ j, P.labels j → ℤ} {grid : ℤ}
  {c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ}
  {initial remaining : Finset P.PacketIndex} {tops : List SlopeBox}

theorem remaining_subset
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining) :
    remaining⊆initial := by
  induction h with
  | stop => exact Finset.Subset.refl _
  | step R T tops remaining _ _ _ ih => exact ih.trans Finset.sdiff_subset

theorem terminal_good
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining) :
    ∀ T, ¬P.sizeTestFails negative w cb tau sigma cell grid c remaining T := by
  induction h with
  | stop R hg => exact hg
  | step _ _ _ _ _ _ _ ih => exact ih

theorem length_le_card
    (h : P.SizeStoppingRun negative w cb tau sigma epsilon A cell grid c initial tops remaining)
    (hA : 1/2≤A) : tops.length+remaining.card ≤ initial.card := by
  induction h with
  | stop => simp
  | step R T tops remaining hT _ _ ih =>
    obtain ⟨q,hq⟩ := P.failing_size_test_nonempty negative w cb tau sigma cell grid c R T hT
    have hqD := P.sizeTestPackets_subset_delete negative w cb A hA cell grid R T hq
    have hqR : q∈R := (Finset.mem_filter.mp hq).1
    have hstrict : R\P.sizeDeletePackets w A cell grid R T⊂R := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.sdiff_subset,?_⟩
      intro heq
      have hm : q∈R\P.sizeDeletePackets w A cell grid R T := heq.symm ▸ hqR
      exact (Finset.mem_sdiff.mp hm).2 hqD
    have hcard := Finset.card_lt_card hstrict
    simp only [List.length_cons]
    omega

end SizeStoppingRun
end LipschitzHilbert.SourceLabeledLattice

end

end OAI
