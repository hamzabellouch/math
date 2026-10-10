import OAI.Combinatorics.LowSpaceSubsetSum.Storage.OrderedMixerCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.BackgroundPreparationCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredLeafCells
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationLeafArrays

namespace OAI

/-! # Live storage while constructing all leaf profiles

The ordered mixer arrays and completed background rows stay shared through
all eight finite-set profile constructions.
-/

noncomputable section
namespace LowSpaceSubsetSum.LeafArraysCells

variable {n : ℕ}

def run (I : Instance n) (data : RepresentationPrefixArrays.Data n) :
    (Option (RepresentationLeafArrays.Leaves n) × ℕ) × ℕ :=
  let ordered := OrderedMixerCells.run data.layout
  match ordered.1.1 with
  | none => ((none, ordered.1.2+1), ordered.2+16*n+128)
  | some domains =>
    let background := BackgroundPreparationCells.run I data.layout.permutation data.guesses
    match background.1.1 with
    | none => ((none, ordered.1.2+background.1.2+2), ordered.2+background.2+16*n+128)
    | some rows =>
      let out := StoredLeafCells.run domains data.partitions rows data.guesses
      ((some out.1.1, ordered.1.2+background.1.2+out.1.2+3),
        ordered.2+background.2+out.2+16*n+128)

theorem value (I : Instance n) (data : RepresentationPrefixArrays.Data n) :
    (run I data).1 = RepresentationLeafArrays.run I data := by
  have ho₁ := congrArg Prod.fst (OrderedMixerCells.value data.layout)
  have ho₂ := congrArg Prod.snd (OrderedMixerCells.value data.layout)
  have hb₁ := congrArg Prod.fst (BackgroundPreparationCells.value I data.layout.permutation data.guesses)
  have hb₂ := congrArg Prod.snd (BackgroundPreparationCells.value I data.layout.permutation data.guesses)
  simp only [run, RepresentationLeafArrays.run, ho₁, ho₂, hb₁, hb₂]
  split
  · simp_all only
  · split
    · simp_all only
    · simp_all only [StoredLeafCells.value]

theorem cells (I : Instance n) (data : RepresentationPrefixArrays.Data n)
    (hl : ∀ j : Fin 3, data.layout.domains[j.val].length ≤ n) :
    (run I data).2 ≤ 16384*(n+1)^2 := by
  have ho := OrderedMixerCells.cells data.layout hl
  have hb := BackgroundPreparationCells.cells I data.layout.permutation data.guesses
  unfold run
  dsimp only
  split
  · nlinarith only [ho, Nat.zero_le (n^2)]
  next domains hd =>
    split
    · nlinarith only [ho, hb, Nat.zero_le (n^2)]
    next rows hr =>
      have hs : (RepresentationBackgroundPreparation.run I data.layout.permutation data.guesses).1 =
          some rows := by
        rw [← BackgroundPreparationCells.value I data.layout.permutation data.guesses]
        exact hr
      have hw := StoredLeafCells.cells domains data.partitions rows data.guesses
        (RepresentationBackgroundPreparation.lengths I data.layout.permutation data.guesses rows hs)
      change _+_+_+16*n+128 ≤ _
      nlinarith only [ho, hb, hw, Nat.zero_le (n^2)]

end LowSpaceSubsetSum.LeafArraysCells

end

end OAI
