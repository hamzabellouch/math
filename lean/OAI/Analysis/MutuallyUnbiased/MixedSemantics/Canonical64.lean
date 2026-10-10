import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw8192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8192Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8192step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8192step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8192step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8192 raw8192Labels = mixedMoment B node5077 node5077Labels := by
  calc
    mixedMoment B raw8192 raw8192Labels = mixedMoment B raw8192step0 raw8192step0Labels := by
      have ha : raw8192step0 = (fun i j => raw8192 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8192step0 raw8192; decide +kernel
      have hl : raw8192step0Labels = raw8192Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8192 raw8192Labels permutation182 permutation3
    mixedMoment B raw8192step0 raw8192step0Labels = mixedMoment B raw8192step1 raw8192step1Labels := by
      have ha : raw8192step1 = raw8192step0 := by apply Matrix.ext; unfold raw8192step1 raw8192step0; decide +kernel
      have hl : raw8192step0Labels = labelEmbedding6 ∘ raw8192step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8192step0 raw8192step0Labels raw8192step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5077 node5077Labels := by rfl

def raw8193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8193Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8193step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8193step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8193step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8193step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8193 raw8193Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw8193 raw8193Labels = mixedMoment B raw8193step0 raw8193step0Labels := by
      have hz : ∀ j, raw8193 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8193step0 = (fun i j => raw8193 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8193step0 raw8193; decide +kernel
      have hl : raw8193step0Labels = raw8193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8193 raw8193Labels permutation346 hz
    mixedMoment B raw8193step0 raw8193step0Labels = mixedMoment B raw8193step1 raw8193step1Labels := by
      have ha : raw8193step1 = (fun i j => raw8193step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8193step1 raw8193step0; decide +kernel
      have hl : raw8193step1Labels = raw8193step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8193step0 raw8193step0Labels permutation38 permutation3
    mixedMoment B raw8193step1 raw8193step1Labels = mixedMoment B raw8193step2 raw8193step2Labels := by
      have ha : raw8193step2 = raw8193step1 := by apply Matrix.ext; unfold raw8193step2 raw8193step1; decide +kernel
      have hl : raw8193step1Labels = labelEmbedding6 ∘ raw8193step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8193step1 raw8193step1Labels raw8193step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5173 node5173Labels := by rfl

def raw8194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8194Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8194step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8194step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8194step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8194step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8194 raw8194Labels = mixedMoment B node5288 node5288Labels := by
  calc
    mixedMoment B raw8194 raw8194Labels = mixedMoment B raw8194step0 raw8194step0Labels := by
      have hz : ∀ j, raw8194 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8194step0 = (fun i j => raw8194 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8194step0 raw8194; decide +kernel
      have hl : raw8194step0Labels = raw8194Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8194 raw8194Labels permutation346 hz
    mixedMoment B raw8194step0 raw8194step0Labels = mixedMoment B raw8194step1 raw8194step1Labels := by
      have ha : raw8194step1 = (fun i j => raw8194step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8194step1 raw8194step0; decide +kernel
      have hl : raw8194step1Labels = raw8194step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8194step0 raw8194step0Labels permutation42 permutation3
    mixedMoment B raw8194step1 raw8194step1Labels = mixedMoment B raw8194step2 raw8194step2Labels := by
      have ha : raw8194step2 = raw8194step1 := by apply Matrix.ext; unfold raw8194step2 raw8194step1; decide +kernel
      have hl : raw8194step1Labels = labelEmbedding6 ∘ raw8194step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8194step1 raw8194step1Labels raw8194step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5288 node5288Labels := by rfl

def raw8195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8195Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8195step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8195step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8195step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8195step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8195 raw8195Labels = mixedMoment B node4462 node4462Labels := by
  calc
    mixedMoment B raw8195 raw8195Labels = mixedMoment B raw8195step0 raw8195step0Labels := by
      have hz : ∀ j, raw8195 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8195step0 = (fun i j => raw8195 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8195step0 raw8195; decide +kernel
      have hl : raw8195step0Labels = raw8195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8195 raw8195Labels permutation265 hz
    mixedMoment B raw8195step0 raw8195step0Labels = mixedMoment B raw8195step1 raw8195step1Labels := by
      have ha : raw8195step1 = (fun i j => raw8195step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8195step1 raw8195step0; decide +kernel
      have hl : raw8195step1Labels = raw8195step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8195step0 raw8195step0Labels permutation38 permutation3
    mixedMoment B raw8195step1 raw8195step1Labels = mixedMoment B raw8195step2 raw8195step2Labels := by
      have ha : raw8195step2 = raw8195step1 := by apply Matrix.ext; unfold raw8195step2 raw8195step1; decide +kernel
      have hl : raw8195step1Labels = labelEmbedding6 ∘ raw8195step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8195step1 raw8195step1Labels raw8195step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4462 node4462Labels := by rfl

def raw8196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8196Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8196step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8196step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8196step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8196 raw8196Labels = mixedMoment B node5077 node5077Labels := by
  calc
    mixedMoment B raw8196 raw8196Labels = mixedMoment B raw8196step0 raw8196step0Labels := by
      have ha : raw8196step0 = (fun i j => raw8196 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8196step0 raw8196; decide +kernel
      have hl : raw8196step0Labels = raw8196Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8196 raw8196Labels permutation158 permutation3
    mixedMoment B raw8196step0 raw8196step0Labels = mixedMoment B raw8196step1 raw8196step1Labels := by
      have ha : raw8196step1 = raw8196step0 := by apply Matrix.ext; unfold raw8196step1 raw8196step0; decide +kernel
      have hl : raw8196step0Labels = labelEmbedding6 ∘ raw8196step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8196step0 raw8196step0Labels raw8196step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5077 node5077Labels := by rfl

def raw8197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8197Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8197step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8197step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8197step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8197step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8197step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8197 raw8197Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw8197 raw8197Labels = mixedMoment B raw8197step0 raw8197step0Labels := by
      have hz : ∀ j, raw8197 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8197step0 = (fun i j => raw8197 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8197step0 raw8197; decide +kernel
      have hl : raw8197step0Labels = raw8197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8197 raw8197Labels permutation265 hz
    mixedMoment B raw8197step0 raw8197step0Labels = mixedMoment B raw8197step1 raw8197step1Labels := by
      have ha : raw8197step1 = (fun i j => raw8197step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8197step1 raw8197step0; decide +kernel
      have hl : raw8197step1Labels = raw8197step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8197step0 raw8197step0Labels permutation38 permutation3
    mixedMoment B raw8197step1 raw8197step1Labels = mixedMoment B raw8197step2 raw8197step2Labels := by
      have ha : raw8197step2 = raw8197step1 := by apply Matrix.ext; unfold raw8197step2 raw8197step1; decide +kernel
      have hl : raw8197step1Labels = labelEmbedding6 ∘ raw8197step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8197step1 raw8197step1Labels raw8197step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5173 node5173Labels := by rfl

def raw8198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8198Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8198step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8198step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8198step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8198 raw8198Labels = mixedMoment B node5288 node5288Labels := by
  calc
    mixedMoment B raw8198 raw8198Labels = mixedMoment B raw8198step0 raw8198step0Labels := by
      have hz : ∀ j, raw8198 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8198step0 = (fun i j => raw8198 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8198step0 raw8198; decide +kernel
      have hl : raw8198step0Labels = raw8198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8198 raw8198Labels permutation265 hz
    mixedMoment B raw8198step0 raw8198step0Labels = mixedMoment B raw8198step1 raw8198step1Labels := by
      have ha : raw8198step1 = (fun i j => raw8198step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8198step1 raw8198step0; decide +kernel
      have hl : raw8198step1Labels = raw8198step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8198step0 raw8198step0Labels permutation42 permutation3
    mixedMoment B raw8198step1 raw8198step1Labels = mixedMoment B raw8198step2 raw8198step2Labels := by
      have ha : raw8198step2 = raw8198step1 := by apply Matrix.ext; unfold raw8198step2 raw8198step1; decide +kernel
      have hl : raw8198step1Labels = labelEmbedding6 ∘ raw8198step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8198step1 raw8198step1Labels raw8198step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5288 node5288Labels := by rfl

def raw8199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8199Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8199step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8199step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8199step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8199step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw8199step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8199step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw8199step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8199 raw8199Labels = mixedMoment B node4506 node4506Labels := by
  calc
    mixedMoment B raw8199 raw8199Labels = mixedMoment B raw8199step0 raw8199step0Labels := by
      have hz : ∀ j, raw8199 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8199step0 = (fun i j => raw8199 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8199step0 raw8199; decide +kernel
      have hl : raw8199step0Labels = raw8199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8199 raw8199Labels permutation346 hz
    mixedMoment B raw8199step0 raw8199step0Labels = mixedMoment B raw8199step1 raw8199step1Labels := by
      have hz : ∀ j, raw8199step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8199step1 = (fun i j => raw8199step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8199step1 raw8199step0; decide +kernel
      have hl : raw8199step1Labels = raw8199step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8199step0 raw8199step0Labels permutation56 hz
    mixedMoment B raw8199step1 raw8199step1Labels = mixedMoment B raw8199step2 raw8199step2Labels := by
      have ha : raw8199step2 = (fun i j => raw8199step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8199step2 raw8199step1; decide +kernel
      have hl : raw8199step2Labels = raw8199step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8199step1 raw8199step1Labels permutation8 permutation3
    mixedMoment B raw8199step2 raw8199step2Labels = mixedMoment B raw8199step3 raw8199step3Labels := by
      have ha : raw8199step3 = raw8199step2 := by apply Matrix.ext; unfold raw8199step3 raw8199step2; decide +kernel
      have hl : raw8199step2Labels = labelEmbedding6 ∘ raw8199step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8199step2 raw8199step2Labels raw8199step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4506 node4506Labels := by rfl

def raw8200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8200step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw8200step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8200step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw8200step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8200 raw8200Labels = mixedMoment B node5108 node5108Labels := by
  calc
    mixedMoment B raw8200 raw8200Labels = mixedMoment B raw8200step0 raw8200step0Labels := by
      have hz : ∀ j, raw8200 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8200step0 = (fun i j => raw8200 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8200step0 raw8200; decide +kernel
      have hl : raw8200step0Labels = raw8200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8200 raw8200Labels permutation346 hz
    mixedMoment B raw8200step0 raw8200step0Labels = mixedMoment B raw8200step1 raw8200step1Labels := by
      have ha : raw8200step1 = (fun i j => raw8200step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8200step1 raw8200step0; decide +kernel
      have hl : raw8200step1Labels = raw8200step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8200step0 raw8200step0Labels permutation32 permutation3
    mixedMoment B raw8200step1 raw8200step1Labels = mixedMoment B raw8200step2 raw8200step2Labels := by
      have ha : raw8200step2 = raw8200step1 := by apply Matrix.ext; unfold raw8200step2 raw8200step1; decide +kernel
      have hl : raw8200step1Labels = labelEmbedding6 ∘ raw8200step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8200step1 raw8200step1Labels raw8200step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5108 node5108Labels := by rfl

def raw8201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8201Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8201step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8201step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw8201step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8201step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw8201step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8201 raw8201Labels = mixedMoment B node5108 node5108Labels := by
  calc
    mixedMoment B raw8201 raw8201Labels = mixedMoment B raw8201step0 raw8201step0Labels := by
      have hz : ∀ j, raw8201 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8201step0 = (fun i j => raw8201 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8201step0 raw8201; decide +kernel
      have hl : raw8201step0Labels = raw8201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8201 raw8201Labels permutation265 hz
    mixedMoment B raw8201step0 raw8201step0Labels = mixedMoment B raw8201step1 raw8201step1Labels := by
      have ha : raw8201step1 = (fun i j => raw8201step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8201step1 raw8201step0; decide +kernel
      have hl : raw8201step1Labels = raw8201step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8201step0 raw8201step0Labels permutation32 permutation3
    mixedMoment B raw8201step1 raw8201step1Labels = mixedMoment B raw8201step2 raw8201step2Labels := by
      have ha : raw8201step2 = raw8201step1 := by apply Matrix.ext; unfold raw8201step2 raw8201step1; decide +kernel
      have hl : raw8201step1Labels = labelEmbedding6 ∘ raw8201step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8201step1 raw8201step1Labels raw8201step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5108 node5108Labels := by rfl

def raw8202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8202step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8202step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8202step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8202step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw8202step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8202step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw8202step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8202 raw8202Labels = mixedMoment B node5303 node5303Labels := by
  calc
    mixedMoment B raw8202 raw8202Labels = mixedMoment B raw8202step0 raw8202step0Labels := by
      have hz : ∀ j, raw8202 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8202step0 = (fun i j => raw8202 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8202step0 raw8202; decide +kernel
      have hl : raw8202step0Labels = raw8202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8202 raw8202Labels permutation346 hz
    mixedMoment B raw8202step0 raw8202step0Labels = mixedMoment B raw8202step1 raw8202step1Labels := by
      have hz : ∀ j, raw8202step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8202step1 = (fun i j => raw8202step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8202step1 raw8202step0; decide +kernel
      have hl : raw8202step1Labels = raw8202step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8202step0 raw8202step0Labels permutation56 hz
    mixedMoment B raw8202step1 raw8202step1Labels = mixedMoment B raw8202step2 raw8202step2Labels := by
      have ha : raw8202step2 = (fun i j => raw8202step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8202step2 raw8202step1; decide +kernel
      have hl : raw8202step2Labels = raw8202step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8202step1 raw8202step1Labels permutation12 permutation3
    mixedMoment B raw8202step2 raw8202step2Labels = mixedMoment B raw8202step3 raw8202step3Labels := by
      have ha : raw8202step3 = raw8202step2 := by apply Matrix.ext; unfold raw8202step3 raw8202step2; decide +kernel
      have hl : raw8202step2Labels = labelEmbedding6 ∘ raw8202step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8202step2 raw8202step2Labels raw8202step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5303 node5303Labels := by rfl

def raw8203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8203Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8203step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8203step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8203step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8203step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw8203step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8203step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw8203step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8203 raw8203Labels = mixedMoment B node4465 node4465Labels := by
  calc
    mixedMoment B raw8203 raw8203Labels = mixedMoment B raw8203step0 raw8203step0Labels := by
      have hz : ∀ j, raw8203 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8203step0 = (fun i j => raw8203 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8203step0 raw8203; decide +kernel
      have hl : raw8203step0Labels = raw8203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8203 raw8203Labels permutation346 hz
    mixedMoment B raw8203step0 raw8203step0Labels = mixedMoment B raw8203step1 raw8203step1Labels := by
      have hz : ∀ j, raw8203step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8203step1 = (fun i j => raw8203step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8203step1 raw8203step0; decide +kernel
      have hl : raw8203step1Labels = raw8203step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8203step0 raw8203step0Labels permutation56 hz
    mixedMoment B raw8203step1 raw8203step1Labels = mixedMoment B raw8203step2 raw8203step2Labels := by
      have ha : raw8203step2 = (fun i j => raw8203step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8203step2 raw8203step1; decide +kernel
      have hl : raw8203step2Labels = raw8203step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8203step1 raw8203step1Labels permutation9 permutation3
    mixedMoment B raw8203step2 raw8203step2Labels = mixedMoment B raw8203step3 raw8203step3Labels := by
      have ha : raw8203step3 = raw8203step2 := by apply Matrix.ext; unfold raw8203step3 raw8203step2; decide +kernel
      have hl : raw8203step2Labels = labelEmbedding6 ∘ raw8203step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8203step2 raw8203step2Labels raw8203step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4465 node4465Labels := by rfl

def raw8204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8204Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8204step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8204step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw8204step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8204step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw8204step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8204 raw8204Labels = mixedMoment B node5079 node5079Labels := by
  calc
    mixedMoment B raw8204 raw8204Labels = mixedMoment B raw8204step0 raw8204step0Labels := by
      have hz : ∀ j, raw8204 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8204step0 = (fun i j => raw8204 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8204step0 raw8204; decide +kernel
      have hl : raw8204step0Labels = raw8204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8204 raw8204Labels permutation346 hz
    mixedMoment B raw8204step0 raw8204step0Labels = mixedMoment B raw8204step1 raw8204step1Labels := by
      have ha : raw8204step1 = (fun i j => raw8204step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8204step1 raw8204step0; decide +kernel
      have hl : raw8204step1Labels = raw8204step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8204step0 raw8204step0Labels permutation33 permutation3
    mixedMoment B raw8204step1 raw8204step1Labels = mixedMoment B raw8204step2 raw8204step2Labels := by
      have ha : raw8204step2 = raw8204step1 := by apply Matrix.ext; unfold raw8204step2 raw8204step1; decide +kernel
      have hl : raw8204step1Labels = labelEmbedding6 ∘ raw8204step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8204step1 raw8204step1Labels raw8204step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5079 node5079Labels := by rfl

def raw8205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8205Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8205step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8205step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw8205step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8205step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw8205step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8205 raw8205Labels = mixedMoment B node5079 node5079Labels := by
  calc
    mixedMoment B raw8205 raw8205Labels = mixedMoment B raw8205step0 raw8205step0Labels := by
      have hz : ∀ j, raw8205 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8205step0 = (fun i j => raw8205 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8205step0 raw8205; decide +kernel
      have hl : raw8205step0Labels = raw8205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8205 raw8205Labels permutation265 hz
    mixedMoment B raw8205step0 raw8205step0Labels = mixedMoment B raw8205step1 raw8205step1Labels := by
      have ha : raw8205step1 = (fun i j => raw8205step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8205step1 raw8205step0; decide +kernel
      have hl : raw8205step1Labels = raw8205step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8205step0 raw8205step0Labels permutation33 permutation3
    mixedMoment B raw8205step1 raw8205step1Labels = mixedMoment B raw8205step2 raw8205step2Labels := by
      have ha : raw8205step2 = raw8205step1 := by apply Matrix.ext; unfold raw8205step2 raw8205step1; decide +kernel
      have hl : raw8205step1Labels = labelEmbedding6 ∘ raw8205step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8205step1 raw8205step1Labels raw8205step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5079 node5079Labels := by rfl

def raw8206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8206Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8206step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8206step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8206step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8206step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw8206step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8206step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw8206step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8206 raw8206Labels = mixedMoment B node5175 node5175Labels := by
  calc
    mixedMoment B raw8206 raw8206Labels = mixedMoment B raw8206step0 raw8206step0Labels := by
      have hz : ∀ j, raw8206 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8206step0 = (fun i j => raw8206 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8206step0 raw8206; decide +kernel
      have hl : raw8206step0Labels = raw8206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8206 raw8206Labels permutation346 hz
    mixedMoment B raw8206step0 raw8206step0Labels = mixedMoment B raw8206step1 raw8206step1Labels := by
      have hz : ∀ j, raw8206step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8206step1 = (fun i j => raw8206step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8206step1 raw8206step0; decide +kernel
      have hl : raw8206step1Labels = raw8206step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8206step0 raw8206step0Labels permutation56 hz
    mixedMoment B raw8206step1 raw8206step1Labels = mixedMoment B raw8206step2 raw8206step2Labels := by
      have ha : raw8206step2 = (fun i j => raw8206step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8206step2 raw8206step1; decide +kernel
      have hl : raw8206step2Labels = raw8206step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8206step1 raw8206step1Labels permutation9 permutation3
    mixedMoment B raw8206step2 raw8206step2Labels = mixedMoment B raw8206step3 raw8206step3Labels := by
      have ha : raw8206step3 = raw8206step2 := by apply Matrix.ext; unfold raw8206step3 raw8206step2; decide +kernel
      have hl : raw8206step2Labels = labelEmbedding6 ∘ raw8206step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8206step2 raw8206step2Labels raw8206step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5175 node5175Labels := by rfl

def raw8207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![1, 2, -3]]
def raw8207Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![1, 2, -3]]
def raw8207step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8207step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -3, 1], ![1, 2, -3]]
def raw8207step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8207step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw8207step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw8207step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw8207step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8207 raw8207Labels = mixedMoment B node5175 node5175Labels := by
  calc
    mixedMoment B raw8207 raw8207Labels = mixedMoment B raw8207step0 raw8207step0Labels := by
      have hz : ∀ j, raw8207 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8207step0 = (fun i j => raw8207 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8207step0 raw8207; decide +kernel
      have hl : raw8207step0Labels = raw8207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8207 raw8207Labels permutation346 hz
    mixedMoment B raw8207step0 raw8207step0Labels = mixedMoment B raw8207step1 raw8207step1Labels := by
      have hz : ∀ j, raw8207step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8207step1 = (fun i j => raw8207step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8207step1 raw8207step0; decide +kernel
      have hl : raw8207step1Labels = raw8207step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8207step0 raw8207step0Labels permutation56 hz
    mixedMoment B raw8207step1 raw8207step1Labels = mixedMoment B raw8207step2 raw8207step2Labels := by
      have ha : raw8207step2 = (fun i j => raw8207step1 (permutation23 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8207step2 raw8207step1; decide +kernel
      have hl : raw8207step2Labels = raw8207step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8207step1 raw8207step1Labels permutation23 permutation5
    mixedMoment B raw8207step2 raw8207step2Labels = mixedMoment B raw8207step3 raw8207step3Labels := by
      have ha : raw8207step3 = raw8207step2 := by apply Matrix.ext; unfold raw8207step3 raw8207step2; decide +kernel
      have hl : raw8207step2Labels = labelEmbedding8 ∘ raw8207step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8207step2 raw8207step2Labels raw8207step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5175 node5175Labels := by rfl

def raw8208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw8208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw8208step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8208step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw8208step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8208step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw8208step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8208step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw8208step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8208 raw8208Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw8208 raw8208Labels = mixedMoment B raw8208step0 raw8208step0Labels := by
      have hz : ∀ j, raw8208 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8208step0 = (fun i j => raw8208 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8208step0 raw8208; decide +kernel
      have hl : raw8208step0Labels = raw8208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8208 raw8208Labels permutation346 hz
    mixedMoment B raw8208step0 raw8208step0Labels = mixedMoment B raw8208step1 raw8208step1Labels := by
      have hz : ∀ j, raw8208step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8208step1 = (fun i j => raw8208step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8208step1 raw8208step0; decide +kernel
      have hl : raw8208step1Labels = raw8208step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8208step0 raw8208step0Labels permutation56 hz
    mixedMoment B raw8208step1 raw8208step1Labels = mixedMoment B raw8208step2 raw8208step2Labels := by
      have ha : raw8208step2 = (fun i j => raw8208step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8208step2 raw8208step1; decide +kernel
      have hl : raw8208step2Labels = raw8208step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8208step1 raw8208step1Labels permutation29 permutation2
    mixedMoment B raw8208step2 raw8208step2Labels = mixedMoment B raw8208step3 raw8208step3Labels := by
      have ha : raw8208step3 = -raw8208step2 := by apply Matrix.ext; change ∀ i j, raw8208step3 i j = -(raw8208step2 i j); unfold raw8208step3 raw8208step2; decide +kernel
      have hl : raw8208step3Labels = raw8208step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4890 node4890Labels := by rfl

def raw8209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8209Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8209step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8209step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8209step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8209 raw8209Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw8209 raw8209Labels = mixedMoment B raw8209step0 raw8209step0Labels := by
      have hz : ∀ j, raw8209 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8209step0 = (fun i j => raw8209 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8209step0 raw8209; decide +kernel
      have hl : raw8209step0Labels = raw8209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8209 raw8209Labels permutation346 hz
    mixedMoment B raw8209step0 raw8209step0Labels = mixedMoment B raw8209step1 raw8209step1Labels := by
      have ha : raw8209step1 = (fun i j => raw8209step0 (permutation134 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8209step1 raw8209step0; decide +kernel
      have hl : raw8209step1Labels = raw8209step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8209step0 raw8209step0Labels permutation134 permutation6
    _ = mixedMoment B node3097 node3097Labels := by rfl

def raw8210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8210Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8210step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8210step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8210step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8210 raw8210Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw8210 raw8210Labels = mixedMoment B raw8210step0 raw8210step0Labels := by
      have hz : ∀ j, raw8210 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8210step0 = (fun i j => raw8210 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8210step0 raw8210; decide +kernel
      have hl : raw8210step0Labels = raw8210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8210 raw8210Labels permutation265 hz
    mixedMoment B raw8210step0 raw8210step0Labels = mixedMoment B raw8210step1 raw8210step1Labels := by
      have ha : raw8210step1 = (fun i j => raw8210step0 (permutation134 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8210step1 raw8210step0; decide +kernel
      have hl : raw8210step1Labels = raw8210step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8210step0 raw8210step0Labels permutation134 permutation6
    _ = mixedMoment B node3097 node3097Labels := by rfl

def raw8211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8211Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8211step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8211step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8211step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8211step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8211step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8211 raw8211Labels = mixedMoment B node3119 node3119Labels := by
  calc
    mixedMoment B raw8211 raw8211Labels = mixedMoment B raw8211step0 raw8211step0Labels := by
      have hz : ∀ j, raw8211 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8211step0 = (fun i j => raw8211 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8211step0 raw8211; decide +kernel
      have hl : raw8211step0Labels = raw8211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8211 raw8211Labels permutation346 hz
    mixedMoment B raw8211step0 raw8211step0Labels = mixedMoment B raw8211step1 raw8211step1Labels := by
      have hz : ∀ j, raw8211step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8211step1 = (fun i j => raw8211step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8211step1 raw8211step0; decide +kernel
      have hl : raw8211step1Labels = raw8211step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8211step0 raw8211step0Labels permutation56 hz
    mixedMoment B raw8211step1 raw8211step1Labels = mixedMoment B raw8211step2 raw8211step2Labels := by
      have ha : raw8211step2 = (fun i j => raw8211step1 (permutation26 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8211step2 raw8211step1; decide +kernel
      have hl : raw8211step2Labels = raw8211step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8211step1 raw8211step1Labels permutation26 permutation6
    _ = mixedMoment B node3119 node3119Labels := by rfl

def raw8212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8212Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8212step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8212step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8212step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8212step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8212step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8212 raw8212Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw8212 raw8212Labels = mixedMoment B raw8212step0 raw8212step0Labels := by
      have hz : ∀ j, raw8212 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8212step0 = (fun i j => raw8212 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8212step0 raw8212; decide +kernel
      have hl : raw8212step0Labels = raw8212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8212 raw8212Labels permutation346 hz
    mixedMoment B raw8212step0 raw8212step0Labels = mixedMoment B raw8212step1 raw8212step1Labels := by
      have hz : ∀ j, raw8212step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8212step1 = (fun i j => raw8212step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8212step1 raw8212step0; decide +kernel
      have hl : raw8212step1Labels = raw8212step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8212step0 raw8212step0Labels permutation56 hz
    mixedMoment B raw8212step1 raw8212step1Labels = mixedMoment B raw8212step2 raw8212step2Labels := by
      have ha : raw8212step2 = (fun i j => raw8212step1 (permutation26 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8212step2 raw8212step1; decide +kernel
      have hl : raw8212step2Labels = raw8212step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8212step1 raw8212step1Labels permutation26 permutation6
    _ = mixedMoment B node2782 node2782Labels := by rfl

def raw8213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8213Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8213step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8213step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8213step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8213 raw8213Labels = mixedMoment B node1045 node1045Labels := by
  calc
    mixedMoment B raw8213 raw8213Labels = mixedMoment B raw8213step0 raw8213step0Labels := by
      have hz : ∀ j, raw8213 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8213step0 = (fun i j => raw8213 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8213step0 raw8213; decide +kernel
      have hl : raw8213step0Labels = raw8213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8213 raw8213Labels permutation346 hz
    mixedMoment B raw8213step0 raw8213step0Labels = mixedMoment B raw8213step1 raw8213step1Labels := by
      have ha : raw8213step1 = (fun i j => raw8213step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8213step1 raw8213step0; decide +kernel
      have hl : raw8213step1Labels = raw8213step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8213step0 raw8213step0Labels permutation38 permutation3
    _ = mixedMoment B node1045 node1045Labels := by rfl

def raw8214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8214Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8214step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8214step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8214 raw8214Labels = mixedMoment B node2484 node2484Labels := by
  calc
    mixedMoment B raw8214 raw8214Labels = mixedMoment B raw8214step0 raw8214step0Labels := by
      have ha : raw8214step0 = (fun i j => raw8214 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8214step0 raw8214; decide +kernel
      have hl : raw8214step0Labels = raw8214Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8214 raw8214Labels permutation182 permutation3
    _ = mixedMoment B node2484 node2484Labels := by rfl

def raw8215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8215Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8215step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8215step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8215step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8215 raw8215Labels = mixedMoment B node2600 node2600Labels := by
  calc
    mixedMoment B raw8215 raw8215Labels = mixedMoment B raw8215step0 raw8215step0Labels := by
      have hz : ∀ j, raw8215 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8215step0 = (fun i j => raw8215 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8215step0 raw8215; decide +kernel
      have hl : raw8215step0Labels = raw8215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8215 raw8215Labels permutation346 hz
    mixedMoment B raw8215step0 raw8215step0Labels = mixedMoment B raw8215step1 raw8215step1Labels := by
      have ha : raw8215step1 = (fun i j => raw8215step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8215step1 raw8215step0; decide +kernel
      have hl : raw8215step1Labels = raw8215step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8215step0 raw8215step0Labels permutation38 permutation3
    _ = mixedMoment B node2600 node2600Labels := by rfl

def raw8216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8216Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8216step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8216step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8216 raw8216Labels = mixedMoment B node2760 node2760Labels := by
  calc
    mixedMoment B raw8216 raw8216Labels = mixedMoment B raw8216step0 raw8216step0Labels := by
      have hz : ∀ j, raw8216 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8216step0 = (fun i j => raw8216 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8216step0 raw8216; decide +kernel
      have hl : raw8216step0Labels = raw8216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8216 raw8216Labels permutation346 hz
    mixedMoment B raw8216step0 raw8216step0Labels = mixedMoment B raw8216step1 raw8216step1Labels := by
      have ha : raw8216step1 = (fun i j => raw8216step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8216step1 raw8216step0; decide +kernel
      have hl : raw8216step1Labels = raw8216step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8216step0 raw8216step0Labels permutation42 permutation3
    _ = mixedMoment B node2760 node2760Labels := by rfl

def raw8217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8217Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8217step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8217step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8217 raw8217Labels = mixedMoment B node1045 node1045Labels := by
  calc
    mixedMoment B raw8217 raw8217Labels = mixedMoment B raw8217step0 raw8217step0Labels := by
      have hz : ∀ j, raw8217 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8217step0 = (fun i j => raw8217 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8217step0 raw8217; decide +kernel
      have hl : raw8217step0Labels = raw8217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8217 raw8217Labels permutation265 hz
    mixedMoment B raw8217step0 raw8217step0Labels = mixedMoment B raw8217step1 raw8217step1Labels := by
      have ha : raw8217step1 = (fun i j => raw8217step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8217step1 raw8217step0; decide +kernel
      have hl : raw8217step1Labels = raw8217step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8217step0 raw8217step0Labels permutation38 permutation3
    _ = mixedMoment B node1045 node1045Labels := by rfl

def raw8218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8218Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8218step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8218 raw8218Labels = mixedMoment B node2484 node2484Labels := by
  calc
    mixedMoment B raw8218 raw8218Labels = mixedMoment B raw8218step0 raw8218step0Labels := by
      have ha : raw8218step0 = (fun i j => raw8218 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8218step0 raw8218; decide +kernel
      have hl : raw8218step0Labels = raw8218Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8218 raw8218Labels permutation158 permutation3
    _ = mixedMoment B node2484 node2484Labels := by rfl

def raw8219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8219Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8219step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8219step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8219step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8219 raw8219Labels = mixedMoment B node2600 node2600Labels := by
  calc
    mixedMoment B raw8219 raw8219Labels = mixedMoment B raw8219step0 raw8219step0Labels := by
      have hz : ∀ j, raw8219 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8219step0 = (fun i j => raw8219 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8219step0 raw8219; decide +kernel
      have hl : raw8219step0Labels = raw8219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8219 raw8219Labels permutation265 hz
    mixedMoment B raw8219step0 raw8219step0Labels = mixedMoment B raw8219step1 raw8219step1Labels := by
      have ha : raw8219step1 = (fun i j => raw8219step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8219step1 raw8219step0; decide +kernel
      have hl : raw8219step1Labels = raw8219step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8219step0 raw8219step0Labels permutation38 permutation3
    _ = mixedMoment B node2600 node2600Labels := by rfl

def raw8220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8220Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8220step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw8220step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8220 raw8220Labels = mixedMoment B node2760 node2760Labels := by
  calc
    mixedMoment B raw8220 raw8220Labels = mixedMoment B raw8220step0 raw8220step0Labels := by
      have hz : ∀ j, raw8220 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8220step0 = (fun i j => raw8220 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8220step0 raw8220; decide +kernel
      have hl : raw8220step0Labels = raw8220Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8220 raw8220Labels permutation265 hz
    mixedMoment B raw8220step0 raw8220step0Labels = mixedMoment B raw8220step1 raw8220step1Labels := by
      have ha : raw8220step1 = (fun i j => raw8220step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8220step1 raw8220step0; decide +kernel
      have hl : raw8220step1Labels = raw8220step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8220step0 raw8220step0Labels permutation42 permutation3
    _ = mixedMoment B node2760 node2760Labels := by rfl

def raw8221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8221Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8221step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8221step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8221step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8221step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw8221step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8221 raw8221Labels = mixedMoment B node1090 node1090Labels := by
  calc
    mixedMoment B raw8221 raw8221Labels = mixedMoment B raw8221step0 raw8221step0Labels := by
      have hz : ∀ j, raw8221 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8221step0 = (fun i j => raw8221 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8221step0 raw8221; decide +kernel
      have hl : raw8221step0Labels = raw8221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8221 raw8221Labels permutation346 hz
    mixedMoment B raw8221step0 raw8221step0Labels = mixedMoment B raw8221step1 raw8221step1Labels := by
      have hz : ∀ j, raw8221step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8221step1 = (fun i j => raw8221step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8221step1 raw8221step0; decide +kernel
      have hl : raw8221step1Labels = raw8221step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8221step0 raw8221step0Labels permutation56 hz
    mixedMoment B raw8221step1 raw8221step1Labels = mixedMoment B raw8221step2 raw8221step2Labels := by
      have ha : raw8221step2 = (fun i j => raw8221step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8221step2 raw8221step1; decide +kernel
      have hl : raw8221step2Labels = raw8221step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8221step1 raw8221step1Labels permutation8 permutation3
    _ = mixedMoment B node1090 node1090Labels := by rfl

def raw8222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8222Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8222step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8222step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw8222step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8222 raw8222Labels = mixedMoment B node2518 node2518Labels := by
  calc
    mixedMoment B raw8222 raw8222Labels = mixedMoment B raw8222step0 raw8222step0Labels := by
      have hz : ∀ j, raw8222 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8222step0 = (fun i j => raw8222 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8222step0 raw8222; decide +kernel
      have hl : raw8222step0Labels = raw8222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8222 raw8222Labels permutation346 hz
    mixedMoment B raw8222step0 raw8222step0Labels = mixedMoment B raw8222step1 raw8222step1Labels := by
      have ha : raw8222step1 = (fun i j => raw8222step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8222step1 raw8222step0; decide +kernel
      have hl : raw8222step1Labels = raw8222step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8222step0 raw8222step0Labels permutation32 permutation3
    _ = mixedMoment B node2518 node2518Labels := by rfl

def raw8223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8223Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8223step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw8223step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8223 raw8223Labels = mixedMoment B node2518 node2518Labels := by
  calc
    mixedMoment B raw8223 raw8223Labels = mixedMoment B raw8223step0 raw8223step0Labels := by
      have hz : ∀ j, raw8223 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8223step0 = (fun i j => raw8223 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8223step0 raw8223; decide +kernel
      have hl : raw8223step0Labels = raw8223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8223 raw8223Labels permutation265 hz
    mixedMoment B raw8223step0 raw8223step0Labels = mixedMoment B raw8223step1 raw8223step1Labels := by
      have ha : raw8223step1 = (fun i j => raw8223step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8223step1 raw8223step0; decide +kernel
      have hl : raw8223step1Labels = raw8223step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8223step0 raw8223step0Labels permutation32 permutation3
    _ = mixedMoment B node2518 node2518Labels := by rfl

def raw8224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8224Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8224step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8224step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8224step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8224step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw8224step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8224 raw8224Labels = mixedMoment B node2779 node2779Labels := by
  calc
    mixedMoment B raw8224 raw8224Labels = mixedMoment B raw8224step0 raw8224step0Labels := by
      have hz : ∀ j, raw8224 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8224step0 = (fun i j => raw8224 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8224step0 raw8224; decide +kernel
      have hl : raw8224step0Labels = raw8224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8224 raw8224Labels permutation346 hz
    mixedMoment B raw8224step0 raw8224step0Labels = mixedMoment B raw8224step1 raw8224step1Labels := by
      have hz : ∀ j, raw8224step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8224step1 = (fun i j => raw8224step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8224step1 raw8224step0; decide +kernel
      have hl : raw8224step1Labels = raw8224step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8224step0 raw8224step0Labels permutation56 hz
    mixedMoment B raw8224step1 raw8224step1Labels = mixedMoment B raw8224step2 raw8224step2Labels := by
      have ha : raw8224step2 = (fun i j => raw8224step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8224step2 raw8224step1; decide +kernel
      have hl : raw8224step2Labels = raw8224step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8224step1 raw8224step1Labels permutation12 permutation3
    _ = mixedMoment B node2779 node2779Labels := by rfl

def raw8225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8225Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8225step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8225step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8225step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8225step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw8225step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8225 raw8225Labels = mixedMoment B node1048 node1048Labels := by
  calc
    mixedMoment B raw8225 raw8225Labels = mixedMoment B raw8225step0 raw8225step0Labels := by
      have hz : ∀ j, raw8225 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8225step0 = (fun i j => raw8225 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8225step0 raw8225; decide +kernel
      have hl : raw8225step0Labels = raw8225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8225 raw8225Labels permutation346 hz
    mixedMoment B raw8225step0 raw8225step0Labels = mixedMoment B raw8225step1 raw8225step1Labels := by
      have hz : ∀ j, raw8225step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8225step1 = (fun i j => raw8225step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8225step1 raw8225step0; decide +kernel
      have hl : raw8225step1Labels = raw8225step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8225step0 raw8225step0Labels permutation56 hz
    mixedMoment B raw8225step1 raw8225step1Labels = mixedMoment B raw8225step2 raw8225step2Labels := by
      have ha : raw8225step2 = (fun i j => raw8225step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8225step2 raw8225step1; decide +kernel
      have hl : raw8225step2Labels = raw8225step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8225step1 raw8225step1Labels permutation9 permutation3
    _ = mixedMoment B node1048 node1048Labels := by rfl

def raw8226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8226Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8226step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw8226step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8226 raw8226Labels = mixedMoment B node2487 node2487Labels := by
  calc
    mixedMoment B raw8226 raw8226Labels = mixedMoment B raw8226step0 raw8226step0Labels := by
      have hz : ∀ j, raw8226 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8226step0 = (fun i j => raw8226 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8226step0 raw8226; decide +kernel
      have hl : raw8226step0Labels = raw8226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8226 raw8226Labels permutation346 hz
    mixedMoment B raw8226step0 raw8226step0Labels = mixedMoment B raw8226step1 raw8226step1Labels := by
      have ha : raw8226step1 = (fun i j => raw8226step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8226step1 raw8226step0; decide +kernel
      have hl : raw8226step1Labels = raw8226step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8226step0 raw8226step0Labels permutation33 permutation3
    _ = mixedMoment B node2487 node2487Labels := by rfl

def raw8227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8227Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8227step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8227step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw8227step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8227 raw8227Labels = mixedMoment B node2487 node2487Labels := by
  calc
    mixedMoment B raw8227 raw8227Labels = mixedMoment B raw8227step0 raw8227step0Labels := by
      have hz : ∀ j, raw8227 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8227step0 = (fun i j => raw8227 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8227step0 raw8227; decide +kernel
      have hl : raw8227step0Labels = raw8227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8227 raw8227Labels permutation265 hz
    mixedMoment B raw8227step0 raw8227step0Labels = mixedMoment B raw8227step1 raw8227step1Labels := by
      have ha : raw8227step1 = (fun i j => raw8227step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8227step1 raw8227step0; decide +kernel
      have hl : raw8227step1Labels = raw8227step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8227step0 raw8227step0Labels permutation33 permutation3
    _ = mixedMoment B node2487 node2487Labels := by rfl

def raw8228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8228Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8228step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8228step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8228step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8228step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw8228step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8228 raw8228Labels = mixedMoment B node2603 node2603Labels := by
  calc
    mixedMoment B raw8228 raw8228Labels = mixedMoment B raw8228step0 raw8228step0Labels := by
      have hz : ∀ j, raw8228 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8228step0 = (fun i j => raw8228 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8228step0 raw8228; decide +kernel
      have hl : raw8228step0Labels = raw8228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8228 raw8228Labels permutation346 hz
    mixedMoment B raw8228step0 raw8228step0Labels = mixedMoment B raw8228step1 raw8228step1Labels := by
      have hz : ∀ j, raw8228step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8228step1 = (fun i j => raw8228step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8228step1 raw8228step0; decide +kernel
      have hl : raw8228step1Labels = raw8228step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8228step0 raw8228step0Labels permutation56 hz
    mixedMoment B raw8228step1 raw8228step1Labels = mixedMoment B raw8228step2 raw8228step2Labels := by
      have ha : raw8228step2 = (fun i j => raw8228step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8228step2 raw8228step1; decide +kernel
      have hl : raw8228step2Labels = raw8228step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8228step1 raw8228step1Labels permutation9 permutation3
    _ = mixedMoment B node2603 node2603Labels := by rfl

def raw8229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![1, 2, -3]]
def raw8229Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![1, 2, -3]]
def raw8229step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8229step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -3, 1], ![1, 2, -3]]
def raw8229step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8229step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw8229step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8229 raw8229Labels = mixedMoment B node2761 node2761Labels := by
  calc
    mixedMoment B raw8229 raw8229Labels = mixedMoment B raw8229step0 raw8229step0Labels := by
      have hz : ∀ j, raw8229 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8229step0 = (fun i j => raw8229 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8229step0 raw8229; decide +kernel
      have hl : raw8229step0Labels = raw8229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8229 raw8229Labels permutation346 hz
    mixedMoment B raw8229step0 raw8229step0Labels = mixedMoment B raw8229step1 raw8229step1Labels := by
      have hz : ∀ j, raw8229step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8229step1 = (fun i j => raw8229step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8229step1 raw8229step0; decide +kernel
      have hl : raw8229step1Labels = raw8229step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8229step0 raw8229step0Labels permutation56 hz
    mixedMoment B raw8229step1 raw8229step1Labels = mixedMoment B raw8229step2 raw8229step2Labels := by
      have ha : raw8229step2 = (fun i j => raw8229step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8229step2 raw8229step1; decide +kernel
      have hl : raw8229step2Labels = raw8229step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8229step1 raw8229step1Labels permutation9 permutation3
    _ = mixedMoment B node2761 node2761Labels := by rfl

def raw8230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw8230Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw8230step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8230step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw8230step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8230step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw8230step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8230 raw8230Labels = mixedMoment B node2755 node2755Labels := by
  calc
    mixedMoment B raw8230 raw8230Labels = mixedMoment B raw8230step0 raw8230step0Labels := by
      have hz : ∀ j, raw8230 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8230step0 = (fun i j => raw8230 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8230step0 raw8230; decide +kernel
      have hl : raw8230step0Labels = raw8230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8230 raw8230Labels permutation346 hz
    mixedMoment B raw8230step0 raw8230step0Labels = mixedMoment B raw8230step1 raw8230step1Labels := by
      have hz : ∀ j, raw8230step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8230step1 = (fun i j => raw8230step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8230step1 raw8230step0; decide +kernel
      have hl : raw8230step1Labels = raw8230step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8230step0 raw8230step0Labels permutation56 hz
    mixedMoment B raw8230step1 raw8230step1Labels = mixedMoment B raw8230step2 raw8230step2Labels := by
      have ha : raw8230step2 = (fun i j => raw8230step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8230step2 raw8230step1; decide +kernel
      have hl : raw8230step2Labels = raw8230step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8230step1 raw8230step1Labels permutation8 permutation3
    _ = mixedMoment B node2755 node2755Labels := by rfl

def raw8231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8231Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8231step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8231step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8231step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8231step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8231step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8231 raw8231Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw8231 raw8231Labels = mixedMoment B raw8231step0 raw8231step0Labels := by
      have hz : ∀ j, raw8231 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8231step0 = (fun i j => raw8231 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8231step0 raw8231; decide +kernel
      have hl : raw8231step0Labels = raw8231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8231 raw8231Labels permutation346 hz
    mixedMoment B raw8231step0 raw8231step0Labels = mixedMoment B raw8231step1 raw8231step1Labels := by
      have ha : raw8231step1 = (fun i j => raw8231step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8231step1 raw8231step0; decide +kernel
      have hl : raw8231step1Labels = raw8231step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8231step0 raw8231step0Labels permutation139 permutation7
    mixedMoment B raw8231step1 raw8231step1Labels = mixedMoment B raw8231step2 raw8231step2Labels := by
      have ha : raw8231step2 = raw8231step1 := by apply Matrix.ext; unfold raw8231step2 raw8231step1; decide +kernel
      have hl : raw8231step1Labels = labelEmbedding1 ∘ raw8231step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8231step1 raw8231step1Labels raw8231step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2763 node2763Labels := by rfl

def raw8232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8232Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8232step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8232step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8232step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8232step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8232 raw8232Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw8232 raw8232Labels = mixedMoment B raw8232step0 raw8232step0Labels := by
      have hz : ∀ j, raw8232 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8232step0 = (fun i j => raw8232 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8232step0 raw8232; decide +kernel
      have hl : raw8232step0Labels = raw8232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8232 raw8232Labels permutation265 hz
    mixedMoment B raw8232step0 raw8232step0Labels = mixedMoment B raw8232step1 raw8232step1Labels := by
      have ha : raw8232step1 = (fun i j => raw8232step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8232step1 raw8232step0; decide +kernel
      have hl : raw8232step1Labels = raw8232step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8232step0 raw8232step0Labels permutation139 permutation7
    mixedMoment B raw8232step1 raw8232step1Labels = mixedMoment B raw8232step2 raw8232step2Labels := by
      have ha : raw8232step2 = raw8232step1 := by apply Matrix.ext; unfold raw8232step2 raw8232step1; decide +kernel
      have hl : raw8232step1Labels = labelEmbedding1 ∘ raw8232step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8232step1 raw8232step1Labels raw8232step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2763 node2763Labels := by rfl

def raw8233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8233Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8233step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8233step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8233step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8233step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8233step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8233step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8233step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8233 raw8233Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw8233 raw8233Labels = mixedMoment B raw8233step0 raw8233step0Labels := by
      have hz : ∀ j, raw8233 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8233step0 = (fun i j => raw8233 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8233step0 raw8233; decide +kernel
      have hl : raw8233step0Labels = raw8233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8233 raw8233Labels permutation346 hz
    mixedMoment B raw8233step0 raw8233step0Labels = mixedMoment B raw8233step1 raw8233step1Labels := by
      have hz : ∀ j, raw8233step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8233step1 = (fun i j => raw8233step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8233step1 raw8233step0; decide +kernel
      have hl : raw8233step1Labels = raw8233step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8233step0 raw8233step0Labels permutation56 hz
    mixedMoment B raw8233step1 raw8233step1Labels = mixedMoment B raw8233step2 raw8233step2Labels := by
      have ha : raw8233step2 = (fun i j => raw8233step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8233step2 raw8233step1; decide +kernel
      have hl : raw8233step2Labels = raw8233step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8233step1 raw8233step1Labels permutation31 permutation7
    mixedMoment B raw8233step2 raw8233step2Labels = mixedMoment B raw8233step3 raw8233step3Labels := by
      have ha : raw8233step3 = raw8233step2 := by apply Matrix.ext; unfold raw8233step3 raw8233step2; decide +kernel
      have hl : raw8233step2Labels = labelEmbedding1 ∘ raw8233step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8233step2 raw8233step2Labels raw8233step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2782 node2782Labels := by rfl

def raw8234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8234Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8234step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8234step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8234step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8234step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8234step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8234step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8234step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8234 raw8234Labels = mixedMoment B node3119 node3119Labels := by
  calc
    mixedMoment B raw8234 raw8234Labels = mixedMoment B raw8234step0 raw8234step0Labels := by
      have hz : ∀ j, raw8234 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8234step0 = (fun i j => raw8234 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8234step0 raw8234; decide +kernel
      have hl : raw8234step0Labels = raw8234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8234 raw8234Labels permutation346 hz
    mixedMoment B raw8234step0 raw8234step0Labels = mixedMoment B raw8234step1 raw8234step1Labels := by
      have hz : ∀ j, raw8234step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8234step1 = (fun i j => raw8234step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8234step1 raw8234step0; decide +kernel
      have hl : raw8234step1Labels = raw8234step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8234step0 raw8234step0Labels permutation56 hz
    mixedMoment B raw8234step1 raw8234step1Labels = mixedMoment B raw8234step2 raw8234step2Labels := by
      have ha : raw8234step2 = (fun i j => raw8234step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8234step2 raw8234step1; decide +kernel
      have hl : raw8234step2Labels = raw8234step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8234step1 raw8234step1Labels permutation31 permutation7
    mixedMoment B raw8234step2 raw8234step2Labels = mixedMoment B raw8234step3 raw8234step3Labels := by
      have ha : raw8234step3 = raw8234step2 := by apply Matrix.ext; unfold raw8234step3 raw8234step2; decide +kernel
      have hl : raw8234step2Labels = labelEmbedding1 ∘ raw8234step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8234step2 raw8234step2Labels raw8234step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3119 node3119Labels := by rfl

def raw8235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8235Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8235step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw8235step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8235step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw8235step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8235step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw8235step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8235 raw8235Labels = mixedMoment B node1656 node1656Labels := by
  calc
    mixedMoment B raw8235 raw8235Labels = mixedMoment B raw8235step0 raw8235step0Labels := by
      have hz : ∀ j, raw8235 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8235step0 = (fun i j => raw8235 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8235step0 raw8235; decide +kernel
      have hl : raw8235step0Labels = raw8235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8235 raw8235Labels permutation346 hz
    mixedMoment B raw8235step0 raw8235step0Labels = mixedMoment B raw8235step1 raw8235step1Labels := by
      have ha : raw8235step1 = (fun i j => raw8235step0 (permutation52 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8235step1 raw8235step0; decide +kernel
      have hl : raw8235step1Labels = raw8235step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8235step0 raw8235step0Labels permutation52 permutation5
    mixedMoment B raw8235step1 raw8235step1Labels = mixedMoment B raw8235step2 raw8235step2Labels := by
      have ha : raw8235step2 = -raw8235step1 := by apply Matrix.ext; change ∀ i j, raw8235step2 i j = -(raw8235step1 i j); unfold raw8235step2 raw8235step1; decide +kernel
      have hl : raw8235step2Labels = raw8235step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8235step2 raw8235step2Labels = mixedMoment B raw8235step3 raw8235step3Labels := by
      have ha : raw8235step3 = raw8235step2 := by apply Matrix.ext; unfold raw8235step3 raw8235step2; decide +kernel
      have hl : raw8235step2Labels = labelEmbedding1 ∘ raw8235step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8235step2 raw8235step2Labels raw8235step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1656 node1656Labels := by rfl

def raw8236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8236Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8236step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw8236step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8236step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw8236step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8236 raw8236Labels = mixedMoment B node2717 node2717Labels := by
  calc
    mixedMoment B raw8236 raw8236Labels = mixedMoment B raw8236step0 raw8236step0Labels := by
      have ha : raw8236step0 = (fun i j => raw8236 (permutation611 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8236step0 raw8236; decide +kernel
      have hl : raw8236step0Labels = raw8236Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8236 raw8236Labels permutation611 permutation7
    mixedMoment B raw8236step0 raw8236step0Labels = mixedMoment B raw8236step1 raw8236step1Labels := by
      have ha : raw8236step1 = raw8236step0 := by apply Matrix.ext; unfold raw8236step1 raw8236step0; decide +kernel
      have hl : raw8236step0Labels = labelEmbedding1 ∘ raw8236step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8236step0 raw8236step0Labels raw8236step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2717 node2717Labels := by rfl

def raw8237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8237Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8237step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8237step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw8237step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8237step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw8237step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8237 raw8237Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw8237 raw8237Labels = mixedMoment B raw8237step0 raw8237step0Labels := by
      have hz : ∀ j, raw8237 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8237step0 = (fun i j => raw8237 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8237step0 raw8237; decide +kernel
      have hl : raw8237step0Labels = raw8237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8237 raw8237Labels permutation346 hz
    mixedMoment B raw8237step0 raw8237step0Labels = mixedMoment B raw8237step1 raw8237step1Labels := by
      have ha : raw8237step1 = (fun i j => raw8237step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8237step1 raw8237step0; decide +kernel
      have hl : raw8237step1Labels = raw8237step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8237step0 raw8237step0Labels permutation139 permutation7
    mixedMoment B raw8237step1 raw8237step1Labels = mixedMoment B raw8237step2 raw8237step2Labels := by
      have ha : raw8237step2 = raw8237step1 := by apply Matrix.ext; unfold raw8237step2 raw8237step1; decide +kernel
      have hl : raw8237step1Labels = labelEmbedding1 ∘ raw8237step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8237step1 raw8237step1Labels raw8237step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2735 node2735Labels := by rfl

def raw8238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8238Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8238step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8238step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw8238step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8238step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw8238step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8238 raw8238Labels = mixedMoment B node3096 node3096Labels := by
  calc
    mixedMoment B raw8238 raw8238Labels = mixedMoment B raw8238step0 raw8238step0Labels := by
      have hz : ∀ j, raw8238 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8238step0 = (fun i j => raw8238 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8238step0 raw8238; decide +kernel
      have hl : raw8238step0Labels = raw8238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8238 raw8238Labels permutation346 hz
    mixedMoment B raw8238step0 raw8238step0Labels = mixedMoment B raw8238step1 raw8238step1Labels := by
      have ha : raw8238step1 = (fun i j => raw8238step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8238step1 raw8238step0; decide +kernel
      have hl : raw8238step1Labels = raw8238step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8238step0 raw8238step0Labels permutation139 permutation7
    mixedMoment B raw8238step1 raw8238step1Labels = mixedMoment B raw8238step2 raw8238step2Labels := by
      have ha : raw8238step2 = raw8238step1 := by apply Matrix.ext; unfold raw8238step2 raw8238step1; decide +kernel
      have hl : raw8238step1Labels = labelEmbedding1 ∘ raw8238step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8238step1 raw8238step1Labels raw8238step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3096 node3096Labels := by rfl

def raw8239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8239Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8239step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8239step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw8239step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8239step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw8239step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8239step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw8239step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8239 raw8239Labels = mixedMoment B node1656 node1656Labels := by
  calc
    mixedMoment B raw8239 raw8239Labels = mixedMoment B raw8239step0 raw8239step0Labels := by
      have hz : ∀ j, raw8239 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8239step0 = (fun i j => raw8239 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8239step0 raw8239; decide +kernel
      have hl : raw8239step0Labels = raw8239Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8239 raw8239Labels permutation265 hz
    mixedMoment B raw8239step0 raw8239step0Labels = mixedMoment B raw8239step1 raw8239step1Labels := by
      have ha : raw8239step1 = (fun i j => raw8239step0 (permutation52 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8239step1 raw8239step0; decide +kernel
      have hl : raw8239step1Labels = raw8239step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8239step0 raw8239step0Labels permutation52 permutation5
    mixedMoment B raw8239step1 raw8239step1Labels = mixedMoment B raw8239step2 raw8239step2Labels := by
      have ha : raw8239step2 = -raw8239step1 := by apply Matrix.ext; change ∀ i j, raw8239step2 i j = -(raw8239step1 i j); unfold raw8239step2 raw8239step1; decide +kernel
      have hl : raw8239step2Labels = raw8239step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8239step2 raw8239step2Labels = mixedMoment B raw8239step3 raw8239step3Labels := by
      have ha : raw8239step3 = raw8239step2 := by apply Matrix.ext; unfold raw8239step3 raw8239step2; decide +kernel
      have hl : raw8239step2Labels = labelEmbedding1 ∘ raw8239step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8239step2 raw8239step2Labels raw8239step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1656 node1656Labels := by rfl

def raw8240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8240Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8240step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw8240step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8240step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw8240step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8240 raw8240Labels = mixedMoment B node2717 node2717Labels := by
  calc
    mixedMoment B raw8240 raw8240Labels = mixedMoment B raw8240step0 raw8240step0Labels := by
      have ha : raw8240step0 = (fun i j => raw8240 (permutation634 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8240step0 raw8240; decide +kernel
      have hl : raw8240step0Labels = raw8240Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8240 raw8240Labels permutation634 permutation7
    mixedMoment B raw8240step0 raw8240step0Labels = mixedMoment B raw8240step1 raw8240step1Labels := by
      have ha : raw8240step1 = raw8240step0 := by apply Matrix.ext; unfold raw8240step1 raw8240step0; decide +kernel
      have hl : raw8240step0Labels = labelEmbedding1 ∘ raw8240step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8240step0 raw8240step0Labels raw8240step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2717 node2717Labels := by rfl

def raw8241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8241Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8241step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8241step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw8241step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8241step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw8241step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8241 raw8241Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw8241 raw8241Labels = mixedMoment B raw8241step0 raw8241step0Labels := by
      have hz : ∀ j, raw8241 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8241step0 = (fun i j => raw8241 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8241step0 raw8241; decide +kernel
      have hl : raw8241step0Labels = raw8241Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8241 raw8241Labels permutation265 hz
    mixedMoment B raw8241step0 raw8241step0Labels = mixedMoment B raw8241step1 raw8241step1Labels := by
      have ha : raw8241step1 = (fun i j => raw8241step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8241step1 raw8241step0; decide +kernel
      have hl : raw8241step1Labels = raw8241step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8241step0 raw8241step0Labels permutation139 permutation7
    mixedMoment B raw8241step1 raw8241step1Labels = mixedMoment B raw8241step2 raw8241step2Labels := by
      have ha : raw8241step2 = raw8241step1 := by apply Matrix.ext; unfold raw8241step2 raw8241step1; decide +kernel
      have hl : raw8241step1Labels = labelEmbedding1 ∘ raw8241step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8241step1 raw8241step1Labels raw8241step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2735 node2735Labels := by rfl

def raw8242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8242Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8242step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8242step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw8242step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8242step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw8242step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8242 raw8242Labels = mixedMoment B node3096 node3096Labels := by
  calc
    mixedMoment B raw8242 raw8242Labels = mixedMoment B raw8242step0 raw8242step0Labels := by
      have hz : ∀ j, raw8242 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8242step0 = (fun i j => raw8242 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8242step0 raw8242; decide +kernel
      have hl : raw8242step0Labels = raw8242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8242 raw8242Labels permutation265 hz
    mixedMoment B raw8242step0 raw8242step0Labels = mixedMoment B raw8242step1 raw8242step1Labels := by
      have ha : raw8242step1 = (fun i j => raw8242step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8242step1 raw8242step0; decide +kernel
      have hl : raw8242step1Labels = raw8242step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8242step0 raw8242step0Labels permutation139 permutation7
    mixedMoment B raw8242step1 raw8242step1Labels = mixedMoment B raw8242step2 raw8242step2Labels := by
      have ha : raw8242step2 = raw8242step1 := by apply Matrix.ext; unfold raw8242step2 raw8242step1; decide +kernel
      have hl : raw8242step1Labels = labelEmbedding1 ∘ raw8242step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8242step1 raw8242step1Labels raw8242step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3096 node3096Labels := by rfl

def raw8243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8243Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8243step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8243step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8243step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8243step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw8243step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8243step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![2, -1, -1], ![2, -1, -1]]
def raw8243step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8243step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![2, -1, -1], ![2, -1, -1]]
def raw8243step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8243 raw8243Labels = mixedMoment B node1661 node1661Labels := by
  calc
    mixedMoment B raw8243 raw8243Labels = mixedMoment B raw8243step0 raw8243step0Labels := by
      have hz : ∀ j, raw8243 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8243step0 = (fun i j => raw8243 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8243step0 raw8243; decide +kernel
      have hl : raw8243step0Labels = raw8243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8243 raw8243Labels permutation346 hz
    mixedMoment B raw8243step0 raw8243step0Labels = mixedMoment B raw8243step1 raw8243step1Labels := by
      have hz : ∀ j, raw8243step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8243step1 = (fun i j => raw8243step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8243step1 raw8243step0; decide +kernel
      have hl : raw8243step1Labels = raw8243step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8243step0 raw8243step0Labels permutation56 hz
    mixedMoment B raw8243step1 raw8243step1Labels = mixedMoment B raw8243step2 raw8243step2Labels := by
      have ha : raw8243step2 = (fun i j => raw8243step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8243step2 raw8243step1; decide +kernel
      have hl : raw8243step2Labels = raw8243step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8243step1 raw8243step1Labels permutation12 permutation5
    mixedMoment B raw8243step2 raw8243step2Labels = mixedMoment B raw8243step3 raw8243step3Labels := by
      have ha : raw8243step3 = -raw8243step2 := by apply Matrix.ext; change ∀ i j, raw8243step3 i j = -(raw8243step2 i j); unfold raw8243step3 raw8243step2; decide +kernel
      have hl : raw8243step3Labels = raw8243step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8243step3 raw8243step3Labels = mixedMoment B raw8243step4 raw8243step4Labels := by
      have ha : raw8243step4 = raw8243step3 := by apply Matrix.ext; unfold raw8243step4 raw8243step3; decide +kernel
      have hl : raw8243step3Labels = labelEmbedding1 ∘ raw8243step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8243step3 raw8243step3Labels raw8243step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1661 node1661Labels := by rfl

def raw8244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8244Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8244step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8244step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8244step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8244step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8244 raw8244Labels = mixedMoment B node2762 node2762Labels := by
  calc
    mixedMoment B raw8244 raw8244Labels = mixedMoment B raw8244step0 raw8244step0Labels := by
      have hz : ∀ j, raw8244 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8244step0 = (fun i j => raw8244 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8244step0 raw8244; decide +kernel
      have hl : raw8244step0Labels = raw8244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8244 raw8244Labels permutation346 hz
    mixedMoment B raw8244step0 raw8244step0Labels = mixedMoment B raw8244step1 raw8244step1Labels := by
      have ha : raw8244step1 = (fun i j => raw8244step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8244step1 raw8244step0; decide +kernel
      have hl : raw8244step1Labels = raw8244step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8244step0 raw8244step0Labels permutation137 permutation7
    mixedMoment B raw8244step1 raw8244step1Labels = mixedMoment B raw8244step2 raw8244step2Labels := by
      have ha : raw8244step2 = raw8244step1 := by apply Matrix.ext; unfold raw8244step2 raw8244step1; decide +kernel
      have hl : raw8244step1Labels = labelEmbedding1 ∘ raw8244step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8244step1 raw8244step1Labels raw8244step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2762 node2762Labels := by rfl

def raw8245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8245Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8245step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8245step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8245step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8245step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8245step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8245 raw8245Labels = mixedMoment B node2762 node2762Labels := by
  calc
    mixedMoment B raw8245 raw8245Labels = mixedMoment B raw8245step0 raw8245step0Labels := by
      have hz : ∀ j, raw8245 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8245step0 = (fun i j => raw8245 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8245step0 raw8245; decide +kernel
      have hl : raw8245step0Labels = raw8245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8245 raw8245Labels permutation265 hz
    mixedMoment B raw8245step0 raw8245step0Labels = mixedMoment B raw8245step1 raw8245step1Labels := by
      have ha : raw8245step1 = (fun i j => raw8245step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8245step1 raw8245step0; decide +kernel
      have hl : raw8245step1Labels = raw8245step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8245step0 raw8245step0Labels permutation137 permutation7
    mixedMoment B raw8245step1 raw8245step1Labels = mixedMoment B raw8245step2 raw8245step2Labels := by
      have ha : raw8245step2 = raw8245step1 := by apply Matrix.ext; unfold raw8245step2 raw8245step1; decide +kernel
      have hl : raw8245step1Labels = labelEmbedding1 ∘ raw8245step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8245step1 raw8245step1Labels raw8245step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2762 node2762Labels := by rfl

def raw8246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8246Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8246step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8246step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8246step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8246step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8246step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8246step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8246step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8246 raw8246Labels = mixedMoment B node3118 node3118Labels := by
  calc
    mixedMoment B raw8246 raw8246Labels = mixedMoment B raw8246step0 raw8246step0Labels := by
      have hz : ∀ j, raw8246 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8246step0 = (fun i j => raw8246 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8246step0 raw8246; decide +kernel
      have hl : raw8246step0Labels = raw8246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8246 raw8246Labels permutation346 hz
    mixedMoment B raw8246step0 raw8246step0Labels = mixedMoment B raw8246step1 raw8246step1Labels := by
      have hz : ∀ j, raw8246step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8246step1 = (fun i j => raw8246step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8246step1 raw8246step0; decide +kernel
      have hl : raw8246step1Labels = raw8246step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8246step0 raw8246step0Labels permutation56 hz
    mixedMoment B raw8246step1 raw8246step1Labels = mixedMoment B raw8246step2 raw8246step2Labels := by
      have ha : raw8246step2 = (fun i j => raw8246step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8246step2 raw8246step1; decide +kernel
      have hl : raw8246step2Labels = raw8246step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8246step1 raw8246step1Labels permutation29 permutation7
    mixedMoment B raw8246step2 raw8246step2Labels = mixedMoment B raw8246step3 raw8246step3Labels := by
      have ha : raw8246step3 = raw8246step2 := by apply Matrix.ext; unfold raw8246step3 raw8246step2; decide +kernel
      have hl : raw8246step2Labels = labelEmbedding1 ∘ raw8246step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8246step2 raw8246step2Labels raw8246step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3118 node3118Labels := by rfl

def raw8247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8247Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8247step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8247step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8247step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8247step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw8247step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8247step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![3, -1, -2]]
def raw8247step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8247step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![3, -1, -2]]
def raw8247step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8247 raw8247Labels = mixedMoment B node1657 node1657Labels := by
  calc
    mixedMoment B raw8247 raw8247Labels = mixedMoment B raw8247step0 raw8247step0Labels := by
      have hz : ∀ j, raw8247 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8247step0 = (fun i j => raw8247 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8247step0 raw8247; decide +kernel
      have hl : raw8247step0Labels = raw8247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8247 raw8247Labels permutation346 hz
    mixedMoment B raw8247step0 raw8247step0Labels = mixedMoment B raw8247step1 raw8247step1Labels := by
      have hz : ∀ j, raw8247step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8247step1 = (fun i j => raw8247step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8247step1 raw8247step0; decide +kernel
      have hl : raw8247step1Labels = raw8247step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8247step0 raw8247step0Labels permutation56 hz
    mixedMoment B raw8247step1 raw8247step1Labels = mixedMoment B raw8247step2 raw8247step2Labels := by
      have ha : raw8247step2 = (fun i j => raw8247step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8247step2 raw8247step1; decide +kernel
      have hl : raw8247step2Labels = raw8247step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8247step1 raw8247step1Labels permutation12 permutation5
    mixedMoment B raw8247step2 raw8247step2Labels = mixedMoment B raw8247step3 raw8247step3Labels := by
      have ha : raw8247step3 = -raw8247step2 := by apply Matrix.ext; change ∀ i j, raw8247step3 i j = -(raw8247step2 i j); unfold raw8247step3 raw8247step2; decide +kernel
      have hl : raw8247step3Labels = raw8247step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8247step3 raw8247step3Labels = mixedMoment B raw8247step4 raw8247step4Labels := by
      have ha : raw8247step4 = raw8247step3 := by apply Matrix.ext; unfold raw8247step4 raw8247step3; decide +kernel
      have hl : raw8247step3Labels = labelEmbedding1 ∘ raw8247step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8247step3 raw8247step3Labels raw8247step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1657 node1657Labels := by rfl

def raw8248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8248Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8248step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw8248step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8248step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw8248step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8248 raw8248Labels = mixedMoment B node2584 node2584Labels := by
  calc
    mixedMoment B raw8248 raw8248Labels = mixedMoment B raw8248step0 raw8248step0Labels := by
      have hz : ∀ j, raw8248 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8248step0 = (fun i j => raw8248 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8248step0 raw8248; decide +kernel
      have hl : raw8248step0Labels = raw8248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8248 raw8248Labels permutation346 hz
    mixedMoment B raw8248step0 raw8248step0Labels = mixedMoment B raw8248step1 raw8248step1Labels := by
      have ha : raw8248step1 = (fun i j => raw8248step0 (permutation121 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8248step1 raw8248step0; decide +kernel
      have hl : raw8248step1Labels = raw8248step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8248step0 raw8248step0Labels permutation121 permutation5
    mixedMoment B raw8248step1 raw8248step1Labels = mixedMoment B raw8248step2 raw8248step2Labels := by
      have ha : raw8248step2 = raw8248step1 := by apply Matrix.ext; unfold raw8248step2 raw8248step1; decide +kernel
      have hl : raw8248step1Labels = labelEmbedding1 ∘ raw8248step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8248step1 raw8248step1Labels raw8248step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2584 node2584Labels := by rfl

def raw8249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8249Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8249step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw8249step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8249step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw8249step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8249 raw8249Labels = mixedMoment B node2584 node2584Labels := by
  calc
    mixedMoment B raw8249 raw8249Labels = mixedMoment B raw8249step0 raw8249step0Labels := by
      have hz : ∀ j, raw8249 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8249step0 = (fun i j => raw8249 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8249step0 raw8249; decide +kernel
      have hl : raw8249step0Labels = raw8249Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8249 raw8249Labels permutation265 hz
    mixedMoment B raw8249step0 raw8249step0Labels = mixedMoment B raw8249step1 raw8249step1Labels := by
      have ha : raw8249step1 = (fun i j => raw8249step0 (permutation121 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8249step1 raw8249step0; decide +kernel
      have hl : raw8249step1Labels = raw8249step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8249step0 raw8249step0Labels permutation121 permutation5
    mixedMoment B raw8249step1 raw8249step1Labels = mixedMoment B raw8249step2 raw8249step2Labels := by
      have ha : raw8249step2 = raw8249step1 := by apply Matrix.ext; unfold raw8249step2 raw8249step1; decide +kernel
      have hl : raw8249step1Labels = labelEmbedding1 ∘ raw8249step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8249step1 raw8249step1Labels raw8249step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2584 node2584Labels := by rfl

def raw8250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8250Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8250step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8250step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8250step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8250step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw8250step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8250step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw8250step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8250 raw8250Labels = mixedMoment B node2761 node2761Labels := by
  calc
    mixedMoment B raw8250 raw8250Labels = mixedMoment B raw8250step0 raw8250step0Labels := by
      have hz : ∀ j, raw8250 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8250step0 = (fun i j => raw8250 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8250step0 raw8250; decide +kernel
      have hl : raw8250step0Labels = raw8250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8250 raw8250Labels permutation346 hz
    mixedMoment B raw8250step0 raw8250step0Labels = mixedMoment B raw8250step1 raw8250step1Labels := by
      have hz : ∀ j, raw8250step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8250step1 = (fun i j => raw8250step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8250step1 raw8250step0; decide +kernel
      have hl : raw8250step1Labels = raw8250step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8250step0 raw8250step0Labels permutation56 hz
    mixedMoment B raw8250step1 raw8250step1Labels = mixedMoment B raw8250step2 raw8250step2Labels := by
      have ha : raw8250step2 = (fun i j => raw8250step1 (permutation23 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8250step2 raw8250step1; decide +kernel
      have hl : raw8250step2Labels = raw8250step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8250step1 raw8250step1Labels permutation23 permutation5
    mixedMoment B raw8250step2 raw8250step2Labels = mixedMoment B raw8250step3 raw8250step3Labels := by
      have ha : raw8250step3 = raw8250step2 := by apply Matrix.ext; unfold raw8250step3 raw8250step2; decide +kernel
      have hl : raw8250step2Labels = labelEmbedding1 ∘ raw8250step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8250step2 raw8250step2Labels raw8250step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2761 node2761Labels := by rfl

def raw8251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![1, 2, -3]]
def raw8251Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![1, 2, -3]]
def raw8251step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8251step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -3, 1], ![1, 2, -3]]
def raw8251step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8251step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw8251step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8251step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw8251step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8251 raw8251Labels = mixedMoment B node2603 node2603Labels := by
  calc
    mixedMoment B raw8251 raw8251Labels = mixedMoment B raw8251step0 raw8251step0Labels := by
      have hz : ∀ j, raw8251 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8251step0 = (fun i j => raw8251 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8251step0 raw8251; decide +kernel
      have hl : raw8251step0Labels = raw8251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8251 raw8251Labels permutation346 hz
    mixedMoment B raw8251step0 raw8251step0Labels = mixedMoment B raw8251step1 raw8251step1Labels := by
      have hz : ∀ j, raw8251step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8251step1 = (fun i j => raw8251step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8251step1 raw8251step0; decide +kernel
      have hl : raw8251step1Labels = raw8251step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8251step0 raw8251step0Labels permutation56 hz
    mixedMoment B raw8251step1 raw8251step1Labels = mixedMoment B raw8251step2 raw8251step2Labels := by
      have ha : raw8251step2 = (fun i j => raw8251step1 (permutation23 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8251step2 raw8251step1; decide +kernel
      have hl : raw8251step2Labels = raw8251step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8251step1 raw8251step1Labels permutation23 permutation5
    mixedMoment B raw8251step2 raw8251step2Labels = mixedMoment B raw8251step3 raw8251step3Labels := by
      have ha : raw8251step3 = raw8251step2 := by apply Matrix.ext; unfold raw8251step3 raw8251step2; decide +kernel
      have hl : raw8251step2Labels = labelEmbedding1 ∘ raw8251step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8251step2 raw8251step2Labels raw8251step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2603 node2603Labels := by rfl

def raw8252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw8252Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw8252step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8252step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw8252step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8252step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw8252step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8252step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw8252step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8252 raw8252Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw8252 raw8252Labels = mixedMoment B raw8252step0 raw8252step0Labels := by
      have hz : ∀ j, raw8252 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8252step0 = (fun i j => raw8252 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8252step0 raw8252; decide +kernel
      have hl : raw8252step0Labels = raw8252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8252 raw8252Labels permutation346 hz
    mixedMoment B raw8252step0 raw8252step0Labels = mixedMoment B raw8252step1 raw8252step1Labels := by
      have hz : ∀ j, raw8252step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8252step1 = (fun i j => raw8252step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8252step1 raw8252step0; decide +kernel
      have hl : raw8252step1Labels = raw8252step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8252step0 raw8252step0Labels permutation56 hz
    mixedMoment B raw8252step1 raw8252step1Labels = mixedMoment B raw8252step2 raw8252step2Labels := by
      have ha : raw8252step2 = (fun i j => raw8252step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8252step2 raw8252step1; decide +kernel
      have hl : raw8252step2Labels = raw8252step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8252step1 raw8252step1Labels permutation29 permutation7
    mixedMoment B raw8252step2 raw8252step2Labels = mixedMoment B raw8252step3 raw8252step3Labels := by
      have ha : raw8252step3 = raw8252step2 := by apply Matrix.ext; unfold raw8252step3 raw8252step2; decide +kernel
      have hl : raw8252step2Labels = labelEmbedding1 ∘ raw8252step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8252step2 raw8252step2Labels raw8252step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2290 node2290Labels := by rfl

def raw8253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8253Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8253step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8253step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8253step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8253 raw8253Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw8253 raw8253Labels = mixedMoment B raw8253step0 raw8253step0Labels := by
      have hz : ∀ j, raw8253 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8253step0 = (fun i j => raw8253 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8253step0 raw8253; decide +kernel
      have hl : raw8253step0Labels = raw8253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8253 raw8253Labels permutation346 hz
    mixedMoment B raw8253step0 raw8253step0Labels = mixedMoment B raw8253step1 raw8253step1Labels := by
      have hz : ∀ j, raw8253step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8253step1 = (fun i j => raw8253step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8253step1 raw8253step0; decide +kernel
      have hl : raw8253step1Labels = raw8253step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8253step0 raw8253step0Labels permutation56 hz
    _ = mixedMoment B node3098 node3098Labels := by rfl

def raw8254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8254Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8254step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw8254step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8254step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8254step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8254 raw8254Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw8254 raw8254Labels = mixedMoment B raw8254step0 raw8254step0Labels := by
      have hz : ∀ j, raw8254 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8254step0 = (fun i j => raw8254 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8254step0 raw8254; decide +kernel
      have hl : raw8254step0Labels = raw8254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8254 raw8254Labels permutation346 hz
    mixedMoment B raw8254step0 raw8254step0Labels = mixedMoment B raw8254step1 raw8254step1Labels := by
      have ha : raw8254step1 = (fun i j => raw8254step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8254step1 raw8254step0; decide +kernel
      have hl : raw8254step1Labels = raw8254step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8254step0 raw8254step0Labels permutation151 permutation2
    mixedMoment B raw8254step1 raw8254step1Labels = mixedMoment B raw8254step2 raw8254step2Labels := by
      have ha : raw8254step2 = -raw8254step1 := by apply Matrix.ext; change ∀ i j, raw8254step2 i j = -(raw8254step1 i j); unfold raw8254step2 raw8254step1; decide +kernel
      have hl : raw8254step2Labels = raw8254step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw8255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8255Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8255step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8255step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw8255step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8255step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8255step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8255 raw8255Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw8255 raw8255Labels = mixedMoment B raw8255step0 raw8255step0Labels := by
      have hz : ∀ j, raw8255 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8255step0 = (fun i j => raw8255 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8255step0 raw8255; decide +kernel
      have hl : raw8255step0Labels = raw8255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8255 raw8255Labels permutation265 hz
    mixedMoment B raw8255step0 raw8255step0Labels = mixedMoment B raw8255step1 raw8255step1Labels := by
      have ha : raw8255step1 = (fun i j => raw8255step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8255step1 raw8255step0; decide +kernel
      have hl : raw8255step1Labels = raw8255step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8255step0 raw8255step0Labels permutation151 permutation2
    mixedMoment B raw8255step1 raw8255step1Labels = mixedMoment B raw8255step2 raw8255step2Labels := by
      have ha : raw8255step2 = -raw8255step1 := by apply Matrix.ext; change ∀ i j, raw8255step2 i j = -(raw8255step1 i j); unfold raw8255step2 raw8255step1; decide +kernel
      have hl : raw8255step2Labels = raw8255step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw8256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8256Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8256step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8256step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8256step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8256step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw8256step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8256step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8256step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8256 raw8256Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw8256 raw8256Labels = mixedMoment B raw8256step0 raw8256step0Labels := by
      have hz : ∀ j, raw8256 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8256step0 = (fun i j => raw8256 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8256step0 raw8256; decide +kernel
      have hl : raw8256step0Labels = raw8256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8256 raw8256Labels permutation346 hz
    mixedMoment B raw8256step0 raw8256step0Labels = mixedMoment B raw8256step1 raw8256step1Labels := by
      have hz : ∀ j, raw8256step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8256step1 = (fun i j => raw8256step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8256step1 raw8256step0; decide +kernel
      have hl : raw8256step1Labels = raw8256step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8256step0 raw8256step0Labels permutation56 hz
    mixedMoment B raw8256step1 raw8256step1Labels = mixedMoment B raw8256step2 raw8256step2Labels := by
      have ha : raw8256step2 = (fun i j => raw8256step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8256step2 raw8256step1; decide +kernel
      have hl : raw8256step2Labels = raw8256step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8256step1 raw8256step1Labels permutation31 permutation2
    mixedMoment B raw8256step2 raw8256step2Labels = mixedMoment B raw8256step3 raw8256step3Labels := by
      have ha : raw8256step3 = -raw8256step2 := by apply Matrix.ext; change ∀ i j, raw8256step3 i j = -(raw8256step2 i j); unfold raw8256step3 raw8256step2; decide +kernel
      have hl : raw8256step3Labels = raw8256step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3583 node3583Labels := by rfl

def raw8257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8257Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8257step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8257step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8257step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8257step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw8257step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8257step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8257step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8257 raw8257Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw8257 raw8257Labels = mixedMoment B raw8257step0 raw8257step0Labels := by
      have hz : ∀ j, raw8257 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8257step0 = (fun i j => raw8257 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8257step0 raw8257; decide +kernel
      have hl : raw8257step0Labels = raw8257Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8257 raw8257Labels permutation346 hz
    mixedMoment B raw8257step0 raw8257step0Labels = mixedMoment B raw8257step1 raw8257step1Labels := by
      have hz : ∀ j, raw8257step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8257step1 = (fun i j => raw8257step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8257step1 raw8257step0; decide +kernel
      have hl : raw8257step1Labels = raw8257step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8257step0 raw8257step0Labels permutation56 hz
    mixedMoment B raw8257step1 raw8257step1Labels = mixedMoment B raw8257step2 raw8257step2Labels := by
      have ha : raw8257step2 = (fun i j => raw8257step1 (permutation26 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8257step2 raw8257step1; decide +kernel
      have hl : raw8257step2Labels = raw8257step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8257step1 raw8257step1Labels permutation26 permutation4
    mixedMoment B raw8257step2 raw8257step2Labels = mixedMoment B raw8257step3 raw8257step3Labels := by
      have ha : raw8257step3 = -raw8257step2 := by apply Matrix.ext; change ∀ i j, raw8257step3 i j = -(raw8257step2 i j); unfold raw8257step3 raw8257step2; decide +kernel
      have hl : raw8257step3Labels = raw8257step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3583 node3583Labels := by rfl

def raw8258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8258Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8258step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8258step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8258 raw8258Labels = mixedMoment B node1404 node1404Labels := by
  calc
    mixedMoment B raw8258 raw8258Labels = mixedMoment B raw8258step0 raw8258step0Labels := by
      have hz : ∀ j, raw8258 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8258step0 = (fun i j => raw8258 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8258step0 raw8258; decide +kernel
      have hl : raw8258step0Labels = raw8258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8258 raw8258Labels permutation346 hz
    mixedMoment B raw8258step0 raw8258step0Labels = mixedMoment B raw8258step1 raw8258step1Labels := by
      have ha : raw8258step1 = (fun i j => raw8258step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8258step1 raw8258step0; decide +kernel
      have hl : raw8258step1Labels = raw8258step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8258step0 raw8258step0Labels permutation40 permutation2
    _ = mixedMoment B node1404 node1404Labels := by rfl

def raw8259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8259Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8259step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8259step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8259step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8259 raw8259Labels = mixedMoment B node1404 node1404Labels := by
  calc
    mixedMoment B raw8259 raw8259Labels = mixedMoment B raw8259step0 raw8259step0Labels := by
      have hz : ∀ j, raw8259 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8259step0 = (fun i j => raw8259 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8259step0 raw8259; decide +kernel
      have hl : raw8259step0Labels = raw8259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8259 raw8259Labels permutation265 hz
    mixedMoment B raw8259step0 raw8259step0Labels = mixedMoment B raw8259step1 raw8259step1Labels := by
      have ha : raw8259step1 = (fun i j => raw8259step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8259step1 raw8259step0; decide +kernel
      have hl : raw8259step1Labels = raw8259step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8259step0 raw8259step0Labels permutation40 permutation2
    _ = mixedMoment B node1404 node1404Labels := by rfl

def raw8260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8260Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8260step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8260step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8260step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8260 raw8260Labels = mixedMoment B node1440 node1440Labels := by
  calc
    mixedMoment B raw8260 raw8260Labels = mixedMoment B raw8260step0 raw8260step0Labels := by
      have hz : ∀ j, raw8260 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8260step0 = (fun i j => raw8260 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8260step0 raw8260; decide +kernel
      have hl : raw8260step0Labels = raw8260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8260 raw8260Labels permutation346 hz
    mixedMoment B raw8260step0 raw8260step0Labels = mixedMoment B raw8260step1 raw8260step1Labels := by
      have hz : ∀ j, raw8260step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8260step1 = (fun i j => raw8260step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8260step1 raw8260step0; decide +kernel
      have hl : raw8260step1Labels = raw8260step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8260step0 raw8260step0Labels permutation56 hz
    _ = mixedMoment B node1440 node1440Labels := by rfl

def raw8261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8261Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8261step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8261step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8261step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8261 raw8261Labels = mixedMoment B node1418 node1418Labels := by
  calc
    mixedMoment B raw8261 raw8261Labels = mixedMoment B raw8261step0 raw8261step0Labels := by
      have hz : ∀ j, raw8261 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8261step0 = (fun i j => raw8261 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8261step0 raw8261; decide +kernel
      have hl : raw8261step0Labels = raw8261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8261 raw8261Labels permutation346 hz
    mixedMoment B raw8261step0 raw8261step0Labels = mixedMoment B raw8261step1 raw8261step1Labels := by
      have hz : ∀ j, raw8261step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8261step1 = (fun i j => raw8261step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8261step1 raw8261step0; decide +kernel
      have hl : raw8261step1Labels = raw8261step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8261step0 raw8261step0Labels permutation56 hz
    _ = mixedMoment B node1418 node1418Labels := by rfl

def raw8262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8262Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8262step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8262step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8262 raw8262Labels = mixedMoment B node2983 node2983Labels := by
  calc
    mixedMoment B raw8262 raw8262Labels = mixedMoment B raw8262step0 raw8262step0Labels := by
      have ha : raw8262step0 = (fun i j => raw8262 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8262step0 raw8262; decide +kernel
      have hl : raw8262step0Labels = raw8262Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8262 raw8262Labels permutation184 permutation2
    _ = mixedMoment B node2983 node2983Labels := by rfl

def raw8263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8263Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8263step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8263step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8263 raw8263Labels = mixedMoment B node2952 node2952Labels := by
  calc
    mixedMoment B raw8263 raw8263Labels = mixedMoment B raw8263step0 raw8263step0Labels := by
      have hz : ∀ j, raw8263 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8263step0 = (fun i j => raw8263 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8263step0 raw8263; decide +kernel
      have hl : raw8263step0Labels = raw8263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8263 raw8263Labels permutation346 hz
    mixedMoment B raw8263step0 raw8263step0Labels = mixedMoment B raw8263step1 raw8263step1Labels := by
      have ha : raw8263step1 = (fun i j => raw8263step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8263step1 raw8263step0; decide +kernel
      have hl : raw8263step1Labels = raw8263step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8263step0 raw8263step0Labels permutation40 permutation2
    _ = mixedMoment B node2952 node2952Labels := by rfl

def raw8264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8264Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8264step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw8264step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8264 raw8264Labels = mixedMoment B node3096 node3096Labels := by
  calc
    mixedMoment B raw8264 raw8264Labels = mixedMoment B raw8264step0 raw8264step0Labels := by
      have hz : ∀ j, raw8264 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8264step0 = (fun i j => raw8264 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8264step0 raw8264; decide +kernel
      have hl : raw8264step0Labels = raw8264Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8264 raw8264Labels permutation346 hz
    mixedMoment B raw8264step0 raw8264step0Labels = mixedMoment B raw8264step1 raw8264step1Labels := by
      have ha : raw8264step1 = (fun i j => raw8264step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8264step1 raw8264step0; decide +kernel
      have hl : raw8264step1Labels = raw8264step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8264step0 raw8264step0Labels permutation40 permutation2
    _ = mixedMoment B node3096 node3096Labels := by rfl

def raw8265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8265Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8265step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8265 raw8265Labels = mixedMoment B node2983 node2983Labels := by
  calc
    mixedMoment B raw8265 raw8265Labels = mixedMoment B raw8265step0 raw8265step0Labels := by
      have ha : raw8265step0 = (fun i j => raw8265 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8265step0 raw8265; decide +kernel
      have hl : raw8265step0Labels = raw8265Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8265 raw8265Labels permutation160 permutation2
    _ = mixedMoment B node2983 node2983Labels := by rfl

def raw8266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8266Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8266step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8266 raw8266Labels = mixedMoment B node2995 node2995Labels := by
  calc
    mixedMoment B raw8266 raw8266Labels = mixedMoment B raw8266step0 raw8266step0Labels := by
      have hz : ∀ j, raw8266 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8266step0 = (fun i j => raw8266 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8266step0 raw8266; decide +kernel
      have hl : raw8266step0Labels = raw8266Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8266 raw8266Labels permutation346 hz
    _ = mixedMoment B node2995 node2995Labels := by rfl

def raw8267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8267Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8267step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw8267step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8267 raw8267Labels = mixedMoment B node2962 node2962Labels := by
  calc
    mixedMoment B raw8267 raw8267Labels = mixedMoment B raw8267step0 raw8267step0Labels := by
      have hz : ∀ j, raw8267 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8267step0 = (fun i j => raw8267 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8267step0 raw8267; decide +kernel
      have hl : raw8267step0Labels = raw8267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8267 raw8267Labels permutation346 hz
    mixedMoment B raw8267step0 raw8267step0Labels = mixedMoment B raw8267step1 raw8267step1Labels := by
      have ha : raw8267step1 = (fun i j => raw8267step0 (permutation119 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8267step1 raw8267step0; decide +kernel
      have hl : raw8267step1Labels = raw8267step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8267step0 raw8267step0Labels permutation119 permutation4
    _ = mixedMoment B node2962 node2962Labels := by rfl

def raw8268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8268Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8268step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8268 raw8268Labels = mixedMoment B node2995 node2995Labels := by
  calc
    mixedMoment B raw8268 raw8268Labels = mixedMoment B raw8268step0 raw8268step0Labels := by
      have hz : ∀ j, raw8268 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8268step0 = (fun i j => raw8268 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8268step0 raw8268; decide +kernel
      have hl : raw8268step0Labels = raw8268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8268 raw8268Labels permutation265 hz
    _ = mixedMoment B node2995 node2995Labels := by rfl

def raw8269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8269Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8269step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8269step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8269step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8269 raw8269Labels = mixedMoment B node3118 node3118Labels := by
  calc
    mixedMoment B raw8269 raw8269Labels = mixedMoment B raw8269step0 raw8269step0Labels := by
      have hz : ∀ j, raw8269 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8269step0 = (fun i j => raw8269 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8269step0 raw8269; decide +kernel
      have hl : raw8269step0Labels = raw8269Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8269 raw8269Labels permutation346 hz
    mixedMoment B raw8269step0 raw8269step0Labels = mixedMoment B raw8269step1 raw8269step1Labels := by
      have hz : ∀ j, raw8269step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8269step1 = (fun i j => raw8269step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8269step1 raw8269step0; decide +kernel
      have hl : raw8269step1Labels = raw8269step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8269step0 raw8269step0Labels permutation56 hz
    _ = mixedMoment B node3118 node3118Labels := by rfl

def raw8270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8270Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8270step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8270step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8270step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8270 raw8270Labels = mixedMoment B node2952 node2952Labels := by
  calc
    mixedMoment B raw8270 raw8270Labels = mixedMoment B raw8270step0 raw8270step0Labels := by
      have hz : ∀ j, raw8270 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8270step0 = (fun i j => raw8270 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8270step0 raw8270; decide +kernel
      have hl : raw8270step0Labels = raw8270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8270 raw8270Labels permutation265 hz
    mixedMoment B raw8270step0 raw8270step0Labels = mixedMoment B raw8270step1 raw8270step1Labels := by
      have ha : raw8270step1 = (fun i j => raw8270step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8270step1 raw8270step0; decide +kernel
      have hl : raw8270step1Labels = raw8270step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8270step0 raw8270step0Labels permutation40 permutation2
    _ = mixedMoment B node2952 node2952Labels := by rfl

def raw8271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8271Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8271step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8271step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8271step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8271 raw8271Labels = mixedMoment B node2967 node2967Labels := by
  calc
    mixedMoment B raw8271 raw8271Labels = mixedMoment B raw8271step0 raw8271step0Labels := by
      have hz : ∀ j, raw8271 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8271step0 = (fun i j => raw8271 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8271step0 raw8271; decide +kernel
      have hl : raw8271step0Labels = raw8271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8271 raw8271Labels permutation346 hz
    mixedMoment B raw8271step0 raw8271step0Labels = mixedMoment B raw8271step1 raw8271step1Labels := by
      have hz : ∀ j, raw8271step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8271step1 = (fun i j => raw8271step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8271step1 raw8271step0; decide +kernel
      have hl : raw8271step1Labels = raw8271step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8271step0 raw8271step0Labels permutation56 hz
    _ = mixedMoment B node2967 node2967Labels := by rfl

def raw8272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8272Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8272step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw8272step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8272 raw8272Labels = mixedMoment B node2962 node2962Labels := by
  calc
    mixedMoment B raw8272 raw8272Labels = mixedMoment B raw8272step0 raw8272step0Labels := by
      have hz : ∀ j, raw8272 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8272step0 = (fun i j => raw8272 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8272step0 raw8272; decide +kernel
      have hl : raw8272step0Labels = raw8272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8272 raw8272Labels permutation265 hz
    mixedMoment B raw8272step0 raw8272step0Labels = mixedMoment B raw8272step1 raw8272step1Labels := by
      have ha : raw8272step1 = (fun i j => raw8272step0 (permutation119 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8272step1 raw8272step0; decide +kernel
      have hl : raw8272step1Labels = raw8272step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8272step0 raw8272step0Labels permutation119 permutation4
    _ = mixedMoment B node2962 node2962Labels := by rfl

def raw8273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![1, 2, -3]]
def raw8273Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![1, 2, -3]]
def raw8273step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8273step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -3, 1], ![1, 2, -3]]
def raw8273step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8273step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw8273step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8273 raw8273Labels = mixedMoment B node2967 node2967Labels := by
  calc
    mixedMoment B raw8273 raw8273Labels = mixedMoment B raw8273step0 raw8273step0Labels := by
      have hz : ∀ j, raw8273 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8273step0 = (fun i j => raw8273 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8273step0 raw8273; decide +kernel
      have hl : raw8273step0Labels = raw8273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8273 raw8273Labels permutation346 hz
    mixedMoment B raw8273step0 raw8273step0Labels = mixedMoment B raw8273step1 raw8273step1Labels := by
      have hz : ∀ j, raw8273step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8273step1 = (fun i j => raw8273step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8273step1 raw8273step0; decide +kernel
      have hl : raw8273step1Labels = raw8273step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8273step0 raw8273step0Labels permutation56 hz
    mixedMoment B raw8273step1 raw8273step1Labels = mixedMoment B raw8273step2 raw8273step2Labels := by
      have ha : raw8273step2 = (fun i j => raw8273step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8273step2 raw8273step1; decide +kernel
      have hl : raw8273step2Labels = raw8273step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8273step1 raw8273step1Labels permutation22 permutation4
    _ = mixedMoment B node2967 node2967Labels := by rfl

def raw8274 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8274step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8274step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8274step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8274 raw8274Labels = mixedMoment B node5161 node5161Labels := by
  calc
    mixedMoment B raw8274 raw8274Labels = mixedMoment B raw8274step0 raw8274step0Labels := by
      have hz : ∀ j, raw8274 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8274step0 = (fun i j => raw8274 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8274step0 raw8274; decide +kernel
      have hl : raw8274step0Labels = raw8274Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8274 raw8274Labels permutation265 hz
    mixedMoment B raw8274step0 raw8274step0Labels = mixedMoment B raw8274step1 raw8274step1Labels := by
      have ha : raw8274step1 = (fun i j => raw8274step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8274step1 raw8274step0; decide +kernel
      have hl : raw8274step1Labels = raw8274step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8274step0 raw8274step0Labels permutation139 permutation2
    _ = mixedMoment B node5161 node5161Labels := by rfl

def raw8275 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8275step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8275step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8275step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8275step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8275step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8275 raw8275Labels = mixedMoment B node4617 node4617Labels := by
  calc
    mixedMoment B raw8275 raw8275Labels = mixedMoment B raw8275step0 raw8275step0Labels := by
      have hz : ∀ j, raw8275 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8275step0 = (fun i j => raw8275 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8275step0 raw8275; decide +kernel
      have hl : raw8275step0Labels = raw8275Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8275 raw8275Labels permutation346 hz
    mixedMoment B raw8275step0 raw8275step0Labels = mixedMoment B raw8275step1 raw8275step1Labels := by
      have hz : ∀ j, raw8275step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8275step1 = (fun i j => raw8275step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8275step1 raw8275step0; decide +kernel
      have hl : raw8275step1Labels = raw8275step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8275step0 raw8275step0Labels permutation56 hz
    mixedMoment B raw8275step1 raw8275step1Labels = mixedMoment B raw8275step2 raw8275step2Labels := by
      have ha : raw8275step2 = (fun i j => raw8275step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8275step2 raw8275step1; decide +kernel
      have hl : raw8275step2Labels = raw8275step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8275step1 raw8275step1Labels permutation31 permutation2
    _ = mixedMoment B node4617 node4617Labels := by rfl

def raw8276 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8276step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw8276step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8276step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw8276step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8276step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw8276step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8276 raw8276Labels = mixedMoment B node4879 node4879Labels := by
  calc
    mixedMoment B raw8276 raw8276Labels = mixedMoment B raw8276step0 raw8276step0Labels := by
      have hz : ∀ j, raw8276 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8276step0 = (fun i j => raw8276 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8276step0 raw8276; decide +kernel
      have hl : raw8276step0Labels = raw8276Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8276 raw8276Labels permutation346 hz
    mixedMoment B raw8276step0 raw8276step0Labels = mixedMoment B raw8276step1 raw8276step1Labels := by
      have ha : raw8276step1 = (fun i j => raw8276step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8276step1 raw8276step0; decide +kernel
      have hl : raw8276step1Labels = raw8276step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8276step0 raw8276step0Labels permutation50 permutation4
    mixedMoment B raw8276step1 raw8276step1Labels = mixedMoment B raw8276step2 raw8276step2Labels := by
      have ha : raw8276step2 = -raw8276step1 := by apply Matrix.ext; change ∀ i j, raw8276step2 i j = -(raw8276step1 i j); unfold raw8276step2 raw8276step1; decide +kernel
      have hl : raw8276step2Labels = raw8276step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8276step2 raw8276step2Labels = mixedMoment B raw8276step3 raw8276step3Labels := by
      have ha : raw8276step3 = raw8276step2 := by apply Matrix.ext; unfold raw8276step3 raw8276step2; decide +kernel
      have hl : raw8276step2Labels = labelEmbedding7 ∘ raw8276step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8276step2 raw8276step2Labels raw8276step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4879 node4879Labels := by rfl

def raw8277 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8277step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw8277step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8277 raw8277Labels = mixedMoment B node5159 node5159Labels := by
  calc
    mixedMoment B raw8277 raw8277Labels = mixedMoment B raw8277step0 raw8277step0Labels := by
      have ha : raw8277step0 = (fun i j => raw8277 (permutation644 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8277step0 raw8277; decide +kernel
      have hl : raw8277step0Labels = raw8277Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8277 raw8277Labels permutation644 permutation2
    _ = mixedMoment B node5159 node5159Labels := by rfl

def raw8278 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8278step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8278step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw8278step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8278step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw8278step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8278 raw8278Labels = mixedMoment B node4613 node4613Labels := by
  calc
    mixedMoment B raw8278 raw8278Labels = mixedMoment B raw8278step0 raw8278step0Labels := by
      have hz : ∀ j, raw8278 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8278step0 = (fun i j => raw8278 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8278step0 raw8278; decide +kernel
      have hl : raw8278step0Labels = raw8278Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8278 raw8278Labels permutation346 hz
    mixedMoment B raw8278step0 raw8278step0Labels = mixedMoment B raw8278step1 raw8278step1Labels := by
      have ha : raw8278step1 = (fun i j => raw8278step0 (permutation128 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8278step1 raw8278step0; decide +kernel
      have hl : raw8278step1Labels = raw8278step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8278step0 raw8278step0Labels permutation128 permutation3
    mixedMoment B raw8278step1 raw8278step1Labels = mixedMoment B raw8278step2 raw8278step2Labels := by
      have ha : raw8278step2 = raw8278step1 := by apply Matrix.ext; unfold raw8278step2 raw8278step1; decide +kernel
      have hl : raw8278step1Labels = labelEmbedding6 ∘ raw8278step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8278step1 raw8278step1Labels raw8278step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4613 node4613Labels := by rfl

def raw8279 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8279step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8279step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw8279step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8279step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw8279step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8279step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw8279step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8279 raw8279Labels = mixedMoment B node4879 node4879Labels := by
  calc
    mixedMoment B raw8279 raw8279Labels = mixedMoment B raw8279step0 raw8279step0Labels := by
      have hz : ∀ j, raw8279 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8279step0 = (fun i j => raw8279 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8279step0 raw8279; decide +kernel
      have hl : raw8279step0Labels = raw8279Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8279 raw8279Labels permutation265 hz
    mixedMoment B raw8279step0 raw8279step0Labels = mixedMoment B raw8279step1 raw8279step1Labels := by
      have ha : raw8279step1 = (fun i j => raw8279step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8279step1 raw8279step0; decide +kernel
      have hl : raw8279step1Labels = raw8279step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8279step0 raw8279step0Labels permutation50 permutation4
    mixedMoment B raw8279step1 raw8279step1Labels = mixedMoment B raw8279step2 raw8279step2Labels := by
      have ha : raw8279step2 = -raw8279step1 := by apply Matrix.ext; change ∀ i j, raw8279step2 i j = -(raw8279step1 i j); unfold raw8279step2 raw8279step1; decide +kernel
      have hl : raw8279step2Labels = raw8279step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8279step2 raw8279step2Labels = mixedMoment B raw8279step3 raw8279step3Labels := by
      have ha : raw8279step3 = raw8279step2 := by apply Matrix.ext; unfold raw8279step3 raw8279step2; decide +kernel
      have hl : raw8279step2Labels = labelEmbedding7 ∘ raw8279step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8279step2 raw8279step2Labels raw8279step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4879 node4879Labels := by rfl

def raw8280 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8280step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw8280step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8280step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw8280step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8280 raw8280Labels = mixedMoment B node4613 node4613Labels := by
  calc
    mixedMoment B raw8280 raw8280Labels = mixedMoment B raw8280step0 raw8280step0Labels := by
      have hz : ∀ j, raw8280 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8280step0 = (fun i j => raw8280 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8280step0 raw8280; decide +kernel
      have hl : raw8280step0Labels = raw8280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8280 raw8280Labels permutation265 hz
    mixedMoment B raw8280step0 raw8280step0Labels = mixedMoment B raw8280step1 raw8280step1Labels := by
      have ha : raw8280step1 = (fun i j => raw8280step0 (permutation128 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8280step1 raw8280step0; decide +kernel
      have hl : raw8280step1Labels = raw8280step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8280step0 raw8280step0Labels permutation128 permutation3
    mixedMoment B raw8280step1 raw8280step1Labels = mixedMoment B raw8280step2 raw8280step2Labels := by
      have ha : raw8280step2 = raw8280step1 := by apply Matrix.ext; unfold raw8280step2 raw8280step1; decide +kernel
      have hl : raw8280step1Labels = labelEmbedding6 ∘ raw8280step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8280step1 raw8280step1Labels raw8280step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4613 node4613Labels := by rfl

def raw8281 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8281step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8281step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8281step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8281step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw8281step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8281step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8281step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8281step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw8281step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8281 raw8281Labels = mixedMoment B node4884 node4884Labels := by
  calc
    mixedMoment B raw8281 raw8281Labels = mixedMoment B raw8281step0 raw8281step0Labels := by
      have hz : ∀ j, raw8281 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8281step0 = (fun i j => raw8281 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8281step0 raw8281; decide +kernel
      have hl : raw8281step0Labels = raw8281Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8281 raw8281Labels permutation346 hz
    mixedMoment B raw8281step0 raw8281step0Labels = mixedMoment B raw8281step1 raw8281step1Labels := by
      have hz : ∀ j, raw8281step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8281step1 = (fun i j => raw8281step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8281step1 raw8281step0; decide +kernel
      have hl : raw8281step1Labels = raw8281step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8281step0 raw8281step0Labels permutation56 hz
    mixedMoment B raw8281step1 raw8281step1Labels = mixedMoment B raw8281step2 raw8281step2Labels := by
      have ha : raw8281step2 = (fun i j => raw8281step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8281step2 raw8281step1; decide +kernel
      have hl : raw8281step2Labels = raw8281step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8281step1 raw8281step1Labels permutation12 permutation4
    mixedMoment B raw8281step2 raw8281step2Labels = mixedMoment B raw8281step3 raw8281step3Labels := by
      have ha : raw8281step3 = -raw8281step2 := by apply Matrix.ext; change ∀ i j, raw8281step3 i j = -(raw8281step2 i j); unfold raw8281step3 raw8281step2; decide +kernel
      have hl : raw8281step3Labels = raw8281step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8281step3 raw8281step3Labels = mixedMoment B raw8281step4 raw8281step4Labels := by
      have ha : raw8281step4 = raw8281step3 := by apply Matrix.ext; unfold raw8281step4 raw8281step3; decide +kernel
      have hl : raw8281step3Labels = labelEmbedding7 ∘ raw8281step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8281step3 raw8281step3Labels raw8281step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4884 node4884Labels := by rfl

def raw8282 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8282step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8282step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -2, 0]]
def raw8282step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8282 raw8282Labels = mixedMoment B node5165 node5165Labels := by
  calc
    mixedMoment B raw8282 raw8282Labels = mixedMoment B raw8282step0 raw8282step0Labels := by
      have hz : ∀ j, raw8282 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8282step0 = (fun i j => raw8282 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8282step0 raw8282; decide +kernel
      have hl : raw8282step0Labels = raw8282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8282 raw8282Labels permutation265 hz
    mixedMoment B raw8282step0 raw8282step0Labels = mixedMoment B raw8282step1 raw8282step1Labels := by
      have ha : raw8282step1 = (fun i j => raw8282step0 (permutation138 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8282step1 raw8282step0; decide +kernel
      have hl : raw8282step1Labels = raw8282step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8282step0 raw8282step0Labels permutation138 permutation2
    _ = mixedMoment B node5165 node5165Labels := by rfl

def raw8283 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8283step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8283step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8283step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw8283step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8283step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw8283step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8283 raw8283Labels = mixedMoment B node4615 node4615Labels := by
  calc
    mixedMoment B raw8283 raw8283Labels = mixedMoment B raw8283step0 raw8283step0Labels := by
      have hz : ∀ j, raw8283 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8283step0 = (fun i j => raw8283 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8283step0 raw8283; decide +kernel
      have hl : raw8283step0Labels = raw8283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8283 raw8283Labels permutation346 hz
    mixedMoment B raw8283step0 raw8283step0Labels = mixedMoment B raw8283step1 raw8283step1Labels := by
      have hz : ∀ j, raw8283step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8283step1 = (fun i j => raw8283step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8283step1 raw8283step0; decide +kernel
      have hl : raw8283step1Labels = raw8283step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8283step0 raw8283step0Labels permutation56 hz
    mixedMoment B raw8283step1 raw8283step1Labels = mixedMoment B raw8283step2 raw8283step2Labels := by
      have ha : raw8283step2 = (fun i j => raw8283step1 (permutation27 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8283step2 raw8283step1; decide +kernel
      have hl : raw8283step2Labels = raw8283step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8283step1 raw8283step1Labels permutation27 permutation3
    mixedMoment B raw8283step2 raw8283step2Labels = mixedMoment B raw8283step3 raw8283step3Labels := by
      have ha : raw8283step3 = raw8283step2 := by apply Matrix.ext; unfold raw8283step3 raw8283step2; decide +kernel
      have hl : raw8283step2Labels = labelEmbedding6 ∘ raw8283step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8283step2 raw8283step2Labels raw8283step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4615 node4615Labels := by rfl

def raw8284 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw8284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw8284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8284step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw8284step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8284step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw8284step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8284step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw8284step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw8284step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw8284step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8284 raw8284Labels = mixedMoment B node4881 node4881Labels := by
  calc
    mixedMoment B raw8284 raw8284Labels = mixedMoment B raw8284step0 raw8284step0Labels := by
      have hz : ∀ j, raw8284 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8284step0 = (fun i j => raw8284 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8284step0 raw8284; decide +kernel
      have hl : raw8284step0Labels = raw8284Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8284 raw8284Labels permutation346 hz
    mixedMoment B raw8284step0 raw8284step0Labels = mixedMoment B raw8284step1 raw8284step1Labels := by
      have hz : ∀ j, raw8284step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8284step1 = (fun i j => raw8284step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8284step1 raw8284step0; decide +kernel
      have hl : raw8284step1Labels = raw8284step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8284step0 raw8284step0Labels permutation56 hz
    mixedMoment B raw8284step1 raw8284step1Labels = mixedMoment B raw8284step2 raw8284step2Labels := by
      have ha : raw8284step2 = (fun i j => raw8284step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8284step2 raw8284step1; decide +kernel
      have hl : raw8284step2Labels = raw8284step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8284step1 raw8284step1Labels permutation12 permutation4
    mixedMoment B raw8284step2 raw8284step2Labels = mixedMoment B raw8284step3 raw8284step3Labels := by
      have ha : raw8284step3 = -raw8284step2 := by apply Matrix.ext; change ∀ i j, raw8284step3 i j = -(raw8284step2 i j); unfold raw8284step3 raw8284step2; decide +kernel
      have hl : raw8284step3Labels = raw8284step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8284step3 raw8284step3Labels = mixedMoment B raw8284step4 raw8284step4Labels := by
      have ha : raw8284step4 = raw8284step3 := by apply Matrix.ext; unfold raw8284step4 raw8284step3; decide +kernel
      have hl : raw8284step3Labels = labelEmbedding7 ∘ raw8284step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8284step3 raw8284step3Labels raw8284step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4881 node4881Labels := by rfl

def raw8285 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw8285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw8285step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8285step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw8285step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw8285step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw8285step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8285 raw8285Labels = mixedMoment B node5106 node5106Labels := by
  calc
    mixedMoment B raw8285 raw8285Labels = mixedMoment B raw8285step0 raw8285step0Labels := by
      have hz : ∀ j, raw8285 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8285step0 = (fun i j => raw8285 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8285step0 raw8285; decide +kernel
      have hl : raw8285step0Labels = raw8285Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8285 raw8285Labels permutation265 hz
    mixedMoment B raw8285step0 raw8285step0Labels = mixedMoment B raw8285step1 raw8285step1Labels := by
      have ha : raw8285step1 = (fun i j => raw8285step0 (permutation119 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8285step1 raw8285step0; decide +kernel
      have hl : raw8285step1Labels = raw8285step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8285step0 raw8285step0Labels permutation119 permutation5
    mixedMoment B raw8285step1 raw8285step1Labels = mixedMoment B raw8285step2 raw8285step2Labels := by
      have ha : raw8285step2 = raw8285step1 := by apply Matrix.ext; unfold raw8285step2 raw8285step1; decide +kernel
      have hl : raw8285step1Labels = labelEmbedding8 ∘ raw8285step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8285step1 raw8285step1Labels raw8285step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5106 node5106Labels := by rfl

def raw8286 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-4, 2, 2]]
def raw8286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-4, 2, 2]]
def raw8286step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8286step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -3, 1], ![-4, 2, 2]]
def raw8286step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8286step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw8286step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8286step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw8286step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8286 raw8286Labels = mixedMoment B node4614 node4614Labels := by
  calc
    mixedMoment B raw8286 raw8286Labels = mixedMoment B raw8286step0 raw8286step0Labels := by
      have hz : ∀ j, raw8286 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8286step0 = (fun i j => raw8286 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8286step0 raw8286; decide +kernel
      have hl : raw8286step0Labels = raw8286Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8286 raw8286Labels permutation346 hz
    mixedMoment B raw8286step0 raw8286step0Labels = mixedMoment B raw8286step1 raw8286step1Labels := by
      have hz : ∀ j, raw8286step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8286step1 = (fun i j => raw8286step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8286step1 raw8286step0; decide +kernel
      have hl : raw8286step1Labels = raw8286step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8286step0 raw8286step0Labels permutation56 hz
    mixedMoment B raw8286step1 raw8286step1Labels = mixedMoment B raw8286step2 raw8286step2Labels := by
      have ha : raw8286step2 = (fun i j => raw8286step1 (permutation26 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8286step2 raw8286step1; decide +kernel
      have hl : raw8286step2Labels = raw8286step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8286step1 raw8286step1Labels permutation26 permutation3
    mixedMoment B raw8286step2 raw8286step2Labels = mixedMoment B raw8286step3 raw8286step3Labels := by
      have ha : raw8286step3 = raw8286step2 := by apply Matrix.ext; unfold raw8286step3 raw8286step2; decide +kernel
      have hl : raw8286step2Labels = labelEmbedding6 ∘ raw8286step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8286step2 raw8286step2Labels raw8286step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4614 node4614Labels := by rfl

def raw8287 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8287Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8287step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8287step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8287 raw8287Labels = mixedMoment B node2964 node2964Labels := by
  calc
    mixedMoment B raw8287 raw8287Labels = mixedMoment B raw8287step0 raw8287step0Labels := by
      have hz : ∀ j, raw8287 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8287step0 = (fun i j => raw8287 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8287step0 raw8287; decide +kernel
      have hl : raw8287step0Labels = raw8287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8287 raw8287Labels permutation265 hz
    mixedMoment B raw8287step0 raw8287step0Labels = mixedMoment B raw8287step1 raw8287step1Labels := by
      have ha : raw8287step1 = (fun i j => raw8287step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8287step1 raw8287step0; decide +kernel
      have hl : raw8287step1Labels = raw8287step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8287step0 raw8287step0Labels permutation137 permutation3
    _ = mixedMoment B node2964 node2964Labels := by rfl

def raw8288 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8288Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8288step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8288step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8288step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8288step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8288step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8288 raw8288Labels = mixedMoment B node1306 node1306Labels := by
  calc
    mixedMoment B raw8288 raw8288Labels = mixedMoment B raw8288step0 raw8288step0Labels := by
      have hz : ∀ j, raw8288 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8288step0 = (fun i j => raw8288 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8288step0 raw8288; decide +kernel
      have hl : raw8288step0Labels = raw8288Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8288 raw8288Labels permutation346 hz
    mixedMoment B raw8288step0 raw8288step0Labels = mixedMoment B raw8288step1 raw8288step1Labels := by
      have hz : ∀ j, raw8288step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8288step1 = (fun i j => raw8288step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8288step1 raw8288step0; decide +kernel
      have hl : raw8288step1Labels = raw8288step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8288step0 raw8288step0Labels permutation56 hz
    mixedMoment B raw8288step1 raw8288step1Labels = mixedMoment B raw8288step2 raw8288step2Labels := by
      have ha : raw8288step2 = (fun i j => raw8288step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8288step2 raw8288step1; decide +kernel
      have hl : raw8288step2Labels = raw8288step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8288step1 raw8288step1Labels permutation29 permutation3
    _ = mixedMoment B node1306 node1306Labels := by rfl

def raw8289 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8289Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8289step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8289step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8289step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8289 raw8289Labels = mixedMoment B node2246 node2246Labels := by
  calc
    mixedMoment B raw8289 raw8289Labels = mixedMoment B raw8289step0 raw8289step0Labels := by
      have hz : ∀ j, raw8289 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8289step0 = (fun i j => raw8289 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8289step0 raw8289; decide +kernel
      have hl : raw8289step0Labels = raw8289Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8289 raw8289Labels permutation346 hz
    mixedMoment B raw8289step0 raw8289step0Labels = mixedMoment B raw8289step1 raw8289step1Labels := by
      have ha : raw8289step1 = (fun i j => raw8289step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8289step1 raw8289step0; decide +kernel
      have hl : raw8289step1Labels = raw8289step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8289step0 raw8289step0Labels permutation32 permutation6
    _ = mixedMoment B node2246 node2246Labels := by rfl

def raw8290 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8290Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8290step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8290step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8290 raw8290Labels = mixedMoment B node2711 node2711Labels := by
  calc
    mixedMoment B raw8290 raw8290Labels = mixedMoment B raw8290step0 raw8290step0Labels := by
      have ha : raw8290step0 = (fun i j => raw8290 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8290step0 raw8290; decide +kernel
      have hl : raw8290step0Labels = raw8290Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8290 raw8290Labels permutation176 permutation6
    _ = mixedMoment B node2711 node2711Labels := by rfl

def raw8291 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8291Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8291step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw8291step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8291 raw8291Labels = mixedMoment B node1286 node1286Labels := by
  calc
    mixedMoment B raw8291 raw8291Labels = mixedMoment B raw8291step0 raw8291step0Labels := by
      have hz : ∀ j, raw8291 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8291step0 = (fun i j => raw8291 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8291step0 raw8291; decide +kernel
      have hl : raw8291step0Labels = raw8291Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8291 raw8291Labels permutation346 hz
    mixedMoment B raw8291step0 raw8291step0Labels = mixedMoment B raw8291step1 raw8291step1Labels := by
      have ha : raw8291step1 = (fun i j => raw8291step0 (permutation128 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8291step1 raw8291step0; decide +kernel
      have hl : raw8291step1Labels = raw8291step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8291step0 raw8291step0Labels permutation128 permutation3
    _ = mixedMoment B node1286 node1286Labels := by rfl

def raw8292 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8292Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8292step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8292step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8292 raw8292Labels = mixedMoment B node2246 node2246Labels := by
  calc
    mixedMoment B raw8292 raw8292Labels = mixedMoment B raw8292step0 raw8292step0Labels := by
      have hz : ∀ j, raw8292 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8292step0 = (fun i j => raw8292 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8292step0 raw8292; decide +kernel
      have hl : raw8292step0Labels = raw8292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8292 raw8292Labels permutation265 hz
    mixedMoment B raw8292step0 raw8292step0Labels = mixedMoment B raw8292step1 raw8292step1Labels := by
      have ha : raw8292step1 = (fun i j => raw8292step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8292step1 raw8292step0; decide +kernel
      have hl : raw8292step1Labels = raw8292step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8292step0 raw8292step0Labels permutation32 permutation6
    _ = mixedMoment B node2246 node2246Labels := by rfl

def raw8293 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8293Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8293step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw8293step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8293 raw8293Labels = mixedMoment B node1286 node1286Labels := by
  calc
    mixedMoment B raw8293 raw8293Labels = mixedMoment B raw8293step0 raw8293step0Labels := by
      have hz : ∀ j, raw8293 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8293step0 = (fun i j => raw8293 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8293step0 raw8293; decide +kernel
      have hl : raw8293step0Labels = raw8293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8293 raw8293Labels permutation265 hz
    mixedMoment B raw8293step0 raw8293step0Labels = mixedMoment B raw8293step1 raw8293step1Labels := by
      have ha : raw8293step1 = (fun i j => raw8293step0 (permutation128 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8293step1 raw8293step0; decide +kernel
      have hl : raw8293step1Labels = raw8293step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8293step0 raw8293step0Labels permutation128 permutation3
    _ = mixedMoment B node1286 node1286Labels := by rfl

def raw8294 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8294Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8294step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8294step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8294step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8294step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw8294step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8294 raw8294Labels = mixedMoment B node2280 node2280Labels := by
  calc
    mixedMoment B raw8294 raw8294Labels = mixedMoment B raw8294step0 raw8294step0Labels := by
      have hz : ∀ j, raw8294 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8294step0 = (fun i j => raw8294 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8294step0 raw8294; decide +kernel
      have hl : raw8294step0Labels = raw8294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8294 raw8294Labels permutation346 hz
    mixedMoment B raw8294step0 raw8294step0Labels = mixedMoment B raw8294step1 raw8294step1Labels := by
      have hz : ∀ j, raw8294step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8294step1 = (fun i j => raw8294step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8294step1 raw8294step0; decide +kernel
      have hl : raw8294step1Labels = raw8294step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8294step0 raw8294step0Labels permutation56 hz
    mixedMoment B raw8294step1 raw8294step1Labels = mixedMoment B raw8294step2 raw8294step2Labels := by
      have ha : raw8294step2 = (fun i j => raw8294step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8294step2 raw8294step1; decide +kernel
      have hl : raw8294step2Labels = raw8294step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8294step1 raw8294step1Labels permutation8 permutation6
    _ = mixedMoment B node2280 node2280Labels := by rfl

def raw8295 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8295Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8295step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8295step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw8295step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8295 raw8295Labels = mixedMoment B node2733 node2733Labels := by
  calc
    mixedMoment B raw8295 raw8295Labels = mixedMoment B raw8295step0 raw8295step0Labels := by
      have hz : ∀ j, raw8295 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8295step0 = (fun i j => raw8295 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8295step0 raw8295; decide +kernel
      have hl : raw8295step0Labels = raw8295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8295 raw8295Labels permutation265 hz
    mixedMoment B raw8295step0 raw8295step0Labels = mixedMoment B raw8295step1 raw8295step1Labels := by
      have ha : raw8295step1 = (fun i j => raw8295step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8295step1 raw8295step0; decide +kernel
      have hl : raw8295step1Labels = raw8295step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8295step0 raw8295step0Labels permutation32 permutation6
    _ = mixedMoment B node2733 node2733Labels := by rfl

def raw8296 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8296Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8296step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8296step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8296step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8296step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw8296step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8296 raw8296Labels = mixedMoment B node1288 node1288Labels := by
  calc
    mixedMoment B raw8296 raw8296Labels = mixedMoment B raw8296step0 raw8296step0Labels := by
      have hz : ∀ j, raw8296 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8296step0 = (fun i j => raw8296 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8296step0 raw8296; decide +kernel
      have hl : raw8296step0Labels = raw8296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8296 raw8296Labels permutation346 hz
    mixedMoment B raw8296step0 raw8296step0Labels = mixedMoment B raw8296step1 raw8296step1Labels := by
      have hz : ∀ j, raw8296step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8296step1 = (fun i j => raw8296step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8296step1 raw8296step0; decide +kernel
      have hl : raw8296step1Labels = raw8296step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8296step0 raw8296step0Labels permutation56 hz
    mixedMoment B raw8296step1 raw8296step1Labels = mixedMoment B raw8296step2 raw8296step2Labels := by
      have ha : raw8296step2 = (fun i j => raw8296step1 (permutation27 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8296step2 raw8296step1; decide +kernel
      have hl : raw8296step2Labels = raw8296step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8296step1 raw8296step1Labels permutation27 permutation3
    _ = mixedMoment B node1288 node1288Labels := by rfl

def raw8297 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw8297Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw8297step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8297step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw8297step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8297step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw8297step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8297 raw8297Labels = mixedMoment B node2267 node2267Labels := by
  calc
    mixedMoment B raw8297 raw8297Labels = mixedMoment B raw8297step0 raw8297step0Labels := by
      have hz : ∀ j, raw8297 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8297step0 = (fun i j => raw8297 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8297step0 raw8297; decide +kernel
      have hl : raw8297step0Labels = raw8297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8297 raw8297Labels permutation346 hz
    mixedMoment B raw8297step0 raw8297step0Labels = mixedMoment B raw8297step1 raw8297step1Labels := by
      have hz : ∀ j, raw8297step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8297step1 = (fun i j => raw8297step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8297step1 raw8297step0; decide +kernel
      have hl : raw8297step1Labels = raw8297step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8297step0 raw8297step0Labels permutation56 hz
    mixedMoment B raw8297step1 raw8297step1Labels = mixedMoment B raw8297step2 raw8297step2Labels := by
      have ha : raw8297step2 = (fun i j => raw8297step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8297step2 raw8297step1; decide +kernel
      have hl : raw8297step2Labels = raw8297step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8297step1 raw8297step1Labels permutation8 permutation6
    _ = mixedMoment B node2267 node2267Labels := by rfl

def raw8298 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw8298Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw8298step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw8298step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8298 raw8298Labels = mixedMoment B node2725 node2725Labels := by
  calc
    mixedMoment B raw8298 raw8298Labels = mixedMoment B raw8298step0 raw8298step0Labels := by
      have hz : ∀ j, raw8298 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8298step0 = (fun i j => raw8298 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8298step0 raw8298; decide +kernel
      have hl : raw8298step0Labels = raw8298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8298 raw8298Labels permutation265 hz
    mixedMoment B raw8298step0 raw8298step0Labels = mixedMoment B raw8298step1 raw8298step1Labels := by
      have ha : raw8298step1 = (fun i j => raw8298step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8298step1 raw8298step0; decide +kernel
      have hl : raw8298step1Labels = raw8298step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8298step0 raw8298step0Labels permutation32 permutation6
    _ = mixedMoment B node2725 node2725Labels := by rfl

def raw8299 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-4, 2, 2]]
def raw8299Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-4, 2, 2]]
def raw8299step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8299step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -3, 1], ![-4, 2, 2]]
def raw8299step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8299step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw8299step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8299 raw8299Labels = mixedMoment B node1287 node1287Labels := by
  calc
    mixedMoment B raw8299 raw8299Labels = mixedMoment B raw8299step0 raw8299step0Labels := by
      have hz : ∀ j, raw8299 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8299step0 = (fun i j => raw8299 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8299step0 raw8299; decide +kernel
      have hl : raw8299step0Labels = raw8299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8299 raw8299Labels permutation346 hz
    mixedMoment B raw8299step0 raw8299step0Labels = mixedMoment B raw8299step1 raw8299step1Labels := by
      have hz : ∀ j, raw8299step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8299step1 = (fun i j => raw8299step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8299step1 raw8299step0; decide +kernel
      have hl : raw8299step1Labels = raw8299step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8299step0 raw8299step0Labels permutation56 hz
    mixedMoment B raw8299step1 raw8299step1Labels = mixedMoment B raw8299step2 raw8299step2Labels := by
      have ha : raw8299step2 = (fun i j => raw8299step1 (permutation26 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8299step2 raw8299step1; decide +kernel
      have hl : raw8299step2Labels = raw8299step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8299step1 raw8299step1Labels permutation26 permutation3
    _ = mixedMoment B node1287 node1287Labels := by rfl

def raw8300 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8300Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8300step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8300step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw8300step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8300step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw8300step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8300 raw8300Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw8300 raw8300Labels = mixedMoment B raw8300step0 raw8300step0Labels := by
      have hz : ∀ j, raw8300 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8300step0 = (fun i j => raw8300 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8300step0 raw8300; decide +kernel
      have hl : raw8300step0Labels = raw8300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8300 raw8300Labels permutation265 hz
    mixedMoment B raw8300step0 raw8300step0Labels = mixedMoment B raw8300step1 raw8300step1Labels := by
      have ha : raw8300step1 = (fun i j => raw8300step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8300step1 raw8300step0; decide +kernel
      have hl : raw8300step1Labels = raw8300step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8300step0 raw8300step0Labels permutation38 permutation7
    mixedMoment B raw8300step1 raw8300step1Labels = mixedMoment B raw8300step2 raw8300step2Labels := by
      have ha : raw8300step2 = raw8300step1 := by apply Matrix.ext; unfold raw8300step2 raw8300step1; decide +kernel
      have hl : raw8300step1Labels = labelEmbedding1 ∘ raw8300step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8300step1 raw8300step1Labels raw8300step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2719 node2719Labels := by rfl

def raw8301 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8301Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8301step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8301step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8301step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8301step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8301step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8301step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8301step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8301 raw8301Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw8301 raw8301Labels = mixedMoment B raw8301step0 raw8301step0Labels := by
      have hz : ∀ j, raw8301 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8301step0 = (fun i j => raw8301 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8301step0 raw8301; decide +kernel
      have hl : raw8301step0Labels = raw8301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8301 raw8301Labels permutation346 hz
    mixedMoment B raw8301step0 raw8301step0Labels = mixedMoment B raw8301step1 raw8301step1Labels := by
      have hz : ∀ j, raw8301step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8301step1 = (fun i j => raw8301step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8301step1 raw8301step0; decide +kernel
      have hl : raw8301step1Labels = raw8301step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8301step0 raw8301step0Labels permutation56 hz
    mixedMoment B raw8301step1 raw8301step1Labels = mixedMoment B raw8301step2 raw8301step2Labels := by
      have ha : raw8301step2 = (fun i j => raw8301step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8301step2 raw8301step1; decide +kernel
      have hl : raw8301step2Labels = raw8301step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8301step1 raw8301step1Labels permutation8 permutation7
    mixedMoment B raw8301step2 raw8301step2Labels = mixedMoment B raw8301step3 raw8301step3Labels := by
      have ha : raw8301step3 = raw8301step2 := by apply Matrix.ext; unfold raw8301step3 raw8301step2; decide +kernel
      have hl : raw8301step2Labels = labelEmbedding1 ∘ raw8301step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8301step2 raw8301step2Labels raw8301step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

def raw8302 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8302Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8302step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8302step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8302step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8302step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw8302step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8302step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw8302step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8302 raw8302Labels = mixedMoment B node2737 node2737Labels := by
  calc
    mixedMoment B raw8302 raw8302Labels = mixedMoment B raw8302step0 raw8302step0Labels := by
      have hz : ∀ j, raw8302 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8302step0 = (fun i j => raw8302 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8302step0 raw8302; decide +kernel
      have hl : raw8302step0Labels = raw8302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8302 raw8302Labels permutation346 hz
    mixedMoment B raw8302step0 raw8302step0Labels = mixedMoment B raw8302step1 raw8302step1Labels := by
      have hz : ∀ j, raw8302step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8302step1 = (fun i j => raw8302step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8302step1 raw8302step0; decide +kernel
      have hl : raw8302step1Labels = raw8302step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8302step0 raw8302step0Labels permutation56 hz
    mixedMoment B raw8302step1 raw8302step1Labels = mixedMoment B raw8302step2 raw8302step2Labels := by
      have ha : raw8302step2 = (fun i j => raw8302step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8302step2 raw8302step1; decide +kernel
      have hl : raw8302step2Labels = raw8302step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8302step1 raw8302step1Labels permutation8 permutation7
    mixedMoment B raw8302step2 raw8302step2Labels = mixedMoment B raw8302step3 raw8302step3Labels := by
      have ha : raw8302step3 = raw8302step2 := by apply Matrix.ext; unfold raw8302step3 raw8302step2; decide +kernel
      have hl : raw8302step2Labels = labelEmbedding1 ∘ raw8302step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8302step2 raw8302step2Labels raw8302step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2737 node2737Labels := by rfl

def raw8303 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8303Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8303step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8303step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw8303step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8303step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8303step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8303step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8303step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8303 raw8303Labels = mixedMoment B node3158 node3158Labels := by
  calc
    mixedMoment B raw8303 raw8303Labels = mixedMoment B raw8303step0 raw8303step0Labels := by
      have hz : ∀ j, raw8303 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8303step0 = (fun i j => raw8303 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8303step0 raw8303; decide +kernel
      have hl : raw8303step0Labels = raw8303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8303 raw8303Labels permutation346 hz
    mixedMoment B raw8303step0 raw8303step0Labels = mixedMoment B raw8303step1 raw8303step1Labels := by
      have ha : raw8303step1 = (fun i j => raw8303step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8303step1 raw8303step0; decide +kernel
      have hl : raw8303step1Labels = raw8303step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8303step0 raw8303step0Labels permutation50 permutation5
    mixedMoment B raw8303step1 raw8303step1Labels = mixedMoment B raw8303step2 raw8303step2Labels := by
      have ha : raw8303step2 = -raw8303step1 := by apply Matrix.ext; change ∀ i j, raw8303step2 i j = -(raw8303step1 i j); unfold raw8303step2 raw8303step1; decide +kernel
      have hl : raw8303step2Labels = raw8303step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8303step2 raw8303step2Labels = mixedMoment B raw8303step3 raw8303step3Labels := by
      have ha : raw8303step3 = raw8303step2 := by apply Matrix.ext; unfold raw8303step3 raw8303step2; decide +kernel
      have hl : raw8303step2Labels = labelEmbedding1 ∘ raw8303step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8303step2 raw8303step2Labels raw8303step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3158 node3158Labels := by rfl

def raw8304 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8304Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8304step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw8304step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8304step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw8304step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8304 raw8304Labels = mixedMoment B node3063 node3063Labels := by
  calc
    mixedMoment B raw8304 raw8304Labels = mixedMoment B raw8304step0 raw8304step0Labels := by
      have ha : raw8304step0 = (fun i j => raw8304 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8304step0 raw8304; decide +kernel
      have hl : raw8304step0Labels = raw8304Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8304 raw8304Labels permutation158 permutation7
    mixedMoment B raw8304step0 raw8304step0Labels = mixedMoment B raw8304step1 raw8304step1Labels := by
      have ha : raw8304step1 = raw8304step0 := by apply Matrix.ext; unfold raw8304step1 raw8304step0; decide +kernel
      have hl : raw8304step0Labels = labelEmbedding1 ∘ raw8304step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8304step0 raw8304step0Labels raw8304step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3063 node3063Labels := by rfl

def raw8305 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8305Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8305step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8305step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8305step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8305step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8305step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8305 raw8305Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw8305 raw8305Labels = mixedMoment B raw8305step0 raw8305step0Labels := by
      have hz : ∀ j, raw8305 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8305step0 = (fun i j => raw8305 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8305step0 raw8305; decide +kernel
      have hl : raw8305step0Labels = raw8305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8305 raw8305Labels permutation346 hz
    mixedMoment B raw8305step0 raw8305step0Labels = mixedMoment B raw8305step1 raw8305step1Labels := by
      have ha : raw8305step1 = (fun i j => raw8305step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8305step1 raw8305step0; decide +kernel
      have hl : raw8305step1Labels = raw8305step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8305step0 raw8305step0Labels permutation32 permutation7
    mixedMoment B raw8305step1 raw8305step1Labels = mixedMoment B raw8305step2 raw8305step2Labels := by
      have ha : raw8305step2 = raw8305step1 := by apply Matrix.ext; unfold raw8305step2 raw8305step1; decide +kernel
      have hl : raw8305step1Labels = labelEmbedding1 ∘ raw8305step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8305step1 raw8305step1Labels raw8305step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3075 node3075Labels := by rfl

def raw8306 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8306Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8306step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8306step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw8306step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8306step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw8306step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8306 raw8306Labels = mixedMoment B node3072 node3072Labels := by
  calc
    mixedMoment B raw8306 raw8306Labels = mixedMoment B raw8306step0 raw8306step0Labels := by
      have hz : ∀ j, raw8306 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8306step0 = (fun i j => raw8306 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8306step0 raw8306; decide +kernel
      have hl : raw8306step0Labels = raw8306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8306 raw8306Labels permutation346 hz
    mixedMoment B raw8306step0 raw8306step0Labels = mixedMoment B raw8306step1 raw8306step1Labels := by
      have ha : raw8306step1 = (fun i j => raw8306step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8306step1 raw8306step0; decide +kernel
      have hl : raw8306step1Labels = raw8306step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8306step0 raw8306step0Labels permutation32 permutation7
    mixedMoment B raw8306step1 raw8306step1Labels = mixedMoment B raw8306step2 raw8306step2Labels := by
      have ha : raw8306step2 = raw8306step1 := by apply Matrix.ext; unfold raw8306step2 raw8306step1; decide +kernel
      have hl : raw8306step1Labels = labelEmbedding1 ∘ raw8306step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8306step1 raw8306step1Labels raw8306step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3072 node3072Labels := by rfl

def raw8307 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8307Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8307step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw8307step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8307step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8307step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8307step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8307step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8307 raw8307Labels = mixedMoment B node3158 node3158Labels := by
  calc
    mixedMoment B raw8307 raw8307Labels = mixedMoment B raw8307step0 raw8307step0Labels := by
      have hz : ∀ j, raw8307 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8307step0 = (fun i j => raw8307 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8307step0 raw8307; decide +kernel
      have hl : raw8307step0Labels = raw8307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8307 raw8307Labels permutation265 hz
    mixedMoment B raw8307step0 raw8307step0Labels = mixedMoment B raw8307step1 raw8307step1Labels := by
      have ha : raw8307step1 = (fun i j => raw8307step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8307step1 raw8307step0; decide +kernel
      have hl : raw8307step1Labels = raw8307step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8307step0 raw8307step0Labels permutation50 permutation5
    mixedMoment B raw8307step1 raw8307step1Labels = mixedMoment B raw8307step2 raw8307step2Labels := by
      have ha : raw8307step2 = -raw8307step1 := by apply Matrix.ext; change ∀ i j, raw8307step2 i j = -(raw8307step1 i j); unfold raw8307step2 raw8307step1; decide +kernel
      have hl : raw8307step2Labels = raw8307step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8307step2 raw8307step2Labels = mixedMoment B raw8307step3 raw8307step3Labels := by
      have ha : raw8307step3 = raw8307step2 := by apply Matrix.ext; unfold raw8307step3 raw8307step2; decide +kernel
      have hl : raw8307step2Labels = labelEmbedding1 ∘ raw8307step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8307step2 raw8307step2Labels raw8307step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3158 node3158Labels := by rfl

def raw8308 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8308Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8308step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8308step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw8308step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8308step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw8308step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8308 raw8308Labels = mixedMoment B node3072 node3072Labels := by
  calc
    mixedMoment B raw8308 raw8308Labels = mixedMoment B raw8308step0 raw8308step0Labels := by
      have hz : ∀ j, raw8308 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8308step0 = (fun i j => raw8308 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8308step0 raw8308; decide +kernel
      have hl : raw8308step0Labels = raw8308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8308 raw8308Labels permutation265 hz
    mixedMoment B raw8308step0 raw8308step0Labels = mixedMoment B raw8308step1 raw8308step1Labels := by
      have ha : raw8308step1 = (fun i j => raw8308step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8308step1 raw8308step0; decide +kernel
      have hl : raw8308step1Labels = raw8308step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8308step0 raw8308step0Labels permutation32 permutation7
    mixedMoment B raw8308step1 raw8308step1Labels = mixedMoment B raw8308step2 raw8308step2Labels := by
      have ha : raw8308step2 = raw8308step1 := by apply Matrix.ext; unfold raw8308step2 raw8308step1; decide +kernel
      have hl : raw8308step1Labels = labelEmbedding1 ∘ raw8308step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8308step1 raw8308step1Labels raw8308step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3072 node3072Labels := by rfl

def raw8309 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8309Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8309step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8309step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8309step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8309step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-2, 1, 1], ![-2, 0, 2]]
def raw8309step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8309step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, -1, -1], ![2, 0, -2]]
def raw8309step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8309step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, -1, -1], ![2, 0, -2]]
def raw8309step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8309 raw8309Labels = mixedMoment B node3161 node3161Labels := by
  calc
    mixedMoment B raw8309 raw8309Labels = mixedMoment B raw8309step0 raw8309step0Labels := by
      have hz : ∀ j, raw8309 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8309step0 = (fun i j => raw8309 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8309step0 raw8309; decide +kernel
      have hl : raw8309step0Labels = raw8309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8309 raw8309Labels permutation346 hz
    mixedMoment B raw8309step0 raw8309step0Labels = mixedMoment B raw8309step1 raw8309step1Labels := by
      have hz : ∀ j, raw8309step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8309step1 = (fun i j => raw8309step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8309step1 raw8309step0; decide +kernel
      have hl : raw8309step1Labels = raw8309step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8309step0 raw8309step0Labels permutation56 hz
    mixedMoment B raw8309step1 raw8309step1Labels = mixedMoment B raw8309step2 raw8309step2Labels := by
      have ha : raw8309step2 = (fun i j => raw8309step1 (permutation13 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8309step2 raw8309step1; decide +kernel
      have hl : raw8309step2Labels = raw8309step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8309step1 raw8309step1Labels permutation13 permutation5
    mixedMoment B raw8309step2 raw8309step2Labels = mixedMoment B raw8309step3 raw8309step3Labels := by
      have ha : raw8309step3 = -raw8309step2 := by apply Matrix.ext; change ∀ i j, raw8309step3 i j = -(raw8309step2 i j); unfold raw8309step3 raw8309step2; decide +kernel
      have hl : raw8309step3Labels = raw8309step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8309step3 raw8309step3Labels = mixedMoment B raw8309step4 raw8309step4Labels := by
      have ha : raw8309step4 = raw8309step3 := by apply Matrix.ext; unfold raw8309step4 raw8309step3; decide +kernel
      have hl : raw8309step3Labels = labelEmbedding1 ∘ raw8309step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8309step3 raw8309step3Labels raw8309step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3161 node3161Labels := by rfl

def raw8310 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8310Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8310step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw8310step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8310step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw8310step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8310 raw8310Labels = mixedMoment B node3035 node3035Labels := by
  calc
    mixedMoment B raw8310 raw8310Labels = mixedMoment B raw8310step0 raw8310step0Labels := by
      have hz : ∀ j, raw8310 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8310step0 = (fun i j => raw8310 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8310step0 raw8310; decide +kernel
      have hl : raw8310step0Labels = raw8310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8310 raw8310Labels permutation265 hz
    mixedMoment B raw8310step0 raw8310step0Labels = mixedMoment B raw8310step1 raw8310step1Labels := by
      have ha : raw8310step1 = (fun i j => raw8310step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8310step1 raw8310step0; decide +kernel
      have hl : raw8310step1Labels = raw8310step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8310step0 raw8310step0Labels permutation38 permutation7
    mixedMoment B raw8310step1 raw8310step1Labels = mixedMoment B raw8310step2 raw8310step2Labels := by
      have ha : raw8310step2 = raw8310step1 := by apply Matrix.ext; unfold raw8310step2 raw8310step1; decide +kernel
      have hl : raw8310step1Labels = labelEmbedding1 ∘ raw8310step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8310step1 raw8310step1Labels raw8310step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3035 node3035Labels := by rfl

def raw8311 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8311Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8311step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8311step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8311step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8311step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -2, 1], ![2, 2, -4]]
def raw8311step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8311step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -2, 1], ![2, 2, -4]]
def raw8311step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8311 raw8311Labels = mixedMoment B node3049 node3049Labels := by
  calc
    mixedMoment B raw8311 raw8311Labels = mixedMoment B raw8311step0 raw8311step0Labels := by
      have hz : ∀ j, raw8311 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8311step0 = (fun i j => raw8311 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8311step0 raw8311; decide +kernel
      have hl : raw8311step0Labels = raw8311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8311 raw8311Labels permutation346 hz
    mixedMoment B raw8311step0 raw8311step0Labels = mixedMoment B raw8311step1 raw8311step1Labels := by
      have hz : ∀ j, raw8311step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8311step1 = (fun i j => raw8311step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8311step1 raw8311step0; decide +kernel
      have hl : raw8311step1Labels = raw8311step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8311step0 raw8311step0Labels permutation56 hz
    mixedMoment B raw8311step1 raw8311step1Labels = mixedMoment B raw8311step2 raw8311step2Labels := by
      have ha : raw8311step2 = (fun i j => raw8311step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8311step2 raw8311step1; decide +kernel
      have hl : raw8311step2Labels = raw8311step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8311step1 raw8311step1Labels permutation8 permutation7
    mixedMoment B raw8311step2 raw8311step2Labels = mixedMoment B raw8311step3 raw8311step3Labels := by
      have ha : raw8311step3 = raw8311step2 := by apply Matrix.ext; unfold raw8311step3 raw8311step2; decide +kernel
      have hl : raw8311step2Labels = labelEmbedding1 ∘ raw8311step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8311step2 raw8311step2Labels raw8311step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3049 node3049Labels := by rfl

def raw8312 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw8312Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw8312step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8312step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw8312step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8312step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw8312step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8312step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw8312step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8312 raw8312Labels = mixedMoment B node2520 node2520Labels := by
  calc
    mixedMoment B raw8312 raw8312Labels = mixedMoment B raw8312step0 raw8312step0Labels := by
      have hz : ∀ j, raw8312 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8312step0 = (fun i j => raw8312 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8312step0 raw8312; decide +kernel
      have hl : raw8312step0Labels = raw8312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8312 raw8312Labels permutation346 hz
    mixedMoment B raw8312step0 raw8312step0Labels = mixedMoment B raw8312step1 raw8312step1Labels := by
      have hz : ∀ j, raw8312step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8312step1 = (fun i j => raw8312step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8312step1 raw8312step0; decide +kernel
      have hl : raw8312step1Labels = raw8312step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8312step0 raw8312step0Labels permutation56 hz
    mixedMoment B raw8312step1 raw8312step1Labels = mixedMoment B raw8312step2 raw8312step2Labels := by
      have ha : raw8312step2 = (fun i j => raw8312step1 (permutation23 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8312step2 raw8312step1; decide +kernel
      have hl : raw8312step2Labels = raw8312step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8312step1 raw8312step1Labels permutation23 permutation5
    mixedMoment B raw8312step2 raw8312step2Labels = mixedMoment B raw8312step3 raw8312step3Labels := by
      have ha : raw8312step3 = raw8312step2 := by apply Matrix.ext; unfold raw8312step3 raw8312step2; decide +kernel
      have hl : raw8312step2Labels = labelEmbedding1 ∘ raw8312step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8312step2 raw8312step2Labels raw8312step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2520 node2520Labels := by rfl

def raw8313 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw8313Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw8313step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw8313step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8313step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw8313step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8313 raw8313Labels = mixedMoment B node2516 node2516Labels := by
  calc
    mixedMoment B raw8313 raw8313Labels = mixedMoment B raw8313step0 raw8313step0Labels := by
      have hz : ∀ j, raw8313 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8313step0 = (fun i j => raw8313 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8313step0 raw8313; decide +kernel
      have hl : raw8313step0Labels = raw8313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8313 raw8313Labels permutation265 hz
    mixedMoment B raw8313step0 raw8313step0Labels = mixedMoment B raw8313step1 raw8313step1Labels := by
      have ha : raw8313step1 = (fun i j => raw8313step0 (permutation119 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8313step1 raw8313step0; decide +kernel
      have hl : raw8313step1Labels = raw8313step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8313step0 raw8313step0Labels permutation119 permutation5
    mixedMoment B raw8313step1 raw8313step1Labels = mixedMoment B raw8313step2 raw8313step2Labels := by
      have ha : raw8313step2 = raw8313step1 := by apply Matrix.ext; unfold raw8313step2 raw8313step1; decide +kernel
      have hl : raw8313step1Labels = labelEmbedding1 ∘ raw8313step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8313step1 raw8313step1Labels raw8313step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2516 node2516Labels := by rfl

def raw8314 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-4, 2, 2]]
def raw8314Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-4, 2, 2]]
def raw8314step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8314step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -3, 1], ![-4, 2, 2]]
def raw8314step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8314step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -3, 1], ![2, 2, -4]]
def raw8314step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8314step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -3, 1], ![2, 2, -4]]
def raw8314step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8314 raw8314Labels = mixedMoment B node2521 node2521Labels := by
  calc
    mixedMoment B raw8314 raw8314Labels = mixedMoment B raw8314step0 raw8314step0Labels := by
      have hz : ∀ j, raw8314 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8314step0 = (fun i j => raw8314 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8314step0 raw8314; decide +kernel
      have hl : raw8314step0Labels = raw8314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8314 raw8314Labels permutation346 hz
    mixedMoment B raw8314step0 raw8314step0Labels = mixedMoment B raw8314step1 raw8314step1Labels := by
      have hz : ∀ j, raw8314step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8314step1 = (fun i j => raw8314step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8314step1 raw8314step0; decide +kernel
      have hl : raw8314step1Labels = raw8314step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8314step0 raw8314step0Labels permutation56 hz
    mixedMoment B raw8314step1 raw8314step1Labels = mixedMoment B raw8314step2 raw8314step2Labels := by
      have ha : raw8314step2 = (fun i j => raw8314step1 (permutation22 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8314step2 raw8314step1; decide +kernel
      have hl : raw8314step2Labels = raw8314step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8314step1 raw8314step1Labels permutation22 permutation5
    mixedMoment B raw8314step2 raw8314step2Labels = mixedMoment B raw8314step3 raw8314step3Labels := by
      have ha : raw8314step3 = raw8314step2 := by apply Matrix.ext; unfold raw8314step3 raw8314step2; decide +kernel
      have hl : raw8314step2Labels = labelEmbedding1 ∘ raw8314step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8314step2 raw8314step2Labels raw8314step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2521 node2521Labels := by rfl

def raw8315 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8315Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8315step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8315step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8315 raw8315Labels = mixedMoment B node2588 node2588Labels := by
  calc
    mixedMoment B raw8315 raw8315Labels = mixedMoment B raw8315step0 raw8315step0Labels := by
      have hz : ∀ j, raw8315 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8315step0 = (fun i j => raw8315 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8315step0 raw8315; decide +kernel
      have hl : raw8315step0Labels = raw8315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8315 raw8315Labels permutation265 hz
    mixedMoment B raw8315step0 raw8315step0Labels = mixedMoment B raw8315step1 raw8315step1Labels := by
      have ha : raw8315step1 = (fun i j => raw8315step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8315step1 raw8315step0; decide +kernel
      have hl : raw8315step1Labels = raw8315step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8315step0 raw8315step0Labels permutation139 permutation2
    _ = mixedMoment B node2588 node2588Labels := by rfl

def raw8316 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8316Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8316step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8316step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8316step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8316step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8316step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8316 raw8316Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw8316 raw8316Labels = mixedMoment B raw8316step0 raw8316step0Labels := by
      have hz : ∀ j, raw8316 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8316step0 = (fun i j => raw8316 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8316step0 raw8316; decide +kernel
      have hl : raw8316step0Labels = raw8316Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8316 raw8316Labels permutation346 hz
    mixedMoment B raw8316step0 raw8316step0Labels = mixedMoment B raw8316step1 raw8316step1Labels := by
      have hz : ∀ j, raw8316step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8316step1 = (fun i j => raw8316step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8316step1 raw8316step0; decide +kernel
      have hl : raw8316step1Labels = raw8316step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8316step0 raw8316step0Labels permutation56 hz
    mixedMoment B raw8316step1 raw8316step1Labels = mixedMoment B raw8316step2 raw8316step2Labels := by
      have ha : raw8316step2 = (fun i j => raw8316step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8316step2 raw8316step1; decide +kernel
      have hl : raw8316step2Labels = raw8316step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8316step1 raw8316step1Labels permutation31 permutation2
    _ = mixedMoment B node2740 node2740Labels := by rfl

def raw8317 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8317Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8317step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8317step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-4, 2, 2]]
def raw8317step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8317step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8317step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8317 raw8317Labels = mixedMoment B node1292 node1292Labels := by
  calc
    mixedMoment B raw8317 raw8317Labels = mixedMoment B raw8317step0 raw8317step0Labels := by
      have hz : ∀ j, raw8317 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8317step0 = (fun i j => raw8317 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8317step0 raw8317; decide +kernel
      have hl : raw8317step0Labels = raw8317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8317 raw8317Labels permutation346 hz
    mixedMoment B raw8317step0 raw8317step0Labels = mixedMoment B raw8317step1 raw8317step1Labels := by
      have hz : ∀ j, raw8317step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8317step1 = (fun i j => raw8317step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8317step1 raw8317step0; decide +kernel
      have hl : raw8317step1Labels = raw8317step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8317step0 raw8317step0Labels permutation56 hz
    mixedMoment B raw8317step1 raw8317step1Labels = mixedMoment B raw8317step2 raw8317step2Labels := by
      have ha : raw8317step2 = (fun i j => raw8317step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8317step2 raw8317step1; decide +kernel
      have hl : raw8317step2Labels = raw8317step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8317step1 raw8317step1Labels permutation31 permutation2
    _ = mixedMoment B node1292 node1292Labels := by rfl

def raw8318 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8318Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8318step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw8318step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8318step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw8318step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8318 raw8318Labels = mixedMoment B node2132 node2132Labels := by
  calc
    mixedMoment B raw8318 raw8318Labels = mixedMoment B raw8318step0 raw8318step0Labels := by
      have hz : ∀ j, raw8318 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8318step0 = (fun i j => raw8318 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8318step0 raw8318; decide +kernel
      have hl : raw8318step0Labels = raw8318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8318 raw8318Labels permutation346 hz
    mixedMoment B raw8318step0 raw8318step0Labels = mixedMoment B raw8318step1 raw8318step1Labels := by
      have ha : raw8318step1 = (fun i j => raw8318step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8318step1 raw8318step0; decide +kernel
      have hl : raw8318step1Labels = raw8318step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8318step0 raw8318step0Labels permutation50 permutation4
    mixedMoment B raw8318step1 raw8318step1Labels = mixedMoment B raw8318step2 raw8318step2Labels := by
      have ha : raw8318step2 = -raw8318step1 := by apply Matrix.ext; change ∀ i j, raw8318step2 i j = -(raw8318step1 i j); unfold raw8318step2 raw8318step1; decide +kernel
      have hl : raw8318step2Labels = raw8318step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2132 node2132Labels := by rfl

def raw8319 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8319Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw8319step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8319step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw8319step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8319step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw8319step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8319 raw8319Labels = mixedMoment B node2132 node2132Labels := by
  calc
    mixedMoment B raw8319 raw8319Labels = mixedMoment B raw8319step0 raw8319step0Labels := by
      have hz : ∀ j, raw8319 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8319step0 = (fun i j => raw8319 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8319step0 raw8319; decide +kernel
      have hl : raw8319step0Labels = raw8319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8319 raw8319Labels permutation265 hz
    mixedMoment B raw8319step0 raw8319step0Labels = mixedMoment B raw8319step1 raw8319step1Labels := by
      have ha : raw8319step1 = (fun i j => raw8319step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8319step1 raw8319step0; decide +kernel
      have hl : raw8319step1Labels = raw8319step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8319step0 raw8319step0Labels permutation50 permutation4
    mixedMoment B raw8319step1 raw8319step1Labels = mixedMoment B raw8319step2 raw8319step2Labels := by
      have ha : raw8319step2 = -raw8319step1 := by apply Matrix.ext; change ∀ i j, raw8319step2 i j = -(raw8319step1 i j); unfold raw8319step2 raw8319step1; decide +kernel
      have hl : raw8319step2Labels = raw8319step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2132 node2132Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
