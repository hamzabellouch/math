import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw24192 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24192Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24192step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24192step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24192step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24192step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24192step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24192 raw24192Labels = mixedMoment B node1414 node1414Labels := by
  calc
    mixedMoment B raw24192 raw24192Labels = mixedMoment B raw24192step0 raw24192step0Labels := by
      have hz : ∀ j, raw24192 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24192step0 = (fun i j => raw24192 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24192step0 raw24192; decide +kernel
      have hl : raw24192step0Labels = raw24192Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24192 raw24192Labels permutation265 hz
    mixedMoment B raw24192step0 raw24192step0Labels = mixedMoment B raw24192step1 raw24192step1Labels := by
      have ha : raw24192step1 = (fun i j => raw24192step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24192step1 raw24192step0; decide +kernel
      have hl : raw24192step1Labels = raw24192step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24192step0 raw24192step0Labels permutation32 permutation7
    mixedMoment B raw24192step1 raw24192step1Labels = mixedMoment B raw24192step2 raw24192step2Labels := by
      have ha : raw24192step2 = raw24192step1 := by apply Matrix.ext; unfold raw24192step2 raw24192step1; decide +kernel
      have hl : raw24192step1Labels = labelEmbedding1 ∘ raw24192step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24192step1 raw24192step1Labels raw24192step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1414 node1414Labels := by rfl

def raw24193 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24193Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24193step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24193step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24193step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24193step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24193 raw24193Labels = mixedMoment B node1216 node1216Labels := by
  calc
    mixedMoment B raw24193 raw24193Labels = mixedMoment B raw24193step0 raw24193step0Labels := by
      have ha : raw24193step0 = (fun i j => raw24193 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24193step0 raw24193; decide +kernel
      have hl : raw24193step0Labels = raw24193Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24193 raw24193Labels permutation176 permutation7
    mixedMoment B raw24193step0 raw24193step0Labels = mixedMoment B raw24193step1 raw24193step1Labels := by
      have ha : raw24193step1 = raw24193step0 := by apply Matrix.ext; unfold raw24193step1 raw24193step0; decide +kernel
      have hl : raw24193step0Labels = labelEmbedding1 ∘ raw24193step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24193step0 raw24193step0Labels raw24193step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1216 node1216Labels := by rfl

def raw24194 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24194Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24194step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24194step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24194step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24194step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24194 raw24194Labels = mixedMoment B node1241 node1241Labels := by
  calc
    mixedMoment B raw24194 raw24194Labels = mixedMoment B raw24194step0 raw24194step0Labels := by
      have hz : ∀ j, raw24194 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24194step0 = (fun i j => raw24194 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24194step0 raw24194; decide +kernel
      have hl : raw24194step0Labels = raw24194Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24194 raw24194Labels permutation265 hz
    mixedMoment B raw24194step0 raw24194step0Labels = mixedMoment B raw24194step1 raw24194step1Labels := by
      have ha : raw24194step1 = (fun i j => raw24194step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24194step1 raw24194step0; decide +kernel
      have hl : raw24194step1Labels = raw24194step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24194step0 raw24194step0Labels permutation34 permutation7
    mixedMoment B raw24194step1 raw24194step1Labels = mixedMoment B raw24194step2 raw24194step2Labels := by
      have ha : raw24194step2 = raw24194step1 := by apply Matrix.ext; unfold raw24194step2 raw24194step1; decide +kernel
      have hl : raw24194step1Labels = labelEmbedding1 ∘ raw24194step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24194step1 raw24194step1Labels raw24194step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1241 node1241Labels := by rfl

def raw24195 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24195Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24195step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24195step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24195step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24195step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24195 raw24195Labels = mixedMoment B node1241 node1241Labels := by
  calc
    mixedMoment B raw24195 raw24195Labels = mixedMoment B raw24195step0 raw24195step0Labels := by
      have hz : ∀ j, raw24195 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24195step0 = (fun i j => raw24195 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24195step0 raw24195; decide +kernel
      have hl : raw24195step0Labels = raw24195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24195 raw24195Labels permutation265 hz
    mixedMoment B raw24195step0 raw24195step0Labels = mixedMoment B raw24195step1 raw24195step1Labels := by
      have ha : raw24195step1 = (fun i j => raw24195step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24195step1 raw24195step0; decide +kernel
      have hl : raw24195step1Labels = raw24195step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24195step0 raw24195step0Labels permutation32 permutation7
    mixedMoment B raw24195step1 raw24195step1Labels = mixedMoment B raw24195step2 raw24195step2Labels := by
      have ha : raw24195step2 = raw24195step1 := by apply Matrix.ext; unfold raw24195step2 raw24195step1; decide +kernel
      have hl : raw24195step1Labels = labelEmbedding1 ∘ raw24195step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24195step1 raw24195step1Labels raw24195step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1241 node1241Labels := by rfl

def raw24196 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24196Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24196step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24196step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24196step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24196step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24196step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24196 raw24196Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw24196 raw24196Labels = mixedMoment B raw24196step0 raw24196step0Labels := by
      have hz : ∀ j, raw24196 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24196step0 = (fun i j => raw24196 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24196step0 raw24196; decide +kernel
      have hl : raw24196step0Labels = raw24196Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24196 raw24196Labels permutation265 hz
    mixedMoment B raw24196step0 raw24196step0Labels = mixedMoment B raw24196step1 raw24196step1Labels := by
      have ha : raw24196step1 = (fun i j => raw24196step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24196step1 raw24196step0; decide +kernel
      have hl : raw24196step1Labels = raw24196step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24196step0 raw24196step0Labels permutation32 permutation7
    mixedMoment B raw24196step1 raw24196step1Labels = mixedMoment B raw24196step2 raw24196step2Labels := by
      have ha : raw24196step2 = raw24196step1 := by apply Matrix.ext; unfold raw24196step2 raw24196step1; decide +kernel
      have hl : raw24196step1Labels = labelEmbedding1 ∘ raw24196step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24196step1 raw24196step1Labels raw24196step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1240 node1240Labels := by rfl

def raw24197 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24197Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24197step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24197step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24197step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24197step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24197step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24197step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24197step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24197 raw24197Labels = mixedMoment B node1448 node1448Labels := by
  calc
    mixedMoment B raw24197 raw24197Labels = mixedMoment B raw24197step0 raw24197step0Labels := by
      have hz : ∀ j, raw24197 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24197step0 = (fun i j => raw24197 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24197step0 raw24197; decide +kernel
      have hl : raw24197step0Labels = raw24197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24197 raw24197Labels permutation346 hz
    mixedMoment B raw24197step0 raw24197step0Labels = mixedMoment B raw24197step1 raw24197step1Labels := by
      have hz : ∀ j, raw24197step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24197step1 = (fun i j => raw24197step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24197step1 raw24197step0; decide +kernel
      have hl : raw24197step1Labels = raw24197step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24197step0 raw24197step0Labels permutation56 hz
    mixedMoment B raw24197step1 raw24197step1Labels = mixedMoment B raw24197step2 raw24197step2Labels := by
      have ha : raw24197step2 = (fun i j => raw24197step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24197step2 raw24197step1; decide +kernel
      have hl : raw24197step2Labels = raw24197step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24197step1 raw24197step1Labels permutation8 permutation7
    mixedMoment B raw24197step2 raw24197step2Labels = mixedMoment B raw24197step3 raw24197step3Labels := by
      have ha : raw24197step3 = raw24197step2 := by apply Matrix.ext; unfold raw24197step3 raw24197step2; decide +kernel
      have hl : raw24197step2Labels = labelEmbedding1 ∘ raw24197step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24197step2 raw24197step2Labels raw24197step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1448 node1448Labels := by rfl

def raw24198 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24198Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24198step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24198step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24198step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24198 raw24198Labels = mixedMoment B node1267 node1267Labels := by
  calc
    mixedMoment B raw24198 raw24198Labels = mixedMoment B raw24198step0 raw24198step0Labels := by
      have hz : ∀ j, raw24198 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24198step0 = (fun i j => raw24198 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24198step0 raw24198; decide +kernel
      have hl : raw24198step0Labels = raw24198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24198 raw24198Labels permutation346 hz
    mixedMoment B raw24198step0 raw24198step0Labels = mixedMoment B raw24198step1 raw24198step1Labels := by
      have ha : raw24198step1 = (fun i j => raw24198step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24198step1 raw24198step0; decide +kernel
      have hl : raw24198step1Labels = raw24198step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24198step0 raw24198step0Labels permutation32 permutation7
    mixedMoment B raw24198step1 raw24198step1Labels = mixedMoment B raw24198step2 raw24198step2Labels := by
      have ha : raw24198step2 = raw24198step1 := by apply Matrix.ext; unfold raw24198step2 raw24198step1; decide +kernel
      have hl : raw24198step1Labels = labelEmbedding1 ∘ raw24198step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24198step1 raw24198step1Labels raw24198step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1267 node1267Labels := by rfl

def raw24199 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24199Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24199step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24199step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24199step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24199step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24199step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24199 raw24199Labels = mixedMoment B node1267 node1267Labels := by
  calc
    mixedMoment B raw24199 raw24199Labels = mixedMoment B raw24199step0 raw24199step0Labels := by
      have hz : ∀ j, raw24199 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24199step0 = (fun i j => raw24199 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24199step0 raw24199; decide +kernel
      have hl : raw24199step0Labels = raw24199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24199 raw24199Labels permutation265 hz
    mixedMoment B raw24199step0 raw24199step0Labels = mixedMoment B raw24199step1 raw24199step1Labels := by
      have ha : raw24199step1 = (fun i j => raw24199step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24199step1 raw24199step0; decide +kernel
      have hl : raw24199step1Labels = raw24199step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24199step0 raw24199step0Labels permutation32 permutation7
    mixedMoment B raw24199step1 raw24199step1Labels = mixedMoment B raw24199step2 raw24199step2Labels := by
      have ha : raw24199step2 = raw24199step1 := by apply Matrix.ext; unfold raw24199step2 raw24199step1; decide +kernel
      have hl : raw24199step1Labels = labelEmbedding1 ∘ raw24199step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24199step1 raw24199step1Labels raw24199step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1267 node1267Labels := by rfl

def raw24200 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24200Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24200step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24200step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24200step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24200step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24200step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24200step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24200step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24200 raw24200Labels = mixedMoment B node1302 node1302Labels := by
  calc
    mixedMoment B raw24200 raw24200Labels = mixedMoment B raw24200step0 raw24200step0Labels := by
      have hz : ∀ j, raw24200 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24200step0 = (fun i j => raw24200 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24200step0 raw24200; decide +kernel
      have hl : raw24200step0Labels = raw24200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24200 raw24200Labels permutation346 hz
    mixedMoment B raw24200step0 raw24200step0Labels = mixedMoment B raw24200step1 raw24200step1Labels := by
      have hz : ∀ j, raw24200step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24200step1 = (fun i j => raw24200step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24200step1 raw24200step0; decide +kernel
      have hl : raw24200step1Labels = raw24200step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24200step0 raw24200step0Labels permutation56 hz
    mixedMoment B raw24200step1 raw24200step1Labels = mixedMoment B raw24200step2 raw24200step2Labels := by
      have ha : raw24200step2 = (fun i j => raw24200step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24200step2 raw24200step1; decide +kernel
      have hl : raw24200step2Labels = raw24200step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24200step1 raw24200step1Labels permutation8 permutation7
    mixedMoment B raw24200step2 raw24200step2Labels = mixedMoment B raw24200step3 raw24200step3Labels := by
      have ha : raw24200step3 = raw24200step2 := by apply Matrix.ext; unfold raw24200step3 raw24200step2; decide +kernel
      have hl : raw24200step2Labels = labelEmbedding1 ∘ raw24200step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24200step2 raw24200step2Labels raw24200step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1302 node1302Labels := by rfl

def raw24201 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24201Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24201step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24201step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24201step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24201step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24201step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24201step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24201step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24201 raw24201Labels = mixedMoment B node1301 node1301Labels := by
  calc
    mixedMoment B raw24201 raw24201Labels = mixedMoment B raw24201step0 raw24201step0Labels := by
      have hz : ∀ j, raw24201 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24201step0 = (fun i j => raw24201 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24201step0 raw24201; decide +kernel
      have hl : raw24201step0Labels = raw24201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24201 raw24201Labels permutation346 hz
    mixedMoment B raw24201step0 raw24201step0Labels = mixedMoment B raw24201step1 raw24201step1Labels := by
      have hz : ∀ j, raw24201step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24201step1 = (fun i j => raw24201step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24201step1 raw24201step0; decide +kernel
      have hl : raw24201step1Labels = raw24201step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24201step0 raw24201step0Labels permutation56 hz
    mixedMoment B raw24201step1 raw24201step1Labels = mixedMoment B raw24201step2 raw24201step2Labels := by
      have ha : raw24201step2 = (fun i j => raw24201step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24201step2 raw24201step1; decide +kernel
      have hl : raw24201step2Labels = raw24201step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24201step1 raw24201step1Labels permutation8 permutation7
    mixedMoment B raw24201step2 raw24201step2Labels = mixedMoment B raw24201step3 raw24201step3Labels := by
      have ha : raw24201step3 = raw24201step2 := by apply Matrix.ext; unfold raw24201step3 raw24201step2; decide +kernel
      have hl : raw24201step2Labels = labelEmbedding1 ∘ raw24201step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24201step2 raw24201step2Labels raw24201step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1301 node1301Labels := by rfl

def raw24202 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24202Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24202step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24202step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24202step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24202step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24202step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24202step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24202step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24202 raw24202Labels = mixedMoment B node1448 node1448Labels := by
  calc
    mixedMoment B raw24202 raw24202Labels = mixedMoment B raw24202step0 raw24202step0Labels := by
      have hz : ∀ j, raw24202 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24202step0 = (fun i j => raw24202 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24202step0 raw24202; decide +kernel
      have hl : raw24202step0Labels = raw24202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24202 raw24202Labels permutation346 hz
    mixedMoment B raw24202step0 raw24202step0Labels = mixedMoment B raw24202step1 raw24202step1Labels := by
      have hz : ∀ j, raw24202step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24202step1 = (fun i j => raw24202step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24202step1 raw24202step0; decide +kernel
      have hl : raw24202step1Labels = raw24202step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24202step0 raw24202step0Labels permutation56 hz
    mixedMoment B raw24202step1 raw24202step1Labels = mixedMoment B raw24202step2 raw24202step2Labels := by
      have ha : raw24202step2 = (fun i j => raw24202step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24202step2 raw24202step1; decide +kernel
      have hl : raw24202step2Labels = raw24202step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24202step1 raw24202step1Labels permutation10 permutation7
    mixedMoment B raw24202step2 raw24202step2Labels = mixedMoment B raw24202step3 raw24202step3Labels := by
      have ha : raw24202step3 = raw24202step2 := by apply Matrix.ext; unfold raw24202step3 raw24202step2; decide +kernel
      have hl : raw24202step2Labels = labelEmbedding1 ∘ raw24202step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24202step2 raw24202step2Labels raw24202step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1448 node1448Labels := by rfl

def raw24203 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24203Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24203step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24203step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24203step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24203step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24203 raw24203Labels = mixedMoment B node1267 node1267Labels := by
  calc
    mixedMoment B raw24203 raw24203Labels = mixedMoment B raw24203step0 raw24203step0Labels := by
      have hz : ∀ j, raw24203 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24203step0 = (fun i j => raw24203 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24203step0 raw24203; decide +kernel
      have hl : raw24203step0Labels = raw24203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24203 raw24203Labels permutation346 hz
    mixedMoment B raw24203step0 raw24203step0Labels = mixedMoment B raw24203step1 raw24203step1Labels := by
      have ha : raw24203step1 = (fun i j => raw24203step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24203step1 raw24203step0; decide +kernel
      have hl : raw24203step1Labels = raw24203step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24203step0 raw24203step0Labels permutation34 permutation7
    mixedMoment B raw24203step1 raw24203step1Labels = mixedMoment B raw24203step2 raw24203step2Labels := by
      have ha : raw24203step2 = raw24203step1 := by apply Matrix.ext; unfold raw24203step2 raw24203step1; decide +kernel
      have hl : raw24203step1Labels = labelEmbedding1 ∘ raw24203step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24203step1 raw24203step1Labels raw24203step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1267 node1267Labels := by rfl

def raw24204 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24204Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24204step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24204step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24204step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24204step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24204step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24204 raw24204Labels = mixedMoment B node1267 node1267Labels := by
  calc
    mixedMoment B raw24204 raw24204Labels = mixedMoment B raw24204step0 raw24204step0Labels := by
      have hz : ∀ j, raw24204 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24204step0 = (fun i j => raw24204 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24204step0 raw24204; decide +kernel
      have hl : raw24204step0Labels = raw24204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24204 raw24204Labels permutation265 hz
    mixedMoment B raw24204step0 raw24204step0Labels = mixedMoment B raw24204step1 raw24204step1Labels := by
      have ha : raw24204step1 = (fun i j => raw24204step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24204step1 raw24204step0; decide +kernel
      have hl : raw24204step1Labels = raw24204step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24204step0 raw24204step0Labels permutation34 permutation7
    mixedMoment B raw24204step1 raw24204step1Labels = mixedMoment B raw24204step2 raw24204step2Labels := by
      have ha : raw24204step2 = raw24204step1 := by apply Matrix.ext; unfold raw24204step2 raw24204step1; decide +kernel
      have hl : raw24204step1Labels = labelEmbedding1 ∘ raw24204step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24204step1 raw24204step1Labels raw24204step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1267 node1267Labels := by rfl

def raw24205 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24205Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24205step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24205step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24205step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24205step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24205step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24205step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24205step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24205 raw24205Labels = mixedMoment B node1302 node1302Labels := by
  calc
    mixedMoment B raw24205 raw24205Labels = mixedMoment B raw24205step0 raw24205step0Labels := by
      have hz : ∀ j, raw24205 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24205step0 = (fun i j => raw24205 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24205step0 raw24205; decide +kernel
      have hl : raw24205step0Labels = raw24205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24205 raw24205Labels permutation346 hz
    mixedMoment B raw24205step0 raw24205step0Labels = mixedMoment B raw24205step1 raw24205step1Labels := by
      have hz : ∀ j, raw24205step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24205step1 = (fun i j => raw24205step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24205step1 raw24205step0; decide +kernel
      have hl : raw24205step1Labels = raw24205step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24205step0 raw24205step0Labels permutation56 hz
    mixedMoment B raw24205step1 raw24205step1Labels = mixedMoment B raw24205step2 raw24205step2Labels := by
      have ha : raw24205step2 = (fun i j => raw24205step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24205step2 raw24205step1; decide +kernel
      have hl : raw24205step2Labels = raw24205step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24205step1 raw24205step1Labels permutation10 permutation7
    mixedMoment B raw24205step2 raw24205step2Labels = mixedMoment B raw24205step3 raw24205step3Labels := by
      have ha : raw24205step3 = raw24205step2 := by apply Matrix.ext; unfold raw24205step3 raw24205step2; decide +kernel
      have hl : raw24205step2Labels = labelEmbedding1 ∘ raw24205step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24205step2 raw24205step2Labels raw24205step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1302 node1302Labels := by rfl

def raw24206 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24206Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24206step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24206step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24206step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24206step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24206step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24206step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24206step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24206 raw24206Labels = mixedMoment B node1301 node1301Labels := by
  calc
    mixedMoment B raw24206 raw24206Labels = mixedMoment B raw24206step0 raw24206step0Labels := by
      have hz : ∀ j, raw24206 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24206step0 = (fun i j => raw24206 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24206step0 raw24206; decide +kernel
      have hl : raw24206step0Labels = raw24206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24206 raw24206Labels permutation346 hz
    mixedMoment B raw24206step0 raw24206step0Labels = mixedMoment B raw24206step1 raw24206step1Labels := by
      have hz : ∀ j, raw24206step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24206step1 = (fun i j => raw24206step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24206step1 raw24206step0; decide +kernel
      have hl : raw24206step1Labels = raw24206step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24206step0 raw24206step0Labels permutation56 hz
    mixedMoment B raw24206step1 raw24206step1Labels = mixedMoment B raw24206step2 raw24206step2Labels := by
      have ha : raw24206step2 = (fun i j => raw24206step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24206step2 raw24206step1; decide +kernel
      have hl : raw24206step2Labels = raw24206step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24206step1 raw24206step1Labels permutation10 permutation7
    mixedMoment B raw24206step2 raw24206step2Labels = mixedMoment B raw24206step3 raw24206step3Labels := by
      have ha : raw24206step3 = raw24206step2 := by apply Matrix.ext; unfold raw24206step3 raw24206step2; decide +kernel
      have hl : raw24206step2Labels = labelEmbedding1 ∘ raw24206step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24206step2 raw24206step2Labels raw24206step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1301 node1301Labels := by rfl

def raw24207 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24207Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24207step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24207step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24207step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24207step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24207step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24207step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24207step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24207 raw24207Labels = mixedMoment B node1451 node1451Labels := by
  calc
    mixedMoment B raw24207 raw24207Labels = mixedMoment B raw24207step0 raw24207step0Labels := by
      have hz : ∀ j, raw24207 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24207step0 = (fun i j => raw24207 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24207step0 raw24207; decide +kernel
      have hl : raw24207step0Labels = raw24207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24207 raw24207Labels permutation346 hz
    mixedMoment B raw24207step0 raw24207step0Labels = mixedMoment B raw24207step1 raw24207step1Labels := by
      have hz : ∀ j, raw24207step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24207step1 = (fun i j => raw24207step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24207step1 raw24207step0; decide +kernel
      have hl : raw24207step1Labels = raw24207step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24207step0 raw24207step0Labels permutation56 hz
    mixedMoment B raw24207step1 raw24207step1Labels = mixedMoment B raw24207step2 raw24207step2Labels := by
      have ha : raw24207step2 = (fun i j => raw24207step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24207step2 raw24207step1; decide +kernel
      have hl : raw24207step2Labels = raw24207step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24207step1 raw24207step1Labels permutation8 permutation7
    mixedMoment B raw24207step2 raw24207step2Labels = mixedMoment B raw24207step3 raw24207step3Labels := by
      have ha : raw24207step3 = raw24207step2 := by apply Matrix.ext; unfold raw24207step3 raw24207step2; decide +kernel
      have hl : raw24207step2Labels = labelEmbedding1 ∘ raw24207step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24207step2 raw24207step2Labels raw24207step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1451 node1451Labels := by rfl

def raw24208 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24208Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24208step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24208step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24208step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24208step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24208 raw24208Labels = mixedMoment B node1270 node1270Labels := by
  calc
    mixedMoment B raw24208 raw24208Labels = mixedMoment B raw24208step0 raw24208step0Labels := by
      have hz : ∀ j, raw24208 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24208step0 = (fun i j => raw24208 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24208step0 raw24208; decide +kernel
      have hl : raw24208step0Labels = raw24208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24208 raw24208Labels permutation346 hz
    mixedMoment B raw24208step0 raw24208step0Labels = mixedMoment B raw24208step1 raw24208step1Labels := by
      have ha : raw24208step1 = (fun i j => raw24208step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24208step1 raw24208step0; decide +kernel
      have hl : raw24208step1Labels = raw24208step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24208step0 raw24208step0Labels permutation32 permutation7
    mixedMoment B raw24208step1 raw24208step1Labels = mixedMoment B raw24208step2 raw24208step2Labels := by
      have ha : raw24208step2 = raw24208step1 := by apply Matrix.ext; unfold raw24208step2 raw24208step1; decide +kernel
      have hl : raw24208step1Labels = labelEmbedding1 ∘ raw24208step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24208step1 raw24208step1Labels raw24208step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1270 node1270Labels := by rfl

def raw24209 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24209Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24209step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24209step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24209step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24209step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24209step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24209 raw24209Labels = mixedMoment B node1270 node1270Labels := by
  calc
    mixedMoment B raw24209 raw24209Labels = mixedMoment B raw24209step0 raw24209step0Labels := by
      have hz : ∀ j, raw24209 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24209step0 = (fun i j => raw24209 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24209step0 raw24209; decide +kernel
      have hl : raw24209step0Labels = raw24209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24209 raw24209Labels permutation265 hz
    mixedMoment B raw24209step0 raw24209step0Labels = mixedMoment B raw24209step1 raw24209step1Labels := by
      have ha : raw24209step1 = (fun i j => raw24209step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24209step1 raw24209step0; decide +kernel
      have hl : raw24209step1Labels = raw24209step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24209step0 raw24209step0Labels permutation32 permutation7
    mixedMoment B raw24209step1 raw24209step1Labels = mixedMoment B raw24209step2 raw24209step2Labels := by
      have ha : raw24209step2 = raw24209step1 := by apply Matrix.ext; unfold raw24209step2 raw24209step1; decide +kernel
      have hl : raw24209step1Labels = labelEmbedding1 ∘ raw24209step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24209step1 raw24209step1Labels raw24209step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1270 node1270Labels := by rfl

def raw24210 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24210Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24210step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24210step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24210step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24210step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw24210step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24210step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw24210step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24210 raw24210Labels = mixedMoment B node1306 node1306Labels := by
  calc
    mixedMoment B raw24210 raw24210Labels = mixedMoment B raw24210step0 raw24210step0Labels := by
      have hz : ∀ j, raw24210 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24210step0 = (fun i j => raw24210 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24210step0 raw24210; decide +kernel
      have hl : raw24210step0Labels = raw24210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24210 raw24210Labels permutation346 hz
    mixedMoment B raw24210step0 raw24210step0Labels = mixedMoment B raw24210step1 raw24210step1Labels := by
      have hz : ∀ j, raw24210step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24210step1 = (fun i j => raw24210step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24210step1 raw24210step0; decide +kernel
      have hl : raw24210step1Labels = raw24210step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24210step0 raw24210step0Labels permutation56 hz
    mixedMoment B raw24210step1 raw24210step1Labels = mixedMoment B raw24210step2 raw24210step2Labels := by
      have ha : raw24210step2 = (fun i j => raw24210step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24210step2 raw24210step1; decide +kernel
      have hl : raw24210step2Labels = raw24210step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24210step1 raw24210step1Labels permutation10 permutation7
    mixedMoment B raw24210step2 raw24210step2Labels = mixedMoment B raw24210step3 raw24210step3Labels := by
      have ha : raw24210step3 = raw24210step2 := by apply Matrix.ext; unfold raw24210step3 raw24210step2; decide +kernel
      have hl : raw24210step2Labels = labelEmbedding1 ∘ raw24210step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24210step2 raw24210step2Labels raw24210step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1306 node1306Labels := by rfl

def raw24211 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw24211Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw24211step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24211step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw24211step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24211step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw24211step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24211step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw24211step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24211 raw24211Labels = mixedMoment B node1306 node1306Labels := by
  calc
    mixedMoment B raw24211 raw24211Labels = mixedMoment B raw24211step0 raw24211step0Labels := by
      have hz : ∀ j, raw24211 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24211step0 = (fun i j => raw24211 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24211step0 raw24211; decide +kernel
      have hl : raw24211step0Labels = raw24211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24211 raw24211Labels permutation346 hz
    mixedMoment B raw24211step0 raw24211step0Labels = mixedMoment B raw24211step1 raw24211step1Labels := by
      have hz : ∀ j, raw24211step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24211step1 = (fun i j => raw24211step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24211step1 raw24211step0; decide +kernel
      have hl : raw24211step1Labels = raw24211step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24211step0 raw24211step0Labels permutation56 hz
    mixedMoment B raw24211step1 raw24211step1Labels = mixedMoment B raw24211step2 raw24211step2Labels := by
      have ha : raw24211step2 = (fun i j => raw24211step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24211step2 raw24211step1; decide +kernel
      have hl : raw24211step2Labels = raw24211step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24211step1 raw24211step1Labels permutation8 permutation7
    mixedMoment B raw24211step2 raw24211step2Labels = mixedMoment B raw24211step3 raw24211step3Labels := by
      have ha : raw24211step3 = raw24211step2 := by apply Matrix.ext; unfold raw24211step3 raw24211step2; decide +kernel
      have hl : raw24211step2Labels = labelEmbedding1 ∘ raw24211step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24211step2 raw24211step2Labels raw24211step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1306 node1306Labels := by rfl

def raw24212 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24212Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24212step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24212step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw24212step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24212step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24212step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24212 raw24212Labels = mixedMoment B node1737 node1737Labels := by
  calc
    mixedMoment B raw24212 raw24212Labels = mixedMoment B raw24212step0 raw24212step0Labels := by
      have hz : ∀ j, raw24212 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24212step0 = (fun i j => raw24212 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24212step0 raw24212; decide +kernel
      have hl : raw24212step0Labels = raw24212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24212 raw24212Labels permutation265 hz
    mixedMoment B raw24212step0 raw24212step0Labels = mixedMoment B raw24212step1 raw24212step1Labels := by
      have ha : raw24212step1 = (fun i j => raw24212step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24212step1 raw24212step0; decide +kernel
      have hl : raw24212step1Labels = raw24212step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24212step0 raw24212step0Labels permutation50 permutation2
    mixedMoment B raw24212step1 raw24212step1Labels = mixedMoment B raw24212step2 raw24212step2Labels := by
      have ha : raw24212step2 = -raw24212step1 := by apply Matrix.ext; change ∀ i j, raw24212step2 i j = -(raw24212step1 i j); unfold raw24212step2 raw24212step1; decide +kernel
      have hl : raw24212step2Labels = raw24212step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1737 node1737Labels := by rfl

def raw24213 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24213Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24213step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24213step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24213step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24213step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24213step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24213step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24213step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24213 raw24213Labels = mixedMoment B node1739 node1739Labels := by
  calc
    mixedMoment B raw24213 raw24213Labels = mixedMoment B raw24213step0 raw24213step0Labels := by
      have hz : ∀ j, raw24213 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24213step0 = (fun i j => raw24213 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24213step0 raw24213; decide +kernel
      have hl : raw24213step0Labels = raw24213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24213 raw24213Labels permutation346 hz
    mixedMoment B raw24213step0 raw24213step0Labels = mixedMoment B raw24213step1 raw24213step1Labels := by
      have hz : ∀ j, raw24213step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24213step1 = (fun i j => raw24213step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24213step1 raw24213step0; decide +kernel
      have hl : raw24213step1Labels = raw24213step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24213step0 raw24213step0Labels permutation56 hz
    mixedMoment B raw24213step1 raw24213step1Labels = mixedMoment B raw24213step2 raw24213step2Labels := by
      have ha : raw24213step2 = (fun i j => raw24213step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24213step2 raw24213step1; decide +kernel
      have hl : raw24213step2Labels = raw24213step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24213step1 raw24213step1Labels permutation12 permutation2
    mixedMoment B raw24213step2 raw24213step2Labels = mixedMoment B raw24213step3 raw24213step3Labels := by
      have ha : raw24213step3 = -raw24213step2 := by apply Matrix.ext; change ∀ i j, raw24213step3 i j = -(raw24213step2 i j); unfold raw24213step3 raw24213step2; decide +kernel
      have hl : raw24213step3Labels = raw24213step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1739 node1739Labels := by rfl

def raw24214 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24214Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24214step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24214step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24214step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24214step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24214step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24214 raw24214Labels = mixedMoment B node1753 node1753Labels := by
  calc
    mixedMoment B raw24214 raw24214Labels = mixedMoment B raw24214step0 raw24214step0Labels := by
      have hz : ∀ j, raw24214 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24214step0 = (fun i j => raw24214 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24214step0 raw24214; decide +kernel
      have hl : raw24214step0Labels = raw24214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24214 raw24214Labels permutation346 hz
    mixedMoment B raw24214step0 raw24214step0Labels = mixedMoment B raw24214step1 raw24214step1Labels := by
      have hz : ∀ j, raw24214step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24214step1 = (fun i j => raw24214step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24214step1 raw24214step0; decide +kernel
      have hl : raw24214step1Labels = raw24214step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24214step0 raw24214step0Labels permutation56 hz
    mixedMoment B raw24214step1 raw24214step1Labels = mixedMoment B raw24214step2 raw24214step2Labels := by
      have ha : raw24214step2 = -raw24214step1 := by apply Matrix.ext; change ∀ i j, raw24214step2 i j = -(raw24214step1 i j); unfold raw24214step2 raw24214step1; decide +kernel
      have hl : raw24214step2Labels = raw24214step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1753 node1753Labels := by rfl

def raw24215 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24215Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24215step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24215step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24215step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24215step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24215step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24215step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24215step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24215 raw24215Labels = mixedMoment B node1727 node1727Labels := by
  calc
    mixedMoment B raw24215 raw24215Labels = mixedMoment B raw24215step0 raw24215step0Labels := by
      have hz : ∀ j, raw24215 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24215step0 = (fun i j => raw24215 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24215step0 raw24215; decide +kernel
      have hl : raw24215step0Labels = raw24215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24215 raw24215Labels permutation346 hz
    mixedMoment B raw24215step0 raw24215step0Labels = mixedMoment B raw24215step1 raw24215step1Labels := by
      have hz : ∀ j, raw24215step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24215step1 = (fun i j => raw24215step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24215step1 raw24215step0; decide +kernel
      have hl : raw24215step1Labels = raw24215step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24215step0 raw24215step0Labels permutation56 hz
    mixedMoment B raw24215step1 raw24215step1Labels = mixedMoment B raw24215step2 raw24215step2Labels := by
      have ha : raw24215step2 = (fun i j => raw24215step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24215step2 raw24215step1; decide +kernel
      have hl : raw24215step2Labels = raw24215step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24215step1 raw24215step1Labels permutation10 permutation4
    mixedMoment B raw24215step2 raw24215step2Labels = mixedMoment B raw24215step3 raw24215step3Labels := by
      have ha : raw24215step3 = -raw24215step2 := by apply Matrix.ext; change ∀ i j, raw24215step3 i j = -(raw24215step2 i j); unfold raw24215step3 raw24215step2; decide +kernel
      have hl : raw24215step3Labels = raw24215step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1727 node1727Labels := by rfl

def raw24216 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24216Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24216step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24216step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24216step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24216step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24216 raw24216Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw24216 raw24216Labels = mixedMoment B raw24216step0 raw24216step0Labels := by
      have hz : ∀ j, raw24216 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24216step0 = (fun i j => raw24216 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24216step0 raw24216; decide +kernel
      have hl : raw24216step0Labels = raw24216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24216 raw24216Labels permutation265 hz
    mixedMoment B raw24216step0 raw24216step0Labels = mixedMoment B raw24216step1 raw24216step1Labels := by
      have ha : raw24216step1 = (fun i j => raw24216step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24216step1 raw24216step0; decide +kernel
      have hl : raw24216step1Labels = raw24216step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24216step0 raw24216step0Labels permutation34 permutation4
    mixedMoment B raw24216step1 raw24216step1Labels = mixedMoment B raw24216step2 raw24216step2Labels := by
      have ha : raw24216step2 = -raw24216step1 := by apply Matrix.ext; change ∀ i j, raw24216step2 i j = -(raw24216step1 i j); unfold raw24216step2 raw24216step1; decide +kernel
      have hl : raw24216step2Labels = raw24216step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3293 node3293Labels := by rfl

def raw24217 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24217Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24217step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24217step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24217step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24217step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24217step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24217step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24217step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24217 raw24217Labels = mixedMoment B node3305 node3305Labels := by
  calc
    mixedMoment B raw24217 raw24217Labels = mixedMoment B raw24217step0 raw24217step0Labels := by
      have hz : ∀ j, raw24217 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24217step0 = (fun i j => raw24217 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24217step0 raw24217; decide +kernel
      have hl : raw24217step0Labels = raw24217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24217 raw24217Labels permutation346 hz
    mixedMoment B raw24217step0 raw24217step0Labels = mixedMoment B raw24217step1 raw24217step1Labels := by
      have hz : ∀ j, raw24217step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24217step1 = (fun i j => raw24217step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24217step1 raw24217step0; decide +kernel
      have hl : raw24217step1Labels = raw24217step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24217step0 raw24217step0Labels permutation56 hz
    mixedMoment B raw24217step1 raw24217step1Labels = mixedMoment B raw24217step2 raw24217step2Labels := by
      have ha : raw24217step2 = (fun i j => raw24217step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24217step2 raw24217step1; decide +kernel
      have hl : raw24217step2Labels = raw24217step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24217step1 raw24217step1Labels permutation10 permutation4
    mixedMoment B raw24217step2 raw24217step2Labels = mixedMoment B raw24217step3 raw24217step3Labels := by
      have ha : raw24217step3 = -raw24217step2 := by apply Matrix.ext; change ∀ i j, raw24217step3 i j = -(raw24217step2 i j); unfold raw24217step3 raw24217step2; decide +kernel
      have hl : raw24217step3Labels = raw24217step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3305 node3305Labels := by rfl

def raw24218 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24218Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24218step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24218step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24218step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24218step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24218step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24218 raw24218Labels = mixedMoment B node3309 node3309Labels := by
  calc
    mixedMoment B raw24218 raw24218Labels = mixedMoment B raw24218step0 raw24218step0Labels := by
      have hz : ∀ j, raw24218 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24218step0 = (fun i j => raw24218 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24218step0 raw24218; decide +kernel
      have hl : raw24218step0Labels = raw24218Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24218 raw24218Labels permutation346 hz
    mixedMoment B raw24218step0 raw24218step0Labels = mixedMoment B raw24218step1 raw24218step1Labels := by
      have hz : ∀ j, raw24218step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24218step1 = (fun i j => raw24218step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24218step1 raw24218step0; decide +kernel
      have hl : raw24218step1Labels = raw24218step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24218step0 raw24218step0Labels permutation56 hz
    mixedMoment B raw24218step1 raw24218step1Labels = mixedMoment B raw24218step2 raw24218step2Labels := by
      have ha : raw24218step2 = -raw24218step1 := by apply Matrix.ext; change ∀ i j, raw24218step2 i j = -(raw24218step1 i j); unfold raw24218step2 raw24218step1; decide +kernel
      have hl : raw24218step2Labels = raw24218step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3309 node3309Labels := by rfl

def raw24219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24219Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24219step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24219step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24219step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24219step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24219step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24219 raw24219Labels = mixedMoment B node4175 node4175Labels := by
  calc
    mixedMoment B raw24219 raw24219Labels = mixedMoment B raw24219step0 raw24219step0Labels := by
      have hz : ∀ j, raw24219 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24219step0 = (fun i j => raw24219 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24219step0 raw24219; decide +kernel
      have hl : raw24219step0Labels = raw24219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24219 raw24219Labels permutation346 hz
    mixedMoment B raw24219step0 raw24219step0Labels = mixedMoment B raw24219step1 raw24219step1Labels := by
      have ha : raw24219step1 = (fun i j => raw24219step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24219step1 raw24219step0; decide +kernel
      have hl : raw24219step1Labels = raw24219step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24219step0 raw24219step0Labels permutation44 permutation3
    mixedMoment B raw24219step1 raw24219step1Labels = mixedMoment B raw24219step2 raw24219step2Labels := by
      have ha : raw24219step2 = raw24219step1 := by apply Matrix.ext; unfold raw24219step2 raw24219step1; decide +kernel
      have hl : raw24219step1Labels = labelEmbedding6 ∘ raw24219step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24219step1 raw24219step1Labels raw24219step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4175 node4175Labels := by rfl

def raw24220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24220step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24220step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24220step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24220 raw24220Labels = mixedMoment B node4544 node4544Labels := by
  calc
    mixedMoment B raw24220 raw24220Labels = mixedMoment B raw24220step0 raw24220step0Labels := by
      have ha : raw24220step0 = (fun i j => raw24220 (permutation188 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24220step0 raw24220; decide +kernel
      have hl : raw24220step0Labels = raw24220Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24220 raw24220Labels permutation188 permutation3
    mixedMoment B raw24220step0 raw24220step0Labels = mixedMoment B raw24220step1 raw24220step1Labels := by
      have ha : raw24220step1 = raw24220step0 := by apply Matrix.ext; unfold raw24220step1 raw24220step0; decide +kernel
      have hl : raw24220step0Labels = labelEmbedding6 ∘ raw24220step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24220step0 raw24220step0Labels raw24220step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4544 node4544Labels := by rfl

def raw24221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw24221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw24221step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24221step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24221step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24221step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24221step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24221 raw24221Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw24221 raw24221Labels = mixedMoment B raw24221step0 raw24221step0Labels := by
      have hz : ∀ j, raw24221 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24221step0 = (fun i j => raw24221 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24221step0 raw24221; decide +kernel
      have hl : raw24221step0Labels = raw24221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24221 raw24221Labels permutation346 hz
    mixedMoment B raw24221step0 raw24221step0Labels = mixedMoment B raw24221step1 raw24221step1Labels := by
      have ha : raw24221step1 = (fun i j => raw24221step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24221step1 raw24221step0; decide +kernel
      have hl : raw24221step1Labels = raw24221step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24221step0 raw24221step0Labels permutation44 permutation3
    mixedMoment B raw24221step1 raw24221step1Labels = mixedMoment B raw24221step2 raw24221step2Labels := by
      have ha : raw24221step2 = raw24221step1 := by apply Matrix.ext; unfold raw24221step2 raw24221step1; decide +kernel
      have hl : raw24221step1Labels = labelEmbedding6 ∘ raw24221step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24221step1 raw24221step1Labels raw24221step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4606 node4606Labels := by rfl

def raw24222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24222 raw24222Labels = mixedMoment B node4622 node4622Labels := by
  calc
    mixedMoment B raw24222 raw24222Labels = mixedMoment B raw24222step0 raw24222step0Labels := by
      have hz : ∀ j, raw24222 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24222step0 = (fun i j => raw24222 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24222step0 raw24222; decide +kernel
      have hl : raw24222step0Labels = raw24222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24222 raw24222Labels permutation346 hz
    _ = mixedMoment B node4622 node4622Labels := by rfl

def raw24223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24223step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24223step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24223step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24223 raw24223Labels = mixedMoment B node4175 node4175Labels := by
  calc
    mixedMoment B raw24223 raw24223Labels = mixedMoment B raw24223step0 raw24223step0Labels := by
      have hz : ∀ j, raw24223 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24223step0 = (fun i j => raw24223 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24223step0 raw24223; decide +kernel
      have hl : raw24223step0Labels = raw24223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24223 raw24223Labels permutation265 hz
    mixedMoment B raw24223step0 raw24223step0Labels = mixedMoment B raw24223step1 raw24223step1Labels := by
      have ha : raw24223step1 = (fun i j => raw24223step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24223step1 raw24223step0; decide +kernel
      have hl : raw24223step1Labels = raw24223step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24223step0 raw24223step0Labels permutation44 permutation3
    mixedMoment B raw24223step1 raw24223step1Labels = mixedMoment B raw24223step2 raw24223step2Labels := by
      have ha : raw24223step2 = raw24223step1 := by apply Matrix.ext; unfold raw24223step2 raw24223step1; decide +kernel
      have hl : raw24223step1Labels = labelEmbedding6 ∘ raw24223step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24223step1 raw24223step1Labels raw24223step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4175 node4175Labels := by rfl

def raw24224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24224step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24224step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24224step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24224step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24224 raw24224Labels = mixedMoment B node4544 node4544Labels := by
  calc
    mixedMoment B raw24224 raw24224Labels = mixedMoment B raw24224step0 raw24224step0Labels := by
      have ha : raw24224step0 = (fun i j => raw24224 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24224step0 raw24224; decide +kernel
      have hl : raw24224step0Labels = raw24224Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24224 raw24224Labels permutation164 permutation3
    mixedMoment B raw24224step0 raw24224step0Labels = mixedMoment B raw24224step1 raw24224step1Labels := by
      have ha : raw24224step1 = raw24224step0 := by apply Matrix.ext; unfold raw24224step1 raw24224step0; decide +kernel
      have hl : raw24224step0Labels = labelEmbedding6 ∘ raw24224step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24224step0 raw24224step0Labels raw24224step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4544 node4544Labels := by rfl

def raw24225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw24225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw24225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24225step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24225step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24225step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24225step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24225 raw24225Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw24225 raw24225Labels = mixedMoment B raw24225step0 raw24225step0Labels := by
      have hz : ∀ j, raw24225 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24225step0 = (fun i j => raw24225 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24225step0 raw24225; decide +kernel
      have hl : raw24225step0Labels = raw24225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24225 raw24225Labels permutation265 hz
    mixedMoment B raw24225step0 raw24225step0Labels = mixedMoment B raw24225step1 raw24225step1Labels := by
      have ha : raw24225step1 = (fun i j => raw24225step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24225step1 raw24225step0; decide +kernel
      have hl : raw24225step1Labels = raw24225step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24225step0 raw24225step0Labels permutation44 permutation3
    mixedMoment B raw24225step1 raw24225step1Labels = mixedMoment B raw24225step2 raw24225step2Labels := by
      have ha : raw24225step2 = raw24225step1 := by apply Matrix.ext; unfold raw24225step2 raw24225step1; decide +kernel
      have hl : raw24225step1Labels = labelEmbedding6 ∘ raw24225step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24225step1 raw24225step1Labels raw24225step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4606 node4606Labels := by rfl

def raw24226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24226 raw24226Labels = mixedMoment B node4622 node4622Labels := by
  calc
    mixedMoment B raw24226 raw24226Labels = mixedMoment B raw24226step0 raw24226step0Labels := by
      have hz : ∀ j, raw24226 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24226step0 = (fun i j => raw24226 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24226step0 raw24226; decide +kernel
      have hl : raw24226step0Labels = raw24226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24226 raw24226Labels permutation265 hz
    _ = mixedMoment B node4622 node4622Labels := by rfl

def raw24227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24227step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24227step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24227step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24227step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24227step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24227step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24227 raw24227Labels = mixedMoment B node4180 node4180Labels := by
  calc
    mixedMoment B raw24227 raw24227Labels = mixedMoment B raw24227step0 raw24227step0Labels := by
      have hz : ∀ j, raw24227 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24227step0 = (fun i j => raw24227 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24227step0 raw24227; decide +kernel
      have hl : raw24227step0Labels = raw24227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24227 raw24227Labels permutation346 hz
    mixedMoment B raw24227step0 raw24227step0Labels = mixedMoment B raw24227step1 raw24227step1Labels := by
      have hz : ∀ j, raw24227step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24227step1 = (fun i j => raw24227step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24227step1 raw24227step0; decide +kernel
      have hl : raw24227step1Labels = raw24227step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24227step0 raw24227step0Labels permutation56 hz
    mixedMoment B raw24227step1 raw24227step1Labels = mixedMoment B raw24227step2 raw24227step2Labels := by
      have ha : raw24227step2 = (fun i j => raw24227step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24227step2 raw24227step1; decide +kernel
      have hl : raw24227step2Labels = raw24227step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24227step1 raw24227step1Labels permutation11 permutation3
    mixedMoment B raw24227step2 raw24227step2Labels = mixedMoment B raw24227step3 raw24227step3Labels := by
      have ha : raw24227step3 = raw24227step2 := by apply Matrix.ext; unfold raw24227step3 raw24227step2; decide +kernel
      have hl : raw24227step2Labels = labelEmbedding6 ∘ raw24227step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24227step2 raw24227step2Labels raw24227step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4180 node4180Labels := by rfl

def raw24228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24228step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24228step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24228step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24228step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24228 raw24228Labels = mixedMoment B node4549 node4549Labels := by
  calc
    mixedMoment B raw24228 raw24228Labels = mixedMoment B raw24228step0 raw24228step0Labels := by
      have hz : ∀ j, raw24228 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24228step0 = (fun i j => raw24228 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24228step0 raw24228; decide +kernel
      have hl : raw24228step0Labels = raw24228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24228 raw24228Labels permutation346 hz
    mixedMoment B raw24228step0 raw24228step0Labels = mixedMoment B raw24228step1 raw24228step1Labels := by
      have ha : raw24228step1 = (fun i j => raw24228step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24228step1 raw24228step0; decide +kernel
      have hl : raw24228step1Labels = raw24228step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24228step0 raw24228step0Labels permutation35 permutation3
    mixedMoment B raw24228step1 raw24228step1Labels = mixedMoment B raw24228step2 raw24228step2Labels := by
      have ha : raw24228step2 = raw24228step1 := by apply Matrix.ext; unfold raw24228step2 raw24228step1; decide +kernel
      have hl : raw24228step1Labels = labelEmbedding6 ∘ raw24228step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24228step1 raw24228step1Labels raw24228step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4549 node4549Labels := by rfl

def raw24229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24229step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24229step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24229step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24229step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24229 raw24229Labels = mixedMoment B node4549 node4549Labels := by
  calc
    mixedMoment B raw24229 raw24229Labels = mixedMoment B raw24229step0 raw24229step0Labels := by
      have hz : ∀ j, raw24229 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24229step0 = (fun i j => raw24229 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24229step0 raw24229; decide +kernel
      have hl : raw24229step0Labels = raw24229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24229 raw24229Labels permutation265 hz
    mixedMoment B raw24229step0 raw24229step0Labels = mixedMoment B raw24229step1 raw24229step1Labels := by
      have ha : raw24229step1 = (fun i j => raw24229step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24229step1 raw24229step0; decide +kernel
      have hl : raw24229step1Labels = raw24229step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24229step0 raw24229step0Labels permutation35 permutation3
    mixedMoment B raw24229step1 raw24229step1Labels = mixedMoment B raw24229step2 raw24229step2Labels := by
      have ha : raw24229step2 = raw24229step1 := by apply Matrix.ext; unfold raw24229step2 raw24229step1; decide +kernel
      have hl : raw24229step1Labels = labelEmbedding6 ∘ raw24229step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24229step1 raw24229step1Labels raw24229step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4549 node4549Labels := by rfl

def raw24230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw24230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw24230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24230step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw24230step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24230step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24230step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24230step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24230step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24230 raw24230Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw24230 raw24230Labels = mixedMoment B raw24230step0 raw24230step0Labels := by
      have hz : ∀ j, raw24230 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24230step0 = (fun i j => raw24230 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24230step0 raw24230; decide +kernel
      have hl : raw24230step0Labels = raw24230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24230 raw24230Labels permutation346 hz
    mixedMoment B raw24230step0 raw24230step0Labels = mixedMoment B raw24230step1 raw24230step1Labels := by
      have hz : ∀ j, raw24230step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24230step1 = (fun i j => raw24230step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24230step1 raw24230step0; decide +kernel
      have hl : raw24230step1Labels = raw24230step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24230step0 raw24230step0Labels permutation56 hz
    mixedMoment B raw24230step1 raw24230step1Labels = mixedMoment B raw24230step2 raw24230step2Labels := by
      have ha : raw24230step2 = (fun i j => raw24230step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24230step2 raw24230step1; decide +kernel
      have hl : raw24230step2Labels = raw24230step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24230step1 raw24230step1Labels permutation11 permutation3
    mixedMoment B raw24230step2 raw24230step2Labels = mixedMoment B raw24230step3 raw24230step3Labels := by
      have ha : raw24230step3 = raw24230step2 := by apply Matrix.ext; unfold raw24230step3 raw24230step2; decide +kernel
      have hl : raw24230step2Labels = labelEmbedding6 ∘ raw24230step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24230step2 raw24230step2Labels raw24230step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

def raw24231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24231step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24231step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24231step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24231step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24231step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24231step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24231 raw24231Labels = mixedMoment B node4623 node4623Labels := by
  calc
    mixedMoment B raw24231 raw24231Labels = mixedMoment B raw24231step0 raw24231step0Labels := by
      have hz : ∀ j, raw24231 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24231step0 = (fun i j => raw24231 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24231step0 raw24231; decide +kernel
      have hl : raw24231step0Labels = raw24231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24231 raw24231Labels permutation346 hz
    mixedMoment B raw24231step0 raw24231step0Labels = mixedMoment B raw24231step1 raw24231step1Labels := by
      have hz : ∀ j, raw24231step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24231step1 = (fun i j => raw24231step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24231step1 raw24231step0; decide +kernel
      have hl : raw24231step1Labels = raw24231step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24231step0 raw24231step0Labels permutation56 hz
    mixedMoment B raw24231step1 raw24231step1Labels = mixedMoment B raw24231step2 raw24231step2Labels := by
      have ha : raw24231step2 = (fun i j => raw24231step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24231step2 raw24231step1; decide +kernel
      have hl : raw24231step2Labels = raw24231step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24231step1 raw24231step1Labels permutation11 permutation3
    mixedMoment B raw24231step2 raw24231step2Labels = mixedMoment B raw24231step3 raw24231step3Labels := by
      have ha : raw24231step3 = raw24231step2 := by apply Matrix.ext; unfold raw24231step3 raw24231step2; decide +kernel
      have hl : raw24231step2Labels = labelEmbedding6 ∘ raw24231step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24231step2 raw24231step2Labels raw24231step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4623 node4623Labels := by rfl

def raw24232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24232Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24232step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24232step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24232 raw24232Labels = mixedMoment B node2960 node2960Labels := by
  calc
    mixedMoment B raw24232 raw24232Labels = mixedMoment B raw24232step0 raw24232step0Labels := by
      have hz : ∀ j, raw24232 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24232step0 = (fun i j => raw24232 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24232step0 raw24232; decide +kernel
      have hl : raw24232step0Labels = raw24232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24232 raw24232Labels permutation346 hz
    mixedMoment B raw24232step0 raw24232step0Labels = mixedMoment B raw24232step1 raw24232step1Labels := by
      have ha : raw24232step1 = (fun i j => raw24232step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24232step1 raw24232step0; decide +kernel
      have hl : raw24232step1Labels = raw24232step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24232step0 raw24232step0Labels permutation34 permutation3
    _ = mixedMoment B node2960 node2960Labels := by rfl

def raw24233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24233Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24233step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24233step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24233 raw24233Labels = mixedMoment B node2960 node2960Labels := by
  calc
    mixedMoment B raw24233 raw24233Labels = mixedMoment B raw24233step0 raw24233step0Labels := by
      have hz : ∀ j, raw24233 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24233step0 = (fun i j => raw24233 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24233step0 raw24233; decide +kernel
      have hl : raw24233step0Labels = raw24233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24233 raw24233Labels permutation265 hz
    mixedMoment B raw24233step0 raw24233step0Labels = mixedMoment B raw24233step1 raw24233step1Labels := by
      have ha : raw24233step1 = (fun i j => raw24233step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24233step1 raw24233step0; decide +kernel
      have hl : raw24233step1Labels = raw24233step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24233step0 raw24233step0Labels permutation34 permutation3
    _ = mixedMoment B node2960 node2960Labels := by rfl

def raw24234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24234Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24234step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24234step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24234step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24234step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw24234step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24234 raw24234Labels = mixedMoment B node3122 node3122Labels := by
  calc
    mixedMoment B raw24234 raw24234Labels = mixedMoment B raw24234step0 raw24234step0Labels := by
      have hz : ∀ j, raw24234 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24234step0 = (fun i j => raw24234 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24234step0 raw24234; decide +kernel
      have hl : raw24234step0Labels = raw24234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24234 raw24234Labels permutation346 hz
    mixedMoment B raw24234step0 raw24234step0Labels = mixedMoment B raw24234step1 raw24234step1Labels := by
      have hz : ∀ j, raw24234step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24234step1 = (fun i j => raw24234step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24234step1 raw24234step0; decide +kernel
      have hl : raw24234step1Labels = raw24234step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24234step0 raw24234step0Labels permutation56 hz
    mixedMoment B raw24234step1 raw24234step1Labels = mixedMoment B raw24234step2 raw24234step2Labels := by
      have ha : raw24234step2 = (fun i j => raw24234step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24234step2 raw24234step1; decide +kernel
      have hl : raw24234step2Labels = raw24234step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24234step1 raw24234step1Labels permutation11 permutation3
    _ = mixedMoment B node3122 node3122Labels := by rfl

def raw24235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24235Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24235step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24235step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24235 raw24235Labels = mixedMoment B node603 node603Labels := by
  calc
    mixedMoment B raw24235 raw24235Labels = mixedMoment B raw24235step0 raw24235step0Labels := by
      have hz : ∀ j, raw24235 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24235step0 = (fun i j => raw24235 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24235step0 raw24235; decide +kernel
      have hl : raw24235step0Labels = raw24235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24235 raw24235Labels permutation346 hz
    mixedMoment B raw24235step0 raw24235step0Labels = mixedMoment B raw24235step1 raw24235step1Labels := by
      have ha : raw24235step1 = (fun i j => raw24235step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24235step1 raw24235step0; decide +kernel
      have hl : raw24235step1Labels = raw24235step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24235step0 raw24235step0Labels permutation44 permutation3
    _ = mixedMoment B node603 node603Labels := by rfl

def raw24236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24236Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24236step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24236step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24236 raw24236Labels = mixedMoment B node1129 node1129Labels := by
  calc
    mixedMoment B raw24236 raw24236Labels = mixedMoment B raw24236step0 raw24236step0Labels := by
      have ha : raw24236step0 = (fun i j => raw24236 (permutation188 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24236step0 raw24236; decide +kernel
      have hl : raw24236step0Labels = raw24236Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24236 raw24236Labels permutation188 permutation3
    _ = mixedMoment B node1129 node1129Labels := by rfl

def raw24237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw24237Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw24237step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24237step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24237step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24237 raw24237Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw24237 raw24237Labels = mixedMoment B raw24237step0 raw24237step0Labels := by
      have hz : ∀ j, raw24237 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24237step0 = (fun i j => raw24237 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24237step0 raw24237; decide +kernel
      have hl : raw24237step0Labels = raw24237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24237 raw24237Labels permutation346 hz
    mixedMoment B raw24237step0 raw24237step0Labels = mixedMoment B raw24237step1 raw24237step1Labels := by
      have ha : raw24237step1 = (fun i j => raw24237step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24237step1 raw24237step0; decide +kernel
      have hl : raw24237step1Labels = raw24237step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24237step0 raw24237step0Labels permutation44 permutation3
    _ = mixedMoment B node1240 node1240Labels := by rfl

def raw24238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24238Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24238step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24238step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24238step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24238 raw24238Labels = mixedMoment B node1299 node1299Labels := by
  calc
    mixedMoment B raw24238 raw24238Labels = mixedMoment B raw24238step0 raw24238step0Labels := by
      have hz : ∀ j, raw24238 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24238step0 = (fun i j => raw24238 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24238step0 raw24238; decide +kernel
      have hl : raw24238step0Labels = raw24238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24238 raw24238Labels permutation346 hz
    mixedMoment B raw24238step0 raw24238step0Labels = mixedMoment B raw24238step1 raw24238step1Labels := by
      have ha : raw24238step1 = (fun i j => raw24238step0 (permutation48 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24238step1 raw24238step0; decide +kernel
      have hl : raw24238step1Labels = raw24238step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24238step0 raw24238step0Labels permutation48 permutation3
    _ = mixedMoment B node1299 node1299Labels := by rfl

def raw24239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24239Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24239step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24239step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24239step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24239 raw24239Labels = mixedMoment B node603 node603Labels := by
  calc
    mixedMoment B raw24239 raw24239Labels = mixedMoment B raw24239step0 raw24239step0Labels := by
      have hz : ∀ j, raw24239 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24239step0 = (fun i j => raw24239 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24239step0 raw24239; decide +kernel
      have hl : raw24239step0Labels = raw24239Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24239 raw24239Labels permutation265 hz
    mixedMoment B raw24239step0 raw24239step0Labels = mixedMoment B raw24239step1 raw24239step1Labels := by
      have ha : raw24239step1 = (fun i j => raw24239step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24239step1 raw24239step0; decide +kernel
      have hl : raw24239step1Labels = raw24239step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24239step0 raw24239step0Labels permutation44 permutation3
    _ = mixedMoment B node603 node603Labels := by rfl

def raw24240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24240Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24240step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24240step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24240 raw24240Labels = mixedMoment B node1129 node1129Labels := by
  calc
    mixedMoment B raw24240 raw24240Labels = mixedMoment B raw24240step0 raw24240step0Labels := by
      have ha : raw24240step0 = (fun i j => raw24240 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24240step0 raw24240; decide +kernel
      have hl : raw24240step0Labels = raw24240Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24240 raw24240Labels permutation164 permutation3
    _ = mixedMoment B node1129 node1129Labels := by rfl

def raw24241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw24241Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw24241step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24241step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24241step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24241 raw24241Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw24241 raw24241Labels = mixedMoment B raw24241step0 raw24241step0Labels := by
      have hz : ∀ j, raw24241 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24241step0 = (fun i j => raw24241 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24241step0 raw24241; decide +kernel
      have hl : raw24241step0Labels = raw24241Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24241 raw24241Labels permutation265 hz
    mixedMoment B raw24241step0 raw24241step0Labels = mixedMoment B raw24241step1 raw24241step1Labels := by
      have ha : raw24241step1 = (fun i j => raw24241step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24241step1 raw24241step0; decide +kernel
      have hl : raw24241step1Labels = raw24241step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24241step0 raw24241step0Labels permutation44 permutation3
    _ = mixedMoment B node1240 node1240Labels := by rfl

def raw24242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24242Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24242step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24242step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24242step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24242 raw24242Labels = mixedMoment B node1299 node1299Labels := by
  calc
    mixedMoment B raw24242 raw24242Labels = mixedMoment B raw24242step0 raw24242step0Labels := by
      have hz : ∀ j, raw24242 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24242step0 = (fun i j => raw24242 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24242step0 raw24242; decide +kernel
      have hl : raw24242step0Labels = raw24242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24242 raw24242Labels permutation265 hz
    mixedMoment B raw24242step0 raw24242step0Labels = mixedMoment B raw24242step1 raw24242step1Labels := by
      have ha : raw24242step1 = (fun i j => raw24242step0 (permutation48 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24242step1 raw24242step0; decide +kernel
      have hl : raw24242step1Labels = raw24242step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24242step0 raw24242step0Labels permutation48 permutation3
    _ = mixedMoment B node1299 node1299Labels := by rfl

def raw24243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24243Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24243step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24243step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24243step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24243step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24243step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24243 raw24243Labels = mixedMoment B node608 node608Labels := by
  calc
    mixedMoment B raw24243 raw24243Labels = mixedMoment B raw24243step0 raw24243step0Labels := by
      have hz : ∀ j, raw24243 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24243step0 = (fun i j => raw24243 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24243step0 raw24243; decide +kernel
      have hl : raw24243step0Labels = raw24243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24243 raw24243Labels permutation346 hz
    mixedMoment B raw24243step0 raw24243step0Labels = mixedMoment B raw24243step1 raw24243step1Labels := by
      have hz : ∀ j, raw24243step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24243step1 = (fun i j => raw24243step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24243step1 raw24243step0; decide +kernel
      have hl : raw24243step1Labels = raw24243step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24243step0 raw24243step0Labels permutation56 hz
    mixedMoment B raw24243step1 raw24243step1Labels = mixedMoment B raw24243step2 raw24243step2Labels := by
      have ha : raw24243step2 = (fun i j => raw24243step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24243step2 raw24243step1; decide +kernel
      have hl : raw24243step2Labels = raw24243step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24243step1 raw24243step1Labels permutation11 permutation3
    _ = mixedMoment B node608 node608Labels := by rfl

def raw24244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24244Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24244step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24244step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24244 raw24244Labels = mixedMoment B node1134 node1134Labels := by
  calc
    mixedMoment B raw24244 raw24244Labels = mixedMoment B raw24244step0 raw24244step0Labels := by
      have hz : ∀ j, raw24244 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24244step0 = (fun i j => raw24244 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24244step0 raw24244; decide +kernel
      have hl : raw24244step0Labels = raw24244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24244 raw24244Labels permutation346 hz
    mixedMoment B raw24244step0 raw24244step0Labels = mixedMoment B raw24244step1 raw24244step1Labels := by
      have ha : raw24244step1 = (fun i j => raw24244step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24244step1 raw24244step0; decide +kernel
      have hl : raw24244step1Labels = raw24244step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24244step0 raw24244step0Labels permutation35 permutation3
    _ = mixedMoment B node1134 node1134Labels := by rfl

def raw24245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24245Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24245step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24245step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24245step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24245 raw24245Labels = mixedMoment B node1134 node1134Labels := by
  calc
    mixedMoment B raw24245 raw24245Labels = mixedMoment B raw24245step0 raw24245step0Labels := by
      have hz : ∀ j, raw24245 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24245step0 = (fun i j => raw24245 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24245step0 raw24245; decide +kernel
      have hl : raw24245step0Labels = raw24245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24245 raw24245Labels permutation265 hz
    mixedMoment B raw24245step0 raw24245step0Labels = mixedMoment B raw24245step1 raw24245step1Labels := by
      have ha : raw24245step1 = (fun i j => raw24245step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24245step1 raw24245step0; decide +kernel
      have hl : raw24245step1Labels = raw24245step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24245step0 raw24245step0Labels permutation35 permutation3
    _ = mixedMoment B node1134 node1134Labels := by rfl

def raw24246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw24246Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw24246step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24246step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw24246step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24246step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24246step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24246 raw24246Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw24246 raw24246Labels = mixedMoment B raw24246step0 raw24246step0Labels := by
      have hz : ∀ j, raw24246 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24246step0 = (fun i j => raw24246 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24246step0 raw24246; decide +kernel
      have hl : raw24246step0Labels = raw24246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24246 raw24246Labels permutation346 hz
    mixedMoment B raw24246step0 raw24246step0Labels = mixedMoment B raw24246step1 raw24246step1Labels := by
      have hz : ∀ j, raw24246step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24246step1 = (fun i j => raw24246step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24246step1 raw24246step0; decide +kernel
      have hl : raw24246step1Labels = raw24246step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24246step0 raw24246step0Labels permutation56 hz
    mixedMoment B raw24246step1 raw24246step1Labels = mixedMoment B raw24246step2 raw24246step2Labels := by
      have ha : raw24246step2 = (fun i j => raw24246step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24246step2 raw24246step1; decide +kernel
      have hl : raw24246step2Labels = raw24246step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24246step1 raw24246step1Labels permutation11 permutation3
    _ = mixedMoment B node1246 node1246Labels := by rfl

def raw24247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24247Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24247step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24247step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24247step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24247step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24247step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24247 raw24247Labels = mixedMoment B node1300 node1300Labels := by
  calc
    mixedMoment B raw24247 raw24247Labels = mixedMoment B raw24247step0 raw24247step0Labels := by
      have hz : ∀ j, raw24247 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24247step0 = (fun i j => raw24247 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24247step0 raw24247; decide +kernel
      have hl : raw24247step0Labels = raw24247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24247 raw24247Labels permutation346 hz
    mixedMoment B raw24247step0 raw24247step0Labels = mixedMoment B raw24247step1 raw24247step1Labels := by
      have hz : ∀ j, raw24247step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24247step1 = (fun i j => raw24247step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24247step1 raw24247step0; decide +kernel
      have hl : raw24247step1Labels = raw24247step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24247step0 raw24247step0Labels permutation56 hz
    mixedMoment B raw24247step1 raw24247step1Labels = mixedMoment B raw24247step2 raw24247step2Labels := by
      have ha : raw24247step2 = (fun i j => raw24247step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24247step2 raw24247step1; decide +kernel
      have hl : raw24247step2Labels = raw24247step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24247step1 raw24247step1Labels permutation11 permutation3
    _ = mixedMoment B node1300 node1300Labels := by rfl

def raw24248 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24248step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24248step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24248step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24248step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24248 raw24248Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw24248 raw24248Labels = mixedMoment B raw24248step0 raw24248step0Labels := by
      have hz : ∀ j, raw24248 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24248step0 = (fun i j => raw24248 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24248step0 raw24248; decide +kernel
      have hl : raw24248step0Labels = raw24248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24248 raw24248Labels permutation346 hz
    mixedMoment B raw24248step0 raw24248step0Labels = mixedMoment B raw24248step1 raw24248step1Labels := by
      have ha : raw24248step1 = (fun i j => raw24248step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24248step1 raw24248step0; decide +kernel
      have hl : raw24248step1Labels = raw24248step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24248step0 raw24248step0Labels permutation34 permutation7
    mixedMoment B raw24248step1 raw24248step1Labels = mixedMoment B raw24248step2 raw24248step2Labels := by
      have ha : raw24248step2 = raw24248step1 := by apply Matrix.ext; unfold raw24248step2 raw24248step1; decide +kernel
      have hl : raw24248step1Labels = labelEmbedding10 ∘ raw24248step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24248step1 raw24248step1Labels raw24248step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw24249 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24249step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24249step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24249step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24249step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24249 raw24249Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw24249 raw24249Labels = mixedMoment B raw24249step0 raw24249step0Labels := by
      have hz : ∀ j, raw24249 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24249step0 = (fun i j => raw24249 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24249step0 raw24249; decide +kernel
      have hl : raw24249step0Labels = raw24249Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24249 raw24249Labels permutation265 hz
    mixedMoment B raw24249step0 raw24249step0Labels = mixedMoment B raw24249step1 raw24249step1Labels := by
      have ha : raw24249step1 = (fun i j => raw24249step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24249step1 raw24249step0; decide +kernel
      have hl : raw24249step1Labels = raw24249step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24249step0 raw24249step0Labels permutation34 permutation7
    mixedMoment B raw24249step1 raw24249step1Labels = mixedMoment B raw24249step2 raw24249step2Labels := by
      have ha : raw24249step2 = raw24249step1 := by apply Matrix.ext; unfold raw24249step2 raw24249step1; decide +kernel
      have hl : raw24249step1Labels = labelEmbedding10 ∘ raw24249step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24249step1 raw24249step1Labels raw24249step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw24250 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24250step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24250step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24250step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24250step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24250step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24250step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24250step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24250 raw24250Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw24250 raw24250Labels = mixedMoment B raw24250step0 raw24250step0Labels := by
      have hz : ∀ j, raw24250 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24250step0 = (fun i j => raw24250 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24250step0 raw24250; decide +kernel
      have hl : raw24250step0Labels = raw24250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24250 raw24250Labels permutation346 hz
    mixedMoment B raw24250step0 raw24250step0Labels = mixedMoment B raw24250step1 raw24250step1Labels := by
      have hz : ∀ j, raw24250step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24250step1 = (fun i j => raw24250step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24250step1 raw24250step0; decide +kernel
      have hl : raw24250step1Labels = raw24250step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24250step0 raw24250step0Labels permutation56 hz
    mixedMoment B raw24250step1 raw24250step1Labels = mixedMoment B raw24250step2 raw24250step2Labels := by
      have ha : raw24250step2 = (fun i j => raw24250step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24250step2 raw24250step1; decide +kernel
      have hl : raw24250step2Labels = raw24250step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24250step1 raw24250step1Labels permutation10 permutation7
    mixedMoment B raw24250step2 raw24250step2Labels = mixedMoment B raw24250step3 raw24250step3Labels := by
      have ha : raw24250step3 = raw24250step2 := by apply Matrix.ext; unfold raw24250step3 raw24250step2; decide +kernel
      have hl : raw24250step2Labels = labelEmbedding10 ∘ raw24250step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24250step2 raw24250step2Labels raw24250step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4499 node4499Labels := by rfl

def raw24251 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24251step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24251step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24251step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24251step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24251step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24251step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24251step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24251 raw24251Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw24251 raw24251Labels = mixedMoment B raw24251step0 raw24251step0Labels := by
      have hz : ∀ j, raw24251 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24251step0 = (fun i j => raw24251 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24251step0 raw24251; decide +kernel
      have hl : raw24251step0Labels = raw24251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24251 raw24251Labels permutation346 hz
    mixedMoment B raw24251step0 raw24251step0Labels = mixedMoment B raw24251step1 raw24251step1Labels := by
      have hz : ∀ j, raw24251step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24251step1 = (fun i j => raw24251step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24251step1 raw24251step0; decide +kernel
      have hl : raw24251step1Labels = raw24251step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24251step0 raw24251step0Labels permutation56 hz
    mixedMoment B raw24251step1 raw24251step1Labels = mixedMoment B raw24251step2 raw24251step2Labels := by
      have ha : raw24251step2 = (fun i j => raw24251step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24251step2 raw24251step1; decide +kernel
      have hl : raw24251step2Labels = raw24251step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24251step1 raw24251step1Labels permutation10 permutation7
    mixedMoment B raw24251step2 raw24251step2Labels = mixedMoment B raw24251step3 raw24251step3Labels := by
      have ha : raw24251step3 = raw24251step2 := by apply Matrix.ext; unfold raw24251step3 raw24251step2; decide +kernel
      have hl : raw24251step2Labels = labelEmbedding10 ∘ raw24251step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24251step2 raw24251step2Labels raw24251step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4498 node4498Labels := by rfl

def raw24252 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24252step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24252step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24252step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24252step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24252 raw24252Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw24252 raw24252Labels = mixedMoment B raw24252step0 raw24252step0Labels := by
      have hz : ∀ j, raw24252 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24252step0 = (fun i j => raw24252 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24252step0 raw24252; decide +kernel
      have hl : raw24252step0Labels = raw24252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24252 raw24252Labels permutation346 hz
    mixedMoment B raw24252step0 raw24252step0Labels = mixedMoment B raw24252step1 raw24252step1Labels := by
      have ha : raw24252step1 = (fun i j => raw24252step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24252step1 raw24252step0; decide +kernel
      have hl : raw24252step1Labels = raw24252step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24252step0 raw24252step0Labels permutation32 permutation6
    mixedMoment B raw24252step1 raw24252step1Labels = mixedMoment B raw24252step2 raw24252step2Labels := by
      have ha : raw24252step2 = raw24252step1 := by apply Matrix.ext; unfold raw24252step2 raw24252step1; decide +kernel
      have hl : raw24252step1Labels = labelEmbedding9 ∘ raw24252step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24252step1 raw24252step1Labels raw24252step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw24253 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24253step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24253step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24253step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24253step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24253 raw24253Labels = mixedMoment B node4590 node4590Labels := by
  calc
    mixedMoment B raw24253 raw24253Labels = mixedMoment B raw24253step0 raw24253step0Labels := by
      have ha : raw24253step0 = (fun i j => raw24253 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24253step0 raw24253; decide +kernel
      have hl : raw24253step0Labels = raw24253Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24253 raw24253Labels permutation176 permutation6
    mixedMoment B raw24253step0 raw24253step0Labels = mixedMoment B raw24253step1 raw24253step1Labels := by
      have ha : raw24253step1 = raw24253step0 := by apply Matrix.ext; unfold raw24253step1 raw24253step0; decide +kernel
      have hl : raw24253step0Labels = labelEmbedding9 ∘ raw24253step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24253step0 raw24253step0Labels raw24253step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4590 node4590Labels := by rfl

def raw24254 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24254step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24254step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24254step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24254step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24254 raw24254Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw24254 raw24254Labels = mixedMoment B raw24254step0 raw24254step0Labels := by
      have hz : ∀ j, raw24254 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24254step0 = (fun i j => raw24254 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24254step0 raw24254; decide +kernel
      have hl : raw24254step0Labels = raw24254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24254 raw24254Labels permutation346 hz
    mixedMoment B raw24254step0 raw24254step0Labels = mixedMoment B raw24254step1 raw24254step1Labels := by
      have ha : raw24254step1 = (fun i j => raw24254step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24254step1 raw24254step0; decide +kernel
      have hl : raw24254step1Labels = raw24254step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24254step0 raw24254step0Labels permutation34 permutation7
    mixedMoment B raw24254step1 raw24254step1Labels = mixedMoment B raw24254step2 raw24254step2Labels := by
      have ha : raw24254step2 = raw24254step1 := by apply Matrix.ext; unfold raw24254step2 raw24254step1; decide +kernel
      have hl : raw24254step1Labels = labelEmbedding10 ∘ raw24254step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24254step1 raw24254step1Labels raw24254step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4603 node4603Labels := by rfl

def raw24255 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24255step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24255step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24255step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24255step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24255step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24255 raw24255Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw24255 raw24255Labels = mixedMoment B raw24255step0 raw24255step0Labels := by
      have hz : ∀ j, raw24255 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24255step0 = (fun i j => raw24255 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24255step0 raw24255; decide +kernel
      have hl : raw24255step0Labels = raw24255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24255 raw24255Labels permutation346 hz
    mixedMoment B raw24255step0 raw24255step0Labels = mixedMoment B raw24255step1 raw24255step1Labels := by
      have ha : raw24255step1 = (fun i j => raw24255step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24255step1 raw24255step0; decide +kernel
      have hl : raw24255step1Labels = raw24255step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24255step0 raw24255step0Labels permutation34 permutation7
    mixedMoment B raw24255step1 raw24255step1Labels = mixedMoment B raw24255step2 raw24255step2Labels := by
      have ha : raw24255step2 = raw24255step1 := by apply Matrix.ext; unfold raw24255step2 raw24255step1; decide +kernel
      have hl : raw24255step1Labels = labelEmbedding10 ∘ raw24255step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24255step1 raw24255step1Labels raw24255step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw24256 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24256step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24256step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24256step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24256step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24256 raw24256Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw24256 raw24256Labels = mixedMoment B raw24256step0 raw24256step0Labels := by
      have hz : ∀ j, raw24256 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24256step0 = (fun i j => raw24256 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24256step0 raw24256; decide +kernel
      have hl : raw24256step0Labels = raw24256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24256 raw24256Labels permutation265 hz
    mixedMoment B raw24256step0 raw24256step0Labels = mixedMoment B raw24256step1 raw24256step1Labels := by
      have ha : raw24256step1 = (fun i j => raw24256step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24256step1 raw24256step0; decide +kernel
      have hl : raw24256step1Labels = raw24256step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24256step0 raw24256step0Labels permutation32 permutation6
    mixedMoment B raw24256step1 raw24256step1Labels = mixedMoment B raw24256step2 raw24256step2Labels := by
      have ha : raw24256step2 = raw24256step1 := by apply Matrix.ext; unfold raw24256step2 raw24256step1; decide +kernel
      have hl : raw24256step1Labels = labelEmbedding9 ∘ raw24256step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24256step1 raw24256step1Labels raw24256step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw24257 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24257Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24257step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24257step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24257step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24257step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24257 raw24257Labels = mixedMoment B node4590 node4590Labels := by
  calc
    mixedMoment B raw24257 raw24257Labels = mixedMoment B raw24257step0 raw24257step0Labels := by
      have ha : raw24257step0 = (fun i j => raw24257 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24257step0 raw24257; decide +kernel
      have hl : raw24257step0Labels = raw24257Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24257 raw24257Labels permutation152 permutation6
    mixedMoment B raw24257step0 raw24257step0Labels = mixedMoment B raw24257step1 raw24257step1Labels := by
      have ha : raw24257step1 = raw24257step0 := by apply Matrix.ext; unfold raw24257step1 raw24257step0; decide +kernel
      have hl : raw24257step0Labels = labelEmbedding9 ∘ raw24257step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24257step0 raw24257step0Labels raw24257step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4590 node4590Labels := by rfl

def raw24258 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24258step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24258step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24258step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24258step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24258 raw24258Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw24258 raw24258Labels = mixedMoment B raw24258step0 raw24258step0Labels := by
      have hz : ∀ j, raw24258 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24258step0 = (fun i j => raw24258 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24258step0 raw24258; decide +kernel
      have hl : raw24258step0Labels = raw24258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24258 raw24258Labels permutation265 hz
    mixedMoment B raw24258step0 raw24258step0Labels = mixedMoment B raw24258step1 raw24258step1Labels := by
      have ha : raw24258step1 = (fun i j => raw24258step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24258step1 raw24258step0; decide +kernel
      have hl : raw24258step1Labels = raw24258step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24258step0 raw24258step0Labels permutation34 permutation7
    mixedMoment B raw24258step1 raw24258step1Labels = mixedMoment B raw24258step2 raw24258step2Labels := by
      have ha : raw24258step2 = raw24258step1 := by apply Matrix.ext; unfold raw24258step2 raw24258step1; decide +kernel
      have hl : raw24258step1Labels = labelEmbedding10 ∘ raw24258step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24258step1 raw24258step1Labels raw24258step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4603 node4603Labels := by rfl

def raw24259 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24259step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24259step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24259step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24259step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24259step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24259 raw24259Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw24259 raw24259Labels = mixedMoment B raw24259step0 raw24259step0Labels := by
      have hz : ∀ j, raw24259 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24259step0 = (fun i j => raw24259 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24259step0 raw24259; decide +kernel
      have hl : raw24259step0Labels = raw24259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24259 raw24259Labels permutation265 hz
    mixedMoment B raw24259step0 raw24259step0Labels = mixedMoment B raw24259step1 raw24259step1Labels := by
      have ha : raw24259step1 = (fun i j => raw24259step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24259step1 raw24259step0; decide +kernel
      have hl : raw24259step1Labels = raw24259step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24259step0 raw24259step0Labels permutation34 permutation7
    mixedMoment B raw24259step1 raw24259step1Labels = mixedMoment B raw24259step2 raw24259step2Labels := by
      have ha : raw24259step2 = raw24259step1 := by apply Matrix.ext; unfold raw24259step2 raw24259step1; decide +kernel
      have hl : raw24259step1Labels = labelEmbedding10 ∘ raw24259step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24259step1 raw24259step1Labels raw24259step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw24260 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24260step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24260step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24260step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24260step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24260step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24260step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24260step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24260 raw24260Labels = mixedMoment B node4502 node4502Labels := by
  calc
    mixedMoment B raw24260 raw24260Labels = mixedMoment B raw24260step0 raw24260step0Labels := by
      have hz : ∀ j, raw24260 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24260step0 = (fun i j => raw24260 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24260step0 raw24260; decide +kernel
      have hl : raw24260step0Labels = raw24260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24260 raw24260Labels permutation346 hz
    mixedMoment B raw24260step0 raw24260step0Labels = mixedMoment B raw24260step1 raw24260step1Labels := by
      have hz : ∀ j, raw24260step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24260step1 = (fun i j => raw24260step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24260step1 raw24260step0; decide +kernel
      have hl : raw24260step1Labels = raw24260step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24260step0 raw24260step0Labels permutation56 hz
    mixedMoment B raw24260step1 raw24260step1Labels = mixedMoment B raw24260step2 raw24260step2Labels := by
      have ha : raw24260step2 = (fun i j => raw24260step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24260step2 raw24260step1; decide +kernel
      have hl : raw24260step2Labels = raw24260step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24260step1 raw24260step1Labels permutation8 permutation6
    mixedMoment B raw24260step2 raw24260step2Labels = mixedMoment B raw24260step3 raw24260step3Labels := by
      have ha : raw24260step3 = raw24260step2 := by apply Matrix.ext; unfold raw24260step3 raw24260step2; decide +kernel
      have hl : raw24260step2Labels = labelEmbedding9 ∘ raw24260step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24260step2 raw24260step2Labels raw24260step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4502 node4502Labels := by rfl

def raw24261 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24261step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24261step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24261step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24261step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24261 raw24261Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw24261 raw24261Labels = mixedMoment B raw24261step0 raw24261step0Labels := by
      have hz : ∀ j, raw24261 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24261step0 = (fun i j => raw24261 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24261step0 raw24261; decide +kernel
      have hl : raw24261step0Labels = raw24261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24261 raw24261Labels permutation346 hz
    mixedMoment B raw24261step0 raw24261step0Labels = mixedMoment B raw24261step1 raw24261step1Labels := by
      have ha : raw24261step1 = (fun i j => raw24261step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24261step1 raw24261step0; decide +kernel
      have hl : raw24261step1Labels = raw24261step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24261step0 raw24261step0Labels permutation32 permutation6
    mixedMoment B raw24261step1 raw24261step1Labels = mixedMoment B raw24261step2 raw24261step2Labels := by
      have ha : raw24261step2 = raw24261step1 := by apply Matrix.ext; unfold raw24261step2 raw24261step1; decide +kernel
      have hl : raw24261step1Labels = labelEmbedding9 ∘ raw24261step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24261step1 raw24261step1Labels raw24261step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4606 node4606Labels := by rfl

def raw24262 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24262step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24262step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24262step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24262step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24262 raw24262Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw24262 raw24262Labels = mixedMoment B raw24262step0 raw24262step0Labels := by
      have hz : ∀ j, raw24262 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24262step0 = (fun i j => raw24262 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24262step0 raw24262; decide +kernel
      have hl : raw24262step0Labels = raw24262Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24262 raw24262Labels permutation265 hz
    mixedMoment B raw24262step0 raw24262step0Labels = mixedMoment B raw24262step1 raw24262step1Labels := by
      have ha : raw24262step1 = (fun i j => raw24262step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24262step1 raw24262step0; decide +kernel
      have hl : raw24262step1Labels = raw24262step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24262step0 raw24262step0Labels permutation32 permutation6
    mixedMoment B raw24262step1 raw24262step1Labels = mixedMoment B raw24262step2 raw24262step2Labels := by
      have ha : raw24262step2 = raw24262step1 := by apply Matrix.ext; unfold raw24262step2 raw24262step1; decide +kernel
      have hl : raw24262step1Labels = labelEmbedding9 ∘ raw24262step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24262step1 raw24262step1Labels raw24262step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4606 node4606Labels := by rfl

def raw24263 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24263step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24263step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24263step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24263step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24263step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24263step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24263step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24263 raw24263Labels = mixedMoment B node4623 node4623Labels := by
  calc
    mixedMoment B raw24263 raw24263Labels = mixedMoment B raw24263step0 raw24263step0Labels := by
      have hz : ∀ j, raw24263 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24263step0 = (fun i j => raw24263 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24263step0 raw24263; decide +kernel
      have hl : raw24263step0Labels = raw24263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24263 raw24263Labels permutation346 hz
    mixedMoment B raw24263step0 raw24263step0Labels = mixedMoment B raw24263step1 raw24263step1Labels := by
      have hz : ∀ j, raw24263step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24263step1 = (fun i j => raw24263step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24263step1 raw24263step0; decide +kernel
      have hl : raw24263step1Labels = raw24263step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24263step0 raw24263step0Labels permutation56 hz
    mixedMoment B raw24263step1 raw24263step1Labels = mixedMoment B raw24263step2 raw24263step2Labels := by
      have ha : raw24263step2 = (fun i j => raw24263step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24263step2 raw24263step1; decide +kernel
      have hl : raw24263step2Labels = raw24263step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24263step1 raw24263step1Labels permutation8 permutation7
    mixedMoment B raw24263step2 raw24263step2Labels = mixedMoment B raw24263step3 raw24263step3Labels := by
      have ha : raw24263step3 = raw24263step2 := by apply Matrix.ext; unfold raw24263step3 raw24263step2; decide +kernel
      have hl : raw24263step2Labels = labelEmbedding10 ∘ raw24263step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24263step2 raw24263step2Labels raw24263step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4623 node4623Labels := by rfl

def raw24264 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24264step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24264step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24264step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24264step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24264step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24264step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24264step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24264 raw24264Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw24264 raw24264Labels = mixedMoment B raw24264step0 raw24264step0Labels := by
      have hz : ∀ j, raw24264 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24264step0 = (fun i j => raw24264 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24264step0 raw24264; decide +kernel
      have hl : raw24264step0Labels = raw24264Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24264 raw24264Labels permutation346 hz
    mixedMoment B raw24264step0 raw24264step0Labels = mixedMoment B raw24264step1 raw24264step1Labels := by
      have hz : ∀ j, raw24264step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24264step1 = (fun i j => raw24264step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24264step1 raw24264step0; decide +kernel
      have hl : raw24264step1Labels = raw24264step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24264step0 raw24264step0Labels permutation56 hz
    mixedMoment B raw24264step1 raw24264step1Labels = mixedMoment B raw24264step2 raw24264step2Labels := by
      have ha : raw24264step2 = (fun i j => raw24264step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24264step2 raw24264step1; decide +kernel
      have hl : raw24264step2Labels = raw24264step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24264step1 raw24264step1Labels permutation8 permutation6
    mixedMoment B raw24264step2 raw24264step2Labels = mixedMoment B raw24264step3 raw24264step3Labels := by
      have ha : raw24264step3 = raw24264step2 := by apply Matrix.ext; unfold raw24264step3 raw24264step2; decide +kernel
      have hl : raw24264step2Labels = labelEmbedding9 ∘ raw24264step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24264step2 raw24264step2Labels raw24264step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4499 node4499Labels := by rfl

def raw24265 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24265step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24265step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24265step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24265step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24265step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24265 raw24265Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw24265 raw24265Labels = mixedMoment B raw24265step0 raw24265step0Labels := by
      have hz : ∀ j, raw24265 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24265step0 = (fun i j => raw24265 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24265step0 raw24265; decide +kernel
      have hl : raw24265step0Labels = raw24265Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24265 raw24265Labels permutation346 hz
    mixedMoment B raw24265step0 raw24265step0Labels = mixedMoment B raw24265step1 raw24265step1Labels := by
      have ha : raw24265step1 = (fun i j => raw24265step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24265step1 raw24265step0; decide +kernel
      have hl : raw24265step1Labels = raw24265step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24265step0 raw24265step0Labels permutation32 permutation6
    mixedMoment B raw24265step1 raw24265step1Labels = mixedMoment B raw24265step2 raw24265step2Labels := by
      have ha : raw24265step2 = raw24265step1 := by apply Matrix.ext; unfold raw24265step2 raw24265step1; decide +kernel
      have hl : raw24265step1Labels = labelEmbedding9 ∘ raw24265step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24265step1 raw24265step1Labels raw24265step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4603 node4603Labels := by rfl

def raw24266 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24266step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24266step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24266step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24266step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24266 raw24266Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw24266 raw24266Labels = mixedMoment B raw24266step0 raw24266step0Labels := by
      have hz : ∀ j, raw24266 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24266step0 = (fun i j => raw24266 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24266step0 raw24266; decide +kernel
      have hl : raw24266step0Labels = raw24266Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24266 raw24266Labels permutation265 hz
    mixedMoment B raw24266step0 raw24266step0Labels = mixedMoment B raw24266step1 raw24266step1Labels := by
      have ha : raw24266step1 = (fun i j => raw24266step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24266step1 raw24266step0; decide +kernel
      have hl : raw24266step1Labels = raw24266step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24266step0 raw24266step0Labels permutation32 permutation6
    mixedMoment B raw24266step1 raw24266step1Labels = mixedMoment B raw24266step2 raw24266step2Labels := by
      have ha : raw24266step2 = raw24266step1 := by apply Matrix.ext; unfold raw24266step2 raw24266step1; decide +kernel
      have hl : raw24266step1Labels = labelEmbedding9 ∘ raw24266step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24266step1 raw24266step1Labels raw24266step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4603 node4603Labels := by rfl

def raw24267 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24267step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24267step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24267step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24267step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw24267step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24267step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw24267step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24267 raw24267Labels = mixedMoment B node4620 node4620Labels := by
  calc
    mixedMoment B raw24267 raw24267Labels = mixedMoment B raw24267step0 raw24267step0Labels := by
      have hz : ∀ j, raw24267 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24267step0 = (fun i j => raw24267 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24267step0 raw24267; decide +kernel
      have hl : raw24267step0Labels = raw24267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24267 raw24267Labels permutation346 hz
    mixedMoment B raw24267step0 raw24267step0Labels = mixedMoment B raw24267step1 raw24267step1Labels := by
      have hz : ∀ j, raw24267step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24267step1 = (fun i j => raw24267step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24267step1 raw24267step0; decide +kernel
      have hl : raw24267step1Labels = raw24267step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24267step0 raw24267step0Labels permutation56 hz
    mixedMoment B raw24267step1 raw24267step1Labels = mixedMoment B raw24267step2 raw24267step2Labels := by
      have ha : raw24267step2 = (fun i j => raw24267step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24267step2 raw24267step1; decide +kernel
      have hl : raw24267step2Labels = raw24267step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24267step1 raw24267step1Labels permutation8 permutation6
    mixedMoment B raw24267step2 raw24267step2Labels = mixedMoment B raw24267step3 raw24267step3Labels := by
      have ha : raw24267step3 = raw24267step2 := by apply Matrix.ext; unfold raw24267step3 raw24267step2; decide +kernel
      have hl : raw24267step2Labels = labelEmbedding9 ∘ raw24267step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24267step2 raw24267step2Labels raw24267step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4620 node4620Labels := by rfl

def raw24268 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24268step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24268step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24268step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24268step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24268step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24268step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24268step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24268 raw24268Labels = mixedMoment B node4619 node4619Labels := by
  calc
    mixedMoment B raw24268 raw24268Labels = mixedMoment B raw24268step0 raw24268step0Labels := by
      have hz : ∀ j, raw24268 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24268step0 = (fun i j => raw24268 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24268step0 raw24268; decide +kernel
      have hl : raw24268step0Labels = raw24268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24268 raw24268Labels permutation346 hz
    mixedMoment B raw24268step0 raw24268step0Labels = mixedMoment B raw24268step1 raw24268step1Labels := by
      have hz : ∀ j, raw24268step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24268step1 = (fun i j => raw24268step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24268step1 raw24268step0; decide +kernel
      have hl : raw24268step1Labels = raw24268step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24268step0 raw24268step0Labels permutation56 hz
    mixedMoment B raw24268step1 raw24268step1Labels = mixedMoment B raw24268step2 raw24268step2Labels := by
      have ha : raw24268step2 = (fun i j => raw24268step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24268step2 raw24268step1; decide +kernel
      have hl : raw24268step2Labels = raw24268step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24268step1 raw24268step1Labels permutation10 permutation7
    mixedMoment B raw24268step2 raw24268step2Labels = mixedMoment B raw24268step3 raw24268step3Labels := by
      have ha : raw24268step3 = raw24268step2 := by apply Matrix.ext; unfold raw24268step3 raw24268step2; decide +kernel
      have hl : raw24268step2Labels = labelEmbedding10 ∘ raw24268step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24268step2 raw24268step2Labels raw24268step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4619 node4619Labels := by rfl

def raw24269 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24269step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24269step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24269step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24269step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24269step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24269step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24269step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24269 raw24269Labels = mixedMoment B node4623 node4623Labels := by
  calc
    mixedMoment B raw24269 raw24269Labels = mixedMoment B raw24269step0 raw24269step0Labels := by
      have hz : ∀ j, raw24269 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24269step0 = (fun i j => raw24269 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24269step0 raw24269; decide +kernel
      have hl : raw24269step0Labels = raw24269Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24269 raw24269Labels permutation346 hz
    mixedMoment B raw24269step0 raw24269step0Labels = mixedMoment B raw24269step1 raw24269step1Labels := by
      have hz : ∀ j, raw24269step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24269step1 = (fun i j => raw24269step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24269step1 raw24269step0; decide +kernel
      have hl : raw24269step1Labels = raw24269step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24269step0 raw24269step0Labels permutation56 hz
    mixedMoment B raw24269step1 raw24269step1Labels = mixedMoment B raw24269step2 raw24269step2Labels := by
      have ha : raw24269step2 = (fun i j => raw24269step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24269step2 raw24269step1; decide +kernel
      have hl : raw24269step2Labels = raw24269step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24269step1 raw24269step1Labels permutation8 permutation6
    mixedMoment B raw24269step2 raw24269step2Labels = mixedMoment B raw24269step3 raw24269step3Labels := by
      have ha : raw24269step3 = raw24269step2 := by apply Matrix.ext; unfold raw24269step3 raw24269step2; decide +kernel
      have hl : raw24269step2Labels = labelEmbedding9 ∘ raw24269step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24269step2 raw24269step2Labels raw24269step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4623 node4623Labels := by rfl

def raw24270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24270step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24270step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24270step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24270step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24270step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24270 raw24270Labels = mixedMoment B node4165 node4165Labels := by
  calc
    mixedMoment B raw24270 raw24270Labels = mixedMoment B raw24270step0 raw24270step0Labels := by
      have hz : ∀ j, raw24270 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24270step0 = (fun i j => raw24270 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24270step0 raw24270; decide +kernel
      have hl : raw24270step0Labels = raw24270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24270 raw24270Labels permutation346 hz
    mixedMoment B raw24270step0 raw24270step0Labels = mixedMoment B raw24270step1 raw24270step1Labels := by
      have ha : raw24270step1 = (fun i j => raw24270step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24270step1 raw24270step0; decide +kernel
      have hl : raw24270step1Labels = raw24270step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24270step0 raw24270step0Labels permutation44 permutation3
    mixedMoment B raw24270step1 raw24270step1Labels = mixedMoment B raw24270step2 raw24270step2Labels := by
      have ha : raw24270step2 = raw24270step1 := by apply Matrix.ext; unfold raw24270step2 raw24270step1; decide +kernel
      have hl : raw24270step1Labels = labelEmbedding6 ∘ raw24270step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24270step1 raw24270step1Labels raw24270step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4165 node4165Labels := by rfl

def raw24271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24271step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24271step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24271step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24271step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24271 raw24271Labels = mixedMoment B node4537 node4537Labels := by
  calc
    mixedMoment B raw24271 raw24271Labels = mixedMoment B raw24271step0 raw24271step0Labels := by
      have ha : raw24271step0 = (fun i j => raw24271 (permutation188 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24271step0 raw24271; decide +kernel
      have hl : raw24271step0Labels = raw24271Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24271 raw24271Labels permutation188 permutation3
    mixedMoment B raw24271step0 raw24271step0Labels = mixedMoment B raw24271step1 raw24271step1Labels := by
      have ha : raw24271step1 = raw24271step0 := by apply Matrix.ext; unfold raw24271step1 raw24271step0; decide +kernel
      have hl : raw24271step0Labels = labelEmbedding6 ∘ raw24271step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24271step0 raw24271step0Labels raw24271step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4537 node4537Labels := by rfl

def raw24272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw24272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw24272step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24272step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24272step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24272step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24272 raw24272Labels = mixedMoment B node4570 node4570Labels := by
  calc
    mixedMoment B raw24272 raw24272Labels = mixedMoment B raw24272step0 raw24272step0Labels := by
      have hz : ∀ j, raw24272 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24272step0 = (fun i j => raw24272 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24272step0 raw24272; decide +kernel
      have hl : raw24272step0Labels = raw24272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24272 raw24272Labels permutation346 hz
    mixedMoment B raw24272step0 raw24272step0Labels = mixedMoment B raw24272step1 raw24272step1Labels := by
      have ha : raw24272step1 = (fun i j => raw24272step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24272step1 raw24272step0; decide +kernel
      have hl : raw24272step1Labels = raw24272step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24272step0 raw24272step0Labels permutation44 permutation3
    mixedMoment B raw24272step1 raw24272step1Labels = mixedMoment B raw24272step2 raw24272step2Labels := by
      have ha : raw24272step2 = raw24272step1 := by apply Matrix.ext; unfold raw24272step2 raw24272step1; decide +kernel
      have hl : raw24272step1Labels = labelEmbedding6 ∘ raw24272step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24272step1 raw24272step1Labels raw24272step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4570 node4570Labels := by rfl

def raw24273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw24273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw24273step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24273step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24273step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24273 raw24273Labels = mixedMoment B node4618 node4618Labels := by
  calc
    mixedMoment B raw24273 raw24273Labels = mixedMoment B raw24273step0 raw24273step0Labels := by
      have hz : ∀ j, raw24273 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24273step0 = (fun i j => raw24273 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24273step0 raw24273; decide +kernel
      have hl : raw24273step0Labels = raw24273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24273 raw24273Labels permutation346 hz
    mixedMoment B raw24273step0 raw24273step0Labels = mixedMoment B raw24273step1 raw24273step1Labels := by
      have ha : raw24273step1 = (fun i j => raw24273step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24273step1 raw24273step0; decide +kernel
      have hl : raw24273step1Labels = raw24273step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24273step0 raw24273step0Labels permutation44 permutation3
    mixedMoment B raw24273step1 raw24273step1Labels = mixedMoment B raw24273step2 raw24273step2Labels := by
      have ha : raw24273step2 = raw24273step1 := by apply Matrix.ext; unfold raw24273step2 raw24273step1; decide +kernel
      have hl : raw24273step1Labels = labelEmbedding6 ∘ raw24273step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24273step1 raw24273step1Labels raw24273step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4618 node4618Labels := by rfl

def raw24274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24274step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24274step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24274step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24274step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24274step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24274 raw24274Labels = mixedMoment B node4165 node4165Labels := by
  calc
    mixedMoment B raw24274 raw24274Labels = mixedMoment B raw24274step0 raw24274step0Labels := by
      have hz : ∀ j, raw24274 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24274step0 = (fun i j => raw24274 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24274step0 raw24274; decide +kernel
      have hl : raw24274step0Labels = raw24274Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24274 raw24274Labels permutation265 hz
    mixedMoment B raw24274step0 raw24274step0Labels = mixedMoment B raw24274step1 raw24274step1Labels := by
      have ha : raw24274step1 = (fun i j => raw24274step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24274step1 raw24274step0; decide +kernel
      have hl : raw24274step1Labels = raw24274step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24274step0 raw24274step0Labels permutation44 permutation3
    mixedMoment B raw24274step1 raw24274step1Labels = mixedMoment B raw24274step2 raw24274step2Labels := by
      have ha : raw24274step2 = raw24274step1 := by apply Matrix.ext; unfold raw24274step2 raw24274step1; decide +kernel
      have hl : raw24274step1Labels = labelEmbedding6 ∘ raw24274step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24274step1 raw24274step1Labels raw24274step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4165 node4165Labels := by rfl

def raw24275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24275step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24275step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24275step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24275step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24275 raw24275Labels = mixedMoment B node4537 node4537Labels := by
  calc
    mixedMoment B raw24275 raw24275Labels = mixedMoment B raw24275step0 raw24275step0Labels := by
      have ha : raw24275step0 = (fun i j => raw24275 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24275step0 raw24275; decide +kernel
      have hl : raw24275step0Labels = raw24275Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24275 raw24275Labels permutation164 permutation3
    mixedMoment B raw24275step0 raw24275step0Labels = mixedMoment B raw24275step1 raw24275step1Labels := by
      have ha : raw24275step1 = raw24275step0 := by apply Matrix.ext; unfold raw24275step1 raw24275step0; decide +kernel
      have hl : raw24275step0Labels = labelEmbedding6 ∘ raw24275step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24275step0 raw24275step0Labels raw24275step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4537 node4537Labels := by rfl

def raw24276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw24276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw24276step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24276step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24276step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24276step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24276 raw24276Labels = mixedMoment B node4570 node4570Labels := by
  calc
    mixedMoment B raw24276 raw24276Labels = mixedMoment B raw24276step0 raw24276step0Labels := by
      have hz : ∀ j, raw24276 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24276step0 = (fun i j => raw24276 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24276step0 raw24276; decide +kernel
      have hl : raw24276step0Labels = raw24276Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24276 raw24276Labels permutation265 hz
    mixedMoment B raw24276step0 raw24276step0Labels = mixedMoment B raw24276step1 raw24276step1Labels := by
      have ha : raw24276step1 = (fun i j => raw24276step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24276step1 raw24276step0; decide +kernel
      have hl : raw24276step1Labels = raw24276step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24276step0 raw24276step0Labels permutation44 permutation3
    mixedMoment B raw24276step1 raw24276step1Labels = mixedMoment B raw24276step2 raw24276step2Labels := by
      have ha : raw24276step2 = raw24276step1 := by apply Matrix.ext; unfold raw24276step2 raw24276step1; decide +kernel
      have hl : raw24276step1Labels = labelEmbedding6 ∘ raw24276step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24276step1 raw24276step1Labels raw24276step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4570 node4570Labels := by rfl

def raw24277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw24277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw24277step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24277step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24277step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24277step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24277 raw24277Labels = mixedMoment B node4618 node4618Labels := by
  calc
    mixedMoment B raw24277 raw24277Labels = mixedMoment B raw24277step0 raw24277step0Labels := by
      have hz : ∀ j, raw24277 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24277step0 = (fun i j => raw24277 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24277step0 raw24277; decide +kernel
      have hl : raw24277step0Labels = raw24277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24277 raw24277Labels permutation265 hz
    mixedMoment B raw24277step0 raw24277step0Labels = mixedMoment B raw24277step1 raw24277step1Labels := by
      have ha : raw24277step1 = (fun i j => raw24277step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24277step1 raw24277step0; decide +kernel
      have hl : raw24277step1Labels = raw24277step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24277step0 raw24277step0Labels permutation44 permutation3
    mixedMoment B raw24277step1 raw24277step1Labels = mixedMoment B raw24277step2 raw24277step2Labels := by
      have ha : raw24277step2 = raw24277step1 := by apply Matrix.ext; unfold raw24277step2 raw24277step1; decide +kernel
      have hl : raw24277step1Labels = labelEmbedding6 ∘ raw24277step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24277step1 raw24277step1Labels raw24277step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4618 node4618Labels := by rfl

def raw24278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24278step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24278step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24278step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24278step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw24278step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24278step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw24278step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24278 raw24278Labels = mixedMoment B node4167 node4167Labels := by
  calc
    mixedMoment B raw24278 raw24278Labels = mixedMoment B raw24278step0 raw24278step0Labels := by
      have hz : ∀ j, raw24278 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24278step0 = (fun i j => raw24278 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24278step0 raw24278; decide +kernel
      have hl : raw24278step0Labels = raw24278Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24278 raw24278Labels permutation346 hz
    mixedMoment B raw24278step0 raw24278step0Labels = mixedMoment B raw24278step1 raw24278step1Labels := by
      have hz : ∀ j, raw24278step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24278step1 = (fun i j => raw24278step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24278step1 raw24278step0; decide +kernel
      have hl : raw24278step1Labels = raw24278step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24278step0 raw24278step0Labels permutation56 hz
    mixedMoment B raw24278step1 raw24278step1Labels = mixedMoment B raw24278step2 raw24278step2Labels := by
      have ha : raw24278step2 = (fun i j => raw24278step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24278step2 raw24278step1; decide +kernel
      have hl : raw24278step2Labels = raw24278step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24278step1 raw24278step1Labels permutation10 permutation3
    mixedMoment B raw24278step2 raw24278step2Labels = mixedMoment B raw24278step3 raw24278step3Labels := by
      have ha : raw24278step3 = raw24278step2 := by apply Matrix.ext; unfold raw24278step3 raw24278step2; decide +kernel
      have hl : raw24278step2Labels = labelEmbedding6 ∘ raw24278step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24278step2 raw24278step2Labels raw24278step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4167 node4167Labels := by rfl

def raw24279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24279step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24279step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw24279step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24279step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw24279step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24279 raw24279Labels = mixedMoment B node4539 node4539Labels := by
  calc
    mixedMoment B raw24279 raw24279Labels = mixedMoment B raw24279step0 raw24279step0Labels := by
      have hz : ∀ j, raw24279 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24279step0 = (fun i j => raw24279 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24279step0 raw24279; decide +kernel
      have hl : raw24279step0Labels = raw24279Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24279 raw24279Labels permutation346 hz
    mixedMoment B raw24279step0 raw24279step0Labels = mixedMoment B raw24279step1 raw24279step1Labels := by
      have ha : raw24279step1 = (fun i j => raw24279step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24279step1 raw24279step0; decide +kernel
      have hl : raw24279step1Labels = raw24279step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24279step0 raw24279step0Labels permutation34 permutation3
    mixedMoment B raw24279step1 raw24279step1Labels = mixedMoment B raw24279step2 raw24279step2Labels := by
      have ha : raw24279step2 = raw24279step1 := by apply Matrix.ext; unfold raw24279step2 raw24279step1; decide +kernel
      have hl : raw24279step1Labels = labelEmbedding6 ∘ raw24279step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24279step1 raw24279step1Labels raw24279step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4539 node4539Labels := by rfl

def raw24280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24280step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw24280step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24280step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw24280step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24280 raw24280Labels = mixedMoment B node4539 node4539Labels := by
  calc
    mixedMoment B raw24280 raw24280Labels = mixedMoment B raw24280step0 raw24280step0Labels := by
      have hz : ∀ j, raw24280 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24280step0 = (fun i j => raw24280 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24280step0 raw24280; decide +kernel
      have hl : raw24280step0Labels = raw24280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24280 raw24280Labels permutation265 hz
    mixedMoment B raw24280step0 raw24280step0Labels = mixedMoment B raw24280step1 raw24280step1Labels := by
      have ha : raw24280step1 = (fun i j => raw24280step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24280step1 raw24280step0; decide +kernel
      have hl : raw24280step1Labels = raw24280step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24280step0 raw24280step0Labels permutation34 permutation3
    mixedMoment B raw24280step1 raw24280step1Labels = mixedMoment B raw24280step2 raw24280step2Labels := by
      have ha : raw24280step2 = raw24280step1 := by apply Matrix.ext; unfold raw24280step2 raw24280step1; decide +kernel
      have hl : raw24280step1Labels = labelEmbedding6 ∘ raw24280step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24280step1 raw24280step1Labels raw24280step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4539 node4539Labels := by rfl

def raw24281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 2, -2], ![2, -2, 0]]
def raw24281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![0, 2, -2], ![2, -2, 0]]
def raw24281step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24281step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![0, 2, -2], ![2, -2, 0]]
def raw24281step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24281step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw24281step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24281step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw24281step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24281 raw24281Labels = mixedMoment B node4575 node4575Labels := by
  calc
    mixedMoment B raw24281 raw24281Labels = mixedMoment B raw24281step0 raw24281step0Labels := by
      have hz : ∀ j, raw24281 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24281step0 = (fun i j => raw24281 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24281step0 raw24281; decide +kernel
      have hl : raw24281step0Labels = raw24281Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24281 raw24281Labels permutation346 hz
    mixedMoment B raw24281step0 raw24281step0Labels = mixedMoment B raw24281step1 raw24281step1Labels := by
      have hz : ∀ j, raw24281step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24281step1 = (fun i j => raw24281step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24281step1 raw24281step0; decide +kernel
      have hl : raw24281step1Labels = raw24281step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24281step0 raw24281step0Labels permutation56 hz
    mixedMoment B raw24281step1 raw24281step1Labels = mixedMoment B raw24281step2 raw24281step2Labels := by
      have ha : raw24281step2 = (fun i j => raw24281step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24281step2 raw24281step1; decide +kernel
      have hl : raw24281step2Labels = raw24281step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24281step1 raw24281step1Labels permutation10 permutation3
    mixedMoment B raw24281step2 raw24281step2Labels = mixedMoment B raw24281step3 raw24281step3Labels := by
      have ha : raw24281step3 = raw24281step2 := by apply Matrix.ext; unfold raw24281step3 raw24281step2; decide +kernel
      have hl : raw24281step2Labels = labelEmbedding6 ∘ raw24281step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24281step2 raw24281step2Labels raw24281step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4575 node4575Labels := by rfl

def raw24282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![1, -1, 0]]
def raw24282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![1, -1, 0]]
def raw24282step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24282step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, 1, -2], ![1, -1, 0]]
def raw24282step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24282step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24282step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24282step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24282step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24282 raw24282Labels = mixedMoment B node4619 node4619Labels := by
  calc
    mixedMoment B raw24282 raw24282Labels = mixedMoment B raw24282step0 raw24282step0Labels := by
      have hz : ∀ j, raw24282 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24282step0 = (fun i j => raw24282 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24282step0 raw24282; decide +kernel
      have hl : raw24282step0Labels = raw24282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24282 raw24282Labels permutation346 hz
    mixedMoment B raw24282step0 raw24282step0Labels = mixedMoment B raw24282step1 raw24282step1Labels := by
      have hz : ∀ j, raw24282step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24282step1 = (fun i j => raw24282step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24282step1 raw24282step0; decide +kernel
      have hl : raw24282step1Labels = raw24282step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24282step0 raw24282step0Labels permutation56 hz
    mixedMoment B raw24282step1 raw24282step1Labels = mixedMoment B raw24282step2 raw24282step2Labels := by
      have ha : raw24282step2 = (fun i j => raw24282step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24282step2 raw24282step1; decide +kernel
      have hl : raw24282step2Labels = raw24282step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24282step1 raw24282step1Labels permutation11 permutation3
    mixedMoment B raw24282step2 raw24282step2Labels = mixedMoment B raw24282step3 raw24282step3Labels := by
      have ha : raw24282step3 = raw24282step2 := by apply Matrix.ext; unfold raw24282step3 raw24282step2; decide +kernel
      have hl : raw24282step2Labels = labelEmbedding6 ∘ raw24282step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24282step2 raw24282step2Labels raw24282step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4619 node4619Labels := by rfl

def raw24283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw24283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw24283step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24283step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw24283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24283step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24283step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24283step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24283step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24283 raw24283Labels = mixedMoment B node4185 node4185Labels := by
  calc
    mixedMoment B raw24283 raw24283Labels = mixedMoment B raw24283step0 raw24283step0Labels := by
      have hz : ∀ j, raw24283 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24283step0 = (fun i j => raw24283 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24283step0 raw24283; decide +kernel
      have hl : raw24283step0Labels = raw24283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24283 raw24283Labels permutation346 hz
    mixedMoment B raw24283step0 raw24283step0Labels = mixedMoment B raw24283step1 raw24283step1Labels := by
      have hz : ∀ j, raw24283step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24283step1 = (fun i j => raw24283step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24283step1 raw24283step0; decide +kernel
      have hl : raw24283step1Labels = raw24283step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24283step0 raw24283step0Labels permutation56 hz
    mixedMoment B raw24283step1 raw24283step1Labels = mixedMoment B raw24283step2 raw24283step2Labels := by
      have ha : raw24283step2 = (fun i j => raw24283step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24283step2 raw24283step1; decide +kernel
      have hl : raw24283step2Labels = raw24283step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24283step1 raw24283step1Labels permutation8 permutation3
    mixedMoment B raw24283step2 raw24283step2Labels = mixedMoment B raw24283step3 raw24283step3Labels := by
      have ha : raw24283step3 = raw24283step2 := by apply Matrix.ext; unfold raw24283step3 raw24283step2; decide +kernel
      have hl : raw24283step2Labels = labelEmbedding6 ∘ raw24283step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24283step2 raw24283step2Labels raw24283step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4185 node4185Labels := by rfl

def raw24284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw24284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw24284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24284step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24284step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24284step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24284step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24284 raw24284Labels = mixedMoment B node4553 node4553Labels := by
  calc
    mixedMoment B raw24284 raw24284Labels = mixedMoment B raw24284step0 raw24284step0Labels := by
      have hz : ∀ j, raw24284 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24284step0 = (fun i j => raw24284 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24284step0 raw24284; decide +kernel
      have hl : raw24284step0Labels = raw24284Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24284 raw24284Labels permutation346 hz
    mixedMoment B raw24284step0 raw24284step0Labels = mixedMoment B raw24284step1 raw24284step1Labels := by
      have ha : raw24284step1 = (fun i j => raw24284step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24284step1 raw24284step0; decide +kernel
      have hl : raw24284step1Labels = raw24284step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24284step0 raw24284step0Labels permutation32 permutation3
    mixedMoment B raw24284step1 raw24284step1Labels = mixedMoment B raw24284step2 raw24284step2Labels := by
      have ha : raw24284step2 = raw24284step1 := by apply Matrix.ext; unfold raw24284step2 raw24284step1; decide +kernel
      have hl : raw24284step1Labels = labelEmbedding6 ∘ raw24284step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24284step1 raw24284step1Labels raw24284step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4553 node4553Labels := by rfl

def raw24285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw24285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw24285step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24285step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24285step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24285step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24285step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24285 raw24285Labels = mixedMoment B node4553 node4553Labels := by
  calc
    mixedMoment B raw24285 raw24285Labels = mixedMoment B raw24285step0 raw24285step0Labels := by
      have hz : ∀ j, raw24285 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24285step0 = (fun i j => raw24285 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24285step0 raw24285; decide +kernel
      have hl : raw24285step0Labels = raw24285Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24285 raw24285Labels permutation265 hz
    mixedMoment B raw24285step0 raw24285step0Labels = mixedMoment B raw24285step1 raw24285step1Labels := by
      have ha : raw24285step1 = (fun i j => raw24285step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24285step1 raw24285step0; decide +kernel
      have hl : raw24285step1Labels = raw24285step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24285step0 raw24285step0Labels permutation32 permutation3
    mixedMoment B raw24285step1 raw24285step1Labels = mixedMoment B raw24285step2 raw24285step2Labels := by
      have ha : raw24285step2 = raw24285step1 := by apply Matrix.ext; unfold raw24285step2 raw24285step1; decide +kernel
      have hl : raw24285step1Labels = labelEmbedding6 ∘ raw24285step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24285step1 raw24285step1Labels raw24285step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4553 node4553Labels := by rfl

def raw24286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw24286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw24286step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24286step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw24286step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24286step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24286step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24286 raw24286Labels = mixedMoment B node4623 node4623Labels := by
  calc
    mixedMoment B raw24286 raw24286Labels = mixedMoment B raw24286step0 raw24286step0Labels := by
      have hz : ∀ j, raw24286 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24286step0 = (fun i j => raw24286 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24286step0 raw24286; decide +kernel
      have hl : raw24286step0Labels = raw24286Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24286 raw24286Labels permutation346 hz
    mixedMoment B raw24286step0 raw24286step0Labels = mixedMoment B raw24286step1 raw24286step1Labels := by
      have hz : ∀ j, raw24286step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24286step1 = (fun i j => raw24286step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24286step1 raw24286step0; decide +kernel
      have hl : raw24286step1Labels = raw24286step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24286step0 raw24286step0Labels permutation56 hz
    mixedMoment B raw24286step1 raw24286step1Labels = mixedMoment B raw24286step2 raw24286step2Labels := by
      have ha : raw24286step2 = (fun i j => raw24286step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24286step2 raw24286step1; decide +kernel
      have hl : raw24286step2Labels = raw24286step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24286step1 raw24286step1Labels permutation9 permutation2
    _ = mixedMoment B node4623 node4623Labels := by rfl

def raw24287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24287Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24287step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24287step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24287 raw24287Labels = mixedMoment B node593 node593Labels := by
  calc
    mixedMoment B raw24287 raw24287Labels = mixedMoment B raw24287step0 raw24287step0Labels := by
      have hz : ∀ j, raw24287 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24287step0 = (fun i j => raw24287 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24287step0 raw24287; decide +kernel
      have hl : raw24287step0Labels = raw24287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24287 raw24287Labels permutation346 hz
    mixedMoment B raw24287step0 raw24287step0Labels = mixedMoment B raw24287step1 raw24287step1Labels := by
      have ha : raw24287step1 = (fun i j => raw24287step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24287step1 raw24287step0; decide +kernel
      have hl : raw24287step1Labels = raw24287step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24287step0 raw24287step0Labels permutation44 permutation3
    _ = mixedMoment B node593 node593Labels := by rfl

def raw24288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24288Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24288step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24288step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24288 raw24288Labels = mixedMoment B node1122 node1122Labels := by
  calc
    mixedMoment B raw24288 raw24288Labels = mixedMoment B raw24288step0 raw24288step0Labels := by
      have ha : raw24288step0 = (fun i j => raw24288 (permutation188 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24288step0 raw24288; decide +kernel
      have hl : raw24288step0Labels = raw24288Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24288 raw24288Labels permutation188 permutation3
    _ = mixedMoment B node1122 node1122Labels := by rfl

def raw24289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw24289Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw24289step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24289step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24289step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24289 raw24289Labels = mixedMoment B node1188 node1188Labels := by
  calc
    mixedMoment B raw24289 raw24289Labels = mixedMoment B raw24289step0 raw24289step0Labels := by
      have hz : ∀ j, raw24289 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24289step0 = (fun i j => raw24289 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24289step0 raw24289; decide +kernel
      have hl : raw24289step0Labels = raw24289Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24289 raw24289Labels permutation346 hz
    mixedMoment B raw24289step0 raw24289step0Labels = mixedMoment B raw24289step1 raw24289step1Labels := by
      have ha : raw24289step1 = (fun i j => raw24289step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24289step1 raw24289step0; decide +kernel
      have hl : raw24289step1Labels = raw24289step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24289step0 raw24289step0Labels permutation44 permutation3
    _ = mixedMoment B node1188 node1188Labels := by rfl

def raw24290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw24290Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw24290step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24290step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24290step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24290 raw24290Labels = mixedMoment B node1293 node1293Labels := by
  calc
    mixedMoment B raw24290 raw24290Labels = mixedMoment B raw24290step0 raw24290step0Labels := by
      have hz : ∀ j, raw24290 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24290step0 = (fun i j => raw24290 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24290step0 raw24290; decide +kernel
      have hl : raw24290step0Labels = raw24290Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24290 raw24290Labels permutation346 hz
    mixedMoment B raw24290step0 raw24290step0Labels = mixedMoment B raw24290step1 raw24290step1Labels := by
      have ha : raw24290step1 = (fun i j => raw24290step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24290step1 raw24290step0; decide +kernel
      have hl : raw24290step1Labels = raw24290step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24290step0 raw24290step0Labels permutation44 permutation3
    _ = mixedMoment B node1293 node1293Labels := by rfl

def raw24291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24291Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24291step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24291step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24291 raw24291Labels = mixedMoment B node593 node593Labels := by
  calc
    mixedMoment B raw24291 raw24291Labels = mixedMoment B raw24291step0 raw24291step0Labels := by
      have hz : ∀ j, raw24291 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24291step0 = (fun i j => raw24291 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24291step0 raw24291; decide +kernel
      have hl : raw24291step0Labels = raw24291Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24291 raw24291Labels permutation265 hz
    mixedMoment B raw24291step0 raw24291step0Labels = mixedMoment B raw24291step1 raw24291step1Labels := by
      have ha : raw24291step1 = (fun i j => raw24291step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24291step1 raw24291step0; decide +kernel
      have hl : raw24291step1Labels = raw24291step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24291step0 raw24291step0Labels permutation44 permutation3
    _ = mixedMoment B node593 node593Labels := by rfl

def raw24292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24292Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24292step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24292step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24292 raw24292Labels = mixedMoment B node1122 node1122Labels := by
  calc
    mixedMoment B raw24292 raw24292Labels = mixedMoment B raw24292step0 raw24292step0Labels := by
      have ha : raw24292step0 = (fun i j => raw24292 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24292step0 raw24292; decide +kernel
      have hl : raw24292step0Labels = raw24292Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24292 raw24292Labels permutation164 permutation3
    _ = mixedMoment B node1122 node1122Labels := by rfl

def raw24293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw24293Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw24293step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24293step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24293 raw24293Labels = mixedMoment B node1188 node1188Labels := by
  calc
    mixedMoment B raw24293 raw24293Labels = mixedMoment B raw24293step0 raw24293step0Labels := by
      have hz : ∀ j, raw24293 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24293step0 = (fun i j => raw24293 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24293step0 raw24293; decide +kernel
      have hl : raw24293step0Labels = raw24293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24293 raw24293Labels permutation265 hz
    mixedMoment B raw24293step0 raw24293step0Labels = mixedMoment B raw24293step1 raw24293step1Labels := by
      have ha : raw24293step1 = (fun i j => raw24293step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24293step1 raw24293step0; decide +kernel
      have hl : raw24293step1Labels = raw24293step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24293step0 raw24293step0Labels permutation44 permutation3
    _ = mixedMoment B node1188 node1188Labels := by rfl

def raw24294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw24294Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw24294step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24294step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24294 raw24294Labels = mixedMoment B node1293 node1293Labels := by
  calc
    mixedMoment B raw24294 raw24294Labels = mixedMoment B raw24294step0 raw24294step0Labels := by
      have hz : ∀ j, raw24294 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24294step0 = (fun i j => raw24294 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24294step0 raw24294; decide +kernel
      have hl : raw24294step0Labels = raw24294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24294 raw24294Labels permutation265 hz
    mixedMoment B raw24294step0 raw24294step0Labels = mixedMoment B raw24294step1 raw24294step1Labels := by
      have ha : raw24294step1 = (fun i j => raw24294step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24294step1 raw24294step0; decide +kernel
      have hl : raw24294step1Labels = raw24294step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24294step0 raw24294step0Labels permutation44 permutation3
    _ = mixedMoment B node1293 node1293Labels := by rfl

def raw24295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24295Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24295step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24295step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24295step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24295step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw24295step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24295 raw24295Labels = mixedMoment B node595 node595Labels := by
  calc
    mixedMoment B raw24295 raw24295Labels = mixedMoment B raw24295step0 raw24295step0Labels := by
      have hz : ∀ j, raw24295 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24295step0 = (fun i j => raw24295 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24295step0 raw24295; decide +kernel
      have hl : raw24295step0Labels = raw24295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24295 raw24295Labels permutation346 hz
    mixedMoment B raw24295step0 raw24295step0Labels = mixedMoment B raw24295step1 raw24295step1Labels := by
      have hz : ∀ j, raw24295step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24295step1 = (fun i j => raw24295step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24295step1 raw24295step0; decide +kernel
      have hl : raw24295step1Labels = raw24295step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24295step0 raw24295step0Labels permutation56 hz
    mixedMoment B raw24295step1 raw24295step1Labels = mixedMoment B raw24295step2 raw24295step2Labels := by
      have ha : raw24295step2 = (fun i j => raw24295step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24295step2 raw24295step1; decide +kernel
      have hl : raw24295step2Labels = raw24295step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24295step1 raw24295step1Labels permutation10 permutation3
    _ = mixedMoment B node595 node595Labels := by rfl

def raw24296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24296Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24296step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24296step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw24296step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24296 raw24296Labels = mixedMoment B node1124 node1124Labels := by
  calc
    mixedMoment B raw24296 raw24296Labels = mixedMoment B raw24296step0 raw24296step0Labels := by
      have hz : ∀ j, raw24296 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24296step0 = (fun i j => raw24296 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24296step0 raw24296; decide +kernel
      have hl : raw24296step0Labels = raw24296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24296 raw24296Labels permutation346 hz
    mixedMoment B raw24296step0 raw24296step0Labels = mixedMoment B raw24296step1 raw24296step1Labels := by
      have ha : raw24296step1 = (fun i j => raw24296step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24296step1 raw24296step0; decide +kernel
      have hl : raw24296step1Labels = raw24296step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24296step0 raw24296step0Labels permutation34 permutation3
    _ = mixedMoment B node1124 node1124Labels := by rfl

def raw24297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24297Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24297step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24297step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw24297step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24297 raw24297Labels = mixedMoment B node1124 node1124Labels := by
  calc
    mixedMoment B raw24297 raw24297Labels = mixedMoment B raw24297step0 raw24297step0Labels := by
      have hz : ∀ j, raw24297 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24297step0 = (fun i j => raw24297 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24297step0 raw24297; decide +kernel
      have hl : raw24297step0Labels = raw24297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24297 raw24297Labels permutation265 hz
    mixedMoment B raw24297step0 raw24297step0Labels = mixedMoment B raw24297step1 raw24297step1Labels := by
      have ha : raw24297step1 = (fun i j => raw24297step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24297step1 raw24297step0; decide +kernel
      have hl : raw24297step1Labels = raw24297step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24297step0 raw24297step0Labels permutation34 permutation3
    _ = mixedMoment B node1124 node1124Labels := by rfl

def raw24298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 2, -2], ![2, -2, 0]]
def raw24298Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![0, 2, -2], ![2, -2, 0]]
def raw24298step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24298step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![0, 2, -2], ![2, -2, 0]]
def raw24298step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24298step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw24298step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24298 raw24298Labels = mixedMoment B node1193 node1193Labels := by
  calc
    mixedMoment B raw24298 raw24298Labels = mixedMoment B raw24298step0 raw24298step0Labels := by
      have hz : ∀ j, raw24298 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24298step0 = (fun i j => raw24298 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24298step0 raw24298; decide +kernel
      have hl : raw24298step0Labels = raw24298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24298 raw24298Labels permutation346 hz
    mixedMoment B raw24298step0 raw24298step0Labels = mixedMoment B raw24298step1 raw24298step1Labels := by
      have hz : ∀ j, raw24298step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24298step1 = (fun i j => raw24298step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24298step1 raw24298step0; decide +kernel
      have hl : raw24298step1Labels = raw24298step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24298step0 raw24298step0Labels permutation56 hz
    mixedMoment B raw24298step1 raw24298step1Labels = mixedMoment B raw24298step2 raw24298step2Labels := by
      have ha : raw24298step2 = (fun i j => raw24298step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24298step2 raw24298step1; decide +kernel
      have hl : raw24298step2Labels = raw24298step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24298step1 raw24298step1Labels permutation10 permutation3
    _ = mixedMoment B node1193 node1193Labels := by rfl

def raw24299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![1, -1, 0]]
def raw24299Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![1, -1, 0]]
def raw24299step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24299step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![1, 1, -2], ![1, -1, 0]]
def raw24299step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24299step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24299step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24299 raw24299Labels = mixedMoment B node1294 node1294Labels := by
  calc
    mixedMoment B raw24299 raw24299Labels = mixedMoment B raw24299step0 raw24299step0Labels := by
      have hz : ∀ j, raw24299 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24299step0 = (fun i j => raw24299 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24299step0 raw24299; decide +kernel
      have hl : raw24299step0Labels = raw24299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24299 raw24299Labels permutation346 hz
    mixedMoment B raw24299step0 raw24299step0Labels = mixedMoment B raw24299step1 raw24299step1Labels := by
      have hz : ∀ j, raw24299step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24299step1 = (fun i j => raw24299step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24299step1 raw24299step0; decide +kernel
      have hl : raw24299step1Labels = raw24299step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24299step0 raw24299step0Labels permutation56 hz
    mixedMoment B raw24299step1 raw24299step1Labels = mixedMoment B raw24299step2 raw24299step2Labels := by
      have ha : raw24299step2 = (fun i j => raw24299step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24299step2 raw24299step1; decide +kernel
      have hl : raw24299step2Labels = raw24299step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24299step1 raw24299step1Labels permutation11 permutation3
    _ = mixedMoment B node1294 node1294Labels := by rfl

def raw24300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw24300Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw24300step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24300step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw24300step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24300step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24300step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24300 raw24300Labels = mixedMoment B node613 node613Labels := by
  calc
    mixedMoment B raw24300 raw24300Labels = mixedMoment B raw24300step0 raw24300step0Labels := by
      have hz : ∀ j, raw24300 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24300step0 = (fun i j => raw24300 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24300step0 raw24300; decide +kernel
      have hl : raw24300step0Labels = raw24300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24300 raw24300Labels permutation346 hz
    mixedMoment B raw24300step0 raw24300step0Labels = mixedMoment B raw24300step1 raw24300step1Labels := by
      have hz : ∀ j, raw24300step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24300step1 = (fun i j => raw24300step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24300step1 raw24300step0; decide +kernel
      have hl : raw24300step1Labels = raw24300step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24300step0 raw24300step0Labels permutation56 hz
    mixedMoment B raw24300step1 raw24300step1Labels = mixedMoment B raw24300step2 raw24300step2Labels := by
      have ha : raw24300step2 = (fun i j => raw24300step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24300step2 raw24300step1; decide +kernel
      have hl : raw24300step2Labels = raw24300step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24300step1 raw24300step1Labels permutation8 permutation3
    _ = mixedMoment B node613 node613Labels := by rfl

def raw24301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw24301Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw24301step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24301step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24301 raw24301Labels = mixedMoment B node1138 node1138Labels := by
  calc
    mixedMoment B raw24301 raw24301Labels = mixedMoment B raw24301step0 raw24301step0Labels := by
      have hz : ∀ j, raw24301 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24301step0 = (fun i j => raw24301 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24301step0 raw24301; decide +kernel
      have hl : raw24301step0Labels = raw24301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24301 raw24301Labels permutation346 hz
    mixedMoment B raw24301step0 raw24301step0Labels = mixedMoment B raw24301step1 raw24301step1Labels := by
      have ha : raw24301step1 = (fun i j => raw24301step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24301step1 raw24301step0; decide +kernel
      have hl : raw24301step1Labels = raw24301step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24301step0 raw24301step0Labels permutation32 permutation3
    _ = mixedMoment B node1138 node1138Labels := by rfl

def raw24302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw24302Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw24302step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24302step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24302 raw24302Labels = mixedMoment B node1138 node1138Labels := by
  calc
    mixedMoment B raw24302 raw24302Labels = mixedMoment B raw24302step0 raw24302step0Labels := by
      have hz : ∀ j, raw24302 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24302step0 = (fun i j => raw24302 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24302step0 raw24302; decide +kernel
      have hl : raw24302step0Labels = raw24302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24302 raw24302Labels permutation265 hz
    mixedMoment B raw24302step0 raw24302step0Labels = mixedMoment B raw24302step1 raw24302step1Labels := by
      have ha : raw24302step1 = (fun i j => raw24302step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24302step1 raw24302step0; decide +kernel
      have hl : raw24302step1Labels = raw24302step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24302step0 raw24302step0Labels permutation32 permutation3
    _ = mixedMoment B node1138 node1138Labels := by rfl

def raw24303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw24303Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw24303step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24303step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw24303step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24303step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24303step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24303 raw24303Labels = mixedMoment B node1305 node1305Labels := by
  calc
    mixedMoment B raw24303 raw24303Labels = mixedMoment B raw24303step0 raw24303step0Labels := by
      have hz : ∀ j, raw24303 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24303step0 = (fun i j => raw24303 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24303step0 raw24303; decide +kernel
      have hl : raw24303step0Labels = raw24303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24303 raw24303Labels permutation346 hz
    mixedMoment B raw24303step0 raw24303step0Labels = mixedMoment B raw24303step1 raw24303step1Labels := by
      have hz : ∀ j, raw24303step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24303step1 = (fun i j => raw24303step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24303step1 raw24303step0; decide +kernel
      have hl : raw24303step1Labels = raw24303step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24303step0 raw24303step0Labels permutation56 hz
    mixedMoment B raw24303step1 raw24303step1Labels = mixedMoment B raw24303step2 raw24303step2Labels := by
      have ha : raw24303step2 = (fun i j => raw24303step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24303step2 raw24303step1; decide +kernel
      have hl : raw24303step2Labels = raw24303step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24303step1 raw24303step1Labels permutation9 permutation3
    _ = mixedMoment B node1305 node1305Labels := by rfl

def raw24304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24304Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24304step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24304step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24304step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24304 raw24304Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw24304 raw24304Labels = mixedMoment B raw24304step0 raw24304step0Labels := by
      have hz : ∀ j, raw24304 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24304step0 = (fun i j => raw24304 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24304step0 raw24304; decide +kernel
      have hl : raw24304step0Labels = raw24304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24304 raw24304Labels permutation346 hz
    mixedMoment B raw24304step0 raw24304step0Labels = mixedMoment B raw24304step1 raw24304step1Labels := by
      have ha : raw24304step1 = (fun i j => raw24304step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24304step1 raw24304step0; decide +kernel
      have hl : raw24304step1Labels = raw24304step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24304step0 raw24304step0Labels permutation34 permutation2
    _ = mixedMoment B node5163 node5163Labels := by rfl

def raw24305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24305Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24305step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24305step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24305step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24305 raw24305Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw24305 raw24305Labels = mixedMoment B raw24305step0 raw24305step0Labels := by
      have hz : ∀ j, raw24305 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24305step0 = (fun i j => raw24305 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24305step0 raw24305; decide +kernel
      have hl : raw24305step0Labels = raw24305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24305 raw24305Labels permutation265 hz
    mixedMoment B raw24305step0 raw24305step0Labels = mixedMoment B raw24305step1 raw24305step1Labels := by
      have ha : raw24305step1 = (fun i j => raw24305step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24305step1 raw24305step0; decide +kernel
      have hl : raw24305step1Labels = raw24305step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24305step0 raw24305step0Labels permutation34 permutation2
    _ = mixedMoment B node5163 node5163Labels := by rfl

def raw24306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24306Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24306step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24306step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24306step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24306 raw24306Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw24306 raw24306Labels = mixedMoment B raw24306step0 raw24306step0Labels := by
      have hz : ∀ j, raw24306 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24306step0 = (fun i j => raw24306 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24306step0 raw24306; decide +kernel
      have hl : raw24306step0Labels = raw24306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24306 raw24306Labels permutation346 hz
    mixedMoment B raw24306step0 raw24306step0Labels = mixedMoment B raw24306step1 raw24306step1Labels := by
      have hz : ∀ j, raw24306step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24306step1 = (fun i j => raw24306step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24306step1 raw24306step0; decide +kernel
      have hl : raw24306step1Labels = raw24306step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24306step0 raw24306step0Labels permutation56 hz
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw24307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24307Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24307step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24307step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24307step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24307step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24307step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24307 raw24307Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw24307 raw24307Labels = mixedMoment B raw24307step0 raw24307step0Labels := by
      have hz : ∀ j, raw24307 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24307step0 = (fun i j => raw24307 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24307step0 raw24307; decide +kernel
      have hl : raw24307step0Labels = raw24307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24307 raw24307Labels permutation346 hz
    mixedMoment B raw24307step0 raw24307step0Labels = mixedMoment B raw24307step1 raw24307step1Labels := by
      have hz : ∀ j, raw24307step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24307step1 = (fun i j => raw24307step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24307step1 raw24307step0; decide +kernel
      have hl : raw24307step1Labels = raw24307step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24307step0 raw24307step0Labels permutation56 hz
    mixedMoment B raw24307step1 raw24307step1Labels = mixedMoment B raw24307step2 raw24307step2Labels := by
      have ha : raw24307step2 = (fun i j => raw24307step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24307step2 raw24307step1; decide +kernel
      have hl : raw24307step2Labels = raw24307step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24307step1 raw24307step1Labels permutation10 permutation2
    _ = mixedMoment B node5274 node5274Labels := by rfl

def raw24308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24308Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24308step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24308step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24308step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24308step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw24308step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24308 raw24308Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw24308 raw24308Labels = mixedMoment B raw24308step0 raw24308step0Labels := by
      have hz : ∀ j, raw24308 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24308step0 = (fun i j => raw24308 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24308step0 raw24308; decide +kernel
      have hl : raw24308step0Labels = raw24308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24308 raw24308Labels permutation346 hz
    mixedMoment B raw24308step0 raw24308step0Labels = mixedMoment B raw24308step1 raw24308step1Labels := by
      have hz : ∀ j, raw24308step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24308step1 = (fun i j => raw24308step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24308step1 raw24308step0; decide +kernel
      have hl : raw24308step1Labels = raw24308step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24308step0 raw24308step0Labels permutation56 hz
    mixedMoment B raw24308step1 raw24308step1Labels = mixedMoment B raw24308step2 raw24308step2Labels := by
      have ha : raw24308step2 = (fun i j => raw24308step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24308step2 raw24308step1; decide +kernel
      have hl : raw24308step2Labels = raw24308step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24308step1 raw24308step1Labels permutation10 permutation2
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw24309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24309Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24309step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24309step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24309step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24309step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24309 raw24309Labels = mixedMoment B node4176 node4176Labels := by
  calc
    mixedMoment B raw24309 raw24309Labels = mixedMoment B raw24309step0 raw24309step0Labels := by
      have hz : ∀ j, raw24309 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24309step0 = (fun i j => raw24309 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24309step0 raw24309; decide +kernel
      have hl : raw24309step0Labels = raw24309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24309 raw24309Labels permutation346 hz
    mixedMoment B raw24309step0 raw24309step0Labels = mixedMoment B raw24309step1 raw24309step1Labels := by
      have ha : raw24309step1 = (fun i j => raw24309step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24309step1 raw24309step0; decide +kernel
      have hl : raw24309step1Labels = raw24309step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24309step0 raw24309step0Labels permutation38 permutation3
    mixedMoment B raw24309step1 raw24309step1Labels = mixedMoment B raw24309step2 raw24309step2Labels := by
      have ha : raw24309step2 = raw24309step1 := by apply Matrix.ext; unfold raw24309step2 raw24309step1; decide +kernel
      have hl : raw24309step1Labels = labelEmbedding6 ∘ raw24309step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24309step1 raw24309step1Labels raw24309step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4176 node4176Labels := by rfl

def raw24310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24310Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24310step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24310step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24310step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24310step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24310 raw24310Labels = mixedMoment B node4545 node4545Labels := by
  calc
    mixedMoment B raw24310 raw24310Labels = mixedMoment B raw24310step0 raw24310step0Labels := by
      have ha : raw24310step0 = (fun i j => raw24310 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24310step0 raw24310; decide +kernel
      have hl : raw24310step0Labels = raw24310Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24310 raw24310Labels permutation182 permutation3
    mixedMoment B raw24310step0 raw24310step0Labels = mixedMoment B raw24310step1 raw24310step1Labels := by
      have ha : raw24310step1 = raw24310step0 := by apply Matrix.ext; unfold raw24310step1 raw24310step0; decide +kernel
      have hl : raw24310step0Labels = labelEmbedding6 ∘ raw24310step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24310step0 raw24310step0Labels raw24310step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4545 node4545Labels := by rfl

def raw24311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24311Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24311step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24311step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24311step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24311step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24311 raw24311Labels = mixedMoment B node4607 node4607Labels := by
  calc
    mixedMoment B raw24311 raw24311Labels = mixedMoment B raw24311step0 raw24311step0Labels := by
      have hz : ∀ j, raw24311 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24311step0 = (fun i j => raw24311 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24311step0 raw24311; decide +kernel
      have hl : raw24311step0Labels = raw24311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24311 raw24311Labels permutation346 hz
    mixedMoment B raw24311step0 raw24311step0Labels = mixedMoment B raw24311step1 raw24311step1Labels := by
      have ha : raw24311step1 = (fun i j => raw24311step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24311step1 raw24311step0; decide +kernel
      have hl : raw24311step1Labels = raw24311step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24311step0 raw24311step0Labels permutation38 permutation3
    mixedMoment B raw24311step1 raw24311step1Labels = mixedMoment B raw24311step2 raw24311step2Labels := by
      have ha : raw24311step2 = raw24311step1 := by apply Matrix.ext; unfold raw24311step2 raw24311step1; decide +kernel
      have hl : raw24311step1Labels = labelEmbedding6 ∘ raw24311step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24311step1 raw24311step1Labels raw24311step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4607 node4607Labels := by rfl

def raw24312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24312Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24312step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24312step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24312step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24312 raw24312Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw24312 raw24312Labels = mixedMoment B raw24312step0 raw24312step0Labels := by
      have hz : ∀ j, raw24312 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24312step0 = (fun i j => raw24312 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24312step0 raw24312; decide +kernel
      have hl : raw24312step0Labels = raw24312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24312 raw24312Labels permutation346 hz
    mixedMoment B raw24312step0 raw24312step0Labels = mixedMoment B raw24312step1 raw24312step1Labels := by
      have ha : raw24312step1 = (fun i j => raw24312step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24312step1 raw24312step0; decide +kernel
      have hl : raw24312step1Labels = raw24312step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24312step0 raw24312step0Labels permutation44 permutation2
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw24313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24313Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24313step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24313step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24313 raw24313Labels = mixedMoment B node4616 node4616Labels := by
  calc
    mixedMoment B raw24313 raw24313Labels = mixedMoment B raw24313step0 raw24313step0Labels := by
      have hz : ∀ j, raw24313 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24313step0 = (fun i j => raw24313 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24313step0 raw24313; decide +kernel
      have hl : raw24313step0Labels = raw24313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24313 raw24313Labels permutation346 hz
    mixedMoment B raw24313step0 raw24313step0Labels = mixedMoment B raw24313step1 raw24313step1Labels := by
      have ha : raw24313step1 = (fun i j => raw24313step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24313step1 raw24313step0; decide +kernel
      have hl : raw24313step1Labels = raw24313step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24313step0 raw24313step0Labels permutation44 permutation2
    _ = mixedMoment B node4616 node4616Labels := by rfl

def raw24314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24314Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24314step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24314step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24314step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24314step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24314 raw24314Labels = mixedMoment B node4176 node4176Labels := by
  calc
    mixedMoment B raw24314 raw24314Labels = mixedMoment B raw24314step0 raw24314step0Labels := by
      have hz : ∀ j, raw24314 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24314step0 = (fun i j => raw24314 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24314step0 raw24314; decide +kernel
      have hl : raw24314step0Labels = raw24314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24314 raw24314Labels permutation265 hz
    mixedMoment B raw24314step0 raw24314step0Labels = mixedMoment B raw24314step1 raw24314step1Labels := by
      have ha : raw24314step1 = (fun i j => raw24314step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24314step1 raw24314step0; decide +kernel
      have hl : raw24314step1Labels = raw24314step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24314step0 raw24314step0Labels permutation38 permutation3
    mixedMoment B raw24314step1 raw24314step1Labels = mixedMoment B raw24314step2 raw24314step2Labels := by
      have ha : raw24314step2 = raw24314step1 := by apply Matrix.ext; unfold raw24314step2 raw24314step1; decide +kernel
      have hl : raw24314step1Labels = labelEmbedding6 ∘ raw24314step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24314step1 raw24314step1Labels raw24314step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4176 node4176Labels := by rfl

def raw24315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24315Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24315step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24315step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24315step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24315step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24315 raw24315Labels = mixedMoment B node4545 node4545Labels := by
  calc
    mixedMoment B raw24315 raw24315Labels = mixedMoment B raw24315step0 raw24315step0Labels := by
      have ha : raw24315step0 = (fun i j => raw24315 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24315step0 raw24315; decide +kernel
      have hl : raw24315step0Labels = raw24315Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24315 raw24315Labels permutation158 permutation3
    mixedMoment B raw24315step0 raw24315step0Labels = mixedMoment B raw24315step1 raw24315step1Labels := by
      have ha : raw24315step1 = raw24315step0 := by apply Matrix.ext; unfold raw24315step1 raw24315step0; decide +kernel
      have hl : raw24315step0Labels = labelEmbedding6 ∘ raw24315step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24315step0 raw24315step0Labels raw24315step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4545 node4545Labels := by rfl

def raw24316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24316Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24316step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24316step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24316step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24316step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24316step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24316 raw24316Labels = mixedMoment B node4607 node4607Labels := by
  calc
    mixedMoment B raw24316 raw24316Labels = mixedMoment B raw24316step0 raw24316step0Labels := by
      have hz : ∀ j, raw24316 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24316step0 = (fun i j => raw24316 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24316step0 raw24316; decide +kernel
      have hl : raw24316step0Labels = raw24316Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24316 raw24316Labels permutation265 hz
    mixedMoment B raw24316step0 raw24316step0Labels = mixedMoment B raw24316step1 raw24316step1Labels := by
      have ha : raw24316step1 = (fun i j => raw24316step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24316step1 raw24316step0; decide +kernel
      have hl : raw24316step1Labels = raw24316step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24316step0 raw24316step0Labels permutation38 permutation3
    mixedMoment B raw24316step1 raw24316step1Labels = mixedMoment B raw24316step2 raw24316step2Labels := by
      have ha : raw24316step2 = raw24316step1 := by apply Matrix.ext; unfold raw24316step2 raw24316step1; decide +kernel
      have hl : raw24316step1Labels = labelEmbedding6 ∘ raw24316step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24316step1 raw24316step1Labels raw24316step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4607 node4607Labels := by rfl

def raw24317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24317Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24317step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24317step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24317 raw24317Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw24317 raw24317Labels = mixedMoment B raw24317step0 raw24317step0Labels := by
      have hz : ∀ j, raw24317 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24317step0 = (fun i j => raw24317 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24317step0 raw24317; decide +kernel
      have hl : raw24317step0Labels = raw24317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24317 raw24317Labels permutation265 hz
    mixedMoment B raw24317step0 raw24317step0Labels = mixedMoment B raw24317step1 raw24317step1Labels := by
      have ha : raw24317step1 = (fun i j => raw24317step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24317step1 raw24317step0; decide +kernel
      have hl : raw24317step1Labels = raw24317step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24317step0 raw24317step0Labels permutation44 permutation2
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw24318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24318Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24318step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24318step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24318 raw24318Labels = mixedMoment B node4616 node4616Labels := by
  calc
    mixedMoment B raw24318 raw24318Labels = mixedMoment B raw24318step0 raw24318step0Labels := by
      have hz : ∀ j, raw24318 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24318step0 = (fun i j => raw24318 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24318step0 raw24318; decide +kernel
      have hl : raw24318step0Labels = raw24318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24318 raw24318Labels permutation265 hz
    mixedMoment B raw24318step0 raw24318step0Labels = mixedMoment B raw24318step1 raw24318step1Labels := by
      have ha : raw24318step1 = (fun i j => raw24318step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24318step1 raw24318step0; decide +kernel
      have hl : raw24318step1Labels = raw24318step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24318step0 raw24318step0Labels permutation44 permutation2
    _ = mixedMoment B node4616 node4616Labels := by rfl

def raw24319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24319Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24319step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24319step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24319step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24319step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw24319step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24319step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw24319step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24319 raw24319Labels = mixedMoment B node4188 node4188Labels := by
  calc
    mixedMoment B raw24319 raw24319Labels = mixedMoment B raw24319step0 raw24319step0Labels := by
      have hz : ∀ j, raw24319 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24319step0 = (fun i j => raw24319 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24319step0 raw24319; decide +kernel
      have hl : raw24319step0Labels = raw24319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24319 raw24319Labels permutation346 hz
    mixedMoment B raw24319step0 raw24319step0Labels = mixedMoment B raw24319step1 raw24319step1Labels := by
      have hz : ∀ j, raw24319step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24319step1 = (fun i j => raw24319step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24319step1 raw24319step0; decide +kernel
      have hl : raw24319step1Labels = raw24319step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24319step0 raw24319step0Labels permutation56 hz
    mixedMoment B raw24319step1 raw24319step1Labels = mixedMoment B raw24319step2 raw24319step2Labels := by
      have ha : raw24319step2 = (fun i j => raw24319step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24319step2 raw24319step1; decide +kernel
      have hl : raw24319step2Labels = raw24319step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24319step1 raw24319step1Labels permutation11 permutation3
    mixedMoment B raw24319step2 raw24319step2Labels = mixedMoment B raw24319step3 raw24319step3Labels := by
      have ha : raw24319step3 = raw24319step2 := by apply Matrix.ext; unfold raw24319step3 raw24319step2; decide +kernel
      have hl : raw24319step2Labels = labelEmbedding6 ∘ raw24319step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24319step2 raw24319step2Labels raw24319step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4188 node4188Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
