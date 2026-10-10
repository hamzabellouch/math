import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw36736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![1, 0, -1]]
def raw36736Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![2, -3, 1], ![1, 0, -1], ![1, 0, -1]]
def raw36736step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36736step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36736step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36736step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36736step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36736 raw36736Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw36736 raw36736Labels = mixedMoment B raw36736step0 raw36736step0Labels := by
      have hz : ∀ j, raw36736 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36736step0 = (fun i j => raw36736 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36736step0 raw36736; decide +kernel
      have hl : raw36736step0Labels = raw36736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36736 raw36736Labels permutation346 hz
    mixedMoment B raw36736step0 raw36736step0Labels = mixedMoment B raw36736step1 raw36736step1Labels := by
      have ha : raw36736step1 = (fun i j => raw36736step0 (permutation96 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36736step1 raw36736step0; decide +kernel
      have hl : raw36736step1Labels = raw36736step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36736step0 raw36736step0Labels permutation96 permutation5
    mixedMoment B raw36736step1 raw36736step1Labels = mixedMoment B raw36736step2 raw36736step2Labels := by
      have ha : raw36736step2 = raw36736step1 := by apply Matrix.ext; unfold raw36736step2 raw36736step1; decide +kernel
      have hl : raw36736step1Labels = labelEmbedding8 ∘ raw36736step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36736step1 raw36736step1Labels raw36736step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5248 node5248Labels := by rfl

def raw36737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw36737Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw36737step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw36737step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36737step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw36737step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36737 raw36737Labels = mixedMoment B node4654 node4654Labels := by
  calc
    mixedMoment B raw36737 raw36737Labels = mixedMoment B raw36737step0 raw36737step0Labels := by
      have hz : ∀ j, raw36737 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36737step0 = (fun i j => raw36737 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36737step0 raw36737; decide +kernel
      have hl : raw36737step0Labels = raw36737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36737 raw36737Labels permutation346 hz
    mixedMoment B raw36737step0 raw36737step0Labels = mixedMoment B raw36737step1 raw36737step1Labels := by
      have ha : raw36737step1 = (fun i j => raw36737step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36737step1 raw36737step0; decide +kernel
      have hl : raw36737step1Labels = raw36737step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36737step0 raw36737step0Labels permutation56 permutation3
    mixedMoment B raw36737step1 raw36737step1Labels = mixedMoment B raw36737step2 raw36737step2Labels := by
      have ha : raw36737step2 = raw36737step1 := by apply Matrix.ext; unfold raw36737step2 raw36737step1; decide +kernel
      have hl : raw36737step1Labels = labelEmbedding6 ∘ raw36737step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36737step1 raw36737step1Labels raw36737step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4654 node4654Labels := by rfl

def raw36738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw36738Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36738step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw36738step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36738step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw36738step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36738 raw36738Labels = mixedMoment B node5334 node5334Labels := by
  calc
    mixedMoment B raw36738 raw36738Labels = mixedMoment B raw36738step0 raw36738step0Labels := by
      have ha : raw36738step0 = (fun i j => raw36738 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36738step0 raw36738; decide +kernel
      have hl : raw36738step0Labels = raw36738Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36738 raw36738Labels permutation265 permutation3
    mixedMoment B raw36738step0 raw36738step0Labels = mixedMoment B raw36738step1 raw36738step1Labels := by
      have ha : raw36738step1 = raw36738step0 := by apply Matrix.ext; unfold raw36738step1 raw36738step0; decide +kernel
      have hl : raw36738step0Labels = labelEmbedding6 ∘ raw36738step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36738step0 raw36738step0Labels raw36738step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5334 node5334Labels := by rfl

def raw36739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw36739Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw36739step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36739step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36739step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36739 raw36739Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw36739 raw36739Labels = mixedMoment B raw36739step0 raw36739step0Labels := by
      have hz : ∀ j, raw36739 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36739step0 = (fun i j => raw36739 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36739step0 raw36739; decide +kernel
      have hl : raw36739step0Labels = raw36739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36739 raw36739Labels permutation346 hz
    mixedMoment B raw36739step0 raw36739step0Labels = mixedMoment B raw36739step1 raw36739step1Labels := by
      have ha : raw36739step1 = (fun i j => raw36739step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36739step1 raw36739step0; decide +kernel
      have hl : raw36739step1Labels = raw36739step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36739step0 raw36739step0Labels permutation56 permutation3
    mixedMoment B raw36739step1 raw36739step1Labels = mixedMoment B raw36739step2 raw36739step2Labels := by
      have ha : raw36739step2 = raw36739step1 := by apply Matrix.ext; unfold raw36739step2 raw36739step1; decide +kernel
      have hl : raw36739step1Labels = labelEmbedding6 ∘ raw36739step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36739step1 raw36739step1Labels raw36739step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw36740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw36740Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw36740step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36740step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36740step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36740 raw36740Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw36740 raw36740Labels = mixedMoment B raw36740step0 raw36740step0Labels := by
      have hz : ∀ j, raw36740 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36740step0 = (fun i j => raw36740 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36740step0 raw36740; decide +kernel
      have hl : raw36740step0Labels = raw36740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36740 raw36740Labels permutation346 hz
    mixedMoment B raw36740step0 raw36740step0Labels = mixedMoment B raw36740step1 raw36740step1Labels := by
      have ha : raw36740step1 = (fun i j => raw36740step0 (permutation60 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36740step1 raw36740step0; decide +kernel
      have hl : raw36740step1Labels = raw36740step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36740step0 raw36740step0Labels permutation60 permutation3
    mixedMoment B raw36740step1 raw36740step1Labels = mixedMoment B raw36740step2 raw36740step2Labels := by
      have ha : raw36740step2 = raw36740step1 := by apply Matrix.ext; unfold raw36740step2 raw36740step1; decide +kernel
      have hl : raw36740step1Labels = labelEmbedding6 ∘ raw36740step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36740step1 raw36740step1Labels raw36740step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5368 node5368Labels := by rfl

def raw36741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw36741Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw36741step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36741step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw36741step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36741step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw36741step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36741 raw36741Labels = mixedMoment B node4644 node4644Labels := by
  calc
    mixedMoment B raw36741 raw36741Labels = mixedMoment B raw36741step0 raw36741step0Labels := by
      have hz : ∀ j, raw36741 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36741step0 = (fun i j => raw36741 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36741step0 raw36741; decide +kernel
      have hl : raw36741step0Labels = raw36741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36741 raw36741Labels permutation346 hz
    mixedMoment B raw36741step0 raw36741step0Labels = mixedMoment B raw36741step1 raw36741step1Labels := by
      have ha : raw36741step1 = (fun i j => raw36741step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36741step1 raw36741step0; decide +kernel
      have hl : raw36741step1Labels = raw36741step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36741step0 raw36741step0Labels permutation58 permutation3
    mixedMoment B raw36741step1 raw36741step1Labels = mixedMoment B raw36741step2 raw36741step2Labels := by
      have ha : raw36741step2 = raw36741step1 := by apply Matrix.ext; unfold raw36741step2 raw36741step1; decide +kernel
      have hl : raw36741step1Labels = labelEmbedding6 ∘ raw36741step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36741step1 raw36741step1Labels raw36741step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4644 node4644Labels := by rfl

def raw36742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw36742Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw36742step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36742step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36742step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36742step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36742step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36742 raw36742Labels = mixedMoment B node4987 node4987Labels := by
  calc
    mixedMoment B raw36742 raw36742Labels = mixedMoment B raw36742step0 raw36742step0Labels := by
      have ha : raw36742step0 = (fun i j => raw36742 (permutation663 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36742step0 raw36742; decide +kernel
      have hl : raw36742step0Labels = raw36742Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36742 raw36742Labels permutation663 permutation3
    mixedMoment B raw36742step0 raw36742step0Labels = mixedMoment B raw36742step1 raw36742step1Labels := by
      have ha : raw36742step1 = -raw36742step0 := by apply Matrix.ext; change ∀ i j, raw36742step1 i j = -(raw36742step0 i j); unfold raw36742step1 raw36742step0; decide +kernel
      have hl : raw36742step1Labels = raw36742step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36742step1 raw36742step1Labels = mixedMoment B raw36742step2 raw36742step2Labels := by
      have ha : raw36742step2 = raw36742step1 := by apply Matrix.ext; unfold raw36742step2 raw36742step1; decide +kernel
      have hl : raw36742step1Labels = labelEmbedding6 ∘ raw36742step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36742step1 raw36742step1Labels raw36742step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4987 node4987Labels := by rfl

def raw36743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw36743Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw36743step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw36743step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36743step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw36743step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36743step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw36743step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36743 raw36743Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw36743 raw36743Labels = mixedMoment B raw36743step0 raw36743step0Labels := by
      have hz : ∀ j, raw36743 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36743step0 = (fun i j => raw36743 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36743step0 raw36743; decide +kernel
      have hl : raw36743step0Labels = raw36743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36743 raw36743Labels permutation346 hz
    mixedMoment B raw36743step0 raw36743step0Labels = mixedMoment B raw36743step1 raw36743step1Labels := by
      have ha : raw36743step1 = (fun i j => raw36743step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36743step1 raw36743step0; decide +kernel
      have hl : raw36743step1Labels = raw36743step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36743step0 raw36743step0Labels permutation150 permutation3
    mixedMoment B raw36743step1 raw36743step1Labels = mixedMoment B raw36743step2 raw36743step2Labels := by
      have ha : raw36743step2 = -raw36743step1 := by apply Matrix.ext; change ∀ i j, raw36743step2 i j = -(raw36743step1 i j); unfold raw36743step2 raw36743step1; decide +kernel
      have hl : raw36743step2Labels = raw36743step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36743step2 raw36743step2Labels = mixedMoment B raw36743step3 raw36743step3Labels := by
      have ha : raw36743step3 = raw36743step2 := by apply Matrix.ext; unfold raw36743step3 raw36743step2; decide +kernel
      have hl : raw36743step2Labels = labelEmbedding6 ∘ raw36743step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36743step2 raw36743step2Labels raw36743step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

def raw36744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -2, -1]]
def raw36744Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![0, 1, -1], ![3, -2, -1]]
def raw36744step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw36744step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36744step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36744step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36744step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36744step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36744 raw36744Labels = mixedMoment B node5003 node5003Labels := by
  calc
    mixedMoment B raw36744 raw36744Labels = mixedMoment B raw36744step0 raw36744step0Labels := by
      have hz : ∀ j, raw36744 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36744step0 = (fun i j => raw36744 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36744step0 raw36744; decide +kernel
      have hl : raw36744step0Labels = raw36744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36744 raw36744Labels permutation346 hz
    mixedMoment B raw36744step0 raw36744step0Labels = mixedMoment B raw36744step1 raw36744step1Labels := by
      have ha : raw36744step1 = (fun i j => raw36744step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36744step1 raw36744step0; decide +kernel
      have hl : raw36744step1Labels = raw36744step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36744step0 raw36744step0Labels permutation144 permutation3
    mixedMoment B raw36744step1 raw36744step1Labels = mixedMoment B raw36744step2 raw36744step2Labels := by
      have ha : raw36744step2 = -raw36744step1 := by apply Matrix.ext; change ∀ i j, raw36744step2 i j = -(raw36744step1 i j); unfold raw36744step2 raw36744step1; decide +kernel
      have hl : raw36744step2Labels = raw36744step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36744step2 raw36744step2Labels = mixedMoment B raw36744step3 raw36744step3Labels := by
      have ha : raw36744step3 = raw36744step2 := by apply Matrix.ext; unfold raw36744step3 raw36744step2; decide +kernel
      have hl : raw36744step2Labels = labelEmbedding6 ∘ raw36744step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36744step2 raw36744step2Labels raw36744step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5003 node5003Labels := by rfl

def raw36745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36745Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36745step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36745step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36745 raw36745Labels = mixedMoment B node5104 node5104Labels := by
  calc
    mixedMoment B raw36745 raw36745Labels = mixedMoment B raw36745step0 raw36745step0Labels := by
      have hz : ∀ j, raw36745 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36745step0 = (fun i j => raw36745 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36745step0 raw36745; decide +kernel
      have hl : raw36745step0Labels = raw36745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36745 raw36745Labels permutation346 hz
    mixedMoment B raw36745step0 raw36745step0Labels = mixedMoment B raw36745step1 raw36745step1Labels := by
      have ha : raw36745step1 = (fun i j => raw36745step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36745step1 raw36745step0; decide +kernel
      have hl : raw36745step1Labels = raw36745step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36745step0 raw36745step0Labels permutation56 permutation2
    _ = mixedMoment B node5104 node5104Labels := by rfl

def raw36746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36746Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36746step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36746 raw36746Labels = mixedMoment B node5396 node5396Labels := by
  calc
    mixedMoment B raw36746 raw36746Labels = mixedMoment B raw36746step0 raw36746step0Labels := by
      have ha : raw36746step0 = (fun i j => raw36746 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36746step0 raw36746; decide +kernel
      have hl : raw36746step0Labels = raw36746Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36746 raw36746Labels permutation265 permutation2
    _ = mixedMoment B node5396 node5396Labels := by rfl

def raw36747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36747Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36747step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36747step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36747 raw36747Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw36747 raw36747Labels = mixedMoment B raw36747step0 raw36747step0Labels := by
      have hz : ∀ j, raw36747 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36747step0 = (fun i j => raw36747 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36747step0 raw36747; decide +kernel
      have hl : raw36747step0Labels = raw36747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36747 raw36747Labels permutation346 hz
    mixedMoment B raw36747step0 raw36747step0Labels = mixedMoment B raw36747step1 raw36747step1Labels := by
      have ha : raw36747step1 = (fun i j => raw36747step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36747step1 raw36747step0; decide +kernel
      have hl : raw36747step1Labels = raw36747step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36747step0 raw36747step0Labels permutation56 permutation2
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw36748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw36748Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw36748step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36748step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36748 raw36748Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw36748 raw36748Labels = mixedMoment B raw36748step0 raw36748step0Labels := by
      have hz : ∀ j, raw36748 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36748step0 = (fun i j => raw36748 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36748step0 raw36748; decide +kernel
      have hl : raw36748step0Labels = raw36748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36748 raw36748Labels permutation346 hz
    mixedMoment B raw36748step0 raw36748step0Labels = mixedMoment B raw36748step1 raw36748step1Labels := by
      have ha : raw36748step1 = (fun i j => raw36748step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36748step1 raw36748step0; decide +kernel
      have hl : raw36748step1Labels = raw36748step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36748step0 raw36748step0Labels permutation58 permutation2
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw36749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36749Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36749step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36749step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw36749step1Labels : Fin 2 → Fin 3 := ![0, 2]

def raw36749step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw36749step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw36749step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw36749step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical36749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36749 raw36749Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw36749 raw36749Labels = mixedMoment B raw36749step0 raw36749step0Labels := by
      have hz : ∀ j, raw36749 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36749step0 = (fun i j => raw36749 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36749step0 raw36749; decide +kernel
      have hl : raw36749step0Labels = raw36749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36749 raw36749Labels permutation346 hz
    mixedMoment B raw36749step0 raw36749step0Labels = mixedMoment B raw36749step1 raw36749step1Labels := by
      have hz : ∀ i, raw36749step0 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw36749step1 = (fun i j => raw36749step0 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw36749step1 raw36749step0; decide +kernel
      have hl : raw36749step1Labels = (fun j => raw36749step0Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw36749step0 raw36749step0Labels permutation4 hz
    mixedMoment B raw36749step1 raw36749step1Labels = mixedMoment B raw36749step2 raw36749step2Labels := by
      have ha : raw36749step2 = (fun i j => raw36749step1 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw36749step2 raw36749step1; decide +kernel
      have hl : raw36749step2Labels = raw36749step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36749step1 raw36749step1Labels permutation56 permutation0
    mixedMoment B raw36749step2 raw36749step2Labels = mixedMoment B raw36749step3 raw36749step3Labels := by
      have ha : raw36749step3 = raw36749step2 := by apply Matrix.ext; unfold raw36749step3 raw36749step2; decide +kernel
      have hl : raw36749step2Labels = labelEmbedding2 ∘ raw36749step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36749step2 raw36749step2Labels raw36749step3Labels labelEmbedding2 hl
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw36750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36750Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36750step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36750step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw36750step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36750step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw36750step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36750 raw36750Labels = mixedMoment B node5203 node5203Labels := by
  calc
    mixedMoment B raw36750 raw36750Labels = mixedMoment B raw36750step0 raw36750step0Labels := by
      have hz : ∀ j, raw36750 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36750step0 = (fun i j => raw36750 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36750step0 raw36750; decide +kernel
      have hl : raw36750step0Labels = raw36750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36750 raw36750Labels permutation346 hz
    mixedMoment B raw36750step0 raw36750step0Labels = mixedMoment B raw36750step1 raw36750step1Labels := by
      have ha : raw36750step1 = (fun i j => raw36750step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36750step1 raw36750step0; decide +kernel
      have hl : raw36750step1Labels = raw36750step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36750step0 raw36750step0Labels permutation32 permutation3
    mixedMoment B raw36750step1 raw36750step1Labels = mixedMoment B raw36750step2 raw36750step2Labels := by
      have ha : raw36750step2 = raw36750step1 := by apply Matrix.ext; unfold raw36750step2 raw36750step1; decide +kernel
      have hl : raw36750step1Labels = labelEmbedding6 ∘ raw36750step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36750step1 raw36750step1Labels raw36750step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5203 node5203Labels := by rfl

def raw36751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36751Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36751step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36751step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36751 raw36751Labels = mixedMoment B node4941 node4941Labels := by
  calc
    mixedMoment B raw36751 raw36751Labels = mixedMoment B raw36751step0 raw36751step0Labels := by
      have ha : raw36751step0 = (fun i j => raw36751 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36751step0 raw36751; decide +kernel
      have hl : raw36751step0Labels = raw36751Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36751 raw36751Labels permutation265 permutation2
    _ = mixedMoment B node4941 node4941Labels := by rfl

def raw36752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36752step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36752step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36752 raw36752Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw36752 raw36752Labels = mixedMoment B raw36752step0 raw36752step0Labels := by
      have ha : raw36752step0 = (fun i j => raw36752 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36752step0 raw36752; decide +kernel
      have hl : raw36752step0Labels = raw36752Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36752 raw36752Labels permutation271 permutation2
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw36753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw36753Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36753step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36753 raw36753Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw36753 raw36753Labels = mixedMoment B raw36753step0 raw36753step0Labels := by
      have ha : raw36753step0 = (fun i j => raw36753 (permutation277 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36753step0 raw36753; decide +kernel
      have hl : raw36753step0Labels = raw36753Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36753 raw36753Labels permutation277 permutation2
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw36754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36754Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36754step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36754step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36754 raw36754Labels = mixedMoment B node5366 node5366Labels := by
  calc
    mixedMoment B raw36754 raw36754Labels = mixedMoment B raw36754step0 raw36754step0Labels := by
      have ha : raw36754step0 = (fun i j => raw36754 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36754step0 raw36754; decide +kernel
      have hl : raw36754step0Labels = raw36754Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36754 raw36754Labels permutation265 permutation2
    _ = mixedMoment B node5366 node5366Labels := by rfl

def raw36755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36755Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36755step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36755step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36755 raw36755Labels = mixedMoment B node4950 node4950Labels := by
  calc
    mixedMoment B raw36755 raw36755Labels = mixedMoment B raw36755step0 raw36755step0Labels := by
      have hz : ∀ j, raw36755 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36755step0 = (fun i j => raw36755 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36755step0 raw36755; decide +kernel
      have hl : raw36755step0Labels = raw36755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36755 raw36755Labels permutation346 hz
    mixedMoment B raw36755step0 raw36755step0Labels = mixedMoment B raw36755step1 raw36755step1Labels := by
      have ha : raw36755step1 = (fun i j => raw36755step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36755step1 raw36755step0; decide +kernel
      have hl : raw36755step1Labels = raw36755step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36755step0 raw36755step0Labels permutation58 permutation2
    _ = mixedMoment B node4950 node4950Labels := by rfl

def raw36756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36756Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36756step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36756step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36756 raw36756Labels = mixedMoment B node5337 node5337Labels := by
  calc
    mixedMoment B raw36756 raw36756Labels = mixedMoment B raw36756step0 raw36756step0Labels := by
      have ha : raw36756step0 = (fun i j => raw36756 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36756step0 raw36756; decide +kernel
      have hl : raw36756step0Labels = raw36756Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36756 raw36756Labels permutation267 permutation2
    _ = mixedMoment B node5337 node5337Labels := by rfl

def raw36757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw36757Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw36757step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36757step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36757 raw36757Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw36757 raw36757Labels = mixedMoment B raw36757step0 raw36757step0Labels := by
      have hz : ∀ j, raw36757 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36757step0 = (fun i j => raw36757 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36757step0 raw36757; decide +kernel
      have hl : raw36757step0Labels = raw36757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36757 raw36757Labels permutation346 hz
    mixedMoment B raw36757step0 raw36757step0Labels = mixedMoment B raw36757step1 raw36757step1Labels := by
      have ha : raw36757step1 = (fun i j => raw36757step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36757step1 raw36757step0; decide +kernel
      have hl : raw36757step1Labels = raw36757step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36757step0 raw36757step0Labels permutation58 permutation2
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw36758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36758Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36758step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36758step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36758 raw36758Labels = mixedMoment B node5369 node5369Labels := by
  calc
    mixedMoment B raw36758 raw36758Labels = mixedMoment B raw36758step0 raw36758step0Labels := by
      have hz : ∀ j, raw36758 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36758step0 = (fun i j => raw36758 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36758step0 raw36758; decide +kernel
      have hl : raw36758step0Labels = raw36758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36758 raw36758Labels permutation346 hz
    mixedMoment B raw36758step0 raw36758step0Labels = mixedMoment B raw36758step1 raw36758step1Labels := by
      have ha : raw36758step1 = (fun i j => raw36758step0 (permutation59 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36758step1 raw36758step0; decide +kernel
      have hl : raw36758step1Labels = raw36758step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36758step0 raw36758step0Labels permutation59 permutation2
    _ = mixedMoment B node5369 node5369Labels := by rfl

def raw36759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36759Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36759step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36759step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36759 raw36759Labels = mixedMoment B node4950 node4950Labels := by
  calc
    mixedMoment B raw36759 raw36759Labels = mixedMoment B raw36759step0 raw36759step0Labels := by
      have hz : ∀ j, raw36759 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36759step0 = (fun i j => raw36759 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36759step0 raw36759; decide +kernel
      have hl : raw36759step0Labels = raw36759Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36759 raw36759Labels permutation346 hz
    mixedMoment B raw36759step0 raw36759step0Labels = mixedMoment B raw36759step1 raw36759step1Labels := by
      have ha : raw36759step1 = (fun i j => raw36759step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36759step1 raw36759step0; decide +kernel
      have hl : raw36759step1Labels = raw36759step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36759step0 raw36759step0Labels permutation56 permutation2
    _ = mixedMoment B node4950 node4950Labels := by rfl

def raw36760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36760Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36760step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36760step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36760 raw36760Labels = mixedMoment B node5337 node5337Labels := by
  calc
    mixedMoment B raw36760 raw36760Labels = mixedMoment B raw36760step0 raw36760step0Labels := by
      have ha : raw36760step0 = (fun i j => raw36760 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36760step0 raw36760; decide +kernel
      have hl : raw36760step0Labels = raw36760Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36760 raw36760Labels permutation265 permutation2
    _ = mixedMoment B node5337 node5337Labels := by rfl

def raw36761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36761Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36761step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36761step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36761 raw36761Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw36761 raw36761Labels = mixedMoment B raw36761step0 raw36761step0Labels := by
      have hz : ∀ j, raw36761 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36761step0 = (fun i j => raw36761 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36761step0 raw36761; decide +kernel
      have hl : raw36761step0Labels = raw36761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36761 raw36761Labels permutation346 hz
    mixedMoment B raw36761step0 raw36761step0Labels = mixedMoment B raw36761step1 raw36761step1Labels := by
      have ha : raw36761step1 = (fun i j => raw36761step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36761step1 raw36761step0; decide +kernel
      have hl : raw36761step1Labels = raw36761step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36761step0 raw36761step0Labels permutation56 permutation2
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw36762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw36762Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw36762step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36762step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36762 raw36762Labels = mixedMoment B node5369 node5369Labels := by
  calc
    mixedMoment B raw36762 raw36762Labels = mixedMoment B raw36762step0 raw36762step0Labels := by
      have hz : ∀ j, raw36762 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36762step0 = (fun i j => raw36762 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36762step0 raw36762; decide +kernel
      have hl : raw36762step0Labels = raw36762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36762 raw36762Labels permutation346 hz
    mixedMoment B raw36762step0 raw36762step0Labels = mixedMoment B raw36762step1 raw36762step1Labels := by
      have ha : raw36762step1 = (fun i j => raw36762step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36762step1 raw36762step0; decide +kernel
      have hl : raw36762step1Labels = raw36762step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36762step0 raw36762step0Labels permutation57 permutation2
    _ = mixedMoment B node5369 node5369Labels := by rfl

def raw36763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36763Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36763step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36763step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36763 raw36763Labels = mixedMoment B node4948 node4948Labels := by
  calc
    mixedMoment B raw36763 raw36763Labels = mixedMoment B raw36763step0 raw36763step0Labels := by
      have hz : ∀ j, raw36763 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36763step0 = (fun i j => raw36763 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36763step0 raw36763; decide +kernel
      have hl : raw36763step0Labels = raw36763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36763 raw36763Labels permutation346 hz
    mixedMoment B raw36763step0 raw36763step0Labels = mixedMoment B raw36763step1 raw36763step1Labels := by
      have ha : raw36763step1 = (fun i j => raw36763step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36763step1 raw36763step0; decide +kernel
      have hl : raw36763step1Labels = raw36763step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36763step0 raw36763step0Labels permutation56 permutation2
    _ = mixedMoment B node4948 node4948Labels := by rfl

def raw36764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36764Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36764step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw36764step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36764step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36764step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36764step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36764step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36764 raw36764Labels = mixedMoment B node5117 node5117Labels := by
  calc
    mixedMoment B raw36764 raw36764Labels = mixedMoment B raw36764step0 raw36764step0Labels := by
      have ha : raw36764step0 = (fun i j => raw36764 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36764step0 raw36764; decide +kernel
      have hl : raw36764step0Labels = raw36764Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36764 raw36764Labels permutation664 permutation3
    mixedMoment B raw36764step0 raw36764step0Labels = mixedMoment B raw36764step1 raw36764step1Labels := by
      have ha : raw36764step1 = -raw36764step0 := by apply Matrix.ext; change ∀ i j, raw36764step1 i j = -(raw36764step0 i j); unfold raw36764step1 raw36764step0; decide +kernel
      have hl : raw36764step1Labels = raw36764step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36764step1 raw36764step1Labels = mixedMoment B raw36764step2 raw36764step2Labels := by
      have ha : raw36764step2 = raw36764step1 := by apply Matrix.ext; unfold raw36764step2 raw36764step1; decide +kernel
      have hl : raw36764step1Labels = labelEmbedding6 ∘ raw36764step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36764step1 raw36764step1Labels raw36764step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5117 node5117Labels := by rfl

def raw36765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36765step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw36765step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36765step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36765step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36765step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36765step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36765 raw36765Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw36765 raw36765Labels = mixedMoment B raw36765step0 raw36765step0Labels := by
      have hz : ∀ j, raw36765 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36765step0 = (fun i j => raw36765 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36765step0 raw36765; decide +kernel
      have hl : raw36765step0Labels = raw36765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36765 raw36765Labels permutation346 hz
    mixedMoment B raw36765step0 raw36765step0Labels = mixedMoment B raw36765step1 raw36765step1Labels := by
      have ha : raw36765step1 = (fun i j => raw36765step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36765step1 raw36765step0; decide +kernel
      have hl : raw36765step1Labels = raw36765step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36765step0 raw36765step0Labels permutation151 permutation3
    mixedMoment B raw36765step1 raw36765step1Labels = mixedMoment B raw36765step2 raw36765step2Labels := by
      have ha : raw36765step2 = -raw36765step1 := by apply Matrix.ext; change ∀ i j, raw36765step2 i j = -(raw36765step1 i j); unfold raw36765step2 raw36765step1; decide +kernel
      have hl : raw36765step2Labels = raw36765step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36765step2 raw36765step2Labels = mixedMoment B raw36765step3 raw36765step3Labels := by
      have ha : raw36765step3 = raw36765step2 := by apply Matrix.ext; unfold raw36765step3 raw36765step2; decide +kernel
      have hl : raw36765step2Labels = labelEmbedding6 ∘ raw36765step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36765step2 raw36765step2Labels raw36765step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw36766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw36766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw36766step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw36766step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36766step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36766step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36766step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36766step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36766 raw36766Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw36766 raw36766Labels = mixedMoment B raw36766step0 raw36766step0Labels := by
      have hz : ∀ j, raw36766 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36766step0 = (fun i j => raw36766 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36766step0 raw36766; decide +kernel
      have hl : raw36766step0Labels = raw36766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36766 raw36766Labels permutation346 hz
    mixedMoment B raw36766step0 raw36766step0Labels = mixedMoment B raw36766step1 raw36766step1Labels := by
      have ha : raw36766step1 = (fun i j => raw36766step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36766step1 raw36766step0; decide +kernel
      have hl : raw36766step1Labels = raw36766step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36766step0 raw36766step0Labels permutation145 permutation3
    mixedMoment B raw36766step1 raw36766step1Labels = mixedMoment B raw36766step2 raw36766step2Labels := by
      have ha : raw36766step2 = -raw36766step1 := by apply Matrix.ext; change ∀ i j, raw36766step2 i j = -(raw36766step1 i j); unfold raw36766step2 raw36766step1; decide +kernel
      have hl : raw36766step2Labels = raw36766step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36766step2 raw36766step2Labels = mixedMoment B raw36766step3 raw36766step3Labels := by
      have ha : raw36766step3 = raw36766step2 := by apply Matrix.ext; unfold raw36766step3 raw36766step2; decide +kernel
      have hl : raw36766step2Labels = labelEmbedding6 ∘ raw36766step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36766step2 raw36766step2Labels raw36766step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw36767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36767step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36767 raw36767Labels = mixedMoment B node5101 node5101Labels := by
  calc
    mixedMoment B raw36767 raw36767Labels = mixedMoment B raw36767step0 raw36767step0Labels := by
      have hz : ∀ j, raw36767 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36767step0 = (fun i j => raw36767 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36767step0 raw36767; decide +kernel
      have hl : raw36767step0Labels = raw36767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36767 raw36767Labels permutation346 hz
    mixedMoment B raw36767step0 raw36767step0Labels = mixedMoment B raw36767step1 raw36767step1Labels := by
      have ha : raw36767step1 = (fun i j => raw36767step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36767step1 raw36767step0; decide +kernel
      have hl : raw36767step1Labels = raw36767step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36767step0 raw36767step0Labels permutation58 permutation2
    _ = mixedMoment B node5101 node5101Labels := by rfl

def raw36768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36768step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36768 raw36768Labels = mixedMoment B node5394 node5394Labels := by
  calc
    mixedMoment B raw36768 raw36768Labels = mixedMoment B raw36768step0 raw36768step0Labels := by
      have ha : raw36768step0 = (fun i j => raw36768 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36768step0 raw36768; decide +kernel
      have hl : raw36768step0Labels = raw36768Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36768 raw36768Labels permutation267 permutation2
    _ = mixedMoment B node5394 node5394Labels := by rfl

def raw36769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36769step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36769step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36769 raw36769Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw36769 raw36769Labels = mixedMoment B raw36769step0 raw36769step0Labels := by
      have hz : ∀ j, raw36769 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36769step0 = (fun i j => raw36769 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36769step0 raw36769; decide +kernel
      have hl : raw36769step0Labels = raw36769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36769 raw36769Labels permutation346 hz
    mixedMoment B raw36769step0 raw36769step0Labels = mixedMoment B raw36769step1 raw36769step1Labels := by
      have ha : raw36769step1 = (fun i j => raw36769step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36769step1 raw36769step0; decide +kernel
      have hl : raw36769step1Labels = raw36769step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36769step0 raw36769step0Labels permutation56 permutation2
    _ = mixedMoment B node5409 node5409Labels := by rfl

def raw36770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36770step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36770step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, 0, -1], ![2, 0, -2]]
def raw36770step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36770step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]
def raw36770step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw36770step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw36770step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw36770step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw36770step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical36770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36770 raw36770Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw36770 raw36770Labels = mixedMoment B raw36770step0 raw36770step0Labels := by
      have hz : ∀ j, raw36770 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36770step0 = (fun i j => raw36770 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36770step0 raw36770; decide +kernel
      have hl : raw36770step0Labels = raw36770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36770 raw36770Labels permutation520 hz
    mixedMoment B raw36770step0 raw36770step0Labels = mixedMoment B raw36770step1 raw36770step1Labels := by
      have hz : ∀ j, raw36770step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36770step1 = (fun i j => raw36770step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36770step1 raw36770step0; decide +kernel
      have hl : raw36770step1Labels = raw36770step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36770step0 raw36770step0Labels permutation80 hz
    mixedMoment B raw36770step1 raw36770step1Labels = mixedMoment B raw36770step2 raw36770step2Labels := by
      have hz : ∀ i, raw36770step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw36770step2 = (fun i j => raw36770step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw36770step2 raw36770step1; decide +kernel
      have hl : raw36770step2Labels = (fun j => raw36770step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw36770step1 raw36770step1Labels permutation4 hz
    mixedMoment B raw36770step2 raw36770step2Labels = mixedMoment B raw36770step3 raw36770step3Labels := by
      have ha : raw36770step3 = (fun i j => raw36770step2 (permutation14 i) (permutation0 j)) := by apply Matrix.ext; unfold raw36770step3 raw36770step2; decide +kernel
      have hl : raw36770step3Labels = raw36770step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36770step2 raw36770step2Labels permutation14 permutation0
    mixedMoment B raw36770step3 raw36770step3Labels = mixedMoment B raw36770step4 raw36770step4Labels := by
      have ha : raw36770step4 = raw36770step3 := by apply Matrix.ext; unfold raw36770step4 raw36770step3; decide +kernel
      have hl : raw36770step3Labels = labelEmbedding2 ∘ raw36770step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36770step3 raw36770step3Labels raw36770step4Labels labelEmbedding2 hl
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw36771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36771step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36771step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36771step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36771step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36771step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36771step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36771step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36771 raw36771Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw36771 raw36771Labels = mixedMoment B raw36771step0 raw36771step0Labels := by
      have hz : ∀ j, raw36771 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36771step0 = (fun i j => raw36771 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36771step0 raw36771; decide +kernel
      have hl : raw36771step0Labels = raw36771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36771 raw36771Labels permutation346 hz
    mixedMoment B raw36771step0 raw36771step0Labels = mixedMoment B raw36771step1 raw36771step1Labels := by
      have ha : raw36771step1 = (fun i j => raw36771step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36771step1 raw36771step0; decide +kernel
      have hl : raw36771step1Labels = raw36771step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36771step0 raw36771step0Labels permutation58 permutation7
    mixedMoment B raw36771step1 raw36771step1Labels = mixedMoment B raw36771step2 raw36771step2Labels := by
      have ha : raw36771step2 = -raw36771step1 := by apply Matrix.ext; change ∀ i j, raw36771step2 i j = -(raw36771step1 i j); unfold raw36771step2 raw36771step1; decide +kernel
      have hl : raw36771step2Labels = raw36771step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36771step2 raw36771step2Labels = mixedMoment B raw36771step3 raw36771step3Labels := by
      have ha : raw36771step3 = raw36771step2 := by apply Matrix.ext; unfold raw36771step3 raw36771step2; decide +kernel
      have hl : raw36771step2Labels = labelEmbedding10 ∘ raw36771step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36771step2 raw36771step2Labels raw36771step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw36772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36772step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36772step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36772step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36772step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36772 raw36772Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw36772 raw36772Labels = mixedMoment B raw36772step0 raw36772step0Labels := by
      have hz : ∀ j, raw36772 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36772step0 = (fun i j => raw36772 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36772step0 raw36772; decide +kernel
      have hl : raw36772step0Labels = raw36772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36772 raw36772Labels permutation346 hz
    mixedMoment B raw36772step0 raw36772step0Labels = mixedMoment B raw36772step1 raw36772step1Labels := by
      have ha : raw36772step1 = (fun i j => raw36772step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36772step1 raw36772step0; decide +kernel
      have hl : raw36772step1Labels = raw36772step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36772step0 raw36772step0Labels permutation32 permutation3
    mixedMoment B raw36772step1 raw36772step1Labels = mixedMoment B raw36772step2 raw36772step2Labels := by
      have ha : raw36772step2 = raw36772step1 := by apply Matrix.ext; unfold raw36772step2 raw36772step1; decide +kernel
      have hl : raw36772step1Labels = labelEmbedding6 ∘ raw36772step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36772step1 raw36772step1Labels raw36772step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw36773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36773step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36773 raw36773Labels = mixedMoment B node4939 node4939Labels := by
  calc
    mixedMoment B raw36773 raw36773Labels = mixedMoment B raw36773step0 raw36773step0Labels := by
      have ha : raw36773step0 = (fun i j => raw36773 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36773step0 raw36773; decide +kernel
      have hl : raw36773step0Labels = raw36773Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36773 raw36773Labels permutation267 permutation2
    _ = mixedMoment B node4939 node4939Labels := by rfl

def raw36774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36774step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36774 raw36774Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw36774 raw36774Labels = mixedMoment B raw36774step0 raw36774step0Labels := by
      have ha : raw36774step0 = (fun i j => raw36774 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36774step0 raw36774; decide +kernel
      have hl : raw36774step0Labels = raw36774Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36774 raw36774Labels permutation271 permutation2
    _ = mixedMoment B node5351 node5351Labels := by rfl

def raw36775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36775step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36775 raw36775Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw36775 raw36775Labels = mixedMoment B raw36775step0 raw36775step0Labels := by
      have hz : ∀ j, raw36775 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36775step0 = (fun i j => raw36775 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36775step0 raw36775; decide +kernel
      have hl : raw36775step0Labels = raw36775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36775 raw36775Labels permutation520 hz
    mixedMoment B raw36775step0 raw36775step0Labels = mixedMoment B raw36775step1 raw36775step1Labels := by
      have ha : raw36775step1 = (fun i j => raw36775step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36775step1 raw36775step0; decide +kernel
      have hl : raw36775step1Labels = raw36775step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36775step0 raw36775step0Labels permutation56 permutation2
    _ = mixedMoment B node5367 node5367Labels := by rfl

def raw36776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36776step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36776step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36776 raw36776Labels = mixedMoment B node5365 node5365Labels := by
  calc
    mixedMoment B raw36776 raw36776Labels = mixedMoment B raw36776step0 raw36776step0Labels := by
      have ha : raw36776step0 = (fun i j => raw36776 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36776step0 raw36776; decide +kernel
      have hl : raw36776step0Labels = raw36776Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36776 raw36776Labels permutation267 permutation2
    _ = mixedMoment B node5365 node5365Labels := by rfl

def raw36777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36777step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36777step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36777 raw36777Labels = mixedMoment B node4946 node4946Labels := by
  calc
    mixedMoment B raw36777 raw36777Labels = mixedMoment B raw36777step0 raw36777step0Labels := by
      have hz : ∀ j, raw36777 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36777step0 = (fun i j => raw36777 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36777step0 raw36777; decide +kernel
      have hl : raw36777step0Labels = raw36777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36777 raw36777Labels permutation346 hz
    mixedMoment B raw36777step0 raw36777step0Labels = mixedMoment B raw36777step1 raw36777step1Labels := by
      have ha : raw36777step1 = (fun i j => raw36777step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36777step1 raw36777step0; decide +kernel
      have hl : raw36777step1Labels = raw36777step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36777step0 raw36777step0Labels permutation58 permutation2
    _ = mixedMoment B node4946 node4946Labels := by rfl

def raw36778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36778step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36778 raw36778Labels = mixedMoment B node5335 node5335Labels := by
  calc
    mixedMoment B raw36778 raw36778Labels = mixedMoment B raw36778step0 raw36778step0Labels := by
      have ha : raw36778step0 = (fun i j => raw36778 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36778step0 raw36778; decide +kernel
      have hl : raw36778step0Labels = raw36778Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36778 raw36778Labels permutation267 permutation2
    _ = mixedMoment B node5335 node5335Labels := by rfl

def raw36779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36779step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36779step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, -1, -1], ![2, 0, -2]]
def raw36779step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36779step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw36779step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36779 raw36779Labels = mixedMoment B node5371 node5371Labels := by
  calc
    mixedMoment B raw36779 raw36779Labels = mixedMoment B raw36779step0 raw36779step0Labels := by
      have hz : ∀ j, raw36779 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36779step0 = (fun i j => raw36779 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36779step0 raw36779; decide +kernel
      have hl : raw36779step0Labels = raw36779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36779 raw36779Labels permutation520 hz
    mixedMoment B raw36779step0 raw36779step0Labels = mixedMoment B raw36779step1 raw36779step1Labels := by
      have hz : ∀ j, raw36779step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36779step1 = (fun i j => raw36779step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36779step1 raw36779step0; decide +kernel
      have hl : raw36779step1Labels = raw36779step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36779step0 raw36779step0Labels permutation80 hz
    mixedMoment B raw36779step1 raw36779step1Labels = mixedMoment B raw36779step2 raw36779step2Labels := by
      have ha : raw36779step2 = (fun i j => raw36779step1 (permutation14 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36779step2 raw36779step1; decide +kernel
      have hl : raw36779step2Labels = raw36779step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36779step1 raw36779step1Labels permutation14 permutation2
    _ = mixedMoment B node5371 node5371Labels := by rfl

def raw36780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36780step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36780step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36780 raw36780Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw36780 raw36780Labels = mixedMoment B raw36780step0 raw36780step0Labels := by
      have hz : ∀ j, raw36780 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36780step0 = (fun i j => raw36780 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36780step0 raw36780; decide +kernel
      have hl : raw36780step0Labels = raw36780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36780 raw36780Labels permutation346 hz
    mixedMoment B raw36780step0 raw36780step0Labels = mixedMoment B raw36780step1 raw36780step1Labels := by
      have ha : raw36780step1 = (fun i j => raw36780step0 (permutation59 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36780step1 raw36780step0; decide +kernel
      have hl : raw36780step1Labels = raw36780step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36780step0 raw36780step0Labels permutation59 permutation2
    _ = mixedMoment B node5368 node5368Labels := by rfl

def raw36781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36781Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36781step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36781step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36781step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36781 raw36781Labels = mixedMoment B node4949 node4949Labels := by
  calc
    mixedMoment B raw36781 raw36781Labels = mixedMoment B raw36781step0 raw36781step0Labels := by
      have hz : ∀ j, raw36781 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36781step0 = (fun i j => raw36781 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36781step0 raw36781; decide +kernel
      have hl : raw36781step0Labels = raw36781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36781 raw36781Labels permutation346 hz
    mixedMoment B raw36781step0 raw36781step0Labels = mixedMoment B raw36781step1 raw36781step1Labels := by
      have ha : raw36781step1 = (fun i j => raw36781step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36781step1 raw36781step0; decide +kernel
      have hl : raw36781step1Labels = raw36781step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36781step0 raw36781step0Labels permutation56 permutation2
    _ = mixedMoment B node4949 node4949Labels := by rfl

def raw36782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36782Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36782step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36782step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36782 raw36782Labels = mixedMoment B node5336 node5336Labels := by
  calc
    mixedMoment B raw36782 raw36782Labels = mixedMoment B raw36782step0 raw36782step0Labels := by
      have ha : raw36782step0 = (fun i j => raw36782 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36782step0 raw36782; decide +kernel
      have hl : raw36782step0Labels = raw36782Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36782 raw36782Labels permutation265 permutation2
    _ = mixedMoment B node5336 node5336Labels := by rfl

def raw36783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36783Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36783step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36783step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36783 raw36783Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw36783 raw36783Labels = mixedMoment B raw36783step0 raw36783step0Labels := by
      have hz : ∀ j, raw36783 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36783step0 = (fun i j => raw36783 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36783step0 raw36783; decide +kernel
      have hl : raw36783step0Labels = raw36783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36783 raw36783Labels permutation346 hz
    mixedMoment B raw36783step0 raw36783step0Labels = mixedMoment B raw36783step1 raw36783step1Labels := by
      have ha : raw36783step1 = (fun i j => raw36783step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36783step1 raw36783step0; decide +kernel
      have hl : raw36783step1Labels = raw36783step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36783step0 raw36783step0Labels permutation56 permutation2
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw36784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw36784Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw36784step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36784step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36784 raw36784Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw36784 raw36784Labels = mixedMoment B raw36784step0 raw36784step0Labels := by
      have hz : ∀ j, raw36784 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36784step0 = (fun i j => raw36784 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36784step0 raw36784; decide +kernel
      have hl : raw36784step0Labels = raw36784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36784 raw36784Labels permutation346 hz
    mixedMoment B raw36784step0 raw36784step0Labels = mixedMoment B raw36784step1 raw36784step1Labels := by
      have ha : raw36784step1 = (fun i j => raw36784step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36784step1 raw36784step0; decide +kernel
      have hl : raw36784step1Labels = raw36784step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36784step0 raw36784step0Labels permutation57 permutation2
    _ = mixedMoment B node5370 node5370Labels := by rfl

def raw36785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36785Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36785step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw36785step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36785 raw36785Labels = mixedMoment B node4943 node4943Labels := by
  calc
    mixedMoment B raw36785 raw36785Labels = mixedMoment B raw36785step0 raw36785step0Labels := by
      have hz : ∀ j, raw36785 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36785step0 = (fun i j => raw36785 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36785step0 raw36785; decide +kernel
      have hl : raw36785step0Labels = raw36785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36785 raw36785Labels permutation346 hz
    mixedMoment B raw36785step0 raw36785step0Labels = mixedMoment B raw36785step1 raw36785step1Labels := by
      have ha : raw36785step1 = (fun i j => raw36785step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36785step1 raw36785step0; decide +kernel
      have hl : raw36785step1Labels = raw36785step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36785step0 raw36785step0Labels permutation58 permutation2
    _ = mixedMoment B node4943 node4943Labels := by rfl

def raw36786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36786Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw36786step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36786step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36786step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36786 raw36786Labels = mixedMoment B node5036 node5036Labels := by
  calc
    mixedMoment B raw36786 raw36786Labels = mixedMoment B raw36786step0 raw36786step0Labels := by
      have ha : raw36786step0 = (fun i j => raw36786 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36786step0 raw36786; decide +kernel
      have hl : raw36786step0Labels = raw36786Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36786 raw36786Labels permutation663 permutation2
    mixedMoment B raw36786step0 raw36786step0Labels = mixedMoment B raw36786step1 raw36786step1Labels := by
      have ha : raw36786step1 = -raw36786step0 := by apply Matrix.ext; change ∀ i j, raw36786step1 i j = -(raw36786step0 i j); unfold raw36786step1 raw36786step0; decide +kernel
      have hl : raw36786step1Labels = raw36786step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5036 node5036Labels := by rfl

def raw36787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36787Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36787step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36787step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw36787step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36787step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw36787step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36787 raw36787Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw36787 raw36787Labels = mixedMoment B raw36787step0 raw36787step0Labels := by
      have hz : ∀ j, raw36787 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36787step0 = (fun i j => raw36787 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36787step0 raw36787; decide +kernel
      have hl : raw36787step0Labels = raw36787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36787 raw36787Labels permutation346 hz
    mixedMoment B raw36787step0 raw36787step0Labels = mixedMoment B raw36787step1 raw36787step1Labels := by
      have ha : raw36787step1 = (fun i j => raw36787step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36787step1 raw36787step0; decide +kernel
      have hl : raw36787step1Labels = raw36787step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36787step0 raw36787step0Labels permutation150 permutation2
    mixedMoment B raw36787step1 raw36787step1Labels = mixedMoment B raw36787step2 raw36787step2Labels := by
      have ha : raw36787step2 = -raw36787step1 := by apply Matrix.ext; change ∀ i j, raw36787step2 i j = -(raw36787step1 i j); unfold raw36787step2 raw36787step1; decide +kernel
      have hl : raw36787step2Labels = raw36787step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5141 node5141Labels := by rfl

def raw36788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw36788Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw36788step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36788step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![3, -1, -2]]
def raw36788step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36788step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw36788step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36788step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw36788step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36788 raw36788Labels = mixedMoment B node5111 node5111Labels := by
  calc
    mixedMoment B raw36788 raw36788Labels = mixedMoment B raw36788step0 raw36788step0Labels := by
      have hz : ∀ j, raw36788 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36788step0 = (fun i j => raw36788 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36788step0 raw36788; decide +kernel
      have hl : raw36788step0Labels = raw36788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36788 raw36788Labels permutation520 hz
    mixedMoment B raw36788step0 raw36788step0Labels = mixedMoment B raw36788step1 raw36788step1Labels := by
      have hz : ∀ j, raw36788step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36788step1 = (fun i j => raw36788step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36788step1 raw36788step0; decide +kernel
      have hl : raw36788step1Labels = raw36788step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36788step0 raw36788step0Labels permutation80 hz
    mixedMoment B raw36788step1 raw36788step1Labels = mixedMoment B raw36788step2 raw36788step2Labels := by
      have ha : raw36788step2 = (fun i j => raw36788step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36788step2 raw36788step1; decide +kernel
      have hl : raw36788step2Labels = raw36788step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36788step1 raw36788step1Labels permutation30 permutation2
    mixedMoment B raw36788step2 raw36788step2Labels = mixedMoment B raw36788step3 raw36788step3Labels := by
      have ha : raw36788step3 = -raw36788step2 := by apply Matrix.ext; change ∀ i j, raw36788step3 i j = -(raw36788step2 i j); unfold raw36788step3 raw36788step2; decide +kernel
      have hl : raw36788step3Labels = raw36788step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5111 node5111Labels := by rfl

def raw36789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36789Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36789step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36789step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36789 raw36789Labels = mixedMoment B node5099 node5099Labels := by
  calc
    mixedMoment B raw36789 raw36789Labels = mixedMoment B raw36789step0 raw36789step0Labels := by
      have hz : ∀ j, raw36789 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36789step0 = (fun i j => raw36789 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36789step0 raw36789; decide +kernel
      have hl : raw36789step0Labels = raw36789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36789 raw36789Labels permutation346 hz
    mixedMoment B raw36789step0 raw36789step0Labels = mixedMoment B raw36789step1 raw36789step1Labels := by
      have ha : raw36789step1 = (fun i j => raw36789step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36789step1 raw36789step0; decide +kernel
      have hl : raw36789step1Labels = raw36789step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36789step0 raw36789step0Labels permutation56 permutation2
    _ = mixedMoment B node5099 node5099Labels := by rfl

def raw36790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36790Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36790step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36790step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36790step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36790 raw36790Labels = mixedMoment B node5241 node5241Labels := by
  calc
    mixedMoment B raw36790 raw36790Labels = mixedMoment B raw36790step0 raw36790step0Labels := by
      have ha : raw36790step0 = (fun i j => raw36790 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36790step0 raw36790; decide +kernel
      have hl : raw36790step0Labels = raw36790Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36790 raw36790Labels permutation663 permutation7
    mixedMoment B raw36790step0 raw36790step0Labels = mixedMoment B raw36790step1 raw36790step1Labels := by
      have ha : raw36790step1 = raw36790step0 := by apply Matrix.ext; unfold raw36790step1 raw36790step0; decide +kernel
      have hl : raw36790step0Labels = labelEmbedding10 ∘ raw36790step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36790step0 raw36790step0Labels raw36790step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5241 node5241Labels := by rfl

def raw36791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36791Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36791step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36791step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 1, -3]]
def raw36791step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36791step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36791step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36791step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36791step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36791 raw36791Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw36791 raw36791Labels = mixedMoment B raw36791step0 raw36791step0Labels := by
      have hz : ∀ j, raw36791 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36791step0 = (fun i j => raw36791 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36791step0 raw36791; decide +kernel
      have hl : raw36791step0Labels = raw36791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36791 raw36791Labels permutation434 hz
    mixedMoment B raw36791step0 raw36791step0Labels = mixedMoment B raw36791step1 raw36791step1Labels := by
      have hz : ∀ j, raw36791step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36791step1 = (fun i j => raw36791step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36791step1 raw36791step0; decide +kernel
      have hl : raw36791step1Labels = raw36791step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36791step0 raw36791step0Labels permutation80 hz
    mixedMoment B raw36791step1 raw36791step1Labels = mixedMoment B raw36791step2 raw36791step2Labels := by
      have ha : raw36791step2 = (fun i j => raw36791step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36791step2 raw36791step1; decide +kernel
      have hl : raw36791step2Labels = raw36791step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36791step1 raw36791step1Labels permutation30 permutation7
    mixedMoment B raw36791step2 raw36791step2Labels = mixedMoment B raw36791step3 raw36791step3Labels := by
      have ha : raw36791step3 = raw36791step2 := by apply Matrix.ext; unfold raw36791step3 raw36791step2; decide +kernel
      have hl : raw36791step2Labels = labelEmbedding10 ∘ raw36791step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36791step2 raw36791step2Labels raw36791step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5274 node5274Labels := by rfl

def raw36792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw36792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36792step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36792step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 1, -3]]
def raw36792step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36792step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36792step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36792step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36792step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36792 raw36792Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw36792 raw36792Labels = mixedMoment B raw36792step0 raw36792step0Labels := by
      have hz : ∀ j, raw36792 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36792step0 = (fun i j => raw36792 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36792step0 raw36792; decide +kernel
      have hl : raw36792step0Labels = raw36792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36792 raw36792Labels permutation520 hz
    mixedMoment B raw36792step0 raw36792step0Labels = mixedMoment B raw36792step1 raw36792step1Labels := by
      have hz : ∀ j, raw36792step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36792step1 = (fun i j => raw36792step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36792step1 raw36792step0; decide +kernel
      have hl : raw36792step1Labels = raw36792step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36792step0 raw36792step0Labels permutation80 hz
    mixedMoment B raw36792step1 raw36792step1Labels = mixedMoment B raw36792step2 raw36792step2Labels := by
      have ha : raw36792step2 = (fun i j => raw36792step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36792step2 raw36792step1; decide +kernel
      have hl : raw36792step2Labels = raw36792step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36792step1 raw36792step1Labels permutation30 permutation7
    mixedMoment B raw36792step2 raw36792step2Labels = mixedMoment B raw36792step3 raw36792step3Labels := by
      have ha : raw36792step3 = raw36792step2 := by apply Matrix.ext; unfold raw36792step3 raw36792step2; decide +kernel
      have hl : raw36792step2Labels = labelEmbedding10 ∘ raw36792step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36792step2 raw36792step2Labels raw36792step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5274 node5274Labels := by rfl

def raw36793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw36793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw36793step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw36793step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36793step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw36793step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36793 raw36793Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw36793 raw36793Labels = mixedMoment B raw36793step0 raw36793step0Labels := by
      have hz : ∀ j, raw36793 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36793step0 = (fun i j => raw36793 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36793step0 raw36793; decide +kernel
      have hl : raw36793step0Labels = raw36793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36793 raw36793Labels permutation346 hz
    mixedMoment B raw36793step0 raw36793step0Labels = mixedMoment B raw36793step1 raw36793step1Labels := by
      have ha : raw36793step1 = (fun i j => raw36793step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36793step1 raw36793step0; decide +kernel
      have hl : raw36793step1Labels = raw36793step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36793step0 raw36793step0Labels permutation144 permutation6
    mixedMoment B raw36793step1 raw36793step1Labels = mixedMoment B raw36793step2 raw36793step2Labels := by
      have ha : raw36793step2 = raw36793step1 := by apply Matrix.ext; unfold raw36793step2 raw36793step1; decide +kernel
      have hl : raw36793step1Labels = labelEmbedding9 ∘ raw36793step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36793step1 raw36793step1Labels raw36793step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw36794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36794step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36794step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36794step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36794step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36794 raw36794Labels = mixedMoment B node5242 node5242Labels := by
  calc
    mixedMoment B raw36794 raw36794Labels = mixedMoment B raw36794step0 raw36794step0Labels := by
      have ha : raw36794step0 = (fun i j => raw36794 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36794step0 raw36794; decide +kernel
      have hl : raw36794step0Labels = raw36794Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36794 raw36794Labels permutation663 permutation7
    mixedMoment B raw36794step0 raw36794step0Labels = mixedMoment B raw36794step1 raw36794step1Labels := by
      have ha : raw36794step1 = raw36794step0 := by apply Matrix.ext; unfold raw36794step1 raw36794step0; decide +kernel
      have hl : raw36794step0Labels = labelEmbedding10 ∘ raw36794step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36794step0 raw36794step0Labels raw36794step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5242 node5242Labels := by rfl

def raw36795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw36795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36795step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36795step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 1, -3]]
def raw36795step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36795step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw36795step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36795step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw36795step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36795 raw36795Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw36795 raw36795Labels = mixedMoment B raw36795step0 raw36795step0Labels := by
      have hz : ∀ j, raw36795 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36795step0 = (fun i j => raw36795 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36795step0 raw36795; decide +kernel
      have hl : raw36795step0Labels = raw36795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36795 raw36795Labels permutation520 hz
    mixedMoment B raw36795step0 raw36795step0Labels = mixedMoment B raw36795step1 raw36795step1Labels := by
      have hz : ∀ j, raw36795step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36795step1 = (fun i j => raw36795step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36795step1 raw36795step0; decide +kernel
      have hl : raw36795step1Labels = raw36795step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36795step0 raw36795step0Labels permutation80 hz
    mixedMoment B raw36795step1 raw36795step1Labels = mixedMoment B raw36795step2 raw36795step2Labels := by
      have ha : raw36795step2 = (fun i j => raw36795step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36795step2 raw36795step1; decide +kernel
      have hl : raw36795step2Labels = raw36795step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36795step1 raw36795step1Labels permutation30 permutation7
    mixedMoment B raw36795step2 raw36795step2Labels = mixedMoment B raw36795step3 raw36795step3Labels := by
      have ha : raw36795step3 = raw36795step2 := by apply Matrix.ext; unfold raw36795step3 raw36795step2; decide +kernel
      have hl : raw36795step2Labels = labelEmbedding10 ∘ raw36795step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36795step2 raw36795step2Labels raw36795step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw36796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw36796Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw36796step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36796step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw36796step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36796step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw36796step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36796 raw36796Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw36796 raw36796Labels = mixedMoment B raw36796step0 raw36796step0Labels := by
      have hz : ∀ j, raw36796 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36796step0 = (fun i j => raw36796 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36796step0 raw36796; decide +kernel
      have hl : raw36796step0Labels = raw36796Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36796 raw36796Labels permutation346 hz
    mixedMoment B raw36796step0 raw36796step0Labels = mixedMoment B raw36796step1 raw36796step1Labels := by
      have ha : raw36796step1 = (fun i j => raw36796step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36796step1 raw36796step0; decide +kernel
      have hl : raw36796step1Labels = raw36796step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36796step0 raw36796step0Labels permutation144 permutation6
    mixedMoment B raw36796step1 raw36796step1Labels = mixedMoment B raw36796step2 raw36796step2Labels := by
      have ha : raw36796step2 = raw36796step1 := by apply Matrix.ext; unfold raw36796step2 raw36796step1; decide +kernel
      have hl : raw36796step1Labels = labelEmbedding9 ∘ raw36796step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36796step1 raw36796step1Labels raw36796step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5282 node5282Labels := by rfl

def raw36797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36797step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw36797step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36797step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw36797step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36797 raw36797Labels = mixedMoment B node4975 node4975Labels := by
  calc
    mixedMoment B raw36797 raw36797Labels = mixedMoment B raw36797step0 raw36797step0Labels := by
      have ha : raw36797step0 = (fun i j => raw36797 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36797step0 raw36797; decide +kernel
      have hl : raw36797step0Labels = raw36797Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36797 raw36797Labels permutation152 permutation3
    mixedMoment B raw36797step0 raw36797step0Labels = mixedMoment B raw36797step1 raw36797step1Labels := by
      have ha : raw36797step1 = raw36797step0 := by apply Matrix.ext; unfold raw36797step1 raw36797step0; decide +kernel
      have hl : raw36797step0Labels = labelEmbedding6 ∘ raw36797step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36797step0 raw36797step0Labels raw36797step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4975 node4975Labels := by rfl

def raw36798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36798Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36798step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36798 raw36798Labels = mixedMoment B node4938 node4938Labels := by
  calc
    mixedMoment B raw36798 raw36798Labels = mixedMoment B raw36798step0 raw36798step0Labels := by
      have ha : raw36798step0 = (fun i j => raw36798 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36798step0 raw36798; decide +kernel
      have hl : raw36798step0Labels = raw36798Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36798 raw36798Labels permutation265 permutation2
    _ = mixedMoment B node4938 node4938Labels := by rfl

def raw36799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36799Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36799step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36799step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36799step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36799 raw36799Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw36799 raw36799Labels = mixedMoment B raw36799step0 raw36799step0Labels := by
      have hz : ∀ j, raw36799 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36799step0 = (fun i j => raw36799 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36799step0 raw36799; decide +kernel
      have hl : raw36799step0Labels = raw36799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36799 raw36799Labels permutation434 hz
    mixedMoment B raw36799step0 raw36799step0Labels = mixedMoment B raw36799step1 raw36799step1Labels := by
      have ha : raw36799step1 = (fun i j => raw36799step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36799step1 raw36799step0; decide +kernel
      have hl : raw36799step1Labels = raw36799step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36799step0 raw36799step0Labels permutation144 permutation7
    mixedMoment B raw36799step1 raw36799step1Labels = mixedMoment B raw36799step2 raw36799step2Labels := by
      have ha : raw36799step2 = raw36799step1 := by apply Matrix.ext; unfold raw36799step2 raw36799step1; decide +kernel
      have hl : raw36799step1Labels = labelEmbedding10 ∘ raw36799step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36799step1 raw36799step1Labels raw36799step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5248 node5248Labels := by rfl

def raw36800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw36800Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36800step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36800step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36800step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36800step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36800 raw36800Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw36800 raw36800Labels = mixedMoment B raw36800step0 raw36800step0Labels := by
      have hz : ∀ j, raw36800 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36800step0 = (fun i j => raw36800 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36800step0 raw36800; decide +kernel
      have hl : raw36800step0Labels = raw36800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36800 raw36800Labels permutation520 hz
    mixedMoment B raw36800step0 raw36800step0Labels = mixedMoment B raw36800step1 raw36800step1Labels := by
      have ha : raw36800step1 = (fun i j => raw36800step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36800step1 raw36800step0; decide +kernel
      have hl : raw36800step1Labels = raw36800step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36800step0 raw36800step0Labels permutation144 permutation7
    mixedMoment B raw36800step1 raw36800step1Labels = mixedMoment B raw36800step2 raw36800step2Labels := by
      have ha : raw36800step2 = raw36800step1 := by apply Matrix.ext; unfold raw36800step2 raw36800step1; decide +kernel
      have hl : raw36800step1Labels = labelEmbedding10 ∘ raw36800step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36800step1 raw36800step1Labels raw36800step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5248 node5248Labels := by rfl

def raw36801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw36801Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw36801step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36801step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw36801step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36801 raw36801Labels = mixedMoment B node5277 node5277Labels := by
  calc
    mixedMoment B raw36801 raw36801Labels = mixedMoment B raw36801step0 raw36801step0Labels := by
      have ha : raw36801step0 = (fun i j => raw36801 (permutation639 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36801step0 raw36801; decide +kernel
      have hl : raw36801step0Labels = raw36801Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36801 raw36801Labels permutation639 permutation6
    mixedMoment B raw36801step0 raw36801step0Labels = mixedMoment B raw36801step1 raw36801step1Labels := by
      have ha : raw36801step1 = raw36801step0 := by apply Matrix.ext; unfold raw36801step1 raw36801step0; decide +kernel
      have hl : raw36801step0Labels = labelEmbedding9 ∘ raw36801step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36801step0 raw36801step0Labels raw36801step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5277 node5277Labels := by rfl

def raw36802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36802Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36802step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36802step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw36802step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36802step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw36802step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36802 raw36802Labels = mixedMoment B node4976 node4976Labels := by
  calc
    mixedMoment B raw36802 raw36802Labels = mixedMoment B raw36802step0 raw36802step0Labels := by
      have hz : ∀ j, raw36802 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36802step0 = (fun i j => raw36802 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36802step0 raw36802; decide +kernel
      have hl : raw36802step0Labels = raw36802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36802 raw36802Labels permutation346 hz
    mixedMoment B raw36802step0 raw36802step0Labels = mixedMoment B raw36802step1 raw36802step1Labels := by
      have ha : raw36802step1 = (fun i j => raw36802step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36802step1 raw36802step0; decide +kernel
      have hl : raw36802step1Labels = raw36802step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36802step0 raw36802step0Labels permutation35 permutation3
    mixedMoment B raw36802step1 raw36802step1Labels = mixedMoment B raw36802step2 raw36802step2Labels := by
      have ha : raw36802step2 = raw36802step1 := by apply Matrix.ext; unfold raw36802step2 raw36802step1; decide +kernel
      have hl : raw36802step1Labels = labelEmbedding6 ∘ raw36802step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36802step1 raw36802step1Labels raw36802step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4976 node4976Labels := by rfl

def raw36803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36803Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36803step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36803step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36803step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36803 raw36803Labels = mixedMoment B node4945 node4945Labels := by
  calc
    mixedMoment B raw36803 raw36803Labels = mixedMoment B raw36803step0 raw36803step0Labels := by
      have hz : ∀ j, raw36803 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36803step0 = (fun i j => raw36803 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36803step0 raw36803; decide +kernel
      have hl : raw36803step0Labels = raw36803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36803 raw36803Labels permutation346 hz
    mixedMoment B raw36803step0 raw36803step0Labels = mixedMoment B raw36803step1 raw36803step1Labels := by
      have ha : raw36803step1 = (fun i j => raw36803step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36803step1 raw36803step0; decide +kernel
      have hl : raw36803step1Labels = raw36803step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36803step0 raw36803step0Labels permutation58 permutation2
    _ = mixedMoment B node4945 node4945Labels := by rfl

def raw36804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36804Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36804step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36804step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36804step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36804step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36804 raw36804Labels = mixedMoment B node5215 node5215Labels := by
  calc
    mixedMoment B raw36804 raw36804Labels = mixedMoment B raw36804step0 raw36804step0Labels := by
      have ha : raw36804step0 = (fun i j => raw36804 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36804step0 raw36804; decide +kernel
      have hl : raw36804step0Labels = raw36804Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36804 raw36804Labels permutation663 permutation7
    mixedMoment B raw36804step0 raw36804step0Labels = mixedMoment B raw36804step1 raw36804step1Labels := by
      have ha : raw36804step1 = raw36804step0 := by apply Matrix.ext; unfold raw36804step1 raw36804step0; decide +kernel
      have hl : raw36804step0Labels = labelEmbedding10 ∘ raw36804step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36804step0 raw36804step0Labels raw36804step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5215 node5215Labels := by rfl

def raw36805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 1, -3]]
def raw36805Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36805step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36805step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, -2, 0], ![2, 1, -3]]
def raw36805step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36805step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36805step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36805step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36805step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36805 raw36805Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw36805 raw36805Labels = mixedMoment B raw36805step0 raw36805step0Labels := by
      have hz : ∀ j, raw36805 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36805step0 = (fun i j => raw36805 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36805step0 raw36805; decide +kernel
      have hl : raw36805step0Labels = raw36805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36805 raw36805Labels permutation520 hz
    mixedMoment B raw36805step0 raw36805step0Labels = mixedMoment B raw36805step1 raw36805step1Labels := by
      have hz : ∀ j, raw36805step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36805step1 = (fun i j => raw36805step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36805step1 raw36805step0; decide +kernel
      have hl : raw36805step1Labels = raw36805step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36805step0 raw36805step0Labels permutation80 hz
    mixedMoment B raw36805step1 raw36805step1Labels = mixedMoment B raw36805step2 raw36805step2Labels := by
      have ha : raw36805step2 = (fun i j => raw36805step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36805step2 raw36805step1; decide +kernel
      have hl : raw36805step2Labels = raw36805step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36805step1 raw36805step1Labels permutation30 permutation7
    mixedMoment B raw36805step2 raw36805step2Labels = mixedMoment B raw36805step3 raw36805step3Labels := by
      have ha : raw36805step3 = raw36805step2 := by apply Matrix.ext; unfold raw36805step3 raw36805step2; decide +kernel
      have hl : raw36805step2Labels = labelEmbedding10 ∘ raw36805step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36805step2 raw36805step2Labels raw36805step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5238 node5238Labels := by rfl

def raw36806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw36806Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw36806step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw36806step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36806step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw36806step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36806 raw36806Labels = mixedMoment B node5287 node5287Labels := by
  calc
    mixedMoment B raw36806 raw36806Labels = mixedMoment B raw36806step0 raw36806step0Labels := by
      have hz : ∀ j, raw36806 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36806step0 = (fun i j => raw36806 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36806step0 raw36806; decide +kernel
      have hl : raw36806step0Labels = raw36806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36806 raw36806Labels permutation346 hz
    mixedMoment B raw36806step0 raw36806step0Labels = mixedMoment B raw36806step1 raw36806step1Labels := by
      have ha : raw36806step1 = (fun i j => raw36806step0 (permutation150 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36806step1 raw36806step0; decide +kernel
      have hl : raw36806step1Labels = raw36806step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36806step0 raw36806step0Labels permutation150 permutation6
    mixedMoment B raw36806step1 raw36806step1Labels = mixedMoment B raw36806step2 raw36806step2Labels := by
      have ha : raw36806step2 = raw36806step1 := by apply Matrix.ext; unfold raw36806step2 raw36806step1; decide +kernel
      have hl : raw36806step1Labels = labelEmbedding9 ∘ raw36806step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36806step1 raw36806step1Labels raw36806step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5287 node5287Labels := by rfl

def raw36807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36807Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36807step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36807step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw36807step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36807step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw36807step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36807 raw36807Labels = mixedMoment B node4976 node4976Labels := by
  calc
    mixedMoment B raw36807 raw36807Labels = mixedMoment B raw36807step0 raw36807step0Labels := by
      have hz : ∀ j, raw36807 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36807step0 = (fun i j => raw36807 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36807step0 raw36807; decide +kernel
      have hl : raw36807step0Labels = raw36807Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36807 raw36807Labels permutation346 hz
    mixedMoment B raw36807step0 raw36807step0Labels = mixedMoment B raw36807step1 raw36807step1Labels := by
      have ha : raw36807step1 = (fun i j => raw36807step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36807step1 raw36807step0; decide +kernel
      have hl : raw36807step1Labels = raw36807step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36807step0 raw36807step0Labels permutation33 permutation3
    mixedMoment B raw36807step1 raw36807step1Labels = mixedMoment B raw36807step2 raw36807step2Labels := by
      have ha : raw36807step2 = raw36807step1 := by apply Matrix.ext; unfold raw36807step2 raw36807step1; decide +kernel
      have hl : raw36807step1Labels = labelEmbedding6 ∘ raw36807step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36807step1 raw36807step1Labels raw36807step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4976 node4976Labels := by rfl

def raw36808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36808Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36808step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36808step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36808 raw36808Labels = mixedMoment B node4945 node4945Labels := by
  calc
    mixedMoment B raw36808 raw36808Labels = mixedMoment B raw36808step0 raw36808step0Labels := by
      have hz : ∀ j, raw36808 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36808step0 = (fun i j => raw36808 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36808step0 raw36808; decide +kernel
      have hl : raw36808step0Labels = raw36808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36808 raw36808Labels permutation346 hz
    mixedMoment B raw36808step0 raw36808step0Labels = mixedMoment B raw36808step1 raw36808step1Labels := by
      have ha : raw36808step1 = (fun i j => raw36808step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36808step1 raw36808step0; decide +kernel
      have hl : raw36808step1Labels = raw36808step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36808step0 raw36808step0Labels permutation56 permutation2
    _ = mixedMoment B node4945 node4945Labels := by rfl

def raw36809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36809Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36809step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36809step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36809step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36809step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36809 raw36809Labels = mixedMoment B node5215 node5215Labels := by
  calc
    mixedMoment B raw36809 raw36809Labels = mixedMoment B raw36809step0 raw36809step0Labels := by
      have ha : raw36809step0 = (fun i j => raw36809 (permutation687 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36809step0 raw36809; decide +kernel
      have hl : raw36809step0Labels = raw36809Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36809 raw36809Labels permutation687 permutation7
    mixedMoment B raw36809step0 raw36809step0Labels = mixedMoment B raw36809step1 raw36809step1Labels := by
      have ha : raw36809step1 = raw36809step0 := by apply Matrix.ext; unfold raw36809step1 raw36809step0; decide +kernel
      have hl : raw36809step0Labels = labelEmbedding10 ∘ raw36809step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36809step0 raw36809step0Labels raw36809step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5215 node5215Labels := by rfl

def raw36810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36810Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36810step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36810step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, -2, 0], ![2, 1, -3]]
def raw36810step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36810step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36810step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36810step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36810step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36810 raw36810Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw36810 raw36810Labels = mixedMoment B raw36810step0 raw36810step0Labels := by
      have hz : ∀ j, raw36810 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36810step0 = (fun i j => raw36810 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36810step0 raw36810; decide +kernel
      have hl : raw36810step0Labels = raw36810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36810 raw36810Labels permutation434 hz
    mixedMoment B raw36810step0 raw36810step0Labels = mixedMoment B raw36810step1 raw36810step1Labels := by
      have hz : ∀ j, raw36810step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36810step1 = (fun i j => raw36810step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36810step1 raw36810step0; decide +kernel
      have hl : raw36810step1Labels = raw36810step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36810step0 raw36810step0Labels permutation80 hz
    mixedMoment B raw36810step1 raw36810step1Labels = mixedMoment B raw36810step2 raw36810step2Labels := by
      have ha : raw36810step2 = (fun i j => raw36810step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36810step2 raw36810step1; decide +kernel
      have hl : raw36810step2Labels = raw36810step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36810step1 raw36810step1Labels permutation30 permutation7
    mixedMoment B raw36810step2 raw36810step2Labels = mixedMoment B raw36810step3 raw36810step3Labels := by
      have ha : raw36810step3 = raw36810step2 := by apply Matrix.ext; unfold raw36810step3 raw36810step2; decide +kernel
      have hl : raw36810step2Labels = labelEmbedding10 ∘ raw36810step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36810step2 raw36810step2Labels raw36810step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5238 node5238Labels := by rfl

def raw36811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw36811Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw36811step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw36811step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36811step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw36811step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36811 raw36811Labels = mixedMoment B node5287 node5287Labels := by
  calc
    mixedMoment B raw36811 raw36811Labels = mixedMoment B raw36811step0 raw36811step0Labels := by
      have hz : ∀ j, raw36811 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36811step0 = (fun i j => raw36811 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36811step0 raw36811; decide +kernel
      have hl : raw36811step0Labels = raw36811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36811 raw36811Labels permutation346 hz
    mixedMoment B raw36811step0 raw36811step0Labels = mixedMoment B raw36811step1 raw36811step1Labels := by
      have ha : raw36811step1 = (fun i j => raw36811step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36811step1 raw36811step0; decide +kernel
      have hl : raw36811step1Labels = raw36811step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36811step0 raw36811step0Labels permutation144 permutation6
    mixedMoment B raw36811step1 raw36811step1Labels = mixedMoment B raw36811step2 raw36811step2Labels := by
      have ha : raw36811step2 = raw36811step1 := by apply Matrix.ext; unfold raw36811step2 raw36811step1; decide +kernel
      have hl : raw36811step1Labels = labelEmbedding9 ∘ raw36811step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36811step1 raw36811step1Labels raw36811step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5287 node5287Labels := by rfl

def raw36812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw36812Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw36812step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw36812step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36812step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw36812step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36812 raw36812Labels = mixedMoment B node4769 node4769Labels := by
  calc
    mixedMoment B raw36812 raw36812Labels = mixedMoment B raw36812step0 raw36812step0Labels := by
      have hz : ∀ j, raw36812 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36812step0 = (fun i j => raw36812 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36812step0 raw36812; decide +kernel
      have hl : raw36812step0Labels = raw36812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36812 raw36812Labels permutation346 hz
    mixedMoment B raw36812step0 raw36812step0Labels = mixedMoment B raw36812step1 raw36812step1Labels := by
      have ha : raw36812step1 = (fun i j => raw36812step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36812step1 raw36812step0; decide +kernel
      have hl : raw36812step1Labels = raw36812step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36812step0 raw36812step0Labels permutation144 permutation2
    mixedMoment B raw36812step1 raw36812step1Labels = mixedMoment B raw36812step2 raw36812step2Labels := by
      have ha : raw36812step2 = -raw36812step1 := by apply Matrix.ext; change ∀ i j, raw36812step2 i j = -(raw36812step1 i j); unfold raw36812step2 raw36812step1; decide +kernel
      have hl : raw36812step2Labels = raw36812step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4769 node4769Labels := by rfl

def raw36813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw36813Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36813step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw36813step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36813step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36813step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36813 raw36813Labels = mixedMoment B node4763 node4763Labels := by
  calc
    mixedMoment B raw36813 raw36813Labels = mixedMoment B raw36813step0 raw36813step0Labels := by
      have ha : raw36813step0 = (fun i j => raw36813 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36813step0 raw36813; decide +kernel
      have hl : raw36813step0Labels = raw36813Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36813 raw36813Labels permutation663 permutation2
    mixedMoment B raw36813step0 raw36813step0Labels = mixedMoment B raw36813step1 raw36813step1Labels := by
      have ha : raw36813step1 = -raw36813step0 := by apply Matrix.ext; change ∀ i j, raw36813step1 i j = -(raw36813step0 i j); unfold raw36813step1 raw36813step0; decide +kernel
      have hl : raw36813step1Labels = raw36813step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4763 node4763Labels := by rfl

def raw36814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw36814Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw36814step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36814step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![3, 0, -3]]
def raw36814step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36814step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw36814step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36814step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36814step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36814 raw36814Labels = mixedMoment B node4846 node4846Labels := by
  calc
    mixedMoment B raw36814 raw36814Labels = mixedMoment B raw36814step0 raw36814step0Labels := by
      have hz : ∀ j, raw36814 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36814step0 = (fun i j => raw36814 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36814step0 raw36814; decide +kernel
      have hl : raw36814step0Labels = raw36814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36814 raw36814Labels permutation520 hz
    mixedMoment B raw36814step0 raw36814step0Labels = mixedMoment B raw36814step1 raw36814step1Labels := by
      have hz : ∀ j, raw36814step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36814step1 = (fun i j => raw36814step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36814step1 raw36814step0; decide +kernel
      have hl : raw36814step1Labels = raw36814step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36814step0 raw36814step0Labels permutation80 hz
    mixedMoment B raw36814step1 raw36814step1Labels = mixedMoment B raw36814step2 raw36814step2Labels := by
      have ha : raw36814step2 = (fun i j => raw36814step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36814step2 raw36814step1; decide +kernel
      have hl : raw36814step2Labels = raw36814step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36814step1 raw36814step1Labels permutation30 permutation2
    mixedMoment B raw36814step2 raw36814step2Labels = mixedMoment B raw36814step3 raw36814step3Labels := by
      have ha : raw36814step3 = -raw36814step2 := by apply Matrix.ext; change ∀ i j, raw36814step3 i j = -(raw36814step2 i j); unfold raw36814step3 raw36814step2; decide +kernel
      have hl : raw36814step3Labels = raw36814step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4846 node4846Labels := by rfl

def raw36815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36815Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36815step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw36815step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36815step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw36815step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36815 raw36815Labels = mixedMoment B node2704 node2704Labels := by
  calc
    mixedMoment B raw36815 raw36815Labels = mixedMoment B raw36815step0 raw36815step0Labels := by
      have hz : ∀ j, raw36815 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36815step0 = (fun i j => raw36815 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36815step0 raw36815; decide +kernel
      have hl : raw36815step0Labels = raw36815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36815 raw36815Labels permutation346 hz
    mixedMoment B raw36815step0 raw36815step0Labels = mixedMoment B raw36815step1 raw36815step1Labels := by
      have ha : raw36815step1 = (fun i j => raw36815step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36815step1 raw36815step0; decide +kernel
      have hl : raw36815step1Labels = raw36815step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36815step0 raw36815step0Labels permutation144 permutation7
    mixedMoment B raw36815step1 raw36815step1Labels = mixedMoment B raw36815step2 raw36815step2Labels := by
      have ha : raw36815step2 = raw36815step1 := by apply Matrix.ext; unfold raw36815step2 raw36815step1; decide +kernel
      have hl : raw36815step1Labels = labelEmbedding1 ∘ raw36815step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36815step1 raw36815step1Labels raw36815step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2704 node2704Labels := by rfl

def raw36816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36816Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36816step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36816step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36816step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36816step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36816 raw36816Labels = mixedMoment B node2694 node2694Labels := by
  calc
    mixedMoment B raw36816 raw36816Labels = mixedMoment B raw36816step0 raw36816step0Labels := by
      have ha : raw36816step0 = (fun i j => raw36816 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36816step0 raw36816; decide +kernel
      have hl : raw36816step0Labels = raw36816Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36816 raw36816Labels permutation663 permutation7
    mixedMoment B raw36816step0 raw36816step0Labels = mixedMoment B raw36816step1 raw36816step1Labels := by
      have ha : raw36816step1 = raw36816step0 := by apply Matrix.ext; unfold raw36816step1 raw36816step0; decide +kernel
      have hl : raw36816step0Labels = labelEmbedding1 ∘ raw36816step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36816step0 raw36816step0Labels raw36816step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2694 node2694Labels := by rfl

def raw36817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36817Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36817step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36817step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 1, -3]]
def raw36817step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36817step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36817step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36817step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36817step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36817 raw36817Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw36817 raw36817Labels = mixedMoment B raw36817step0 raw36817step0Labels := by
      have hz : ∀ j, raw36817 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36817step0 = (fun i j => raw36817 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36817step0 raw36817; decide +kernel
      have hl : raw36817step0Labels = raw36817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36817 raw36817Labels permutation434 hz
    mixedMoment B raw36817step0 raw36817step0Labels = mixedMoment B raw36817step1 raw36817step1Labels := by
      have hz : ∀ j, raw36817step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36817step1 = (fun i j => raw36817step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36817step1 raw36817step0; decide +kernel
      have hl : raw36817step1Labels = raw36817step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36817step0 raw36817step0Labels permutation80 hz
    mixedMoment B raw36817step1 raw36817step1Labels = mixedMoment B raw36817step2 raw36817step2Labels := by
      have ha : raw36817step2 = (fun i j => raw36817step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36817step2 raw36817step1; decide +kernel
      have hl : raw36817step2Labels = raw36817step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36817step1 raw36817step1Labels permutation30 permutation7
    mixedMoment B raw36817step2 raw36817step2Labels = mixedMoment B raw36817step3 raw36817step3Labels := by
      have ha : raw36817step3 = raw36817step2 := by apply Matrix.ext; unfold raw36817step3 raw36817step2; decide +kernel
      have hl : raw36817step2Labels = labelEmbedding1 ∘ raw36817step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36817step2 raw36817step2Labels raw36817step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2742 node2742Labels := by rfl

def raw36818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw36818Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36818step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36818step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 1, -3]]
def raw36818step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36818step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36818step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36818step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36818step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36818 raw36818Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw36818 raw36818Labels = mixedMoment B raw36818step0 raw36818step0Labels := by
      have hz : ∀ j, raw36818 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36818step0 = (fun i j => raw36818 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36818step0 raw36818; decide +kernel
      have hl : raw36818step0Labels = raw36818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36818 raw36818Labels permutation520 hz
    mixedMoment B raw36818step0 raw36818step0Labels = mixedMoment B raw36818step1 raw36818step1Labels := by
      have hz : ∀ j, raw36818step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36818step1 = (fun i j => raw36818step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36818step1 raw36818step0; decide +kernel
      have hl : raw36818step1Labels = raw36818step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36818step0 raw36818step0Labels permutation80 hz
    mixedMoment B raw36818step1 raw36818step1Labels = mixedMoment B raw36818step2 raw36818step2Labels := by
      have ha : raw36818step2 = (fun i j => raw36818step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36818step2 raw36818step1; decide +kernel
      have hl : raw36818step2Labels = raw36818step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36818step1 raw36818step1Labels permutation30 permutation7
    mixedMoment B raw36818step2 raw36818step2Labels = mixedMoment B raw36818step3 raw36818step3Labels := by
      have ha : raw36818step3 = raw36818step2 := by apply Matrix.ext; unfold raw36818step3 raw36818step2; decide +kernel
      have hl : raw36818step2Labels = labelEmbedding1 ∘ raw36818step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36818step2 raw36818step2Labels raw36818step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2742 node2742Labels := by rfl

def raw36819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw36819Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw36819step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36819step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36819step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36819step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36819 raw36819Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw36819 raw36819Labels = mixedMoment B raw36819step0 raw36819step0Labels := by
      have hz : ∀ j, raw36819 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36819step0 = (fun i j => raw36819 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36819step0 raw36819; decide +kernel
      have hl : raw36819step0Labels = raw36819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36819 raw36819Labels permutation346 hz
    mixedMoment B raw36819step0 raw36819step0Labels = mixedMoment B raw36819step1 raw36819step1Labels := by
      have ha : raw36819step1 = (fun i j => raw36819step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36819step1 raw36819step0; decide +kernel
      have hl : raw36819step1Labels = raw36819step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36819step0 raw36819step0Labels permutation144 permutation7
    mixedMoment B raw36819step1 raw36819step1Labels = mixedMoment B raw36819step2 raw36819step2Labels := by
      have ha : raw36819step2 = raw36819step1 := by apply Matrix.ext; unfold raw36819step2 raw36819step1; decide +kernel
      have hl : raw36819step1Labels = labelEmbedding1 ∘ raw36819step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36819step1 raw36819step1Labels raw36819step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3077 node3077Labels := by rfl

def raw36820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36820Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36820step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36820step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36820step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36820step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36820 raw36820Labels = mixedMoment B node2695 node2695Labels := by
  calc
    mixedMoment B raw36820 raw36820Labels = mixedMoment B raw36820step0 raw36820step0Labels := by
      have ha : raw36820step0 = (fun i j => raw36820 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36820step0 raw36820; decide +kernel
      have hl : raw36820step0Labels = raw36820Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36820 raw36820Labels permutation663 permutation7
    mixedMoment B raw36820step0 raw36820step0Labels = mixedMoment B raw36820step1 raw36820step1Labels := by
      have ha : raw36820step1 = raw36820step0 := by apply Matrix.ext; unfold raw36820step1 raw36820step0; decide +kernel
      have hl : raw36820step0Labels = labelEmbedding1 ∘ raw36820step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36820step0 raw36820step0Labels raw36820step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2695 node2695Labels := by rfl

def raw36821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw36821Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36821step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36821step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 1, -3]]
def raw36821step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36821step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw36821step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36821step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw36821step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36821 raw36821Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw36821 raw36821Labels = mixedMoment B raw36821step0 raw36821step0Labels := by
      have hz : ∀ j, raw36821 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36821step0 = (fun i j => raw36821 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36821step0 raw36821; decide +kernel
      have hl : raw36821step0Labels = raw36821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36821 raw36821Labels permutation520 hz
    mixedMoment B raw36821step0 raw36821step0Labels = mixedMoment B raw36821step1 raw36821step1Labels := by
      have hz : ∀ j, raw36821step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36821step1 = (fun i j => raw36821step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36821step1 raw36821step0; decide +kernel
      have hl : raw36821step1Labels = raw36821step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36821step0 raw36821step0Labels permutation80 hz
    mixedMoment B raw36821step1 raw36821step1Labels = mixedMoment B raw36821step2 raw36821step2Labels := by
      have ha : raw36821step2 = (fun i j => raw36821step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36821step2 raw36821step1; decide +kernel
      have hl : raw36821step2Labels = raw36821step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36821step1 raw36821step1Labels permutation30 permutation7
    mixedMoment B raw36821step2 raw36821step2Labels = mixedMoment B raw36821step3 raw36821step3Labels := by
      have ha : raw36821step3 = raw36821step2 := by apply Matrix.ext; unfold raw36821step3 raw36821step2; decide +kernel
      have hl : raw36821step2Labels = labelEmbedding1 ∘ raw36821step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36821step2 raw36821step2Labels raw36821step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2743 node2743Labels := by rfl

def raw36822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw36822Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw36822step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36822step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw36822step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36822step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw36822step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36822 raw36822Labels = mixedMoment B node3078 node3078Labels := by
  calc
    mixedMoment B raw36822 raw36822Labels = mixedMoment B raw36822step0 raw36822step0Labels := by
      have hz : ∀ j, raw36822 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36822step0 = (fun i j => raw36822 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36822step0 raw36822; decide +kernel
      have hl : raw36822step0Labels = raw36822Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36822 raw36822Labels permutation346 hz
    mixedMoment B raw36822step0 raw36822step0Labels = mixedMoment B raw36822step1 raw36822step1Labels := by
      have ha : raw36822step1 = (fun i j => raw36822step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36822step1 raw36822step0; decide +kernel
      have hl : raw36822step1Labels = raw36822step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36822step0 raw36822step0Labels permutation144 permutation7
    mixedMoment B raw36822step1 raw36822step1Labels = mixedMoment B raw36822step2 raw36822step2Labels := by
      have ha : raw36822step2 = raw36822step1 := by apply Matrix.ext; unfold raw36822step2 raw36822step1; decide +kernel
      have hl : raw36822step1Labels = labelEmbedding1 ∘ raw36822step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36822step1 raw36822step1Labels raw36822step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3078 node3078Labels := by rfl

def raw36823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36823Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw36823step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36823step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw36823step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36823 raw36823Labels = mixedMoment B node2690 node2690Labels := by
  calc
    mixedMoment B raw36823 raw36823Labels = mixedMoment B raw36823step0 raw36823step0Labels := by
      have ha : raw36823step0 = (fun i j => raw36823 (permutation639 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36823step0 raw36823; decide +kernel
      have hl : raw36823step0Labels = raw36823Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36823 raw36823Labels permutation639 permutation7
    mixedMoment B raw36823step0 raw36823step0Labels = mixedMoment B raw36823step1 raw36823step1Labels := by
      have ha : raw36823step1 = raw36823step0 := by apply Matrix.ext; unfold raw36823step1 raw36823step0; decide +kernel
      have hl : raw36823step0Labels = labelEmbedding1 ∘ raw36823step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36823step0 raw36823step0Labels raw36823step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2690 node2690Labels := by rfl

def raw36824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36824Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36824step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw36824step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36824step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw36824step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36824 raw36824Labels = mixedMoment B node2689 node2689Labels := by
  calc
    mixedMoment B raw36824 raw36824Labels = mixedMoment B raw36824step0 raw36824step0Labels := by
      have ha : raw36824step0 = (fun i j => raw36824 (permutation639 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36824step0 raw36824; decide +kernel
      have hl : raw36824step0Labels = raw36824Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36824 raw36824Labels permutation639 permutation7
    mixedMoment B raw36824step0 raw36824step0Labels = mixedMoment B raw36824step1 raw36824step1Labels := by
      have ha : raw36824step1 = raw36824step0 := by apply Matrix.ext; unfold raw36824step1 raw36824step0; decide +kernel
      have hl : raw36824step0Labels = labelEmbedding1 ∘ raw36824step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36824step0 raw36824step0Labels raw36824step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2689 node2689Labels := by rfl

def raw36825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36825Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36825step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36825step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36825step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36825step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36825 raw36825Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw36825 raw36825Labels = mixedMoment B raw36825step0 raw36825step0Labels := by
      have hz : ∀ j, raw36825 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36825step0 = (fun i j => raw36825 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36825step0 raw36825; decide +kernel
      have hl : raw36825step0Labels = raw36825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36825 raw36825Labels permutation434 hz
    mixedMoment B raw36825step0 raw36825step0Labels = mixedMoment B raw36825step1 raw36825step1Labels := by
      have ha : raw36825step1 = (fun i j => raw36825step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36825step1 raw36825step0; decide +kernel
      have hl : raw36825step1Labels = raw36825step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36825step0 raw36825step0Labels permutation144 permutation7
    mixedMoment B raw36825step1 raw36825step1Labels = mixedMoment B raw36825step2 raw36825step2Labels := by
      have ha : raw36825step2 = raw36825step1 := by apply Matrix.ext; unfold raw36825step2 raw36825step1; decide +kernel
      have hl : raw36825step1Labels = labelEmbedding1 ∘ raw36825step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36825step1 raw36825step1Labels raw36825step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2705 node2705Labels := by rfl

def raw36826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw36826Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36826step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36826step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36826step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36826step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36826step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36826 raw36826Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw36826 raw36826Labels = mixedMoment B raw36826step0 raw36826step0Labels := by
      have hz : ∀ j, raw36826 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36826step0 = (fun i j => raw36826 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36826step0 raw36826; decide +kernel
      have hl : raw36826step0Labels = raw36826Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36826 raw36826Labels permutation520 hz
    mixedMoment B raw36826step0 raw36826step0Labels = mixedMoment B raw36826step1 raw36826step1Labels := by
      have ha : raw36826step1 = (fun i j => raw36826step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36826step1 raw36826step0; decide +kernel
      have hl : raw36826step1Labels = raw36826step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36826step0 raw36826step0Labels permutation144 permutation7
    mixedMoment B raw36826step1 raw36826step1Labels = mixedMoment B raw36826step2 raw36826step2Labels := by
      have ha : raw36826step2 = raw36826step1 := by apply Matrix.ext; unfold raw36826step2 raw36826step1; decide +kernel
      have hl : raw36826step1Labels = labelEmbedding1 ∘ raw36826step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36826step1 raw36826step1Labels raw36826step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2705 node2705Labels := by rfl

def raw36827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw36827Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36827step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36827step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36827step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36827step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36827 raw36827Labels = mixedMoment B node3059 node3059Labels := by
  calc
    mixedMoment B raw36827 raw36827Labels = mixedMoment B raw36827step0 raw36827step0Labels := by
      have ha : raw36827step0 = (fun i j => raw36827 (permutation639 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36827step0 raw36827; decide +kernel
      have hl : raw36827step0Labels = raw36827Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36827 raw36827Labels permutation639 permutation7
    mixedMoment B raw36827step0 raw36827step0Labels = mixedMoment B raw36827step1 raw36827step1Labels := by
      have ha : raw36827step1 = raw36827step0 := by apply Matrix.ext; unfold raw36827step1 raw36827step0; decide +kernel
      have hl : raw36827step0Labels = labelEmbedding1 ∘ raw36827step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36827step0 raw36827step0Labels raw36827step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3059 node3059Labels := by rfl

def raw36828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36828Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36828step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw36828step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36828step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw36828step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36828 raw36828Labels = mixedMoment B node2659 node2659Labels := by
  calc
    mixedMoment B raw36828 raw36828Labels = mixedMoment B raw36828step0 raw36828step0Labels := by
      have hz : ∀ j, raw36828 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36828step0 = (fun i j => raw36828 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36828step0 raw36828; decide +kernel
      have hl : raw36828step0Labels = raw36828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36828 raw36828Labels permutation346 hz
    mixedMoment B raw36828step0 raw36828step0Labels = mixedMoment B raw36828step1 raw36828step1Labels := by
      have ha : raw36828step1 = (fun i j => raw36828step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36828step1 raw36828step0; decide +kernel
      have hl : raw36828step1Labels = raw36828step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36828step0 raw36828step0Labels permutation144 permutation7
    mixedMoment B raw36828step1 raw36828step1Labels = mixedMoment B raw36828step2 raw36828step2Labels := by
      have ha : raw36828step2 = raw36828step1 := by apply Matrix.ext; unfold raw36828step2 raw36828step1; decide +kernel
      have hl : raw36828step1Labels = labelEmbedding1 ∘ raw36828step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36828step1 raw36828step1Labels raw36828step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2659 node2659Labels := by rfl

def raw36829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36829Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36829step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36829step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw36829step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36829step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw36829step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36829 raw36829Labels = mixedMoment B node2658 node2658Labels := by
  calc
    mixedMoment B raw36829 raw36829Labels = mixedMoment B raw36829step0 raw36829step0Labels := by
      have hz : ∀ j, raw36829 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36829step0 = (fun i j => raw36829 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36829step0 raw36829; decide +kernel
      have hl : raw36829step0Labels = raw36829Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36829 raw36829Labels permutation346 hz
    mixedMoment B raw36829step0 raw36829step0Labels = mixedMoment B raw36829step1 raw36829step1Labels := by
      have ha : raw36829step1 = (fun i j => raw36829step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36829step1 raw36829step0; decide +kernel
      have hl : raw36829step1Labels = raw36829step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36829step0 raw36829step0Labels permutation144 permutation7
    mixedMoment B raw36829step1 raw36829step1Labels = mixedMoment B raw36829step2 raw36829step2Labels := by
      have ha : raw36829step2 = raw36829step1 := by apply Matrix.ext; unfold raw36829step2 raw36829step1; decide +kernel
      have hl : raw36829step1Labels = labelEmbedding1 ∘ raw36829step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36829step1 raw36829step1Labels raw36829step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2658 node2658Labels := by rfl

def raw36830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36830Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36830step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36830step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36830step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36830step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36830 raw36830Labels = mixedMoment B node2653 node2653Labels := by
  calc
    mixedMoment B raw36830 raw36830Labels = mixedMoment B raw36830step0 raw36830step0Labels := by
      have ha : raw36830step0 = (fun i j => raw36830 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36830step0 raw36830; decide +kernel
      have hl : raw36830step0Labels = raw36830Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36830 raw36830Labels permutation663 permutation7
    mixedMoment B raw36830step0 raw36830step0Labels = mixedMoment B raw36830step1 raw36830step1Labels := by
      have ha : raw36830step1 = raw36830step0 := by apply Matrix.ext; unfold raw36830step1 raw36830step0; decide +kernel
      have hl : raw36830step0Labels = labelEmbedding1 ∘ raw36830step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36830step0 raw36830step0Labels raw36830step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2653 node2653Labels := by rfl

def raw36831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 1, -3]]
def raw36831Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36831step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36831step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, -2, 0], ![2, 1, -3]]
def raw36831step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36831step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36831step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36831step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36831step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36831 raw36831Labels = mixedMoment B node2686 node2686Labels := by
  calc
    mixedMoment B raw36831 raw36831Labels = mixedMoment B raw36831step0 raw36831step0Labels := by
      have hz : ∀ j, raw36831 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36831step0 = (fun i j => raw36831 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36831step0 raw36831; decide +kernel
      have hl : raw36831step0Labels = raw36831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36831 raw36831Labels permutation520 hz
    mixedMoment B raw36831step0 raw36831step0Labels = mixedMoment B raw36831step1 raw36831step1Labels := by
      have hz : ∀ j, raw36831step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36831step1 = (fun i j => raw36831step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36831step1 raw36831step0; decide +kernel
      have hl : raw36831step1Labels = raw36831step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36831step0 raw36831step0Labels permutation80 hz
    mixedMoment B raw36831step1 raw36831step1Labels = mixedMoment B raw36831step2 raw36831step2Labels := by
      have ha : raw36831step2 = (fun i j => raw36831step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36831step2 raw36831step1; decide +kernel
      have hl : raw36831step2Labels = raw36831step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36831step1 raw36831step1Labels permutation30 permutation7
    mixedMoment B raw36831step2 raw36831step2Labels = mixedMoment B raw36831step3 raw36831step3Labels := by
      have ha : raw36831step3 = raw36831step2 := by apply Matrix.ext; unfold raw36831step3 raw36831step2; decide +kernel
      have hl : raw36831step2Labels = labelEmbedding1 ∘ raw36831step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36831step2 raw36831step2Labels raw36831step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2686 node2686Labels := by rfl

def raw36832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw36832Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw36832step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36832step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36832step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36832step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36832step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36832 raw36832Labels = mixedMoment B node3025 node3025Labels := by
  calc
    mixedMoment B raw36832 raw36832Labels = mixedMoment B raw36832step0 raw36832step0Labels := by
      have hz : ∀ j, raw36832 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36832step0 = (fun i j => raw36832 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36832step0 raw36832; decide +kernel
      have hl : raw36832step0Labels = raw36832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36832 raw36832Labels permutation346 hz
    mixedMoment B raw36832step0 raw36832step0Labels = mixedMoment B raw36832step1 raw36832step1Labels := by
      have ha : raw36832step1 = (fun i j => raw36832step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36832step1 raw36832step0; decide +kernel
      have hl : raw36832step1Labels = raw36832step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36832step0 raw36832step0Labels permutation144 permutation7
    mixedMoment B raw36832step1 raw36832step1Labels = mixedMoment B raw36832step2 raw36832step2Labels := by
      have ha : raw36832step2 = raw36832step1 := by apply Matrix.ext; unfold raw36832step2 raw36832step1; decide +kernel
      have hl : raw36832step1Labels = labelEmbedding1 ∘ raw36832step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36832step1 raw36832step1Labels raw36832step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3025 node3025Labels := by rfl

def raw36833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36833Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36833step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36833step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw36833step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36833step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw36833step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36833 raw36833Labels = mixedMoment B node2659 node2659Labels := by
  calc
    mixedMoment B raw36833 raw36833Labels = mixedMoment B raw36833step0 raw36833step0Labels := by
      have hz : ∀ j, raw36833 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36833step0 = (fun i j => raw36833 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36833step0 raw36833; decide +kernel
      have hl : raw36833step0Labels = raw36833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36833 raw36833Labels permutation346 hz
    mixedMoment B raw36833step0 raw36833step0Labels = mixedMoment B raw36833step1 raw36833step1Labels := by
      have ha : raw36833step1 = (fun i j => raw36833step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36833step1 raw36833step0; decide +kernel
      have hl : raw36833step1Labels = raw36833step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36833step0 raw36833step0Labels permutation150 permutation7
    mixedMoment B raw36833step1 raw36833step1Labels = mixedMoment B raw36833step2 raw36833step2Labels := by
      have ha : raw36833step2 = raw36833step1 := by apply Matrix.ext; unfold raw36833step2 raw36833step1; decide +kernel
      have hl : raw36833step1Labels = labelEmbedding1 ∘ raw36833step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36833step1 raw36833step1Labels raw36833step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2659 node2659Labels := by rfl

def raw36834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36834Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36834step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36834step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw36834step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36834step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw36834step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36834 raw36834Labels = mixedMoment B node2658 node2658Labels := by
  calc
    mixedMoment B raw36834 raw36834Labels = mixedMoment B raw36834step0 raw36834step0Labels := by
      have hz : ∀ j, raw36834 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36834step0 = (fun i j => raw36834 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36834step0 raw36834; decide +kernel
      have hl : raw36834step0Labels = raw36834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36834 raw36834Labels permutation346 hz
    mixedMoment B raw36834step0 raw36834step0Labels = mixedMoment B raw36834step1 raw36834step1Labels := by
      have ha : raw36834step1 = (fun i j => raw36834step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36834step1 raw36834step0; decide +kernel
      have hl : raw36834step1Labels = raw36834step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36834step0 raw36834step0Labels permutation150 permutation7
    mixedMoment B raw36834step1 raw36834step1Labels = mixedMoment B raw36834step2 raw36834step2Labels := by
      have ha : raw36834step2 = raw36834step1 := by apply Matrix.ext; unfold raw36834step2 raw36834step1; decide +kernel
      have hl : raw36834step1Labels = labelEmbedding1 ∘ raw36834step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36834step1 raw36834step1Labels raw36834step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2658 node2658Labels := by rfl

def raw36835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36835Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36835step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36835step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36835step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36835step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36835 raw36835Labels = mixedMoment B node2653 node2653Labels := by
  calc
    mixedMoment B raw36835 raw36835Labels = mixedMoment B raw36835step0 raw36835step0Labels := by
      have ha : raw36835step0 = (fun i j => raw36835 (permutation687 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36835step0 raw36835; decide +kernel
      have hl : raw36835step0Labels = raw36835Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36835 raw36835Labels permutation687 permutation7
    mixedMoment B raw36835step0 raw36835step0Labels = mixedMoment B raw36835step1 raw36835step1Labels := by
      have ha : raw36835step1 = raw36835step0 := by apply Matrix.ext; unfold raw36835step1 raw36835step0; decide +kernel
      have hl : raw36835step0Labels = labelEmbedding1 ∘ raw36835step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36835step0 raw36835step0Labels raw36835step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2653 node2653Labels := by rfl

def raw36836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36836Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36836step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36836step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![2, -2, 0], ![2, 1, -3]]
def raw36836step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36836step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36836step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36836step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw36836step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36836 raw36836Labels = mixedMoment B node2686 node2686Labels := by
  calc
    mixedMoment B raw36836 raw36836Labels = mixedMoment B raw36836step0 raw36836step0Labels := by
      have hz : ∀ j, raw36836 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36836step0 = (fun i j => raw36836 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36836step0 raw36836; decide +kernel
      have hl : raw36836step0Labels = raw36836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36836 raw36836Labels permutation434 hz
    mixedMoment B raw36836step0 raw36836step0Labels = mixedMoment B raw36836step1 raw36836step1Labels := by
      have hz : ∀ j, raw36836step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36836step1 = (fun i j => raw36836step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36836step1 raw36836step0; decide +kernel
      have hl : raw36836step1Labels = raw36836step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36836step0 raw36836step0Labels permutation80 hz
    mixedMoment B raw36836step1 raw36836step1Labels = mixedMoment B raw36836step2 raw36836step2Labels := by
      have ha : raw36836step2 = (fun i j => raw36836step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36836step2 raw36836step1; decide +kernel
      have hl : raw36836step2Labels = raw36836step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36836step1 raw36836step1Labels permutation30 permutation7
    mixedMoment B raw36836step2 raw36836step2Labels = mixedMoment B raw36836step3 raw36836step3Labels := by
      have ha : raw36836step3 = raw36836step2 := by apply Matrix.ext; unfold raw36836step3 raw36836step2; decide +kernel
      have hl : raw36836step2Labels = labelEmbedding1 ∘ raw36836step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36836step2 raw36836step2Labels raw36836step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2686 node2686Labels := by rfl

def raw36837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw36837Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw36837step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36837step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36837step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36837step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36837 raw36837Labels = mixedMoment B node3025 node3025Labels := by
  calc
    mixedMoment B raw36837 raw36837Labels = mixedMoment B raw36837step0 raw36837step0Labels := by
      have hz : ∀ j, raw36837 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36837step0 = (fun i j => raw36837 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36837step0 raw36837; decide +kernel
      have hl : raw36837step0Labels = raw36837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36837 raw36837Labels permutation346 hz
    mixedMoment B raw36837step0 raw36837step0Labels = mixedMoment B raw36837step1 raw36837step1Labels := by
      have ha : raw36837step1 = (fun i j => raw36837step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36837step1 raw36837step0; decide +kernel
      have hl : raw36837step1Labels = raw36837step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36837step0 raw36837step0Labels permutation150 permutation7
    mixedMoment B raw36837step1 raw36837step1Labels = mixedMoment B raw36837step2 raw36837step2Labels := by
      have ha : raw36837step2 = raw36837step1 := by apply Matrix.ext; unfold raw36837step2 raw36837step1; decide +kernel
      have hl : raw36837step1Labels = labelEmbedding1 ∘ raw36837step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36837step1 raw36837step1Labels raw36837step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3025 node3025Labels := by rfl

def raw36838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw36838Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw36838step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36838step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw36838step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36838step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw36838step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36838 raw36838Labels = mixedMoment B node2185 node2185Labels := by
  calc
    mixedMoment B raw36838 raw36838Labels = mixedMoment B raw36838step0 raw36838step0Labels := by
      have hz : ∀ j, raw36838 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36838step0 = (fun i j => raw36838 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36838step0 raw36838; decide +kernel
      have hl : raw36838step0Labels = raw36838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36838 raw36838Labels permutation346 hz
    mixedMoment B raw36838step0 raw36838step0Labels = mixedMoment B raw36838step1 raw36838step1Labels := by
      have ha : raw36838step1 = (fun i j => raw36838step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36838step1 raw36838step0; decide +kernel
      have hl : raw36838step1Labels = raw36838step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36838step0 raw36838step0Labels permutation144 permutation7
    mixedMoment B raw36838step1 raw36838step1Labels = mixedMoment B raw36838step2 raw36838step2Labels := by
      have ha : raw36838step2 = raw36838step1 := by apply Matrix.ext; unfold raw36838step2 raw36838step1; decide +kernel
      have hl : raw36838step1Labels = labelEmbedding1 ∘ raw36838step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36838step1 raw36838step1Labels raw36838step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2185 node2185Labels := by rfl

def raw36839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw36839Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36839step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36839step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36839step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36839step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36839 raw36839Labels = mixedMoment B node2174 node2174Labels := by
  calc
    mixedMoment B raw36839 raw36839Labels = mixedMoment B raw36839step0 raw36839step0Labels := by
      have ha : raw36839step0 = (fun i j => raw36839 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36839step0 raw36839; decide +kernel
      have hl : raw36839step0Labels = raw36839Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36839 raw36839Labels permutation663 permutation7
    mixedMoment B raw36839step0 raw36839step0Labels = mixedMoment B raw36839step1 raw36839step1Labels := by
      have ha : raw36839step1 = raw36839step0 := by apply Matrix.ext; unfold raw36839step1 raw36839step0; decide +kernel
      have hl : raw36839step0Labels = labelEmbedding1 ∘ raw36839step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36839step0 raw36839step0Labels raw36839step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2174 node2174Labels := by rfl

def raw36840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw36840Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw36840step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36840step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![3, 0, -3]]
def raw36840step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36840step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36840step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36840step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw36840step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36840 raw36840Labels = mixedMoment B node2229 node2229Labels := by
  calc
    mixedMoment B raw36840 raw36840Labels = mixedMoment B raw36840step0 raw36840step0Labels := by
      have hz : ∀ j, raw36840 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36840step0 = (fun i j => raw36840 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36840step0 raw36840; decide +kernel
      have hl : raw36840step0Labels = raw36840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36840 raw36840Labels permutation520 hz
    mixedMoment B raw36840step0 raw36840step0Labels = mixedMoment B raw36840step1 raw36840step1Labels := by
      have hz : ∀ j, raw36840step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36840step1 = (fun i j => raw36840step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36840step1 raw36840step0; decide +kernel
      have hl : raw36840step1Labels = raw36840step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36840step0 raw36840step0Labels permutation80 hz
    mixedMoment B raw36840step1 raw36840step1Labels = mixedMoment B raw36840step2 raw36840step2Labels := by
      have ha : raw36840step2 = (fun i j => raw36840step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36840step2 raw36840step1; decide +kernel
      have hl : raw36840step2Labels = raw36840step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36840step1 raw36840step1Labels permutation30 permutation7
    mixedMoment B raw36840step2 raw36840step2Labels = mixedMoment B raw36840step3 raw36840step3Labels := by
      have ha : raw36840step3 = raw36840step2 := by apply Matrix.ext; unfold raw36840step3 raw36840step2; decide +kernel
      have hl : raw36840step2Labels = labelEmbedding1 ∘ raw36840step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36840step2 raw36840step2Labels raw36840step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2229 node2229Labels := by rfl

def raw36841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 3, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw36841Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 3, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw36841step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36841step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36841step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw36841step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36841 raw36841Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw36841 raw36841Labels = mixedMoment B raw36841step0 raw36841step0Labels := by
      have hz : ∀ j, raw36841 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36841step0 = (fun i j => raw36841 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36841step0 raw36841; decide +kernel
      have hl : raw36841step0Labels = raw36841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36841 raw36841Labels permutation346 hz
    mixedMoment B raw36841step0 raw36841step0Labels = mixedMoment B raw36841step1 raw36841step1Labels := by
      have ha : raw36841step1 = (fun i j => raw36841step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36841step1 raw36841step0; decide +kernel
      have hl : raw36841step1Labels = raw36841step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36841step0 raw36841step0Labels permutation56 permutation3
    mixedMoment B raw36841step1 raw36841step1Labels = mixedMoment B raw36841step2 raw36841step2Labels := by
      have ha : raw36841step2 = raw36841step1 := by apply Matrix.ext; unfold raw36841step2 raw36841step1; decide +kernel
      have hl : raw36841step1Labels = labelEmbedding6 ∘ raw36841step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36841step1 raw36841step1Labels raw36841step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4832 node4832Labels := by rfl

def raw36842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw36842Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36842step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36842step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36842step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36842step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36842 raw36842Labels = mixedMoment B node5241 node5241Labels := by
  calc
    mixedMoment B raw36842 raw36842Labels = mixedMoment B raw36842step0 raw36842step0Labels := by
      have ha : raw36842step0 = (fun i j => raw36842 (permutation660 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36842step0 raw36842; decide +kernel
      have hl : raw36842step0Labels = raw36842Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36842 raw36842Labels permutation660 permutation5
    mixedMoment B raw36842step0 raw36842step0Labels = mixedMoment B raw36842step1 raw36842step1Labels := by
      have ha : raw36842step1 = raw36842step0 := by apply Matrix.ext; unfold raw36842step1 raw36842step0; decide +kernel
      have hl : raw36842step0Labels = labelEmbedding8 ∘ raw36842step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36842step0 raw36842step0Labels raw36842step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5241 node5241Labels := by rfl

def raw36843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw36843Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw36843step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36843step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36843step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36843step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36843step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36843 raw36843Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw36843 raw36843Labels = mixedMoment B raw36843step0 raw36843step0Labels := by
      have hz : ∀ j, raw36843 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36843step0 = (fun i j => raw36843 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36843step0 raw36843; decide +kernel
      have hl : raw36843step0Labels = raw36843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36843 raw36843Labels permutation346 hz
    mixedMoment B raw36843step0 raw36843step0Labels = mixedMoment B raw36843step1 raw36843step1Labels := by
      have ha : raw36843step1 = (fun i j => raw36843step0 (permutation147 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36843step1 raw36843step0; decide +kernel
      have hl : raw36843step1Labels = raw36843step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36843step0 raw36843step0Labels permutation147 permutation5
    mixedMoment B raw36843step1 raw36843step1Labels = mixedMoment B raw36843step2 raw36843step2Labels := by
      have ha : raw36843step2 = raw36843step1 := by apply Matrix.ext; unfold raw36843step2 raw36843step1; decide +kernel
      have hl : raw36843step1Labels = labelEmbedding8 ∘ raw36843step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36843step1 raw36843step1Labels raw36843step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw36844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw36844Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw36844step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36844step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36844step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36844step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36844 raw36844Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw36844 raw36844Labels = mixedMoment B raw36844step0 raw36844step0Labels := by
      have hz : ∀ j, raw36844 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36844step0 = (fun i j => raw36844 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36844step0 raw36844; decide +kernel
      have hl : raw36844step0Labels = raw36844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36844 raw36844Labels permutation346 hz
    mixedMoment B raw36844step0 raw36844step0Labels = mixedMoment B raw36844step1 raw36844step1Labels := by
      have ha : raw36844step1 = (fun i j => raw36844step0 (permutation141 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36844step1 raw36844step0; decide +kernel
      have hl : raw36844step1Labels = raw36844step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36844step0 raw36844step0Labels permutation141 permutation5
    mixedMoment B raw36844step1 raw36844step1Labels = mixedMoment B raw36844step2 raw36844step2Labels := by
      have ha : raw36844step2 = raw36844step1 := by apply Matrix.ext; unfold raw36844step2 raw36844step1; decide +kernel
      have hl : raw36844step1Labels = labelEmbedding8 ∘ raw36844step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36844step1 raw36844step1Labels raw36844step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw36845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw36845Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36845step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw36845step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36845step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw36845step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36845 raw36845Labels = mixedMoment B node4639 node4639Labels := by
  calc
    mixedMoment B raw36845 raw36845Labels = mixedMoment B raw36845step0 raw36845step0Labels := by
      have ha : raw36845step0 = (fun i j => raw36845 (permutation273 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36845step0 raw36845; decide +kernel
      have hl : raw36845step0Labels = raw36845Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36845 raw36845Labels permutation273 permutation3
    mixedMoment B raw36845step0 raw36845step0Labels = mixedMoment B raw36845step1 raw36845step1Labels := by
      have ha : raw36845step1 = raw36845step0 := by apply Matrix.ext; unfold raw36845step1 raw36845step0; decide +kernel
      have hl : raw36845step0Labels = labelEmbedding6 ∘ raw36845step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36845step0 raw36845step0Labels raw36845step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4639 node4639Labels := by rfl

def raw36846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw36846Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36846step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36846step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36846step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36846 raw36846Labels = mixedMoment B node5056 node5056Labels := by
  calc
    mixedMoment B raw36846 raw36846Labels = mixedMoment B raw36846step0 raw36846step0Labels := by
      have ha : raw36846step0 = (fun i j => raw36846 (permutation645 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36846step0 raw36846; decide +kernel
      have hl : raw36846step0Labels = raw36846Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36846 raw36846Labels permutation645 permutation5
    mixedMoment B raw36846step0 raw36846step0Labels = mixedMoment B raw36846step1 raw36846step1Labels := by
      have ha : raw36846step1 = raw36846step0 := by apply Matrix.ext; unfold raw36846step1 raw36846step0; decide +kernel
      have hl : raw36846step0Labels = labelEmbedding8 ∘ raw36846step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36846step0 raw36846step0Labels raw36846step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5056 node5056Labels := by rfl

def raw36847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw36847Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36847step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36847step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36847step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36847step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36847 raw36847Labels = mixedMoment B node5056 node5056Labels := by
  calc
    mixedMoment B raw36847 raw36847Labels = mixedMoment B raw36847step0 raw36847step0Labels := by
      have ha : raw36847step0 = (fun i j => raw36847 (permutation639 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36847step0 raw36847; decide +kernel
      have hl : raw36847step0Labels = raw36847Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36847 raw36847Labels permutation639 permutation5
    mixedMoment B raw36847step0 raw36847step0Labels = mixedMoment B raw36847step1 raw36847step1Labels := by
      have ha : raw36847step1 = raw36847step0 := by apply Matrix.ext; unfold raw36847step1 raw36847step0; decide +kernel
      have hl : raw36847step0Labels = labelEmbedding8 ∘ raw36847step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36847step0 raw36847step0Labels raw36847step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5056 node5056Labels := by rfl

def raw36848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw36848Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![2, -1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw36848step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw36848step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36848step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw36848step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36848 raw36848Labels = mixedMoment B node4645 node4645Labels := by
  calc
    mixedMoment B raw36848 raw36848Labels = mixedMoment B raw36848step0 raw36848step0Labels := by
      have hz : ∀ j, raw36848 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36848step0 = (fun i j => raw36848 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36848step0 raw36848; decide +kernel
      have hl : raw36848step0Labels = raw36848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36848 raw36848Labels permutation346 hz
    mixedMoment B raw36848step0 raw36848step0Labels = mixedMoment B raw36848step1 raw36848step1Labels := by
      have ha : raw36848step1 = (fun i j => raw36848step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36848step1 raw36848step0; decide +kernel
      have hl : raw36848step1Labels = raw36848step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36848step0 raw36848step0Labels permutation58 permutation3
    mixedMoment B raw36848step1 raw36848step1Labels = mixedMoment B raw36848step2 raw36848step2Labels := by
      have ha : raw36848step2 = raw36848step1 := by apply Matrix.ext; unfold raw36848step2 raw36848step1; decide +kernel
      have hl : raw36848step1Labels = labelEmbedding6 ∘ raw36848step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36848step1 raw36848step1Labels raw36848step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4645 node4645Labels := by rfl

def raw36849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw36849Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36849step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36849step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36849step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36849 raw36849Labels = mixedMoment B node4990 node4990Labels := by
  calc
    mixedMoment B raw36849 raw36849Labels = mixedMoment B raw36849step0 raw36849step0Labels := by
      have ha : raw36849step0 = (fun i j => raw36849 (permutation663 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36849step0 raw36849; decide +kernel
      have hl : raw36849step0Labels = raw36849Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36849 raw36849Labels permutation663 permutation5
    mixedMoment B raw36849step0 raw36849step0Labels = mixedMoment B raw36849step1 raw36849step1Labels := by
      have ha : raw36849step1 = raw36849step0 := by apply Matrix.ext; unfold raw36849step1 raw36849step0; decide +kernel
      have hl : raw36849step0Labels = labelEmbedding8 ∘ raw36849step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36849step0 raw36849step0Labels raw36849step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4990 node4990Labels := by rfl

def raw36850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw36850Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![2, -1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw36850step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36850step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36850step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36850step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36850 raw36850Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw36850 raw36850Labels = mixedMoment B raw36850step0 raw36850step0Labels := by
      have hz : ∀ j, raw36850 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36850step0 = (fun i j => raw36850 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36850step0 raw36850; decide +kernel
      have hl : raw36850step0Labels = raw36850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36850 raw36850Labels permutation346 hz
    mixedMoment B raw36850step0 raw36850step0Labels = mixedMoment B raw36850step1 raw36850step1Labels := by
      have ha : raw36850step1 = (fun i j => raw36850step0 (permutation144 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36850step1 raw36850step0; decide +kernel
      have hl : raw36850step1Labels = raw36850step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36850step0 raw36850step0Labels permutation144 permutation5
    mixedMoment B raw36850step1 raw36850step1Labels = mixedMoment B raw36850step2 raw36850step2Labels := by
      have ha : raw36850step2 = raw36850step1 := by apply Matrix.ext; unfold raw36850step2 raw36850step1; decide +kernel
      have hl : raw36850step1Labels = labelEmbedding8 ∘ raw36850step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36850step1 raw36850step1Labels raw36850step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5015 node5015Labels := by rfl

def raw36851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -3, 1]]
def raw36851Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![1, 0, -1], ![2, -1, -1], ![2, -3, 1]]
def raw36851step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36851step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw36851step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36851step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw36851step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36851 raw36851Labels = mixedMoment B node4645 node4645Labels := by
  calc
    mixedMoment B raw36851 raw36851Labels = mixedMoment B raw36851step0 raw36851step0Labels := by
      have hz : ∀ j, raw36851 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36851step0 = (fun i j => raw36851 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36851step0 raw36851; decide +kernel
      have hl : raw36851step0Labels = raw36851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36851 raw36851Labels permutation346 hz
    mixedMoment B raw36851step0 raw36851step0Labels = mixedMoment B raw36851step1 raw36851step1Labels := by
      have ha : raw36851step1 = (fun i j => raw36851step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36851step1 raw36851step0; decide +kernel
      have hl : raw36851step1Labels = raw36851step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36851step0 raw36851step0Labels permutation56 permutation3
    mixedMoment B raw36851step1 raw36851step1Labels = mixedMoment B raw36851step2 raw36851step2Labels := by
      have ha : raw36851step2 = raw36851step1 := by apply Matrix.ext; unfold raw36851step2 raw36851step1; decide +kernel
      have hl : raw36851step1Labels = labelEmbedding6 ∘ raw36851step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36851step1 raw36851step1Labels raw36851step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4645 node4645Labels := by rfl

def raw36852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -3, 1]]
def raw36852Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36852step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36852step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36852step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36852step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36852 raw36852Labels = mixedMoment B node4990 node4990Labels := by
  calc
    mixedMoment B raw36852 raw36852Labels = mixedMoment B raw36852step0 raw36852step0Labels := by
      have ha : raw36852step0 = (fun i j => raw36852 (permutation687 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36852step0 raw36852; decide +kernel
      have hl : raw36852step0Labels = raw36852Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36852 raw36852Labels permutation687 permutation5
    mixedMoment B raw36852step0 raw36852step0Labels = mixedMoment B raw36852step1 raw36852step1Labels := by
      have ha : raw36852step1 = raw36852step0 := by apply Matrix.ext; unfold raw36852step1 raw36852step0; decide +kernel
      have hl : raw36852step0Labels = labelEmbedding8 ∘ raw36852step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36852step0 raw36852step0Labels raw36852step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4990 node4990Labels := by rfl

def raw36853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw36853Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw36853step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36853step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36853step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36853step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36853step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36853 raw36853Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw36853 raw36853Labels = mixedMoment B raw36853step0 raw36853step0Labels := by
      have hz : ∀ j, raw36853 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36853step0 = (fun i j => raw36853 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36853step0 raw36853; decide +kernel
      have hl : raw36853step0Labels = raw36853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36853 raw36853Labels permutation346 hz
    mixedMoment B raw36853step0 raw36853step0Labels = mixedMoment B raw36853step1 raw36853step1Labels := by
      have ha : raw36853step1 = (fun i j => raw36853step0 (permutation150 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36853step1 raw36853step0; decide +kernel
      have hl : raw36853step1Labels = raw36853step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36853step0 raw36853step0Labels permutation150 permutation5
    mixedMoment B raw36853step1 raw36853step1Labels = mixedMoment B raw36853step2 raw36853step2Labels := by
      have ha : raw36853step2 = raw36853step1 := by apply Matrix.ext; unfold raw36853step2 raw36853step1; decide +kernel
      have hl : raw36853step1Labels = labelEmbedding8 ∘ raw36853step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36853step1 raw36853step1Labels raw36853step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5015 node5015Labels := by rfl

def raw36854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -4, 1]]
def raw36854Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![1, 0, -1], ![1, 0, -1], ![3, -4, 1]]
def raw36854step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36854step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def raw36854step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36854step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def raw36854step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36854 raw36854Labels = mixedMoment B node4388 node4388Labels := by
  calc
    mixedMoment B raw36854 raw36854Labels = mixedMoment B raw36854step0 raw36854step0Labels := by
      have hz : ∀ j, raw36854 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36854step0 = (fun i j => raw36854 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36854step0 raw36854; decide +kernel
      have hl : raw36854step0Labels = raw36854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36854 raw36854Labels permutation346 hz
    mixedMoment B raw36854step0 raw36854step0Labels = mixedMoment B raw36854step1 raw36854step1Labels := by
      have ha : raw36854step1 = (fun i j => raw36854step0 (permutation144 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36854step1 raw36854step0; decide +kernel
      have hl : raw36854step1Labels = raw36854step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36854step0 raw36854step0Labels permutation144 permutation5
    mixedMoment B raw36854step1 raw36854step1Labels = mixedMoment B raw36854step2 raw36854step2Labels := by
      have ha : raw36854step2 = raw36854step1 := by apply Matrix.ext; unfold raw36854step2 raw36854step1; decide +kernel
      have hl : raw36854step1Labels = labelEmbedding8 ∘ raw36854step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36854step1 raw36854step1Labels raw36854step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4388 node4388Labels := by rfl

def raw36855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -4, 1]]
def raw36855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36855step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36855step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36855step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36855 raw36855Labels = mixedMoment B node4387 node4387Labels := by
  calc
    mixedMoment B raw36855 raw36855Labels = mixedMoment B raw36855step0 raw36855step0Labels := by
      have ha : raw36855step0 = (fun i j => raw36855 (permutation663 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36855step0 raw36855; decide +kernel
      have hl : raw36855step0Labels = raw36855Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36855 raw36855Labels permutation663 permutation5
    mixedMoment B raw36855step0 raw36855step0Labels = mixedMoment B raw36855step1 raw36855step1Labels := by
      have ha : raw36855step1 = raw36855step0 := by apply Matrix.ext; unfold raw36855step1 raw36855step0; decide +kernel
      have hl : raw36855step0Labels = labelEmbedding8 ∘ raw36855step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36855step0 raw36855step0Labels raw36855step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4387 node4387Labels := by rfl

def raw36856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw36856Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw36856step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36856step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36856step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36856step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36856step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36856 raw36856Labels = mixedMoment B node4419 node4419Labels := by
  calc
    mixedMoment B raw36856 raw36856Labels = mixedMoment B raw36856step0 raw36856step0Labels := by
      have hz : ∀ j, raw36856 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36856step0 = (fun i j => raw36856 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36856step0 raw36856; decide +kernel
      have hl : raw36856step0Labels = raw36856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36856 raw36856Labels permutation346 hz
    mixedMoment B raw36856step0 raw36856step0Labels = mixedMoment B raw36856step1 raw36856step1Labels := by
      have ha : raw36856step1 = (fun i j => raw36856step0 (permutation150 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36856step1 raw36856step0; decide +kernel
      have hl : raw36856step1Labels = raw36856step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36856step0 raw36856step0Labels permutation150 permutation5
    mixedMoment B raw36856step1 raw36856step1Labels = mixedMoment B raw36856step2 raw36856step2Labels := by
      have ha : raw36856step2 = raw36856step1 := by apply Matrix.ext; unfold raw36856step2 raw36856step1; decide +kernel
      have hl : raw36856step1Labels = labelEmbedding8 ∘ raw36856step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36856step1 raw36856step1Labels raw36856step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4419 node4419Labels := by rfl

def raw36857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -4, 1]]
def raw36857Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, 0, -1], ![0, 1, -1], ![3, -4, 1]]
def raw36857step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36857step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36857step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36857step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36857 raw36857Labels = mixedMoment B node4419 node4419Labels := by
  calc
    mixedMoment B raw36857 raw36857Labels = mixedMoment B raw36857step0 raw36857step0Labels := by
      have hz : ∀ j, raw36857 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36857step0 = (fun i j => raw36857 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36857step0 raw36857; decide +kernel
      have hl : raw36857step0Labels = raw36857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36857 raw36857Labels permutation346 hz
    mixedMoment B raw36857step0 raw36857step0Labels = mixedMoment B raw36857step1 raw36857step1Labels := by
      have ha : raw36857step1 = (fun i j => raw36857step0 (permutation144 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36857step1 raw36857step0; decide +kernel
      have hl : raw36857step1Labels = raw36857step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36857step0 raw36857step0Labels permutation144 permutation5
    mixedMoment B raw36857step1 raw36857step1Labels = mixedMoment B raw36857step2 raw36857step2Labels := by
      have ha : raw36857step2 = raw36857step1 := by apply Matrix.ext; unfold raw36857step2 raw36857step1; decide +kernel
      have hl : raw36857step1Labels = labelEmbedding8 ∘ raw36857step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36857step1 raw36857step1Labels raw36857step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4419 node4419Labels := by rfl

def raw36858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36858step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36858 raw36858Labels = mixedMoment B node5058 node5058Labels := by
  calc
    mixedMoment B raw36858 raw36858Labels = mixedMoment B raw36858step0 raw36858step0Labels := by
      have ha : raw36858step0 = (fun i j => raw36858 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36858step0 raw36858; decide +kernel
      have hl : raw36858step0Labels = raw36858Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36858 raw36858Labels permutation265 permutation2
    _ = mixedMoment B node5058 node5058Labels := by rfl

def raw36859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36859step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw36859step0Labels : Fin 2 → Fin 3 := ![0, 2]

def raw36859step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw36859step1Labels : Fin 2 → Fin 3 := ![0, 2]

def raw36859step2 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw36859step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical36859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36859 raw36859Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw36859 raw36859Labels = mixedMoment B raw36859step0 raw36859step0Labels := by
      have hz : ∀ i, raw36859 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw36859step0 = (fun i j => raw36859 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw36859step0 raw36859; decide +kernel
      have hl : raw36859step0Labels = (fun j => raw36859Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw36859 raw36859Labels permutation4 hz
    mixedMoment B raw36859step0 raw36859step0Labels = mixedMoment B raw36859step1 raw36859step1Labels := by
      have ha : raw36859step1 = (fun i j => raw36859step0 (permutation265 i) (permutation0 j)) := by apply Matrix.ext; unfold raw36859step1 raw36859step0; decide +kernel
      have hl : raw36859step1Labels = raw36859step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36859step0 raw36859step0Labels permutation265 permutation0
    mixedMoment B raw36859step1 raw36859step1Labels = mixedMoment B raw36859step2 raw36859step2Labels := by
      have ha : raw36859step2 = raw36859step1 := by apply Matrix.ext; unfold raw36859step2 raw36859step1; decide +kernel
      have hl : raw36859step1Labels = labelEmbedding2 ∘ raw36859step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36859step1 raw36859step1Labels raw36859step2Labels labelEmbedding2 hl
    _ = mixedMoment B node4090 node4090Labels := by rfl

def raw36860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36860step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36860step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36860step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36860 raw36860Labels = mixedMoment B node5394 node5394Labels := by
  calc
    mixedMoment B raw36860 raw36860Labels = mixedMoment B raw36860step0 raw36860step0Labels := by
      have ha : raw36860step0 = (fun i j => raw36860 (permutation687 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36860step0 raw36860; decide +kernel
      have hl : raw36860step0Labels = raw36860Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36860 raw36860Labels permutation687 permutation7
    mixedMoment B raw36860step0 raw36860step0Labels = mixedMoment B raw36860step1 raw36860step1Labels := by
      have ha : raw36860step1 = raw36860step0 := by apply Matrix.ext; unfold raw36860step1 raw36860step0; decide +kernel
      have hl : raw36860step0Labels = labelEmbedding10 ∘ raw36860step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36860step0 raw36860step0Labels raw36860step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5394 node5394Labels := by rfl

def raw36861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw36861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36861step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36861step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36861step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36861step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36861 raw36861Labels = mixedMoment B node5394 node5394Labels := by
  calc
    mixedMoment B raw36861 raw36861Labels = mixedMoment B raw36861step0 raw36861step0Labels := by
      have ha : raw36861step0 = (fun i j => raw36861 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36861step0 raw36861; decide +kernel
      have hl : raw36861step0Labels = raw36861Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36861 raw36861Labels permutation663 permutation7
    mixedMoment B raw36861step0 raw36861step0Labels = mixedMoment B raw36861step1 raw36861step1Labels := by
      have ha : raw36861step1 = raw36861step0 := by apply Matrix.ext; unfold raw36861step1 raw36861step0; decide +kernel
      have hl : raw36861step0Labels = labelEmbedding10 ∘ raw36861step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36861step0 raw36861step0Labels raw36861step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5394 node5394Labels := by rfl

def raw36862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36862Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36862step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36862step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36862step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36862step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36862step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36862step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36862 raw36862Labels = mixedMoment B node5396 node5396Labels := by
  calc
    mixedMoment B raw36862 raw36862Labels = mixedMoment B raw36862step0 raw36862step0Labels := by
      have ha : raw36862step0 = (fun i j => raw36862 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36862step0 raw36862; decide +kernel
      have hl : raw36862step0Labels = raw36862Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36862 raw36862Labels permutation265 permutation7
    mixedMoment B raw36862step0 raw36862step0Labels = mixedMoment B raw36862step1 raw36862step1Labels := by
      have ha : raw36862step1 = -raw36862step0 := by apply Matrix.ext; change ∀ i j, raw36862step1 i j = -(raw36862step0 i j); unfold raw36862step1 raw36862step0; decide +kernel
      have hl : raw36862step1Labels = raw36862step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36862step1 raw36862step1Labels = mixedMoment B raw36862step2 raw36862step2Labels := by
      have ha : raw36862step2 = raw36862step1 := by apply Matrix.ext; unfold raw36862step2 raw36862step1; decide +kernel
      have hl : raw36862step1Labels = labelEmbedding10 ∘ raw36862step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36862step1 raw36862step1Labels raw36862step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5396 node5396Labels := by rfl

def raw36863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw36863step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36863step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw36863step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36863 raw36863Labels = mixedMoment B node5192 node5192Labels := by
  calc
    mixedMoment B raw36863 raw36863Labels = mixedMoment B raw36863step0 raw36863step0Labels := by
      have ha : raw36863step0 = (fun i j => raw36863 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36863step0 raw36863; decide +kernel
      have hl : raw36863step0Labels = raw36863Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36863 raw36863Labels permutation152 permutation3
    mixedMoment B raw36863step0 raw36863step0Labels = mixedMoment B raw36863step1 raw36863step1Labels := by
      have ha : raw36863step1 = raw36863step0 := by apply Matrix.ext; unfold raw36863step1 raw36863step0; decide +kernel
      have hl : raw36863step0Labels = labelEmbedding6 ∘ raw36863step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36863step0 raw36863step0Labels raw36863step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5192 node5192Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
