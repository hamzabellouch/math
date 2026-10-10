import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw24576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw24576Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw24576step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw24576step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24576step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw24576step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24576 raw24576Labels = mixedMoment B node4517 node4517Labels := by
  calc
    mixedMoment B raw24576 raw24576Labels = mixedMoment B raw24576step0 raw24576step0Labels := by
      have hz : ∀ j, raw24576 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24576step0 = (fun i j => raw24576 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24576step0 raw24576; decide +kernel
      have hl : raw24576step0Labels = raw24576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24576 raw24576Labels permutation265 hz
    mixedMoment B raw24576step0 raw24576step0Labels = mixedMoment B raw24576step1 raw24576step1Labels := by
      have ha : raw24576step1 = (fun i j => raw24576step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24576step1 raw24576step0; decide +kernel
      have hl : raw24576step1Labels = raw24576step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24576step0 raw24576step0Labels permutation32 permutation3
    mixedMoment B raw24576step1 raw24576step1Labels = mixedMoment B raw24576step2 raw24576step2Labels := by
      have ha : raw24576step2 = raw24576step1 := by apply Matrix.ext; unfold raw24576step2 raw24576step1; decide +kernel
      have hl : raw24576step1Labels = labelEmbedding6 ∘ raw24576step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24576step1 raw24576step1Labels raw24576step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4517 node4517Labels := by rfl

def raw24577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw24577Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw24577step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24577step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw24577step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24577step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw24577step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24577step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw24577step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24577 raw24577Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw24577 raw24577Labels = mixedMoment B raw24577step0 raw24577step0Labels := by
      have hz : ∀ j, raw24577 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24577step0 = (fun i j => raw24577 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24577step0 raw24577; decide +kernel
      have hl : raw24577step0Labels = raw24577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24577 raw24577Labels permutation434 hz
    mixedMoment B raw24577step0 raw24577step0Labels = mixedMoment B raw24577step1 raw24577step1Labels := by
      have hz : ∀ j, raw24577step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24577step1 = (fun i j => raw24577step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24577step1 raw24577step0; decide +kernel
      have hl : raw24577step1Labels = raw24577step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24577step0 raw24577step0Labels permutation56 hz
    mixedMoment B raw24577step1 raw24577step1Labels = mixedMoment B raw24577step2 raw24577step2Labels := by
      have ha : raw24577step2 = (fun i j => raw24577step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24577step2 raw24577step1; decide +kernel
      have hl : raw24577step2Labels = raw24577step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24577step1 raw24577step1Labels permutation8 permutation3
    mixedMoment B raw24577step2 raw24577step2Labels = mixedMoment B raw24577step3 raw24577step3Labels := by
      have ha : raw24577step3 = raw24577step2 := by apply Matrix.ext; unfold raw24577step3 raw24577step2; decide +kernel
      have hl : raw24577step2Labels = labelEmbedding6 ∘ raw24577step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24577step2 raw24577step2Labels raw24577step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4608 node4608Labels := by rfl

def raw24578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -2, -1]]
def raw24578Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw24578step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24578step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw24578step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24578step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw24578step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24578step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw24578step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24578 raw24578Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw24578 raw24578Labels = mixedMoment B raw24578step0 raw24578step0Labels := by
      have hz : ∀ j, raw24578 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24578step0 = (fun i j => raw24578 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24578step0 raw24578; decide +kernel
      have hl : raw24578step0Labels = raw24578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24578 raw24578Labels permutation520 hz
    mixedMoment B raw24578step0 raw24578step0Labels = mixedMoment B raw24578step1 raw24578step1Labels := by
      have hz : ∀ j, raw24578step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24578step1 = (fun i j => raw24578step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24578step1 raw24578step0; decide +kernel
      have hl : raw24578step1Labels = raw24578step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24578step0 raw24578step0Labels permutation56 hz
    mixedMoment B raw24578step1 raw24578step1Labels = mixedMoment B raw24578step2 raw24578step2Labels := by
      have ha : raw24578step2 = (fun i j => raw24578step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24578step2 raw24578step1; decide +kernel
      have hl : raw24578step2Labels = raw24578step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24578step1 raw24578step1Labels permutation8 permutation3
    mixedMoment B raw24578step2 raw24578step2Labels = mixedMoment B raw24578step3 raw24578step3Labels := by
      have ha : raw24578step3 = raw24578step2 := by apply Matrix.ext; unfold raw24578step3 raw24578step2; decide +kernel
      have hl : raw24578step2Labels = labelEmbedding6 ∘ raw24578step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24578step2 raw24578step2Labels raw24578step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4608 node4608Labels := by rfl

def raw24579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw24579Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw24579step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24579step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24579step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24579 raw24579Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw24579 raw24579Labels = mixedMoment B raw24579step0 raw24579step0Labels := by
      have hz : ∀ j, raw24579 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24579step0 = (fun i j => raw24579 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24579step0 raw24579; decide +kernel
      have hl : raw24579step0Labels = raw24579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24579 raw24579Labels permutation265 hz
    mixedMoment B raw24579step0 raw24579step0Labels = mixedMoment B raw24579step1 raw24579step1Labels := by
      have ha : raw24579step1 = (fun i j => raw24579step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24579step1 raw24579step0; decide +kernel
      have hl : raw24579step1Labels = raw24579step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24579step0 raw24579step0Labels permutation36 permutation3
    _ = mixedMoment B node3100 node3100Labels := by rfl

def raw24580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24580Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24580step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24580step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24580 raw24580Labels = mixedMoment B node571 node571Labels := by
  calc
    mixedMoment B raw24580 raw24580Labels = mixedMoment B raw24580step0 raw24580step0Labels := by
      have ha : raw24580step0 = (fun i j => raw24580 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24580step0 raw24580; decide +kernel
      have hl : raw24580step0Labels = raw24580Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24580 raw24580Labels permutation176 permutation3
    _ = mixedMoment B node571 node571Labels := by rfl

def raw24581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24581Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24581step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24581step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24581 raw24581Labels = mixedMoment B node1100 node1100Labels := by
  calc
    mixedMoment B raw24581 raw24581Labels = mixedMoment B raw24581step0 raw24581step0Labels := by
      have ha : raw24581step0 = (fun i j => raw24581 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24581step0 raw24581; decide +kernel
      have hl : raw24581step0Labels = raw24581Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24581 raw24581Labels permutation176 permutation3
    _ = mixedMoment B node1100 node1100Labels := by rfl

def raw24582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24582Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24582step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24582step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24582step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24582 raw24582Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw24582 raw24582Labels = mixedMoment B raw24582step0 raw24582step0Labels := by
      have hz : ∀ j, raw24582 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24582step0 = (fun i j => raw24582 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24582step0 raw24582; decide +kernel
      have hl : raw24582step0Labels = raw24582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24582 raw24582Labels permutation434 hz
    mixedMoment B raw24582step0 raw24582step0Labels = mixedMoment B raw24582step1 raw24582step1Labels := by
      have ha : raw24582step1 = (fun i j => raw24582step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24582step1 raw24582step0; decide +kernel
      have hl : raw24582step1Labels = raw24582step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24582step0 raw24582step0Labels permutation38 permutation3
    _ = mixedMoment B node1240 node1240Labels := by rfl

def raw24583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw24583Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24583step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24583step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24583step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24583 raw24583Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw24583 raw24583Labels = mixedMoment B raw24583step0 raw24583step0Labels := by
      have hz : ∀ j, raw24583 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24583step0 = (fun i j => raw24583 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24583step0 raw24583; decide +kernel
      have hl : raw24583step0Labels = raw24583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24583 raw24583Labels permutation520 hz
    mixedMoment B raw24583step0 raw24583step0Labels = mixedMoment B raw24583step1 raw24583step1Labels := by
      have ha : raw24583step1 = (fun i j => raw24583step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24583step1 raw24583step0; decide +kernel
      have hl : raw24583step1Labels = raw24583step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24583step0 raw24583step0Labels permutation38 permutation3
    _ = mixedMoment B node1240 node1240Labels := by rfl

def raw24584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24584Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24584step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24584step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24584step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24584 raw24584Labels = mixedMoment B node603 node603Labels := by
  calc
    mixedMoment B raw24584 raw24584Labels = mixedMoment B raw24584step0 raw24584step0Labels := by
      have hz : ∀ j, raw24584 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24584step0 = (fun i j => raw24584 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24584step0 raw24584; decide +kernel
      have hl : raw24584step0Labels = raw24584Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24584 raw24584Labels permutation265 hz
    mixedMoment B raw24584step0 raw24584step0Labels = mixedMoment B raw24584step1 raw24584step1Labels := by
      have ha : raw24584step1 = (fun i j => raw24584step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24584step1 raw24584step0; decide +kernel
      have hl : raw24584step1Labels = raw24584step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24584step0 raw24584step0Labels permutation32 permutation3
    _ = mixedMoment B node603 node603Labels := by rfl

def raw24585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24585Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24585step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24585 raw24585Labels = mixedMoment B node1129 node1129Labels := by
  calc
    mixedMoment B raw24585 raw24585Labels = mixedMoment B raw24585step0 raw24585step0Labels := by
      have ha : raw24585step0 = (fun i j => raw24585 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24585step0 raw24585; decide +kernel
      have hl : raw24585step0Labels = raw24585Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24585 raw24585Labels permutation152 permutation3
    _ = mixedMoment B node1129 node1129Labels := by rfl

def raw24586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24586Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24586step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24586step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24586step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24586step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24586step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24586 raw24586Labels = mixedMoment B node1301 node1301Labels := by
  calc
    mixedMoment B raw24586 raw24586Labels = mixedMoment B raw24586step0 raw24586step0Labels := by
      have hz : ∀ j, raw24586 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24586step0 = (fun i j => raw24586 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24586step0 raw24586; decide +kernel
      have hl : raw24586step0Labels = raw24586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24586 raw24586Labels permutation434 hz
    mixedMoment B raw24586step0 raw24586step0Labels = mixedMoment B raw24586step1 raw24586step1Labels := by
      have hz : ∀ j, raw24586step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24586step1 = (fun i j => raw24586step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24586step1 raw24586step0; decide +kernel
      have hl : raw24586step1Labels = raw24586step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24586step0 raw24586step0Labels permutation56 hz
    mixedMoment B raw24586step1 raw24586step1Labels = mixedMoment B raw24586step2 raw24586step2Labels := by
      have ha : raw24586step2 = (fun i j => raw24586step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24586step2 raw24586step1; decide +kernel
      have hl : raw24586step2Labels = raw24586step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24586step1 raw24586step1Labels permutation8 permutation3
    _ = mixedMoment B node1301 node1301Labels := by rfl

def raw24587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw24587Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24587step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24587step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw24587step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24587step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24587step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24587 raw24587Labels = mixedMoment B node1301 node1301Labels := by
  calc
    mixedMoment B raw24587 raw24587Labels = mixedMoment B raw24587step0 raw24587step0Labels := by
      have hz : ∀ j, raw24587 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24587step0 = (fun i j => raw24587 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24587step0 raw24587; decide +kernel
      have hl : raw24587step0Labels = raw24587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24587 raw24587Labels permutation520 hz
    mixedMoment B raw24587step0 raw24587step0Labels = mixedMoment B raw24587step1 raw24587step1Labels := by
      have hz : ∀ j, raw24587step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24587step1 = (fun i j => raw24587step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24587step1 raw24587step0; decide +kernel
      have hl : raw24587step1Labels = raw24587step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24587step0 raw24587step0Labels permutation56 hz
    mixedMoment B raw24587step1 raw24587step1Labels = mixedMoment B raw24587step2 raw24587step2Labels := by
      have ha : raw24587step2 = (fun i j => raw24587step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24587step2 raw24587step1; decide +kernel
      have hl : raw24587step2Labels = raw24587step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24587step1 raw24587step1Labels permutation8 permutation3
    _ = mixedMoment B node1301 node1301Labels := by rfl

def raw24588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24588Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24588step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24588step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24588 raw24588Labels = mixedMoment B node573 node573Labels := by
  calc
    mixedMoment B raw24588 raw24588Labels = mixedMoment B raw24588step0 raw24588step0Labels := by
      have hz : ∀ j, raw24588 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24588step0 = (fun i j => raw24588 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24588step0 raw24588; decide +kernel
      have hl : raw24588step0Labels = raw24588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24588 raw24588Labels permutation265 hz
    mixedMoment B raw24588step0 raw24588step0Labels = mixedMoment B raw24588step1 raw24588step1Labels := by
      have ha : raw24588step1 = (fun i j => raw24588step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24588step1 raw24588step0; decide +kernel
      have hl : raw24588step1Labels = raw24588step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24588step0 raw24588step0Labels permutation35 permutation3
    _ = mixedMoment B node573 node573Labels := by rfl

def raw24589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24589Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24589step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24589 raw24589Labels = mixedMoment B node1108 node1108Labels := by
  calc
    mixedMoment B raw24589 raw24589Labels = mixedMoment B raw24589step0 raw24589step0Labels := by
      have ha : raw24589step0 = (fun i j => raw24589 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24589step0 raw24589; decide +kernel
      have hl : raw24589step0Labels = raw24589Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24589 raw24589Labels permutation155 permutation3
    _ = mixedMoment B node1108 node1108Labels := by rfl

def raw24590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24590Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24590step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24590step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24590step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24590 raw24590Labels = mixedMoment B node1102 node1102Labels := by
  calc
    mixedMoment B raw24590 raw24590Labels = mixedMoment B raw24590step0 raw24590step0Labels := by
      have hz : ∀ j, raw24590 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24590step0 = (fun i j => raw24590 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24590step0 raw24590; decide +kernel
      have hl : raw24590step0Labels = raw24590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24590 raw24590Labels permutation265 hz
    mixedMoment B raw24590step0 raw24590step0Labels = mixedMoment B raw24590step1 raw24590step1Labels := by
      have ha : raw24590step1 = (fun i j => raw24590step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24590step1 raw24590step0; decide +kernel
      have hl : raw24590step1Labels = raw24590step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24590step0 raw24590step0Labels permutation35 permutation3
    _ = mixedMoment B node1102 node1102Labels := by rfl

def raw24591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![2, -1, -1]]
def raw24591Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24591step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24591step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24591step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24591step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24591step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24591 raw24591Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw24591 raw24591Labels = mixedMoment B raw24591step0 raw24591step0Labels := by
      have hz : ∀ j, raw24591 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24591step0 = (fun i j => raw24591 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24591step0 raw24591; decide +kernel
      have hl : raw24591step0Labels = raw24591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24591 raw24591Labels permutation520 hz
    mixedMoment B raw24591step0 raw24591step0Labels = mixedMoment B raw24591step1 raw24591step1Labels := by
      have hz : ∀ j, raw24591step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24591step1 = (fun i j => raw24591step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24591step1 raw24591step0; decide +kernel
      have hl : raw24591step1Labels = raw24591step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24591step0 raw24591step0Labels permutation56 hz
    mixedMoment B raw24591step1 raw24591step1Labels = mixedMoment B raw24591step2 raw24591step2Labels := by
      have ha : raw24591step2 = (fun i j => raw24591step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24591step2 raw24591step1; decide +kernel
      have hl : raw24591step2Labels = raw24591step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24591step1 raw24591step1Labels permutation9 permutation3
    _ = mixedMoment B node1246 node1246Labels := by rfl

def raw24592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw24592Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw24592step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24592step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24592 raw24592Labels = mixedMoment B node573 node573Labels := by
  calc
    mixedMoment B raw24592 raw24592Labels = mixedMoment B raw24592step0 raw24592step0Labels := by
      have hz : ∀ j, raw24592 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24592step0 = (fun i j => raw24592 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24592step0 raw24592; decide +kernel
      have hl : raw24592step0Labels = raw24592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24592 raw24592Labels permutation265 hz
    mixedMoment B raw24592step0 raw24592step0Labels = mixedMoment B raw24592step1 raw24592step1Labels := by
      have ha : raw24592step1 = (fun i j => raw24592step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24592step1 raw24592step0; decide +kernel
      have hl : raw24592step1Labels = raw24592step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24592step0 raw24592step0Labels permutation33 permutation3
    _ = mixedMoment B node573 node573Labels := by rfl

def raw24593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw24593Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24593step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24593 raw24593Labels = mixedMoment B node1108 node1108Labels := by
  calc
    mixedMoment B raw24593 raw24593Labels = mixedMoment B raw24593step0 raw24593step0Labels := by
      have ha : raw24593step0 = (fun i j => raw24593 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24593step0 raw24593; decide +kernel
      have hl : raw24593step0Labels = raw24593Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24593 raw24593Labels permutation153 permutation3
    _ = mixedMoment B node1108 node1108Labels := by rfl

def raw24594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw24594Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw24594step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24594step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24594 raw24594Labels = mixedMoment B node1102 node1102Labels := by
  calc
    mixedMoment B raw24594 raw24594Labels = mixedMoment B raw24594step0 raw24594step0Labels := by
      have hz : ∀ j, raw24594 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24594step0 = (fun i j => raw24594 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24594step0 raw24594; decide +kernel
      have hl : raw24594step0Labels = raw24594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24594 raw24594Labels permutation265 hz
    mixedMoment B raw24594step0 raw24594step0Labels = mixedMoment B raw24594step1 raw24594step1Labels := by
      have ha : raw24594step1 = (fun i j => raw24594step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24594step1 raw24594step0; decide +kernel
      have hl : raw24594step1Labels = raw24594step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24594step0 raw24594step0Labels permutation33 permutation3
    _ = mixedMoment B node1102 node1102Labels := by rfl

def raw24595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw24595Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24595step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24595step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24595step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24595step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24595step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24595 raw24595Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw24595 raw24595Labels = mixedMoment B raw24595step0 raw24595step0Labels := by
      have hz : ∀ j, raw24595 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24595step0 = (fun i j => raw24595 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24595step0 raw24595; decide +kernel
      have hl : raw24595step0Labels = raw24595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24595 raw24595Labels permutation434 hz
    mixedMoment B raw24595step0 raw24595step0Labels = mixedMoment B raw24595step1 raw24595step1Labels := by
      have hz : ∀ j, raw24595step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24595step1 = (fun i j => raw24595step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24595step1 raw24595step0; decide +kernel
      have hl : raw24595step1Labels = raw24595step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24595step0 raw24595step0Labels permutation56 hz
    mixedMoment B raw24595step1 raw24595step1Labels = mixedMoment B raw24595step2 raw24595step2Labels := by
      have ha : raw24595step2 = (fun i j => raw24595step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24595step2 raw24595step1; decide +kernel
      have hl : raw24595step2Labels = raw24595step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24595step1 raw24595step1Labels permutation9 permutation3
    _ = mixedMoment B node1246 node1246Labels := by rfl

def raw24596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw24596Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw24596step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw24596step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24596 raw24596Labels = mixedMoment B node572 node572Labels := by
  calc
    mixedMoment B raw24596 raw24596Labels = mixedMoment B raw24596step0 raw24596step0Labels := by
      have hz : ∀ j, raw24596 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24596step0 = (fun i j => raw24596 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24596step0 raw24596; decide +kernel
      have hl : raw24596step0Labels = raw24596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24596 raw24596Labels permutation265 hz
    mixedMoment B raw24596step0 raw24596step0Labels = mixedMoment B raw24596step1 raw24596step1Labels := by
      have ha : raw24596step1 = (fun i j => raw24596step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24596step1 raw24596step0; decide +kernel
      have hl : raw24596step1Labels = raw24596step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24596step0 raw24596step0Labels permutation32 permutation3
    _ = mixedMoment B node572 node572Labels := by rfl

def raw24597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw24597Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw24597step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24597 raw24597Labels = mixedMoment B node1107 node1107Labels := by
  calc
    mixedMoment B raw24597 raw24597Labels = mixedMoment B raw24597step0 raw24597step0Labels := by
      have ha : raw24597step0 = (fun i j => raw24597 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24597step0 raw24597; decide +kernel
      have hl : raw24597step0Labels = raw24597Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24597 raw24597Labels permutation152 permutation3
    _ = mixedMoment B node1107 node1107Labels := by rfl

def raw24598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw24598Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw24598step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24598step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw24598step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24598 raw24598Labels = mixedMoment B node1101 node1101Labels := by
  calc
    mixedMoment B raw24598 raw24598Labels = mixedMoment B raw24598step0 raw24598step0Labels := by
      have hz : ∀ j, raw24598 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24598step0 = (fun i j => raw24598 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24598step0 raw24598; decide +kernel
      have hl : raw24598step0Labels = raw24598Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24598 raw24598Labels permutation265 hz
    mixedMoment B raw24598step0 raw24598step0Labels = mixedMoment B raw24598step1 raw24598step1Labels := by
      have ha : raw24598step1 = (fun i j => raw24598step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24598step1 raw24598step0; decide +kernel
      have hl : raw24598step1Labels = raw24598step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24598step0 raw24598step0Labels permutation32 permutation3
    _ = mixedMoment B node1101 node1101Labels := by rfl

def raw24599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw24599Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw24599step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24599step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw24599step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24599step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw24599step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24599 raw24599Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw24599 raw24599Labels = mixedMoment B raw24599step0 raw24599step0Labels := by
      have hz : ∀ j, raw24599 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24599step0 = (fun i j => raw24599 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24599step0 raw24599; decide +kernel
      have hl : raw24599step0Labels = raw24599Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24599 raw24599Labels permutation434 hz
    mixedMoment B raw24599step0 raw24599step0Labels = mixedMoment B raw24599step1 raw24599step1Labels := by
      have hz : ∀ j, raw24599step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24599step1 = (fun i j => raw24599step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24599step1 raw24599step0; decide +kernel
      have hl : raw24599step1Labels = raw24599step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24599step0 raw24599step0Labels permutation56 hz
    mixedMoment B raw24599step1 raw24599step1Labels = mixedMoment B raw24599step2 raw24599step2Labels := by
      have ha : raw24599step2 = (fun i j => raw24599step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24599step2 raw24599step1; decide +kernel
      have hl : raw24599step2Labels = raw24599step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24599step1 raw24599step1Labels permutation8 permutation3
    _ = mixedMoment B node1242 node1242Labels := by rfl

def raw24600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -2, -1]]
def raw24600Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw24600step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24600step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw24600step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24600step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw24600step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24600 raw24600Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw24600 raw24600Labels = mixedMoment B raw24600step0 raw24600step0Labels := by
      have hz : ∀ j, raw24600 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24600step0 = (fun i j => raw24600 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24600step0 raw24600; decide +kernel
      have hl : raw24600step0Labels = raw24600Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24600 raw24600Labels permutation520 hz
    mixedMoment B raw24600step0 raw24600step0Labels = mixedMoment B raw24600step1 raw24600step1Labels := by
      have hz : ∀ j, raw24600step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24600step1 = (fun i j => raw24600step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24600step1 raw24600step0; decide +kernel
      have hl : raw24600step1Labels = raw24600step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24600step0 raw24600step0Labels permutation56 hz
    mixedMoment B raw24600step1 raw24600step1Labels = mixedMoment B raw24600step2 raw24600step2Labels := by
      have ha : raw24600step2 = (fun i j => raw24600step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24600step2 raw24600step1; decide +kernel
      have hl : raw24600step2Labels = raw24600step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24600step1 raw24600step1Labels permutation8 permutation3
    _ = mixedMoment B node1242 node1242Labels := by rfl

def raw24601 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24601Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24601step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24601step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24601step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24601step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24601 raw24601Labels = mixedMoment B node4438 node4438Labels := by
  calc
    mixedMoment B raw24601 raw24601Labels = mixedMoment B raw24601step0 raw24601step0Labels := by
      have ha : raw24601step0 = (fun i j => raw24601 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24601step0 raw24601; decide +kernel
      have hl : raw24601step0Labels = raw24601Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24601 raw24601Labels permutation152 permutation7
    mixedMoment B raw24601step0 raw24601step0Labels = mixedMoment B raw24601step1 raw24601step1Labels := by
      have ha : raw24601step1 = raw24601step0 := by apply Matrix.ext; unfold raw24601step1 raw24601step0; decide +kernel
      have hl : raw24601step0Labels = labelEmbedding10 ∘ raw24601step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24601step0 raw24601step0Labels raw24601step1Labels labelEmbedding10 hl
    _ = mixedMoment B node4438 node4438Labels := by rfl

def raw24602 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24602Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24602step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24602step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24602step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw24602step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24602 raw24602Labels = mixedMoment B node4474 node4474Labels := by
  calc
    mixedMoment B raw24602 raw24602Labels = mixedMoment B raw24602step0 raw24602step0Labels := by
      have hz : ∀ j, raw24602 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24602step0 = (fun i j => raw24602 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24602step0 raw24602; decide +kernel
      have hl : raw24602step0Labels = raw24602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24602 raw24602Labels permutation265 hz
    mixedMoment B raw24602step0 raw24602step0Labels = mixedMoment B raw24602step1 raw24602step1Labels := by
      have ha : raw24602step1 = (fun i j => raw24602step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24602step1 raw24602step0; decide +kernel
      have hl : raw24602step1Labels = raw24602step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24602step0 raw24602step0Labels permutation32 permutation7
    mixedMoment B raw24602step1 raw24602step1Labels = mixedMoment B raw24602step2 raw24602step2Labels := by
      have ha : raw24602step2 = raw24602step1 := by apply Matrix.ext; unfold raw24602step2 raw24602step1; decide +kernel
      have hl : raw24602step1Labels = labelEmbedding10 ∘ raw24602step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24602step1 raw24602step1Labels raw24602step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4474 node4474Labels := by rfl

def raw24603 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24603Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24603step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24603step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24603step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24603step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24603step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24603 raw24603Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw24603 raw24603Labels = mixedMoment B raw24603step0 raw24603step0Labels := by
      have hz : ∀ j, raw24603 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24603step0 = (fun i j => raw24603 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24603step0 raw24603; decide +kernel
      have hl : raw24603step0Labels = raw24603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24603 raw24603Labels permutation265 hz
    mixedMoment B raw24603step0 raw24603step0Labels = mixedMoment B raw24603step1 raw24603step1Labels := by
      have ha : raw24603step1 = (fun i j => raw24603step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24603step1 raw24603step0; decide +kernel
      have hl : raw24603step1Labels = raw24603step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24603step0 raw24603step0Labels permutation32 permutation7
    mixedMoment B raw24603step1 raw24603step1Labels = mixedMoment B raw24603step2 raw24603step2Labels := by
      have ha : raw24603step2 = raw24603step1 := by apply Matrix.ext; unfold raw24603step2 raw24603step1; decide +kernel
      have hl : raw24603step1Labels = labelEmbedding10 ∘ raw24603step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24603step1 raw24603step1Labels raw24603step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw24604 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24604step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24604step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24604step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24604step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24604 raw24604Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw24604 raw24604Labels = mixedMoment B raw24604step0 raw24604step0Labels := by
      have hz : ∀ j, raw24604 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24604step0 = (fun i j => raw24604 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24604step0 raw24604; decide +kernel
      have hl : raw24604step0Labels = raw24604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24604 raw24604Labels permutation265 hz
    mixedMoment B raw24604step0 raw24604step0Labels = mixedMoment B raw24604step1 raw24604step1Labels := by
      have ha : raw24604step1 = (fun i j => raw24604step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24604step1 raw24604step0; decide +kernel
      have hl : raw24604step1Labels = raw24604step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24604step0 raw24604step0Labels permutation32 permutation7
    mixedMoment B raw24604step1 raw24604step1Labels = mixedMoment B raw24604step2 raw24604step2Labels := by
      have ha : raw24604step2 = raw24604step1 := by apply Matrix.ext; unfold raw24604step2 raw24604step1; decide +kernel
      have hl : raw24604step1Labels = labelEmbedding10 ∘ raw24604step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24604step1 raw24604step1Labels raw24604step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4457 node4457Labels := by rfl

def raw24605 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24605step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24605step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24605step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24605step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24605 raw24605Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw24605 raw24605Labels = mixedMoment B raw24605step0 raw24605step0Labels := by
      have ha : raw24605step0 = (fun i j => raw24605 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24605step0 raw24605; decide +kernel
      have hl : raw24605step0Labels = raw24605Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24605 raw24605Labels permutation176 permutation6
    mixedMoment B raw24605step0 raw24605step0Labels = mixedMoment B raw24605step1 raw24605step1Labels := by
      have ha : raw24605step1 = raw24605step0 := by apply Matrix.ext; unfold raw24605step1 raw24605step0; decide +kernel
      have hl : raw24605step0Labels = labelEmbedding9 ∘ raw24605step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24605step0 raw24605step0Labels raw24605step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4399 node4399Labels := by rfl

def raw24606 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24606step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24606step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24606step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24606step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24606 raw24606Labels = mixedMoment B node4563 node4563Labels := by
  calc
    mixedMoment B raw24606 raw24606Labels = mixedMoment B raw24606step0 raw24606step0Labels := by
      have ha : raw24606step0 = (fun i j => raw24606 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24606step0 raw24606; decide +kernel
      have hl : raw24606step0Labels = raw24606Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24606 raw24606Labels permutation176 permutation6
    mixedMoment B raw24606step0 raw24606step0Labels = mixedMoment B raw24606step1 raw24606step1Labels := by
      have ha : raw24606step1 = raw24606step0 := by apply Matrix.ext; unfold raw24606step1 raw24606step0; decide +kernel
      have hl : raw24606step0Labels = labelEmbedding9 ∘ raw24606step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24606step0 raw24606step0Labels raw24606step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4563 node4563Labels := by rfl

def raw24607 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24607step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24607step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24607step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24607step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24607 raw24607Labels = mixedMoment B node4590 node4590Labels := by
  calc
    mixedMoment B raw24607 raw24607Labels = mixedMoment B raw24607step0 raw24607step0Labels := by
      have ha : raw24607step0 = (fun i j => raw24607 (permutation178 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24607step0 raw24607; decide +kernel
      have hl : raw24607step0Labels = raw24607Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24607 raw24607Labels permutation178 permutation6
    mixedMoment B raw24607step0 raw24607step0Labels = mixedMoment B raw24607step1 raw24607step1Labels := by
      have ha : raw24607step1 = raw24607step0 := by apply Matrix.ext; unfold raw24607step1 raw24607step0; decide +kernel
      have hl : raw24607step0Labels = labelEmbedding9 ∘ raw24607step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24607step0 raw24607step0Labels raw24607step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4590 node4590Labels := by rfl

def raw24608 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24608step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24608step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24608step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24608step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24608 raw24608Labels = mixedMoment B node4589 node4589Labels := by
  calc
    mixedMoment B raw24608 raw24608Labels = mixedMoment B raw24608step0 raw24608step0Labels := by
      have ha : raw24608step0 = (fun i j => raw24608 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24608step0 raw24608; decide +kernel
      have hl : raw24608step0Labels = raw24608Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24608 raw24608Labels permutation152 permutation7
    mixedMoment B raw24608step0 raw24608step0Labels = mixedMoment B raw24608step1 raw24608step1Labels := by
      have ha : raw24608step1 = raw24608step0 := by apply Matrix.ext; unfold raw24608step1 raw24608step0; decide +kernel
      have hl : raw24608step0Labels = labelEmbedding10 ∘ raw24608step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24608step0 raw24608step0Labels raw24608step1Labels labelEmbedding10 hl
    _ = mixedMoment B node4589 node4589Labels := by rfl

def raw24609 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24609step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24609step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24609step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24609step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24609step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24609 raw24609Labels = mixedMoment B node4424 node4424Labels := by
  calc
    mixedMoment B raw24609 raw24609Labels = mixedMoment B raw24609step0 raw24609step0Labels := by
      have hz : ∀ j, raw24609 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24609step0 = (fun i j => raw24609 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24609step0 raw24609; decide +kernel
      have hl : raw24609step0Labels = raw24609Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24609 raw24609Labels permutation265 hz
    mixedMoment B raw24609step0 raw24609step0Labels = mixedMoment B raw24609step1 raw24609step1Labels := by
      have ha : raw24609step1 = (fun i j => raw24609step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24609step1 raw24609step0; decide +kernel
      have hl : raw24609step1Labels = raw24609step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24609step0 raw24609step0Labels permutation34 permutation6
    mixedMoment B raw24609step1 raw24609step1Labels = mixedMoment B raw24609step2 raw24609step2Labels := by
      have ha : raw24609step2 = raw24609step1 := by apply Matrix.ext; unfold raw24609step2 raw24609step1; decide +kernel
      have hl : raw24609step1Labels = labelEmbedding9 ∘ raw24609step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24609step1 raw24609step1Labels raw24609step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4424 node4424Labels := by rfl

def raw24610 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24610step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24610step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24610step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24610step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24610 raw24610Labels = mixedMoment B node4582 node4582Labels := by
  calc
    mixedMoment B raw24610 raw24610Labels = mixedMoment B raw24610step0 raw24610step0Labels := by
      have ha : raw24610step0 = (fun i j => raw24610 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24610step0 raw24610; decide +kernel
      have hl : raw24610step0Labels = raw24610Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24610 raw24610Labels permutation154 permutation6
    mixedMoment B raw24610step0 raw24610step0Labels = mixedMoment B raw24610step1 raw24610step1Labels := by
      have ha : raw24610step1 = raw24610step0 := by apply Matrix.ext; unfold raw24610step1 raw24610step0; decide +kernel
      have hl : raw24610step0Labels = labelEmbedding9 ∘ raw24610step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24610step0 raw24610step0Labels raw24610step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4582 node4582Labels := by rfl

def raw24611 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24611step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24611step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24611step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24611step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24611 raw24611Labels = mixedMoment B node4571 node4571Labels := by
  calc
    mixedMoment B raw24611 raw24611Labels = mixedMoment B raw24611step0 raw24611step0Labels := by
      have hz : ∀ j, raw24611 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24611step0 = (fun i j => raw24611 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24611step0 raw24611; decide +kernel
      have hl : raw24611step0Labels = raw24611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24611 raw24611Labels permutation265 hz
    mixedMoment B raw24611step0 raw24611step0Labels = mixedMoment B raw24611step1 raw24611step1Labels := by
      have ha : raw24611step1 = (fun i j => raw24611step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24611step1 raw24611step0; decide +kernel
      have hl : raw24611step1Labels = raw24611step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24611step0 raw24611step0Labels permutation34 permutation6
    mixedMoment B raw24611step1 raw24611step1Labels = mixedMoment B raw24611step2 raw24611step2Labels := by
      have ha : raw24611step2 = raw24611step1 := by apply Matrix.ext; unfold raw24611step2 raw24611step1; decide +kernel
      have hl : raw24611step1Labels = labelEmbedding9 ∘ raw24611step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24611step1 raw24611step1Labels raw24611step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4571 node4571Labels := by rfl

def raw24612 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24612Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24612step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24612step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24612step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24612step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24612 raw24612Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw24612 raw24612Labels = mixedMoment B raw24612step0 raw24612step0Labels := by
      have hz : ∀ j, raw24612 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24612step0 = (fun i j => raw24612 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24612step0 raw24612; decide +kernel
      have hl : raw24612step0Labels = raw24612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24612 raw24612Labels permutation265 hz
    mixedMoment B raw24612step0 raw24612step0Labels = mixedMoment B raw24612step1 raw24612step1Labels := by
      have ha : raw24612step1 = (fun i j => raw24612step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24612step1 raw24612step0; decide +kernel
      have hl : raw24612step1Labels = raw24612step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24612step0 raw24612step0Labels permutation34 permutation6
    mixedMoment B raw24612step1 raw24612step1Labels = mixedMoment B raw24612step2 raw24612step2Labels := by
      have ha : raw24612step2 = raw24612step1 := by apply Matrix.ext; unfold raw24612step2 raw24612step1; decide +kernel
      have hl : raw24612step1Labels = labelEmbedding9 ∘ raw24612step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24612step1 raw24612step1Labels raw24612step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4603 node4603Labels := by rfl

def raw24613 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24613step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24613step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24613step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24613step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24613 raw24613Labels = mixedMoment B node4607 node4607Labels := by
  calc
    mixedMoment B raw24613 raw24613Labels = mixedMoment B raw24613step0 raw24613step0Labels := by
      have hz : ∀ j, raw24613 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24613step0 = (fun i j => raw24613 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24613step0 raw24613; decide +kernel
      have hl : raw24613step0Labels = raw24613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24613 raw24613Labels permutation265 hz
    mixedMoment B raw24613step0 raw24613step0Labels = mixedMoment B raw24613step1 raw24613step1Labels := by
      have ha : raw24613step1 = (fun i j => raw24613step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24613step1 raw24613step0; decide +kernel
      have hl : raw24613step1Labels = raw24613step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24613step0 raw24613step0Labels permutation34 permutation6
    mixedMoment B raw24613step1 raw24613step1Labels = mixedMoment B raw24613step2 raw24613step2Labels := by
      have ha : raw24613step2 = raw24613step1 := by apply Matrix.ext; unfold raw24613step2 raw24613step1; decide +kernel
      have hl : raw24613step1Labels = labelEmbedding9 ∘ raw24613step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24613step1 raw24613step1Labels raw24613step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4607 node4607Labels := by rfl

def raw24614 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24614Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24614step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24614step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24614step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24614step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24614 raw24614Labels = mixedMoment B node4424 node4424Labels := by
  calc
    mixedMoment B raw24614 raw24614Labels = mixedMoment B raw24614step0 raw24614step0Labels := by
      have hz : ∀ j, raw24614 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24614step0 = (fun i j => raw24614 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24614step0 raw24614; decide +kernel
      have hl : raw24614step0Labels = raw24614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24614 raw24614Labels permutation265 hz
    mixedMoment B raw24614step0 raw24614step0Labels = mixedMoment B raw24614step1 raw24614step1Labels := by
      have ha : raw24614step1 = (fun i j => raw24614step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24614step1 raw24614step0; decide +kernel
      have hl : raw24614step1Labels = raw24614step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24614step0 raw24614step0Labels permutation32 permutation6
    mixedMoment B raw24614step1 raw24614step1Labels = mixedMoment B raw24614step2 raw24614step2Labels := by
      have ha : raw24614step2 = raw24614step1 := by apply Matrix.ext; unfold raw24614step2 raw24614step1; decide +kernel
      have hl : raw24614step1Labels = labelEmbedding9 ∘ raw24614step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24614step1 raw24614step1Labels raw24614step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4424 node4424Labels := by rfl

def raw24615 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24615Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24615step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24615step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24615step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24615step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24615 raw24615Labels = mixedMoment B node4582 node4582Labels := by
  calc
    mixedMoment B raw24615 raw24615Labels = mixedMoment B raw24615step0 raw24615step0Labels := by
      have ha : raw24615step0 = (fun i j => raw24615 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24615step0 raw24615; decide +kernel
      have hl : raw24615step0Labels = raw24615Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24615 raw24615Labels permutation152 permutation6
    mixedMoment B raw24615step0 raw24615step0Labels = mixedMoment B raw24615step1 raw24615step1Labels := by
      have ha : raw24615step1 = raw24615step0 := by apply Matrix.ext; unfold raw24615step1 raw24615step0; decide +kernel
      have hl : raw24615step0Labels = labelEmbedding9 ∘ raw24615step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24615step0 raw24615step0Labels raw24615step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4582 node4582Labels := by rfl

def raw24616 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24616step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24616step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24616step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24616step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24616 raw24616Labels = mixedMoment B node4571 node4571Labels := by
  calc
    mixedMoment B raw24616 raw24616Labels = mixedMoment B raw24616step0 raw24616step0Labels := by
      have hz : ∀ j, raw24616 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24616step0 = (fun i j => raw24616 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24616step0 raw24616; decide +kernel
      have hl : raw24616step0Labels = raw24616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24616 raw24616Labels permutation265 hz
    mixedMoment B raw24616step0 raw24616step0Labels = mixedMoment B raw24616step1 raw24616step1Labels := by
      have ha : raw24616step1 = (fun i j => raw24616step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24616step1 raw24616step0; decide +kernel
      have hl : raw24616step1Labels = raw24616step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24616step0 raw24616step0Labels permutation32 permutation6
    mixedMoment B raw24616step1 raw24616step1Labels = mixedMoment B raw24616step2 raw24616step2Labels := by
      have ha : raw24616step2 = raw24616step1 := by apply Matrix.ext; unfold raw24616step2 raw24616step1; decide +kernel
      have hl : raw24616step1Labels = labelEmbedding9 ∘ raw24616step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24616step1 raw24616step1Labels raw24616step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4571 node4571Labels := by rfl

def raw24617 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24617step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24617step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24617step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24617step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24617 raw24617Labels = mixedMoment B node4423 node4423Labels := by
  calc
    mixedMoment B raw24617 raw24617Labels = mixedMoment B raw24617step0 raw24617step0Labels := by
      have hz : ∀ j, raw24617 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24617step0 = (fun i j => raw24617 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24617step0 raw24617; decide +kernel
      have hl : raw24617step0Labels = raw24617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24617 raw24617Labels permutation265 hz
    mixedMoment B raw24617step0 raw24617step0Labels = mixedMoment B raw24617step1 raw24617step1Labels := by
      have ha : raw24617step1 = (fun i j => raw24617step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24617step1 raw24617step0; decide +kernel
      have hl : raw24617step1Labels = raw24617step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24617step0 raw24617step0Labels permutation32 permutation6
    mixedMoment B raw24617step1 raw24617step1Labels = mixedMoment B raw24617step2 raw24617step2Labels := by
      have ha : raw24617step2 = raw24617step1 := by apply Matrix.ext; unfold raw24617step2 raw24617step1; decide +kernel
      have hl : raw24617step1Labels = labelEmbedding9 ∘ raw24617step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24617step1 raw24617step1Labels raw24617step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4423 node4423Labels := by rfl

def raw24618 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24618Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24618step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24618step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24618step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24618 raw24618Labels = mixedMoment B node4581 node4581Labels := by
  calc
    mixedMoment B raw24618 raw24618Labels = mixedMoment B raw24618step0 raw24618step0Labels := by
      have ha : raw24618step0 = (fun i j => raw24618 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24618step0 raw24618; decide +kernel
      have hl : raw24618step0Labels = raw24618Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24618 raw24618Labels permutation152 permutation6
    mixedMoment B raw24618step0 raw24618step0Labels = mixedMoment B raw24618step1 raw24618step1Labels := by
      have ha : raw24618step1 = raw24618step0 := by apply Matrix.ext; unfold raw24618step1 raw24618step0; decide +kernel
      have hl : raw24618step0Labels = labelEmbedding9 ∘ raw24618step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24618step0 raw24618step0Labels raw24618step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4581 node4581Labels := by rfl

def raw24619 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24619step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24619step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24619step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24619step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24619 raw24619Labels = mixedMoment B node4570 node4570Labels := by
  calc
    mixedMoment B raw24619 raw24619Labels = mixedMoment B raw24619step0 raw24619step0Labels := by
      have hz : ∀ j, raw24619 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24619step0 = (fun i j => raw24619 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24619step0 raw24619; decide +kernel
      have hl : raw24619step0Labels = raw24619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24619 raw24619Labels permutation265 hz
    mixedMoment B raw24619step0 raw24619step0Labels = mixedMoment B raw24619step1 raw24619step1Labels := by
      have ha : raw24619step1 = (fun i j => raw24619step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24619step1 raw24619step0; decide +kernel
      have hl : raw24619step1Labels = raw24619step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24619step0 raw24619step0Labels permutation32 permutation6
    mixedMoment B raw24619step1 raw24619step1Labels = mixedMoment B raw24619step2 raw24619step2Labels := by
      have ha : raw24619step2 = raw24619step1 := by apply Matrix.ext; unfold raw24619step2 raw24619step1; decide +kernel
      have hl : raw24619step1Labels = labelEmbedding9 ∘ raw24619step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24619step1 raw24619step1Labels raw24619step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4570 node4570Labels := by rfl

def raw24620 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24620Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24620step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24620 raw24620Labels = mixedMoment B node1386 node1386Labels := by
  calc
    mixedMoment B raw24620 raw24620Labels = mixedMoment B raw24620step0 raw24620step0Labels := by
      have ha : raw24620step0 = (fun i j => raw24620 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24620step0 raw24620; decide +kernel
      have hl : raw24620step0Labels = raw24620Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24620 raw24620Labels permutation152 permutation6
    _ = mixedMoment B node1386 node1386Labels := by rfl

def raw24621 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24621Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24621step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24621step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24621 raw24621Labels = mixedMoment B node1370 node1370Labels := by
  calc
    mixedMoment B raw24621 raw24621Labels = mixedMoment B raw24621step0 raw24621step0Labels := by
      have hz : ∀ j, raw24621 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24621step0 = (fun i j => raw24621 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24621step0 raw24621; decide +kernel
      have hl : raw24621step0Labels = raw24621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24621 raw24621Labels permutation265 hz
    mixedMoment B raw24621step0 raw24621step0Labels = mixedMoment B raw24621step1 raw24621step1Labels := by
      have ha : raw24621step1 = (fun i j => raw24621step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24621step1 raw24621step0; decide +kernel
      have hl : raw24621step1Labels = raw24621step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24621step0 raw24621step0Labels permutation32 permutation6
    _ = mixedMoment B node1370 node1370Labels := by rfl

def raw24622 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24622Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24622step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24622step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24622 raw24622Labels = mixedMoment B node1411 node1411Labels := by
  calc
    mixedMoment B raw24622 raw24622Labels = mixedMoment B raw24622step0 raw24622step0Labels := by
      have hz : ∀ j, raw24622 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24622step0 = (fun i j => raw24622 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24622step0 raw24622; decide +kernel
      have hl : raw24622step0Labels = raw24622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24622 raw24622Labels permutation265 hz
    mixedMoment B raw24622step0 raw24622step0Labels = mixedMoment B raw24622step1 raw24622step1Labels := by
      have ha : raw24622step1 = (fun i j => raw24622step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24622step1 raw24622step0; decide +kernel
      have hl : raw24622step1Labels = raw24622step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24622step0 raw24622step0Labels permutation32 permutation6
    _ = mixedMoment B node1411 node1411Labels := by rfl

def raw24623 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24623Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24623step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24623step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24623step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24623 raw24623Labels = mixedMoment B node1411 node1411Labels := by
  calc
    mixedMoment B raw24623 raw24623Labels = mixedMoment B raw24623step0 raw24623step0Labels := by
      have hz : ∀ j, raw24623 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24623step0 = (fun i j => raw24623 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24623step0 raw24623; decide +kernel
      have hl : raw24623step0Labels = raw24623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24623 raw24623Labels permutation265 hz
    mixedMoment B raw24623step0 raw24623step0Labels = mixedMoment B raw24623step1 raw24623step1Labels := by
      have ha : raw24623step1 = (fun i j => raw24623step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24623step1 raw24623step0; decide +kernel
      have hl : raw24623step1Labels = raw24623step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24623step0 raw24623step0Labels permutation34 permutation6
    _ = mixedMoment B node1411 node1411Labels := by rfl

def raw24624 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24624Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24624step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24624step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24624 raw24624Labels = mixedMoment B node1414 node1414Labels := by
  calc
    mixedMoment B raw24624 raw24624Labels = mixedMoment B raw24624step0 raw24624step0Labels := by
      have hz : ∀ j, raw24624 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24624step0 = (fun i j => raw24624 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24624step0 raw24624; decide +kernel
      have hl : raw24624step0Labels = raw24624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24624 raw24624Labels permutation265 hz
    mixedMoment B raw24624step0 raw24624step0Labels = mixedMoment B raw24624step1 raw24624step1Labels := by
      have ha : raw24624step1 = (fun i j => raw24624step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24624step1 raw24624step0; decide +kernel
      have hl : raw24624step1Labels = raw24624step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24624step0 raw24624step0Labels permutation32 permutation6
    _ = mixedMoment B node1414 node1414Labels := by rfl

def raw24625 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24625Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24625step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24625step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24625 raw24625Labels = mixedMoment B node980 node980Labels := by
  calc
    mixedMoment B raw24625 raw24625Labels = mixedMoment B raw24625step0 raw24625step0Labels := by
      have ha : raw24625step0 = (fun i j => raw24625 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24625step0 raw24625; decide +kernel
      have hl : raw24625step0Labels = raw24625Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24625 raw24625Labels permutation176 permutation6
    _ = mixedMoment B node980 node980Labels := by rfl

def raw24626 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24626Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24626step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24626step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24626 raw24626Labels = mixedMoment B node1180 node1180Labels := by
  calc
    mixedMoment B raw24626 raw24626Labels = mixedMoment B raw24626step0 raw24626step0Labels := by
      have ha : raw24626step0 = (fun i j => raw24626 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24626step0 raw24626; decide +kernel
      have hl : raw24626step0Labels = raw24626Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24626 raw24626Labels permutation176 permutation6
    _ = mixedMoment B node1180 node1180Labels := by rfl

def raw24627 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24627Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24627step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24627step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24627 raw24627Labels = mixedMoment B node1213 node1213Labels := by
  calc
    mixedMoment B raw24627 raw24627Labels = mixedMoment B raw24627step0 raw24627step0Labels := by
      have ha : raw24627step0 = (fun i j => raw24627 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24627step0 raw24627; decide +kernel
      have hl : raw24627step0Labels = raw24627Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24627 raw24627Labels permutation176 permutation6
    _ = mixedMoment B node1213 node1213Labels := by rfl

def raw24628 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24628Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24628step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24628 raw24628Labels = mixedMoment B node1213 node1213Labels := by
  calc
    mixedMoment B raw24628 raw24628Labels = mixedMoment B raw24628step0 raw24628step0Labels := by
      have ha : raw24628step0 = (fun i j => raw24628 (permutation178 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24628step0 raw24628; decide +kernel
      have hl : raw24628step0Labels = raw24628Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24628 raw24628Labels permutation178 permutation6
    _ = mixedMoment B node1213 node1213Labels := by rfl

def raw24629 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24629Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24629step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24629 raw24629Labels = mixedMoment B node1216 node1216Labels := by
  calc
    mixedMoment B raw24629 raw24629Labels = mixedMoment B raw24629step0 raw24629step0Labels := by
      have ha : raw24629step0 = (fun i j => raw24629 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24629step0 raw24629; decide +kernel
      have hl : raw24629step0Labels = raw24629Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24629 raw24629Labels permutation176 permutation6
    _ = mixedMoment B node1216 node1216Labels := by rfl

def raw24630 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24630Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24630step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24630step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24630step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24630step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24630step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24630 raw24630Labels = mixedMoment B node1086 node1086Labels := by
  calc
    mixedMoment B raw24630 raw24630Labels = mixedMoment B raw24630step0 raw24630step0Labels := by
      have hz : ∀ j, raw24630 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24630step0 = (fun i j => raw24630 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24630step0 raw24630; decide +kernel
      have hl : raw24630step0Labels = raw24630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24630 raw24630Labels permutation346 hz
    mixedMoment B raw24630step0 raw24630step0Labels = mixedMoment B raw24630step1 raw24630step1Labels := by
      have hz : ∀ j, raw24630step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24630step1 = (fun i j => raw24630step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24630step1 raw24630step0; decide +kernel
      have hl : raw24630step1Labels = raw24630step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24630step0 raw24630step0Labels permutation56 hz
    mixedMoment B raw24630step1 raw24630step1Labels = mixedMoment B raw24630step2 raw24630step2Labels := by
      have ha : raw24630step2 = (fun i j => raw24630step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24630step2 raw24630step1; decide +kernel
      have hl : raw24630step2Labels = raw24630step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24630step1 raw24630step1Labels permutation8 permutation6
    _ = mixedMoment B node1086 node1086Labels := by rfl

def raw24631 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24631Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24631step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24631step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24631step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24631 raw24631Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw24631 raw24631Labels = mixedMoment B raw24631step0 raw24631step0Labels := by
      have hz : ∀ j, raw24631 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24631step0 = (fun i j => raw24631 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24631step0 raw24631; decide +kernel
      have hl : raw24631step0Labels = raw24631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24631 raw24631Labels permutation346 hz
    mixedMoment B raw24631step0 raw24631step0Labels = mixedMoment B raw24631step1 raw24631step1Labels := by
      have ha : raw24631step1 = (fun i j => raw24631step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24631step1 raw24631step0; decide +kernel
      have hl : raw24631step1Labels = raw24631step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24631step0 raw24631step0Labels permutation32 permutation6
    _ = mixedMoment B node1240 node1240Labels := by rfl

def raw24632 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24632Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24632step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24632step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24632step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24632step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24632step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24632 raw24632Labels = mixedMoment B node1301 node1301Labels := by
  calc
    mixedMoment B raw24632 raw24632Labels = mixedMoment B raw24632step0 raw24632step0Labels := by
      have hz : ∀ j, raw24632 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24632step0 = (fun i j => raw24632 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24632step0 raw24632; decide +kernel
      have hl : raw24632step0Labels = raw24632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24632 raw24632Labels permutation346 hz
    mixedMoment B raw24632step0 raw24632step0Labels = mixedMoment B raw24632step1 raw24632step1Labels := by
      have hz : ∀ j, raw24632step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24632step1 = (fun i j => raw24632step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24632step1 raw24632step0; decide +kernel
      have hl : raw24632step1Labels = raw24632step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24632step0 raw24632step0Labels permutation56 hz
    mixedMoment B raw24632step1 raw24632step1Labels = mixedMoment B raw24632step2 raw24632step2Labels := by
      have ha : raw24632step2 = (fun i j => raw24632step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24632step2 raw24632step1; decide +kernel
      have hl : raw24632step2Labels = raw24632step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24632step1 raw24632step1Labels permutation8 permutation6
    _ = mixedMoment B node1301 node1301Labels := by rfl

def raw24633 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24633Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24633step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24633step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24633step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24633step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw24633step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24633 raw24633Labels = mixedMoment B node1301 node1301Labels := by
  calc
    mixedMoment B raw24633 raw24633Labels = mixedMoment B raw24633step0 raw24633step0Labels := by
      have hz : ∀ j, raw24633 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24633step0 = (fun i j => raw24633 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24633step0 raw24633; decide +kernel
      have hl : raw24633step0Labels = raw24633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24633 raw24633Labels permutation346 hz
    mixedMoment B raw24633step0 raw24633step0Labels = mixedMoment B raw24633step1 raw24633step1Labels := by
      have hz : ∀ j, raw24633step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24633step1 = (fun i j => raw24633step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24633step1 raw24633step0; decide +kernel
      have hl : raw24633step1Labels = raw24633step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24633step0 raw24633step0Labels permutation56 hz
    mixedMoment B raw24633step1 raw24633step1Labels = mixedMoment B raw24633step2 raw24633step2Labels := by
      have ha : raw24633step2 = (fun i j => raw24633step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24633step2 raw24633step1; decide +kernel
      have hl : raw24633step2Labels = raw24633step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24633step1 raw24633step1Labels permutation10 permutation6
    _ = mixedMoment B node1301 node1301Labels := by rfl

def raw24634 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24634Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24634step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24634step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24634step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24634step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24634step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24634 raw24634Labels = mixedMoment B node1305 node1305Labels := by
  calc
    mixedMoment B raw24634 raw24634Labels = mixedMoment B raw24634step0 raw24634step0Labels := by
      have hz : ∀ j, raw24634 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24634step0 = (fun i j => raw24634 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24634step0 raw24634; decide +kernel
      have hl : raw24634step0Labels = raw24634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24634 raw24634Labels permutation346 hz
    mixedMoment B raw24634step0 raw24634step0Labels = mixedMoment B raw24634step1 raw24634step1Labels := by
      have hz : ∀ j, raw24634step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24634step1 = (fun i j => raw24634step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24634step1 raw24634step0; decide +kernel
      have hl : raw24634step1Labels = raw24634step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24634step0 raw24634step0Labels permutation56 hz
    mixedMoment B raw24634step1 raw24634step1Labels = mixedMoment B raw24634step2 raw24634step2Labels := by
      have ha : raw24634step2 = (fun i j => raw24634step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24634step2 raw24634step1; decide +kernel
      have hl : raw24634step2Labels = raw24634step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24634step1 raw24634step1Labels permutation8 permutation6
    _ = mixedMoment B node1305 node1305Labels := by rfl

def raw24635 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24635Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24635step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24635step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24635 raw24635Labels = mixedMoment B node1005 node1005Labels := by
  calc
    mixedMoment B raw24635 raw24635Labels = mixedMoment B raw24635step0 raw24635step0Labels := by
      have hz : ∀ j, raw24635 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24635step0 = (fun i j => raw24635 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24635step0 raw24635; decide +kernel
      have hl : raw24635step0Labels = raw24635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24635 raw24635Labels permutation265 hz
    mixedMoment B raw24635step0 raw24635step0Labels = mixedMoment B raw24635step1 raw24635step1Labels := by
      have ha : raw24635step1 = (fun i j => raw24635step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24635step1 raw24635step0; decide +kernel
      have hl : raw24635step1Labels = raw24635step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24635step0 raw24635step0Labels permutation34 permutation6
    _ = mixedMoment B node1005 node1005Labels := by rfl

def raw24636 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24636Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24636step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24636step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24636 raw24636Labels = mixedMoment B node1201 node1201Labels := by
  calc
    mixedMoment B raw24636 raw24636Labels = mixedMoment B raw24636step0 raw24636step0Labels := by
      have ha : raw24636step0 = (fun i j => raw24636 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24636step0 raw24636; decide +kernel
      have hl : raw24636step0Labels = raw24636Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24636 raw24636Labels permutation154 permutation6
    _ = mixedMoment B node1201 node1201Labels := by rfl

def raw24637 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24637Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw24637step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24637step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24637 raw24637Labels = mixedMoment B node1189 node1189Labels := by
  calc
    mixedMoment B raw24637 raw24637Labels = mixedMoment B raw24637step0 raw24637step0Labels := by
      have hz : ∀ j, raw24637 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24637step0 = (fun i j => raw24637 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24637step0 raw24637; decide +kernel
      have hl : raw24637step0Labels = raw24637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24637 raw24637Labels permutation265 hz
    mixedMoment B raw24637step0 raw24637step0Labels = mixedMoment B raw24637step1 raw24637step1Labels := by
      have ha : raw24637step1 = (fun i j => raw24637step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24637step1 raw24637step0; decide +kernel
      have hl : raw24637step1Labels = raw24637step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24637step0 raw24637step0Labels permutation34 permutation6
    _ = mixedMoment B node1189 node1189Labels := by rfl

def raw24638 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24638Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw24638step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24638 raw24638Labels = mixedMoment B node1237 node1237Labels := by
  calc
    mixedMoment B raw24638 raw24638Labels = mixedMoment B raw24638step0 raw24638step0Labels := by
      have hz : ∀ j, raw24638 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24638step0 = (fun i j => raw24638 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24638step0 raw24638; decide +kernel
      have hl : raw24638step0Labels = raw24638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24638 raw24638Labels permutation265 hz
    mixedMoment B raw24638step0 raw24638step0Labels = mixedMoment B raw24638step1 raw24638step1Labels := by
      have ha : raw24638step1 = (fun i j => raw24638step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24638step1 raw24638step0; decide +kernel
      have hl : raw24638step1Labels = raw24638step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24638step0 raw24638step0Labels permutation34 permutation6
    _ = mixedMoment B node1237 node1237Labels := by rfl

def raw24639 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24639Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24639step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24639step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24639 raw24639Labels = mixedMoment B node1241 node1241Labels := by
  calc
    mixedMoment B raw24639 raw24639Labels = mixedMoment B raw24639step0 raw24639step0Labels := by
      have hz : ∀ j, raw24639 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24639step0 = (fun i j => raw24639 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24639step0 raw24639; decide +kernel
      have hl : raw24639step0Labels = raw24639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24639 raw24639Labels permutation265 hz
    mixedMoment B raw24639step0 raw24639step0Labels = mixedMoment B raw24639step1 raw24639step1Labels := by
      have ha : raw24639step1 = (fun i j => raw24639step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24639step1 raw24639step0; decide +kernel
      have hl : raw24639step1Labels = raw24639step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24639step0 raw24639step0Labels permutation34 permutation6
    _ = mixedMoment B node1241 node1241Labels := by rfl

def raw24640 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24640Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24640step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24640step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24640 raw24640Labels = mixedMoment B node1005 node1005Labels := by
  calc
    mixedMoment B raw24640 raw24640Labels = mixedMoment B raw24640step0 raw24640step0Labels := by
      have hz : ∀ j, raw24640 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24640step0 = (fun i j => raw24640 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24640step0 raw24640; decide +kernel
      have hl : raw24640step0Labels = raw24640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24640 raw24640Labels permutation265 hz
    mixedMoment B raw24640step0 raw24640step0Labels = mixedMoment B raw24640step1 raw24640step1Labels := by
      have ha : raw24640step1 = (fun i j => raw24640step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24640step1 raw24640step0; decide +kernel
      have hl : raw24640step1Labels = raw24640step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24640step0 raw24640step0Labels permutation32 permutation6
    _ = mixedMoment B node1005 node1005Labels := by rfl

def raw24641 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24641Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24641step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24641step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24641 raw24641Labels = mixedMoment B node1201 node1201Labels := by
  calc
    mixedMoment B raw24641 raw24641Labels = mixedMoment B raw24641step0 raw24641step0Labels := by
      have ha : raw24641step0 = (fun i j => raw24641 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24641step0 raw24641; decide +kernel
      have hl : raw24641step0Labels = raw24641Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24641 raw24641Labels permutation152 permutation6
    _ = mixedMoment B node1201 node1201Labels := by rfl

def raw24642 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24642Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24642step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24642step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24642 raw24642Labels = mixedMoment B node1189 node1189Labels := by
  calc
    mixedMoment B raw24642 raw24642Labels = mixedMoment B raw24642step0 raw24642step0Labels := by
      have hz : ∀ j, raw24642 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24642step0 = (fun i j => raw24642 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24642step0 raw24642; decide +kernel
      have hl : raw24642step0Labels = raw24642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24642 raw24642Labels permutation265 hz
    mixedMoment B raw24642step0 raw24642step0Labels = mixedMoment B raw24642step1 raw24642step1Labels := by
      have ha : raw24642step1 = (fun i j => raw24642step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24642step1 raw24642step0; decide +kernel
      have hl : raw24642step1Labels = raw24642step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24642step0 raw24642step0Labels permutation32 permutation6
    _ = mixedMoment B node1189 node1189Labels := by rfl

def raw24643 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24643Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24643step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24643step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24643step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24643 raw24643Labels = mixedMoment B node1237 node1237Labels := by
  calc
    mixedMoment B raw24643 raw24643Labels = mixedMoment B raw24643step0 raw24643step0Labels := by
      have hz : ∀ j, raw24643 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24643step0 = (fun i j => raw24643 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24643step0 raw24643; decide +kernel
      have hl : raw24643step0Labels = raw24643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24643 raw24643Labels permutation265 hz
    mixedMoment B raw24643step0 raw24643step0Labels = mixedMoment B raw24643step1 raw24643step1Labels := by
      have ha : raw24643step1 = (fun i j => raw24643step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24643step1 raw24643step0; decide +kernel
      have hl : raw24643step1Labels = raw24643step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24643step0 raw24643step0Labels permutation32 permutation6
    _ = mixedMoment B node1237 node1237Labels := by rfl

def raw24644 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24644Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24644step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24644step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24644 raw24644Labels = mixedMoment B node1241 node1241Labels := by
  calc
    mixedMoment B raw24644 raw24644Labels = mixedMoment B raw24644step0 raw24644step0Labels := by
      have hz : ∀ j, raw24644 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24644step0 = (fun i j => raw24644 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24644step0 raw24644; decide +kernel
      have hl : raw24644step0Labels = raw24644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24644 raw24644Labels permutation265 hz
    mixedMoment B raw24644step0 raw24644step0Labels = mixedMoment B raw24644step1 raw24644step1Labels := by
      have ha : raw24644step1 = (fun i j => raw24644step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24644step1 raw24644step0; decide +kernel
      have hl : raw24644step1Labels = raw24644step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24644step0 raw24644step0Labels permutation32 permutation6
    _ = mixedMoment B node1241 node1241Labels := by rfl

def raw24645 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24645Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24645step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24645step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24645 raw24645Labels = mixedMoment B node1004 node1004Labels := by
  calc
    mixedMoment B raw24645 raw24645Labels = mixedMoment B raw24645step0 raw24645step0Labels := by
      have hz : ∀ j, raw24645 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24645step0 = (fun i j => raw24645 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24645step0 raw24645; decide +kernel
      have hl : raw24645step0Labels = raw24645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24645 raw24645Labels permutation265 hz
    mixedMoment B raw24645step0 raw24645step0Labels = mixedMoment B raw24645step1 raw24645step1Labels := by
      have ha : raw24645step1 = (fun i j => raw24645step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24645step1 raw24645step0; decide +kernel
      have hl : raw24645step1Labels = raw24645step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24645step0 raw24645step0Labels permutation32 permutation6
    _ = mixedMoment B node1004 node1004Labels := by rfl

def raw24646 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24646Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24646step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24646 raw24646Labels = mixedMoment B node1200 node1200Labels := by
  calc
    mixedMoment B raw24646 raw24646Labels = mixedMoment B raw24646step0 raw24646step0Labels := by
      have ha : raw24646step0 = (fun i j => raw24646 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24646step0 raw24646; decide +kernel
      have hl : raw24646step0Labels = raw24646Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24646 raw24646Labels permutation152 permutation6
    _ = mixedMoment B node1200 node1200Labels := by rfl

def raw24647 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24647Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24647step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24647step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24647 raw24647Labels = mixedMoment B node1188 node1188Labels := by
  calc
    mixedMoment B raw24647 raw24647Labels = mixedMoment B raw24647step0 raw24647step0Labels := by
      have hz : ∀ j, raw24647 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24647step0 = (fun i j => raw24647 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24647step0 raw24647; decide +kernel
      have hl : raw24647step0Labels = raw24647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24647 raw24647Labels permutation265 hz
    mixedMoment B raw24647step0 raw24647step0Labels = mixedMoment B raw24647step1 raw24647step1Labels := by
      have ha : raw24647step1 = (fun i j => raw24647step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24647step1 raw24647step0; decide +kernel
      have hl : raw24647step1Labels = raw24647step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24647step0 raw24647step0Labels permutation32 permutation6
    _ = mixedMoment B node1188 node1188Labels := by rfl

def raw24648 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24648Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw24648step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24648step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24648 raw24648Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw24648 raw24648Labels = mixedMoment B raw24648step0 raw24648step0Labels := by
      have hz : ∀ j, raw24648 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24648step0 = (fun i j => raw24648 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24648step0 raw24648; decide +kernel
      have hl : raw24648step0Labels = raw24648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24648 raw24648Labels permutation265 hz
    mixedMoment B raw24648step0 raw24648step0Labels = mixedMoment B raw24648step1 raw24648step1Labels := by
      have ha : raw24648step1 = (fun i j => raw24648step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24648step1 raw24648step0; decide +kernel
      have hl : raw24648step1Labels = raw24648step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24648step0 raw24648step0Labels permutation32 permutation6
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw24649 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24649Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24649step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24649step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24649 raw24649Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw24649 raw24649Labels = mixedMoment B raw24649step0 raw24649step0Labels := by
      have hz : ∀ j, raw24649 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24649step0 = (fun i j => raw24649 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24649step0 raw24649; decide +kernel
      have hl : raw24649step0Labels = raw24649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24649 raw24649Labels permutation265 hz
    mixedMoment B raw24649step0 raw24649step0Labels = mixedMoment B raw24649step1 raw24649step1Labels := by
      have ha : raw24649step1 = (fun i j => raw24649step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24649step1 raw24649step0; decide +kernel
      have hl : raw24649step1Labels = raw24649step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24649step0 raw24649step0Labels permutation34 permutation6
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw24650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24650Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24650step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24650 raw24650Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw24650 raw24650Labels = mixedMoment B raw24650step0 raw24650step0Labels := by
      have ha : raw24650step0 = (fun i j => raw24650 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24650step0 raw24650; decide +kernel
      have hl : raw24650step0Labels = raw24650Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24650 raw24650Labels permutation154 permutation2
    _ = mixedMoment B node5134 node5134Labels := by rfl

def raw24651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24651step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24651step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24651 raw24651Labels = mixedMoment B node5101 node5101Labels := by
  calc
    mixedMoment B raw24651 raw24651Labels = mixedMoment B raw24651step0 raw24651step0Labels := by
      have hz : ∀ j, raw24651 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24651step0 = (fun i j => raw24651 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24651step0 raw24651; decide +kernel
      have hl : raw24651step0Labels = raw24651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24651 raw24651Labels permutation265 hz
    mixedMoment B raw24651step0 raw24651step0Labels = mixedMoment B raw24651step1 raw24651step1Labels := by
      have ha : raw24651step1 = (fun i j => raw24651step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24651step1 raw24651step0; decide +kernel
      have hl : raw24651step1Labels = raw24651step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24651step0 raw24651step0Labels permutation34 permutation2
    _ = mixedMoment B node5101 node5101Labels := by rfl

def raw24652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24652step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24652 raw24652Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw24652 raw24652Labels = mixedMoment B raw24652step0 raw24652step0Labels := by
      have hz : ∀ j, raw24652 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24652step0 = (fun i j => raw24652 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24652step0 raw24652; decide +kernel
      have hl : raw24652step0Labels = raw24652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24652 raw24652Labels permutation265 hz
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw24653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw24653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24653step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24653step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24653step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24653 raw24653Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw24653 raw24653Labels = mixedMoment B raw24653step0 raw24653step0Labels := by
      have hz : ∀ j, raw24653 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24653step0 = (fun i j => raw24653 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24653step0 raw24653; decide +kernel
      have hl : raw24653step0Labels = raw24653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24653 raw24653Labels permutation520 hz
    mixedMoment B raw24653step0 raw24653step0Labels = mixedMoment B raw24653step1 raw24653step1Labels := by
      have hz : ∀ j, raw24653step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24653step1 = (fun i j => raw24653step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24653step1 raw24653step0; decide +kernel
      have hl : raw24653step1Labels = raw24653step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24653step0 raw24653step0Labels permutation56 hz
    _ = mixedMoment B node5274 node5274Labels := by rfl

def raw24654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24654step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24654step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24654 raw24654Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw24654 raw24654Labels = mixedMoment B raw24654step0 raw24654step0Labels := by
      have hz : ∀ j, raw24654 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24654step0 = (fun i j => raw24654 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24654step0 raw24654; decide +kernel
      have hl : raw24654step0Labels = raw24654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24654 raw24654Labels permutation265 hz
    mixedMoment B raw24654step0 raw24654step0Labels = mixedMoment B raw24654step1 raw24654step1Labels := by
      have ha : raw24654step1 = (fun i j => raw24654step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24654step1 raw24654step0; decide +kernel
      have hl : raw24654step1Labels = raw24654step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24654step0 raw24654step0Labels permutation34 permutation2
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw24655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24655step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24655step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24655step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24655 raw24655Labels = mixedMoment B node4152 node4152Labels := by
  calc
    mixedMoment B raw24655 raw24655Labels = mixedMoment B raw24655step0 raw24655step0Labels := by
      have ha : raw24655step0 = (fun i j => raw24655 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24655step0 raw24655; decide +kernel
      have hl : raw24655step0Labels = raw24655Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24655 raw24655Labels permutation182 permutation3
    mixedMoment B raw24655step0 raw24655step0Labels = mixedMoment B raw24655step1 raw24655step1Labels := by
      have ha : raw24655step1 = raw24655step0 := by apply Matrix.ext; unfold raw24655step1 raw24655step0; decide +kernel
      have hl : raw24655step0Labels = labelEmbedding6 ∘ raw24655step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24655step0 raw24655step0Labels raw24655step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4152 node4152Labels := by rfl

def raw24656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24656step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24656 raw24656Labels = mixedMoment B node4541 node4541Labels := by
  calc
    mixedMoment B raw24656 raw24656Labels = mixedMoment B raw24656step0 raw24656step0Labels := by
      have ha : raw24656step0 = (fun i j => raw24656 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24656step0 raw24656; decide +kernel
      have hl : raw24656step0Labels = raw24656Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24656 raw24656Labels permutation178 permutation2
    _ = mixedMoment B node4541 node4541Labels := by rfl

def raw24657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24657step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24657 raw24657Labels = mixedMoment B node4589 node4589Labels := by
  calc
    mixedMoment B raw24657 raw24657Labels = mixedMoment B raw24657step0 raw24657step0Labels := by
      have ha : raw24657step0 = (fun i j => raw24657 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24657step0 raw24657; decide +kernel
      have hl : raw24657step0Labels = raw24657Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24657 raw24657Labels permutation182 permutation2
    _ = mixedMoment B node4589 node4589Labels := by rfl

def raw24658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw24658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24658step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24658step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24658 raw24658Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw24658 raw24658Labels = mixedMoment B raw24658step0 raw24658step0Labels := by
      have hz : ∀ j, raw24658 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24658step0 = (fun i j => raw24658 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24658step0 raw24658; decide +kernel
      have hl : raw24658step0Labels = raw24658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24658 raw24658Labels permutation520 hz
    mixedMoment B raw24658step0 raw24658step0Labels = mixedMoment B raw24658step1 raw24658step1Labels := by
      have ha : raw24658step1 = (fun i j => raw24658step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24658step1 raw24658step0; decide +kernel
      have hl : raw24658step1Labels = raw24658step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24658step0 raw24658step0Labels permutation38 permutation2
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw24659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24659step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24659 raw24659Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw24659 raw24659Labels = mixedMoment B raw24659step0 raw24659step0Labels := by
      have ha : raw24659step0 = (fun i j => raw24659 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24659step0 raw24659; decide +kernel
      have hl : raw24659step0Labels = raw24659Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24659 raw24659Labels permutation178 permutation2
    _ = mixedMoment B node4599 node4599Labels := by rfl

def raw24660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24660step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24660step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24660step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24660step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24660 raw24660Labels = mixedMoment B node4176 node4176Labels := by
  calc
    mixedMoment B raw24660 raw24660Labels = mixedMoment B raw24660step0 raw24660step0Labels := by
      have hz : ∀ j, raw24660 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24660step0 = (fun i j => raw24660 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24660step0 raw24660; decide +kernel
      have hl : raw24660step0Labels = raw24660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24660 raw24660Labels permutation265 hz
    mixedMoment B raw24660step0 raw24660step0Labels = mixedMoment B raw24660step1 raw24660step1Labels := by
      have ha : raw24660step1 = (fun i j => raw24660step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24660step1 raw24660step0; decide +kernel
      have hl : raw24660step1Labels = raw24660step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24660step0 raw24660step0Labels permutation40 permutation3
    mixedMoment B raw24660step1 raw24660step1Labels = mixedMoment B raw24660step2 raw24660step2Labels := by
      have ha : raw24660step2 = raw24660step1 := by apply Matrix.ext; unfold raw24660step2 raw24660step1; decide +kernel
      have hl : raw24660step1Labels = labelEmbedding6 ∘ raw24660step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24660step1 raw24660step1Labels raw24660step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4176 node4176Labels := by rfl

def raw24661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24661Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24661step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24661step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24661step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24661step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24661 raw24661Labels = mixedMoment B node4545 node4545Labels := by
  calc
    mixedMoment B raw24661 raw24661Labels = mixedMoment B raw24661step0 raw24661step0Labels := by
      have ha : raw24661step0 = (fun i j => raw24661 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24661step0 raw24661; decide +kernel
      have hl : raw24661step0Labels = raw24661Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24661 raw24661Labels permutation160 permutation3
    mixedMoment B raw24661step0 raw24661step0Labels = mixedMoment B raw24661step1 raw24661step1Labels := by
      have ha : raw24661step1 = raw24661step0 := by apply Matrix.ext; unfold raw24661step1 raw24661step0; decide +kernel
      have hl : raw24661step0Labels = labelEmbedding6 ∘ raw24661step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24661step0 raw24661step0Labels raw24661step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4545 node4545Labels := by rfl

def raw24662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24662step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24662step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24662step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24662step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24662 raw24662Labels = mixedMoment B node4607 node4607Labels := by
  calc
    mixedMoment B raw24662 raw24662Labels = mixedMoment B raw24662step0 raw24662step0Labels := by
      have hz : ∀ j, raw24662 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24662step0 = (fun i j => raw24662 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24662step0 raw24662; decide +kernel
      have hl : raw24662step0Labels = raw24662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24662 raw24662Labels permutation265 hz
    mixedMoment B raw24662step0 raw24662step0Labels = mixedMoment B raw24662step1 raw24662step1Labels := by
      have ha : raw24662step1 = (fun i j => raw24662step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24662step1 raw24662step0; decide +kernel
      have hl : raw24662step1Labels = raw24662step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24662step0 raw24662step0Labels permutation40 permutation3
    mixedMoment B raw24662step1 raw24662step1Labels = mixedMoment B raw24662step2 raw24662step2Labels := by
      have ha : raw24662step2 = raw24662step1 := by apply Matrix.ext; unfold raw24662step2 raw24662step1; decide +kernel
      have hl : raw24662step1Labels = labelEmbedding6 ∘ raw24662step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24662step1 raw24662step1Labels raw24662step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4607 node4607Labels := by rfl

def raw24663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw24663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24663step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24663step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24663step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24663 raw24663Labels = mixedMoment B node4619 node4619Labels := by
  calc
    mixedMoment B raw24663 raw24663Labels = mixedMoment B raw24663step0 raw24663step0Labels := by
      have hz : ∀ j, raw24663 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24663step0 = (fun i j => raw24663 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24663step0 raw24663; decide +kernel
      have hl : raw24663step0Labels = raw24663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24663 raw24663Labels permutation520 hz
    mixedMoment B raw24663step0 raw24663step0Labels = mixedMoment B raw24663step1 raw24663step1Labels := by
      have hz : ∀ j, raw24663step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24663step1 = (fun i j => raw24663step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24663step1 raw24663step0; decide +kernel
      have hl : raw24663step1Labels = raw24663step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24663step0 raw24663step0Labels permutation56 hz
    _ = mixedMoment B node4619 node4619Labels := by rfl

def raw24664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24664step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24664step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24664 raw24664Labels = mixedMoment B node4616 node4616Labels := by
  calc
    mixedMoment B raw24664 raw24664Labels = mixedMoment B raw24664step0 raw24664step0Labels := by
      have hz : ∀ j, raw24664 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24664step0 = (fun i j => raw24664 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24664step0 raw24664; decide +kernel
      have hl : raw24664step0Labels = raw24664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24664 raw24664Labels permutation265 hz
    mixedMoment B raw24664step0 raw24664step0Labels = mixedMoment B raw24664step1 raw24664step1Labels := by
      have ha : raw24664step1 = (fun i j => raw24664step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24664step1 raw24664step0; decide +kernel
      have hl : raw24664step1Labels = raw24664step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24664step0 raw24664step0Labels permutation34 permutation2
    _ = mixedMoment B node4616 node4616Labels := by rfl

def raw24665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24665step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24665step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24665 raw24665Labels = mixedMoment B node4158 node4158Labels := by
  calc
    mixedMoment B raw24665 raw24665Labels = mixedMoment B raw24665step0 raw24665step0Labels := by
      have hz : ∀ j, raw24665 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24665step0 = (fun i j => raw24665 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24665step0 raw24665; decide +kernel
      have hl : raw24665step0Labels = raw24665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24665 raw24665Labels permutation265 hz
    mixedMoment B raw24665step0 raw24665step0Labels = mixedMoment B raw24665step1 raw24665step1Labels := by
      have ha : raw24665step1 = (fun i j => raw24665step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24665step1 raw24665step0; decide +kernel
      have hl : raw24665step1Labels = raw24665step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24665step0 raw24665step0Labels permutation35 permutation3
    mixedMoment B raw24665step1 raw24665step1Labels = mixedMoment B raw24665step2 raw24665step2Labels := by
      have ha : raw24665step2 = raw24665step1 := by apply Matrix.ext; unfold raw24665step2 raw24665step1; decide +kernel
      have hl : raw24665step1Labels = labelEmbedding6 ∘ raw24665step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24665step1 raw24665step1Labels raw24665step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4158 node4158Labels := by rfl

def raw24666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24666step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24666step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24666step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24666step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24666 raw24666Labels = mixedMoment B node4533 node4533Labels := by
  calc
    mixedMoment B raw24666 raw24666Labels = mixedMoment B raw24666step0 raw24666step0Labels := by
      have ha : raw24666step0 = (fun i j => raw24666 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24666step0 raw24666; decide +kernel
      have hl : raw24666step0Labels = raw24666Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24666 raw24666Labels permutation155 permutation3
    mixedMoment B raw24666step0 raw24666step0Labels = mixedMoment B raw24666step1 raw24666step1Labels := by
      have ha : raw24666step1 = raw24666step0 := by apply Matrix.ext; unfold raw24666step1 raw24666step0; decide +kernel
      have hl : raw24666step0Labels = labelEmbedding6 ∘ raw24666step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24666step0 raw24666step0Labels raw24666step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4533 node4533Labels := by rfl

def raw24667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24667step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24667 raw24667Labels = mixedMoment B node4549 node4549Labels := by
  calc
    mixedMoment B raw24667 raw24667Labels = mixedMoment B raw24667step0 raw24667step0Labels := by
      have hz : ∀ j, raw24667 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24667step0 = (fun i j => raw24667 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24667step0 raw24667; decide +kernel
      have hl : raw24667step0Labels = raw24667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24667 raw24667Labels permutation265 hz
    mixedMoment B raw24667step0 raw24667step0Labels = mixedMoment B raw24667step1 raw24667step1Labels := by
      have ha : raw24667step1 = (fun i j => raw24667step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24667step1 raw24667step0; decide +kernel
      have hl : raw24667step1Labels = raw24667step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24667step0 raw24667step0Labels permutation34 permutation2
    _ = mixedMoment B node4549 node4549Labels := by rfl

def raw24668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw24668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24668step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24668step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24668 raw24668Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw24668 raw24668Labels = mixedMoment B raw24668step0 raw24668step0Labels := by
      have hz : ∀ j, raw24668 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24668step0 = (fun i j => raw24668 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24668step0 raw24668; decide +kernel
      have hl : raw24668step0Labels = raw24668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24668 raw24668Labels permutation520 hz
    mixedMoment B raw24668step0 raw24668step0Labels = mixedMoment B raw24668step1 raw24668step1Labels := by
      have hz : ∀ j, raw24668step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24668step1 = (fun i j => raw24668step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24668step1 raw24668step0; decide +kernel
      have hl : raw24668step1Labels = raw24668step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24668step0 raw24668step0Labels permutation56 hz
    _ = mixedMoment B node4612 node4612Labels := by rfl

def raw24669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw24669step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24669 raw24669Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw24669 raw24669Labels = mixedMoment B raw24669step0 raw24669step0Labels := by
      have hz : ∀ j, raw24669 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24669step0 = (fun i j => raw24669 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24669step0 raw24669; decide +kernel
      have hl : raw24669step0Labels = raw24669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24669 raw24669Labels permutation265 hz
    mixedMoment B raw24669step0 raw24669step0Labels = mixedMoment B raw24669step1 raw24669step1Labels := by
      have ha : raw24669step1 = (fun i j => raw24669step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24669step1 raw24669step0; decide +kernel
      have hl : raw24669step1Labels = raw24669step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24669step0 raw24669step0Labels permutation35 permutation2
    _ = mixedMoment B node4603 node4603Labels := by rfl

def raw24670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24670step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw24670step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24670step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw24670step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24670 raw24670Labels = mixedMoment B node4154 node4154Labels := by
  calc
    mixedMoment B raw24670 raw24670Labels = mixedMoment B raw24670step0 raw24670step0Labels := by
      have hz : ∀ j, raw24670 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24670step0 = (fun i j => raw24670 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24670step0 raw24670; decide +kernel
      have hl : raw24670step0Labels = raw24670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24670 raw24670Labels permutation265 hz
    mixedMoment B raw24670step0 raw24670step0Labels = mixedMoment B raw24670step1 raw24670step1Labels := by
      have ha : raw24670step1 = (fun i j => raw24670step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24670step1 raw24670step0; decide +kernel
      have hl : raw24670step1Labels = raw24670step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24670step0 raw24670step0Labels permutation33 permutation3
    mixedMoment B raw24670step1 raw24670step1Labels = mixedMoment B raw24670step2 raw24670step2Labels := by
      have ha : raw24670step2 = raw24670step1 := by apply Matrix.ext; unfold raw24670step2 raw24670step1; decide +kernel
      have hl : raw24670step1Labels = labelEmbedding6 ∘ raw24670step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24670step1 raw24670step1Labels raw24670step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4154 node4154Labels := by rfl

def raw24671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24671step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw24671step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24671step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw24671step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24671 raw24671Labels = mixedMoment B node4529 node4529Labels := by
  calc
    mixedMoment B raw24671 raw24671Labels = mixedMoment B raw24671step0 raw24671step0Labels := by
      have ha : raw24671step0 = (fun i j => raw24671 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24671step0 raw24671; decide +kernel
      have hl : raw24671step0Labels = raw24671Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24671 raw24671Labels permutation153 permutation3
    mixedMoment B raw24671step0 raw24671step0Labels = mixedMoment B raw24671step1 raw24671step1Labels := by
      have ha : raw24671step1 = raw24671step0 := by apply Matrix.ext; unfold raw24671step1 raw24671step0; decide +kernel
      have hl : raw24671step0Labels = labelEmbedding6 ∘ raw24671step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24671step0 raw24671step0Labels raw24671step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4529 node4529Labels := by rfl

def raw24672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24672step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24672 raw24672Labels = mixedMoment B node4553 node4553Labels := by
  calc
    mixedMoment B raw24672 raw24672Labels = mixedMoment B raw24672step0 raw24672step0Labels := by
      have hz : ∀ j, raw24672 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24672step0 = (fun i j => raw24672 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24672step0 raw24672; decide +kernel
      have hl : raw24672step0Labels = raw24672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24672 raw24672Labels permutation265 hz
    _ = mixedMoment B node4553 node4553Labels := by rfl

def raw24673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24673step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24673 raw24673Labels = mixedMoment B node4592 node4592Labels := by
  calc
    mixedMoment B raw24673 raw24673Labels = mixedMoment B raw24673step0 raw24673step0Labels := by
      have hz : ∀ j, raw24673 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24673step0 = (fun i j => raw24673 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24673step0 raw24673; decide +kernel
      have hl : raw24673step0Labels = raw24673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24673 raw24673Labels permutation265 hz
    _ = mixedMoment B node4592 node4592Labels := by rfl

def raw24674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw24674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw24674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24674step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24674 raw24674Labels = mixedMoment B node4607 node4607Labels := by
  calc
    mixedMoment B raw24674 raw24674Labels = mixedMoment B raw24674step0 raw24674step0Labels := by
      have hz : ∀ j, raw24674 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24674step0 = (fun i j => raw24674 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24674step0 raw24674; decide +kernel
      have hl : raw24674step0Labels = raw24674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24674 raw24674Labels permutation265 hz
    mixedMoment B raw24674step0 raw24674step0Labels = mixedMoment B raw24674step1 raw24674step1Labels := by
      have ha : raw24674step1 = (fun i j => raw24674step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24674step1 raw24674step0; decide +kernel
      have hl : raw24674step1Labels = raw24674step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24674step0 raw24674step0Labels permutation33 permutation2
    _ = mixedMoment B node4607 node4607Labels := by rfl

def raw24675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw24675step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24675step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw24675step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24675 raw24675Labels = mixedMoment B node4153 node4153Labels := by
  calc
    mixedMoment B raw24675 raw24675Labels = mixedMoment B raw24675step0 raw24675step0Labels := by
      have hz : ∀ j, raw24675 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24675step0 = (fun i j => raw24675 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24675step0 raw24675; decide +kernel
      have hl : raw24675step0Labels = raw24675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24675 raw24675Labels permutation265 hz
    mixedMoment B raw24675step0 raw24675step0Labels = mixedMoment B raw24675step1 raw24675step1Labels := by
      have ha : raw24675step1 = (fun i j => raw24675step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24675step1 raw24675step0; decide +kernel
      have hl : raw24675step1Labels = raw24675step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24675step0 raw24675step0Labels permutation32 permutation3
    mixedMoment B raw24675step1 raw24675step1Labels = mixedMoment B raw24675step2 raw24675step2Labels := by
      have ha : raw24675step2 = raw24675step1 := by apply Matrix.ext; unfold raw24675step2 raw24675step1; decide +kernel
      have hl : raw24675step1Labels = labelEmbedding6 ∘ raw24675step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24675step1 raw24675step1Labels raw24675step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4153 node4153Labels := by rfl

def raw24676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24676step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw24676step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24676step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw24676step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24676 raw24676Labels = mixedMoment B node4528 node4528Labels := by
  calc
    mixedMoment B raw24676 raw24676Labels = mixedMoment B raw24676step0 raw24676step0Labels := by
      have ha : raw24676step0 = (fun i j => raw24676 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24676step0 raw24676; decide +kernel
      have hl : raw24676step0Labels = raw24676Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24676 raw24676Labels permutation152 permutation3
    mixedMoment B raw24676step0 raw24676step0Labels = mixedMoment B raw24676step1 raw24676step1Labels := by
      have ha : raw24676step1 = raw24676step0 := by apply Matrix.ext; unfold raw24676step1 raw24676step0; decide +kernel
      have hl : raw24676step0Labels = labelEmbedding6 ∘ raw24676step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24676step0 raw24676step0Labels raw24676step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4528 node4528Labels := by rfl

def raw24677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw24677step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24677 raw24677Labels = mixedMoment B node4546 node4546Labels := by
  calc
    mixedMoment B raw24677 raw24677Labels = mixedMoment B raw24677step0 raw24677step0Labels := by
      have hz : ∀ j, raw24677 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24677step0 = (fun i j => raw24677 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24677step0 raw24677; decide +kernel
      have hl : raw24677step0Labels = raw24677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24677 raw24677Labels permutation265 hz
    mixedMoment B raw24677step0 raw24677step0Labels = mixedMoment B raw24677step1 raw24677step1Labels := by
      have ha : raw24677step1 = (fun i j => raw24677step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24677step1 raw24677step0; decide +kernel
      have hl : raw24677step1Labels = raw24677step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24677step0 raw24677step0Labels permutation34 permutation2
    _ = mixedMoment B node4546 node4546Labels := by rfl

def raw24678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24678step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24678 raw24678Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw24678 raw24678Labels = mixedMoment B raw24678step0 raw24678step0Labels := by
      have hz : ∀ j, raw24678 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24678step0 = (fun i j => raw24678 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24678step0 raw24678; decide +kernel
      have hl : raw24678step0Labels = raw24678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24678 raw24678Labels permutation265 hz
    _ = mixedMoment B node4591 node4591Labels := by rfl

def raw24679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw24679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw24679step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24679step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw24679step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24679 raw24679Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw24679 raw24679Labels = mixedMoment B raw24679step0 raw24679step0Labels := by
      have hz : ∀ j, raw24679 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24679step0 = (fun i j => raw24679 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24679step0 raw24679; decide +kernel
      have hl : raw24679step0Labels = raw24679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24679 raw24679Labels permutation520 hz
    mixedMoment B raw24679step0 raw24679step0Labels = mixedMoment B raw24679step1 raw24679step1Labels := by
      have hz : ∀ j, raw24679step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24679step1 = (fun i j => raw24679step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24679step1 raw24679step0; decide +kernel
      have hl : raw24679step1Labels = raw24679step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24679step0 raw24679step0Labels permutation56 hz
    _ = mixedMoment B node4608 node4608Labels := by rfl

def raw24680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24680Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24680step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24680step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24680 raw24680Labels = mixedMoment B node2937 node2937Labels := by
  calc
    mixedMoment B raw24680 raw24680Labels = mixedMoment B raw24680step0 raw24680step0Labels := by
      have ha : raw24680step0 = (fun i j => raw24680 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24680step0 raw24680; decide +kernel
      have hl : raw24680step0Labels = raw24680Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24680 raw24680Labels permutation152 permutation3
    _ = mixedMoment B node2937 node2937Labels := by rfl

def raw24681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24681Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24681step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24681step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24681 raw24681Labels = mixedMoment B node3001 node3001Labels := by
  calc
    mixedMoment B raw24681 raw24681Labels = mixedMoment B raw24681step0 raw24681step0Labels := by
      have hz : ∀ j, raw24681 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24681step0 = (fun i j => raw24681 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24681step0 raw24681; decide +kernel
      have hl : raw24681step0Labels = raw24681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24681 raw24681Labels permutation265 hz
    mixedMoment B raw24681step0 raw24681step0Labels = mixedMoment B raw24681step1 raw24681step1Labels := by
      have ha : raw24681step1 = (fun i j => raw24681step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24681step1 raw24681step0; decide +kernel
      have hl : raw24681step1Labels = raw24681step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24681step0 raw24681step0Labels permutation32 permutation3
    _ = mixedMoment B node3001 node3001Labels := by rfl

def raw24682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24682Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24682step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24682step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24682 raw24682Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw24682 raw24682Labels = mixedMoment B raw24682step0 raw24682step0Labels := by
      have hz : ∀ j, raw24682 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24682step0 = (fun i j => raw24682 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24682step0 raw24682; decide +kernel
      have hl : raw24682step0Labels = raw24682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24682 raw24682Labels permutation265 hz
    mixedMoment B raw24682step0 raw24682step0Labels = mixedMoment B raw24682step1 raw24682step1Labels := by
      have ha : raw24682step1 = (fun i j => raw24682step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24682step1 raw24682step0; decide +kernel
      have hl : raw24682step1Labels = raw24682step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24682step0 raw24682step0Labels permutation38 permutation3
    _ = mixedMoment B node3089 node3089Labels := by rfl

def raw24683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw24683Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24683step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24683step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24683step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24683step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw24683step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24683 raw24683Labels = mixedMoment B node3112 node3112Labels := by
  calc
    mixedMoment B raw24683 raw24683Labels = mixedMoment B raw24683step0 raw24683step0Labels := by
      have hz : ∀ j, raw24683 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24683step0 = (fun i j => raw24683 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24683step0 raw24683; decide +kernel
      have hl : raw24683step0Labels = raw24683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24683 raw24683Labels permutation520 hz
    mixedMoment B raw24683step0 raw24683step0Labels = mixedMoment B raw24683step1 raw24683step1Labels := by
      have hz : ∀ j, raw24683step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24683step1 = (fun i j => raw24683step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24683step1 raw24683step0; decide +kernel
      have hl : raw24683step1Labels = raw24683step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24683step0 raw24683step0Labels permutation56 hz
    mixedMoment B raw24683step1 raw24683step1Labels = mixedMoment B raw24683step2 raw24683step2Labels := by
      have ha : raw24683step2 = (fun i j => raw24683step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24683step2 raw24683step1; decide +kernel
      have hl : raw24683step2Labels = raw24683step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24683step1 raw24683step1Labels permutation8 permutation3
    _ = mixedMoment B node3112 node3112Labels := by rfl

def raw24684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24684Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24684step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw24684step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24684 raw24684Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw24684 raw24684Labels = mixedMoment B raw24684step0 raw24684step0Labels := by
      have hz : ∀ j, raw24684 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24684step0 = (fun i j => raw24684 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24684step0 raw24684; decide +kernel
      have hl : raw24684step0Labels = raw24684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24684 raw24684Labels permutation265 hz
    mixedMoment B raw24684step0 raw24684step0Labels = mixedMoment B raw24684step1 raw24684step1Labels := by
      have ha : raw24684step1 = (fun i j => raw24684step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24684step1 raw24684step0; decide +kernel
      have hl : raw24684step1Labels = raw24684step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24684step0 raw24684step0Labels permutation36 permutation3
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw24685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24685Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24685step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24685step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24685 raw24685Labels = mixedMoment B node580 node580Labels := by
  calc
    mixedMoment B raw24685 raw24685Labels = mixedMoment B raw24685step0 raw24685step0Labels := by
      have ha : raw24685step0 = (fun i j => raw24685 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24685step0 raw24685; decide +kernel
      have hl : raw24685step0Labels = raw24685Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24685 raw24685Labels permutation182 permutation3
    _ = mixedMoment B node580 node580Labels := by rfl

def raw24686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24686Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24686step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24686step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24686 raw24686Labels = mixedMoment B node1164 node1164Labels := by
  calc
    mixedMoment B raw24686 raw24686Labels = mixedMoment B raw24686step0 raw24686step0Labels := by
      have ha : raw24686step0 = (fun i j => raw24686 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24686step0 raw24686; decide +kernel
      have hl : raw24686step0Labels = raw24686Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24686 raw24686Labels permutation182 permutation3
    _ = mixedMoment B node1164 node1164Labels := by rfl

def raw24687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24687Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24687step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24687step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24687 raw24687Labels = mixedMoment B node1216 node1216Labels := by
  calc
    mixedMoment B raw24687 raw24687Labels = mixedMoment B raw24687step0 raw24687step0Labels := by
      have ha : raw24687step0 = (fun i j => raw24687 (permutation206 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24687step0 raw24687; decide +kernel
      have hl : raw24687step0Labels = raw24687Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24687 raw24687Labels permutation206 permutation3
    _ = mixedMoment B node1216 node1216Labels := by rfl

def raw24688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw24688Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24688step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24688step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24688 raw24688Labels = mixedMoment B node1267 node1267Labels := by
  calc
    mixedMoment B raw24688 raw24688Labels = mixedMoment B raw24688step0 raw24688step0Labels := by
      have hz : ∀ j, raw24688 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24688step0 = (fun i j => raw24688 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24688step0 raw24688; decide +kernel
      have hl : raw24688step0Labels = raw24688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24688 raw24688Labels permutation520 hz
    mixedMoment B raw24688step0 raw24688step0Labels = mixedMoment B raw24688step1 raw24688step1Labels := by
      have ha : raw24688step1 = (fun i j => raw24688step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24688step1 raw24688step0; decide +kernel
      have hl : raw24688step1Labels = raw24688step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24688step0 raw24688step0Labels permutation40 permutation3
    _ = mixedMoment B node1267 node1267Labels := by rfl

def raw24689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24689Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24689step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24689step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24689 raw24689Labels = mixedMoment B node1260 node1260Labels := by
  calc
    mixedMoment B raw24689 raw24689Labels = mixedMoment B raw24689step0 raw24689step0Labels := by
      have ha : raw24689step0 = (fun i j => raw24689 (permutation196 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24689step0 raw24689; decide +kernel
      have hl : raw24689step0Labels = raw24689Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24689 raw24689Labels permutation196 permutation3
    _ = mixedMoment B node1260 node1260Labels := by rfl

def raw24690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24690Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24690step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24690step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24690 raw24690Labels = mixedMoment B node604 node604Labels := by
  calc
    mixedMoment B raw24690 raw24690Labels = mixedMoment B raw24690step0 raw24690step0Labels := by
      have hz : ∀ j, raw24690 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24690step0 = (fun i j => raw24690 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24690step0 raw24690; decide +kernel
      have hl : raw24690step0Labels = raw24690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24690 raw24690Labels permutation265 hz
    mixedMoment B raw24690step0 raw24690step0Labels = mixedMoment B raw24690step1 raw24690step1Labels := by
      have ha : raw24690step1 = (fun i j => raw24690step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24690step1 raw24690step0; decide +kernel
      have hl : raw24690step1Labels = raw24690step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24690step0 raw24690step0Labels permutation40 permutation3
    _ = mixedMoment B node604 node604Labels := by rfl

def raw24691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24691Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24691step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24691step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24691 raw24691Labels = mixedMoment B node1130 node1130Labels := by
  calc
    mixedMoment B raw24691 raw24691Labels = mixedMoment B raw24691step0 raw24691step0Labels := by
      have ha : raw24691step0 = (fun i j => raw24691 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24691step0 raw24691; decide +kernel
      have hl : raw24691step0Labels = raw24691Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24691 raw24691Labels permutation160 permutation3
    _ = mixedMoment B node1130 node1130Labels := by rfl

def raw24692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24692Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24692step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24692step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24692 raw24692Labels = mixedMoment B node1241 node1241Labels := by
  calc
    mixedMoment B raw24692 raw24692Labels = mixedMoment B raw24692step0 raw24692step0Labels := by
      have hz : ∀ j, raw24692 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24692step0 = (fun i j => raw24692 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24692step0 raw24692; decide +kernel
      have hl : raw24692step0Labels = raw24692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24692 raw24692Labels permutation265 hz
    mixedMoment B raw24692step0 raw24692step0Labels = mixedMoment B raw24692step1 raw24692step1Labels := by
      have ha : raw24692step1 = (fun i j => raw24692step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24692step1 raw24692step0; decide +kernel
      have hl : raw24692step1Labels = raw24692step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24692step0 raw24692step0Labels permutation40 permutation3
    _ = mixedMoment B node1241 node1241Labels := by rfl

def raw24693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw24693Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24693step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24693step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24693step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24693step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24693step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24693 raw24693Labels = mixedMoment B node1302 node1302Labels := by
  calc
    mixedMoment B raw24693 raw24693Labels = mixedMoment B raw24693step0 raw24693step0Labels := by
      have hz : ∀ j, raw24693 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24693step0 = (fun i j => raw24693 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24693step0 raw24693; decide +kernel
      have hl : raw24693step0Labels = raw24693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24693 raw24693Labels permutation520 hz
    mixedMoment B raw24693step0 raw24693step0Labels = mixedMoment B raw24693step1 raw24693step1Labels := by
      have hz : ∀ j, raw24693step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24693step1 = (fun i j => raw24693step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24693step1 raw24693step0; decide +kernel
      have hl : raw24693step1Labels = raw24693step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24693step0 raw24693step0Labels permutation56 hz
    mixedMoment B raw24693step1 raw24693step1Labels = mixedMoment B raw24693step2 raw24693step2Labels := by
      have ha : raw24693step2 = (fun i j => raw24693step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24693step2 raw24693step1; decide +kernel
      have hl : raw24693step2Labels = raw24693step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24693step1 raw24693step1Labels permutation10 permutation3
    _ = mixedMoment B node1302 node1302Labels := by rfl

def raw24694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24694Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24694step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24694step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24694 raw24694Labels = mixedMoment B node1291 node1291Labels := by
  calc
    mixedMoment B raw24694 raw24694Labels = mixedMoment B raw24694step0 raw24694step0Labels := by
      have hz : ∀ j, raw24694 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24694step0 = (fun i j => raw24694 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24694step0 raw24694; decide +kernel
      have hl : raw24694step0Labels = raw24694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24694 raw24694Labels permutation265 hz
    mixedMoment B raw24694step0 raw24694step0Labels = mixedMoment B raw24694step1 raw24694step1Labels := by
      have ha : raw24694step1 = (fun i j => raw24694step0 (permutation53 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24694step1 raw24694step0; decide +kernel
      have hl : raw24694step1Labels = raw24694step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24694step0 raw24694step0Labels permutation53 permutation3
    _ = mixedMoment B node1291 node1291Labels := by rfl

def raw24695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24695Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24695step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24695step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24695 raw24695Labels = mixedMoment B node586 node586Labels := by
  calc
    mixedMoment B raw24695 raw24695Labels = mixedMoment B raw24695step0 raw24695step0Labels := by
      have hz : ∀ j, raw24695 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24695step0 = (fun i j => raw24695 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24695step0 raw24695; decide +kernel
      have hl : raw24695step0Labels = raw24695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24695 raw24695Labels permutation265 hz
    mixedMoment B raw24695step0 raw24695step0Labels = mixedMoment B raw24695step1 raw24695step1Labels := by
      have ha : raw24695step1 = (fun i j => raw24695step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24695step1 raw24695step0; decide +kernel
      have hl : raw24695step1Labels = raw24695step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24695step0 raw24695step0Labels permutation35 permutation3
    _ = mixedMoment B node586 node586Labels := by rfl

def raw24696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24696Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24696step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24696 raw24696Labels = mixedMoment B node1117 node1117Labels := by
  calc
    mixedMoment B raw24696 raw24696Labels = mixedMoment B raw24696step0 raw24696step0Labels := by
      have ha : raw24696step0 = (fun i j => raw24696 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24696step0 raw24696; decide +kernel
      have hl : raw24696step0Labels = raw24696Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24696 raw24696Labels permutation155 permutation3
    _ = mixedMoment B node1117 node1117Labels := by rfl

def raw24697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24697Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24697step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24697step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24697 raw24697Labels = mixedMoment B node1172 node1172Labels := by
  calc
    mixedMoment B raw24697 raw24697Labels = mixedMoment B raw24697step0 raw24697step0Labels := by
      have hz : ∀ j, raw24697 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24697step0 = (fun i j => raw24697 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24697step0 raw24697; decide +kernel
      have hl : raw24697step0Labels = raw24697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24697 raw24697Labels permutation265 hz
    mixedMoment B raw24697step0 raw24697step0Labels = mixedMoment B raw24697step1 raw24697step1Labels := by
      have ha : raw24697step1 = (fun i j => raw24697step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24697step1 raw24697step0; decide +kernel
      have hl : raw24697step1Labels = raw24697step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24697step0 raw24697step0Labels permutation35 permutation3
    _ = mixedMoment B node1172 node1172Labels := by rfl

def raw24698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw24698Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24698step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24698step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24698step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24698step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24698step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24698 raw24698Labels = mixedMoment B node1274 node1274Labels := by
  calc
    mixedMoment B raw24698 raw24698Labels = mixedMoment B raw24698step0 raw24698step0Labels := by
      have hz : ∀ j, raw24698 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24698step0 = (fun i j => raw24698 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24698step0 raw24698; decide +kernel
      have hl : raw24698step0Labels = raw24698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24698 raw24698Labels permutation520 hz
    mixedMoment B raw24698step0 raw24698step0Labels = mixedMoment B raw24698step1 raw24698step1Labels := by
      have hz : ∀ j, raw24698step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24698step1 = (fun i j => raw24698step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24698step1 raw24698step0; decide +kernel
      have hl : raw24698step1Labels = raw24698step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24698step0 raw24698step0Labels permutation56 hz
    mixedMoment B raw24698step1 raw24698step1Labels = mixedMoment B raw24698step2 raw24698step2Labels := by
      have ha : raw24698step2 = (fun i j => raw24698step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24698step2 raw24698step1; decide +kernel
      have hl : raw24698step2Labels = raw24698step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24698step1 raw24698step1Labels permutation9 permutation3
    _ = mixedMoment B node1274 node1274Labels := by rfl

def raw24699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24699Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24699step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24699 raw24699Labels = mixedMoment B node1262 node1262Labels := by
  calc
    mixedMoment B raw24699 raw24699Labels = mixedMoment B raw24699step0 raw24699step0Labels := by
      have hz : ∀ j, raw24699 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24699step0 = (fun i j => raw24699 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24699step0 raw24699; decide +kernel
      have hl : raw24699step0Labels = raw24699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24699 raw24699Labels permutation265 hz
    mixedMoment B raw24699step0 raw24699step0Labels = mixedMoment B raw24699step1 raw24699step1Labels := by
      have ha : raw24699step1 = (fun i j => raw24699step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24699step1 raw24699step0; decide +kernel
      have hl : raw24699step1Labels = raw24699step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24699step0 raw24699step0Labels permutation37 permutation3
    _ = mixedMoment B node1262 node1262Labels := by rfl

def raw24700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24700Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24700step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw24700step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24700 raw24700Labels = mixedMoment B node582 node582Labels := by
  calc
    mixedMoment B raw24700 raw24700Labels = mixedMoment B raw24700step0 raw24700step0Labels := by
      have hz : ∀ j, raw24700 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24700step0 = (fun i j => raw24700 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24700step0 raw24700; decide +kernel
      have hl : raw24700step0Labels = raw24700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24700 raw24700Labels permutation265 hz
    mixedMoment B raw24700step0 raw24700step0Labels = mixedMoment B raw24700step1 raw24700step1Labels := by
      have ha : raw24700step1 = (fun i j => raw24700step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24700step1 raw24700step0; decide +kernel
      have hl : raw24700step1Labels = raw24700step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24700step0 raw24700step0Labels permutation33 permutation3
    _ = mixedMoment B node582 node582Labels := by rfl

def raw24701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24701Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24701step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw24701step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24701 raw24701Labels = mixedMoment B node1113 node1113Labels := by
  calc
    mixedMoment B raw24701 raw24701Labels = mixedMoment B raw24701step0 raw24701step0Labels := by
      have ha : raw24701step0 = (fun i j => raw24701 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24701step0 raw24701; decide +kernel
      have hl : raw24701step0Labels = raw24701Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24701 raw24701Labels permutation153 permutation3
    _ = mixedMoment B node1113 node1113Labels := by rfl

def raw24702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24702Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24702step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24702step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw24702step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24702 raw24702Labels = mixedMoment B node1166 node1166Labels := by
  calc
    mixedMoment B raw24702 raw24702Labels = mixedMoment B raw24702step0 raw24702step0Labels := by
      have hz : ∀ j, raw24702 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24702step0 = (fun i j => raw24702 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24702step0 raw24702; decide +kernel
      have hl : raw24702step0Labels = raw24702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24702 raw24702Labels permutation265 hz
    mixedMoment B raw24702step0 raw24702step0Labels = mixedMoment B raw24702step1 raw24702step1Labels := by
      have ha : raw24702step1 = (fun i j => raw24702step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24702step1 raw24702step0; decide +kernel
      have hl : raw24702step1Labels = raw24702step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24702step0 raw24702step0Labels permutation33 permutation3
    _ = mixedMoment B node1166 node1166Labels := by rfl

def raw24703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24703Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24703step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24703step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24703 raw24703Labels = mixedMoment B node1219 node1219Labels := by
  calc
    mixedMoment B raw24703 raw24703Labels = mixedMoment B raw24703step0 raw24703step0Labels := by
      have hz : ∀ j, raw24703 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24703step0 = (fun i j => raw24703 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24703step0 raw24703; decide +kernel
      have hl : raw24703step0Labels = raw24703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24703 raw24703Labels permutation265 hz
    mixedMoment B raw24703step0 raw24703step0Labels = mixedMoment B raw24703step1 raw24703step1Labels := by
      have ha : raw24703step1 = (fun i j => raw24703step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24703step1 raw24703step0; decide +kernel
      have hl : raw24703step1Labels = raw24703step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24703step0 raw24703step0Labels permutation39 permutation3
    _ = mixedMoment B node1219 node1219Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
