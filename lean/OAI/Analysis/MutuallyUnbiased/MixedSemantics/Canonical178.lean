import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw22784 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22784Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22784step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22784step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22784step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22784step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22784 raw22784Labels = mixedMoment B node4585 node4585Labels := by
  calc
    mixedMoment B raw22784 raw22784Labels = mixedMoment B raw22784step0 raw22784step0Labels := by
      have hz : ∀ j, raw22784 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22784step0 = (fun i j => raw22784 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22784step0 raw22784; decide +kernel
      have hl : raw22784step0Labels = raw22784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22784 raw22784Labels permutation346 hz
    mixedMoment B raw22784step0 raw22784step0Labels = mixedMoment B raw22784step1 raw22784step1Labels := by
      have ha : raw22784step1 = (fun i j => raw22784step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22784step1 raw22784step0; decide +kernel
      have hl : raw22784step1Labels = raw22784step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22784step0 raw22784step0Labels permutation33 permutation6
    mixedMoment B raw22784step1 raw22784step1Labels = mixedMoment B raw22784step2 raw22784step2Labels := by
      have ha : raw22784step2 = raw22784step1 := by apply Matrix.ext; unfold raw22784step2 raw22784step1; decide +kernel
      have hl : raw22784step1Labels = labelEmbedding9 ∘ raw22784step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22784step1 raw22784step1Labels raw22784step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4585 node4585Labels := by rfl

def raw22785 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22785Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22785step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22785step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22785step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22785step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22785 raw22785Labels = mixedMoment B node4585 node4585Labels := by
  calc
    mixedMoment B raw22785 raw22785Labels = mixedMoment B raw22785step0 raw22785step0Labels := by
      have hz : ∀ j, raw22785 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22785step0 = (fun i j => raw22785 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22785step0 raw22785; decide +kernel
      have hl : raw22785step0Labels = raw22785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22785 raw22785Labels permutation265 hz
    mixedMoment B raw22785step0 raw22785step0Labels = mixedMoment B raw22785step1 raw22785step1Labels := by
      have ha : raw22785step1 = (fun i j => raw22785step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22785step1 raw22785step0; decide +kernel
      have hl : raw22785step1Labels = raw22785step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22785step0 raw22785step0Labels permutation33 permutation6
    mixedMoment B raw22785step1 raw22785step1Labels = mixedMoment B raw22785step2 raw22785step2Labels := by
      have ha : raw22785step2 = raw22785step1 := by apply Matrix.ext; unfold raw22785step2 raw22785step1; decide +kernel
      have hl : raw22785step1Labels = labelEmbedding9 ∘ raw22785step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22785step1 raw22785step1Labels raw22785step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4585 node4585Labels := by rfl

def raw22786 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22786Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 2, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22786step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22786step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22786step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22786step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw22786step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22786step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw22786step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22786 raw22786Labels = mixedMoment B node4574 node4574Labels := by
  calc
    mixedMoment B raw22786 raw22786Labels = mixedMoment B raw22786step0 raw22786step0Labels := by
      have hz : ∀ j, raw22786 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22786step0 = (fun i j => raw22786 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22786step0 raw22786; decide +kernel
      have hl : raw22786step0Labels = raw22786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22786 raw22786Labels permutation346 hz
    mixedMoment B raw22786step0 raw22786step0Labels = mixedMoment B raw22786step1 raw22786step1Labels := by
      have hz : ∀ j, raw22786step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22786step1 = (fun i j => raw22786step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22786step1 raw22786step0; decide +kernel
      have hl : raw22786step1Labels = raw22786step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22786step0 raw22786step0Labels permutation56 hz
    mixedMoment B raw22786step1 raw22786step1Labels = mixedMoment B raw22786step2 raw22786step2Labels := by
      have ha : raw22786step2 = (fun i j => raw22786step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22786step2 raw22786step1; decide +kernel
      have hl : raw22786step2Labels = raw22786step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22786step1 raw22786step1Labels permutation9 permutation6
    mixedMoment B raw22786step2 raw22786step2Labels = mixedMoment B raw22786step3 raw22786step3Labels := by
      have ha : raw22786step3 = raw22786step2 := by apply Matrix.ext; unfold raw22786step3 raw22786step2; decide +kernel
      have hl : raw22786step2Labels = labelEmbedding9 ∘ raw22786step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22786step2 raw22786step2Labels raw22786step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4574 node4574Labels := by rfl

def raw22787 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw22787Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw22787step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22787step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw22787step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22787step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22787step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22787step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22787step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22787 raw22787Labels = mixedMoment B node4611 node4611Labels := by
  calc
    mixedMoment B raw22787 raw22787Labels = mixedMoment B raw22787step0 raw22787step0Labels := by
      have hz : ∀ j, raw22787 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22787step0 = (fun i j => raw22787 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22787step0 raw22787; decide +kernel
      have hl : raw22787step0Labels = raw22787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22787 raw22787Labels permutation346 hz
    mixedMoment B raw22787step0 raw22787step0Labels = mixedMoment B raw22787step1 raw22787step1Labels := by
      have hz : ∀ j, raw22787step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22787step1 = (fun i j => raw22787step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22787step1 raw22787step0; decide +kernel
      have hl : raw22787step1Labels = raw22787step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22787step0 raw22787step0Labels permutation56 hz
    mixedMoment B raw22787step1 raw22787step1Labels = mixedMoment B raw22787step2 raw22787step2Labels := by
      have ha : raw22787step2 = (fun i j => raw22787step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22787step2 raw22787step1; decide +kernel
      have hl : raw22787step2Labels = raw22787step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22787step1 raw22787step1Labels permutation9 permutation6
    mixedMoment B raw22787step2 raw22787step2Labels = mixedMoment B raw22787step3 raw22787step3Labels := by
      have ha : raw22787step3 = raw22787step2 := by apply Matrix.ext; unfold raw22787step3 raw22787step2; decide +kernel
      have hl : raw22787step2Labels = labelEmbedding9 ∘ raw22787step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22787step2 raw22787step2Labels raw22787step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4611 node4611Labels := by rfl

def raw22788 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22788Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22788step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22788step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22788step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22788step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22788step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22788step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22788step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22788 raw22788Labels = mixedMoment B node4432 node4432Labels := by
  calc
    mixedMoment B raw22788 raw22788Labels = mixedMoment B raw22788step0 raw22788step0Labels := by
      have hz : ∀ j, raw22788 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22788step0 = (fun i j => raw22788 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22788step0 raw22788; decide +kernel
      have hl : raw22788step0Labels = raw22788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22788 raw22788Labels permutation346 hz
    mixedMoment B raw22788step0 raw22788step0Labels = mixedMoment B raw22788step1 raw22788step1Labels := by
      have hz : ∀ j, raw22788step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22788step1 = (fun i j => raw22788step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22788step1 raw22788step0; decide +kernel
      have hl : raw22788step1Labels = raw22788step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22788step0 raw22788step0Labels permutation56 hz
    mixedMoment B raw22788step1 raw22788step1Labels = mixedMoment B raw22788step2 raw22788step2Labels := by
      have ha : raw22788step2 = (fun i j => raw22788step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22788step2 raw22788step1; decide +kernel
      have hl : raw22788step2Labels = raw22788step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22788step1 raw22788step1Labels permutation8 permutation6
    mixedMoment B raw22788step2 raw22788step2Labels = mixedMoment B raw22788step3 raw22788step3Labels := by
      have ha : raw22788step3 = raw22788step2 := by apply Matrix.ext; unfold raw22788step3 raw22788step2; decide +kernel
      have hl : raw22788step2Labels = labelEmbedding9 ∘ raw22788step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22788step2 raw22788step2Labels raw22788step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4432 node4432Labels := by rfl

def raw22789 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22789Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22789step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22789step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22789step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22789step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22789 raw22789Labels = mixedMoment B node4586 node4586Labels := by
  calc
    mixedMoment B raw22789 raw22789Labels = mixedMoment B raw22789step0 raw22789step0Labels := by
      have hz : ∀ j, raw22789 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22789step0 = (fun i j => raw22789 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22789step0 raw22789; decide +kernel
      have hl : raw22789step0Labels = raw22789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22789 raw22789Labels permutation346 hz
    mixedMoment B raw22789step0 raw22789step0Labels = mixedMoment B raw22789step1 raw22789step1Labels := by
      have ha : raw22789step1 = (fun i j => raw22789step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22789step1 raw22789step0; decide +kernel
      have hl : raw22789step1Labels = raw22789step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22789step0 raw22789step0Labels permutation32 permutation6
    mixedMoment B raw22789step1 raw22789step1Labels = mixedMoment B raw22789step2 raw22789step2Labels := by
      have ha : raw22789step2 = raw22789step1 := by apply Matrix.ext; unfold raw22789step2 raw22789step1; decide +kernel
      have hl : raw22789step1Labels = labelEmbedding9 ∘ raw22789step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22789step1 raw22789step1Labels raw22789step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4586 node4586Labels := by rfl

def raw22790 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22790Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22790step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22790step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22790step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22790step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22790step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22790 raw22790Labels = mixedMoment B node4586 node4586Labels := by
  calc
    mixedMoment B raw22790 raw22790Labels = mixedMoment B raw22790step0 raw22790step0Labels := by
      have hz : ∀ j, raw22790 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22790step0 = (fun i j => raw22790 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22790step0 raw22790; decide +kernel
      have hl : raw22790step0Labels = raw22790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22790 raw22790Labels permutation265 hz
    mixedMoment B raw22790step0 raw22790step0Labels = mixedMoment B raw22790step1 raw22790step1Labels := by
      have ha : raw22790step1 = (fun i j => raw22790step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22790step1 raw22790step0; decide +kernel
      have hl : raw22790step1Labels = raw22790step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22790step0 raw22790step0Labels permutation32 permutation6
    mixedMoment B raw22790step1 raw22790step1Labels = mixedMoment B raw22790step2 raw22790step2Labels := by
      have ha : raw22790step2 = raw22790step1 := by apply Matrix.ext; unfold raw22790step2 raw22790step1; decide +kernel
      have hl : raw22790step1Labels = labelEmbedding9 ∘ raw22790step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22790step1 raw22790step1Labels raw22790step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4586 node4586Labels := by rfl

def raw22791 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22791Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22791step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22791step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22791step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22791step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22791step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22791step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22791step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22791 raw22791Labels = mixedMoment B node4575 node4575Labels := by
  calc
    mixedMoment B raw22791 raw22791Labels = mixedMoment B raw22791step0 raw22791step0Labels := by
      have hz : ∀ j, raw22791 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22791step0 = (fun i j => raw22791 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22791step0 raw22791; decide +kernel
      have hl : raw22791step0Labels = raw22791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22791 raw22791Labels permutation346 hz
    mixedMoment B raw22791step0 raw22791step0Labels = mixedMoment B raw22791step1 raw22791step1Labels := by
      have hz : ∀ j, raw22791step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22791step1 = (fun i j => raw22791step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22791step1 raw22791step0; decide +kernel
      have hl : raw22791step1Labels = raw22791step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22791step0 raw22791step0Labels permutation56 hz
    mixedMoment B raw22791step1 raw22791step1Labels = mixedMoment B raw22791step2 raw22791step2Labels := by
      have ha : raw22791step2 = (fun i j => raw22791step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22791step2 raw22791step1; decide +kernel
      have hl : raw22791step2Labels = raw22791step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22791step1 raw22791step1Labels permutation8 permutation6
    mixedMoment B raw22791step2 raw22791step2Labels = mixedMoment B raw22791step3 raw22791step3Labels := by
      have ha : raw22791step3 = raw22791step2 := by apply Matrix.ext; unfold raw22791step3 raw22791step2; decide +kernel
      have hl : raw22791step2Labels = labelEmbedding9 ∘ raw22791step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22791step2 raw22791step2Labels raw22791step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4575 node4575Labels := by rfl

def raw22792 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22792Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22792step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22792step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22792 raw22792Labels = mixedMoment B node1391 node1391Labels := by
  calc
    mixedMoment B raw22792 raw22792Labels = mixedMoment B raw22792step0 raw22792step0Labels := by
      have hz : ∀ j, raw22792 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22792step0 = (fun i j => raw22792 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22792step0 raw22792; decide +kernel
      have hl : raw22792step0Labels = raw22792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22792 raw22792Labels permutation346 hz
    mixedMoment B raw22792step0 raw22792step0Labels = mixedMoment B raw22792step1 raw22792step1Labels := by
      have ha : raw22792step1 = (fun i j => raw22792step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22792step1 raw22792step0; decide +kernel
      have hl : raw22792step1Labels = raw22792step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22792step0 raw22792step0Labels permutation33 permutation6
    _ = mixedMoment B node1391 node1391Labels := by rfl

def raw22793 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22793Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22793step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22793step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22793 raw22793Labels = mixedMoment B node1391 node1391Labels := by
  calc
    mixedMoment B raw22793 raw22793Labels = mixedMoment B raw22793step0 raw22793step0Labels := by
      have hz : ∀ j, raw22793 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22793step0 = (fun i j => raw22793 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22793step0 raw22793; decide +kernel
      have hl : raw22793step0Labels = raw22793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22793 raw22793Labels permutation265 hz
    mixedMoment B raw22793step0 raw22793step0Labels = mixedMoment B raw22793step1 raw22793step1Labels := by
      have ha : raw22793step1 = (fun i j => raw22793step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22793step1 raw22793step0; decide +kernel
      have hl : raw22793step1Labels = raw22793step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22793step0 raw22793step0Labels permutation33 permutation6
    _ = mixedMoment B node1391 node1391Labels := by rfl

def raw22794 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22794Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22794step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22794step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22794step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22794step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw22794step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22794 raw22794Labels = mixedMoment B node1375 node1375Labels := by
  calc
    mixedMoment B raw22794 raw22794Labels = mixedMoment B raw22794step0 raw22794step0Labels := by
      have hz : ∀ j, raw22794 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22794step0 = (fun i j => raw22794 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22794step0 raw22794; decide +kernel
      have hl : raw22794step0Labels = raw22794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22794 raw22794Labels permutation346 hz
    mixedMoment B raw22794step0 raw22794step0Labels = mixedMoment B raw22794step1 raw22794step1Labels := by
      have hz : ∀ j, raw22794step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22794step1 = (fun i j => raw22794step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22794step1 raw22794step0; decide +kernel
      have hl : raw22794step1Labels = raw22794step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22794step0 raw22794step0Labels permutation56 hz
    mixedMoment B raw22794step1 raw22794step1Labels = mixedMoment B raw22794step2 raw22794step2Labels := by
      have ha : raw22794step2 = (fun i j => raw22794step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22794step2 raw22794step1; decide +kernel
      have hl : raw22794step2Labels = raw22794step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22794step1 raw22794step1Labels permutation9 permutation6
    _ = mixedMoment B node1375 node1375Labels := by rfl

def raw22795 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22795Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22795step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22795step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22795step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22795step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw22795step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22795 raw22795Labels = mixedMoment B node1419 node1419Labels := by
  calc
    mixedMoment B raw22795 raw22795Labels = mixedMoment B raw22795step0 raw22795step0Labels := by
      have hz : ∀ j, raw22795 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22795step0 = (fun i j => raw22795 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22795step0 raw22795; decide +kernel
      have hl : raw22795step0Labels = raw22795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22795 raw22795Labels permutation346 hz
    mixedMoment B raw22795step0 raw22795step0Labels = mixedMoment B raw22795step1 raw22795step1Labels := by
      have hz : ∀ j, raw22795step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22795step1 = (fun i j => raw22795step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22795step1 raw22795step0; decide +kernel
      have hl : raw22795step1Labels = raw22795step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22795step0 raw22795step0Labels permutation56 hz
    mixedMoment B raw22795step1 raw22795step1Labels = mixedMoment B raw22795step2 raw22795step2Labels := by
      have ha : raw22795step2 = (fun i j => raw22795step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22795step2 raw22795step1; decide +kernel
      have hl : raw22795step2Labels = raw22795step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22795step1 raw22795step1Labels permutation9 permutation6
    _ = mixedMoment B node1419 node1419Labels := by rfl

def raw22796 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22796Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22796step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22796step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22796step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22796 raw22796Labels = mixedMoment B node985 node985Labels := by
  calc
    mixedMoment B raw22796 raw22796Labels = mixedMoment B raw22796step0 raw22796step0Labels := by
      have hz : ∀ j, raw22796 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22796step0 = (fun i j => raw22796 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22796step0 raw22796; decide +kernel
      have hl : raw22796step0Labels = raw22796Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22796 raw22796Labels permutation346 hz
    mixedMoment B raw22796step0 raw22796step0Labels = mixedMoment B raw22796step1 raw22796step1Labels := by
      have ha : raw22796step1 = (fun i j => raw22796step0 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22796step1 raw22796step0; decide +kernel
      have hl : raw22796step1Labels = raw22796step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22796step0 raw22796step0Labels permutation39 permutation6
    _ = mixedMoment B node985 node985Labels := by rfl

def raw22797 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22797Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22797step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22797step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22797 raw22797Labels = mixedMoment B node1196 node1196Labels := by
  calc
    mixedMoment B raw22797 raw22797Labels = mixedMoment B raw22797step0 raw22797step0Labels := by
      have ha : raw22797step0 = (fun i j => raw22797 (permutation183 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22797step0 raw22797; decide +kernel
      have hl : raw22797step0Labels = raw22797Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22797 raw22797Labels permutation183 permutation6
    _ = mixedMoment B node1196 node1196Labels := by rfl

def raw22798 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22798Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22798step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22798step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22798 raw22798Labels = mixedMoment B node1182 node1182Labels := by
  calc
    mixedMoment B raw22798 raw22798Labels = mixedMoment B raw22798step0 raw22798step0Labels := by
      have hz : ∀ j, raw22798 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22798step0 = (fun i j => raw22798 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22798step0 raw22798; decide +kernel
      have hl : raw22798step0Labels = raw22798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22798 raw22798Labels permutation346 hz
    mixedMoment B raw22798step0 raw22798step0Labels = mixedMoment B raw22798step1 raw22798step1Labels := by
      have ha : raw22798step1 = (fun i j => raw22798step0 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22798step1 raw22798step0; decide +kernel
      have hl : raw22798step1Labels = raw22798step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22798step0 raw22798step0Labels permutation39 permutation6
    _ = mixedMoment B node1182 node1182Labels := by rfl

def raw22799 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22799Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22799step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22799step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22799 raw22799Labels = mixedMoment B node1219 node1219Labels := by
  calc
    mixedMoment B raw22799 raw22799Labels = mixedMoment B raw22799step0 raw22799step0Labels := by
      have hz : ∀ j, raw22799 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22799step0 = (fun i j => raw22799 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22799step0 raw22799; decide +kernel
      have hl : raw22799step0Labels = raw22799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22799 raw22799Labels permutation346 hz
    mixedMoment B raw22799step0 raw22799step0Labels = mixedMoment B raw22799step1 raw22799step1Labels := by
      have ha : raw22799step1 = (fun i j => raw22799step0 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22799step1 raw22799step0; decide +kernel
      have hl : raw22799step1Labels = raw22799step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22799step0 raw22799step0Labels permutation39 permutation6
    _ = mixedMoment B node1219 node1219Labels := by rfl

def raw22800 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22800Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22800step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22800step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22800 raw22800Labels = mixedMoment B node985 node985Labels := by
  calc
    mixedMoment B raw22800 raw22800Labels = mixedMoment B raw22800step0 raw22800step0Labels := by
      have hz : ∀ j, raw22800 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22800step0 = (fun i j => raw22800 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22800step0 raw22800; decide +kernel
      have hl : raw22800step0Labels = raw22800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22800 raw22800Labels permutation265 hz
    mixedMoment B raw22800step0 raw22800step0Labels = mixedMoment B raw22800step1 raw22800step1Labels := by
      have ha : raw22800step1 = (fun i j => raw22800step0 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22800step1 raw22800step0; decide +kernel
      have hl : raw22800step1Labels = raw22800step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22800step0 raw22800step0Labels permutation39 permutation6
    _ = mixedMoment B node985 node985Labels := by rfl

def raw22801 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22801Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22801step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22801 raw22801Labels = mixedMoment B node1196 node1196Labels := by
  calc
    mixedMoment B raw22801 raw22801Labels = mixedMoment B raw22801step0 raw22801step0Labels := by
      have ha : raw22801step0 = (fun i j => raw22801 (permutation159 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22801step0 raw22801; decide +kernel
      have hl : raw22801step0Labels = raw22801Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22801 raw22801Labels permutation159 permutation6
    _ = mixedMoment B node1196 node1196Labels := by rfl

def raw22802 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22802Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22802step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22802step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22802step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22802 raw22802Labels = mixedMoment B node1182 node1182Labels := by
  calc
    mixedMoment B raw22802 raw22802Labels = mixedMoment B raw22802step0 raw22802step0Labels := by
      have hz : ∀ j, raw22802 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22802step0 = (fun i j => raw22802 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22802step0 raw22802; decide +kernel
      have hl : raw22802step0Labels = raw22802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22802 raw22802Labels permutation265 hz
    mixedMoment B raw22802step0 raw22802step0Labels = mixedMoment B raw22802step1 raw22802step1Labels := by
      have ha : raw22802step1 = (fun i j => raw22802step0 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22802step1 raw22802step0; decide +kernel
      have hl : raw22802step1Labels = raw22802step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22802step0 raw22802step0Labels permutation39 permutation6
    _ = mixedMoment B node1182 node1182Labels := by rfl

def raw22803 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22803Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22803step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22803step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22803step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22803 raw22803Labels = mixedMoment B node1219 node1219Labels := by
  calc
    mixedMoment B raw22803 raw22803Labels = mixedMoment B raw22803step0 raw22803step0Labels := by
      have hz : ∀ j, raw22803 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22803step0 = (fun i j => raw22803 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22803step0 raw22803; decide +kernel
      have hl : raw22803step0Labels = raw22803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22803 raw22803Labels permutation265 hz
    mixedMoment B raw22803step0 raw22803step0Labels = mixedMoment B raw22803step1 raw22803step1Labels := by
      have ha : raw22803step1 = (fun i j => raw22803step0 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22803step1 raw22803step0; decide +kernel
      have hl : raw22803step1Labels = raw22803step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22803step0 raw22803step0Labels permutation39 permutation6
    _ = mixedMoment B node1219 node1219Labels := by rfl

def raw22804 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22804Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22804step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22804step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22804step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22804step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22804step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22804 raw22804Labels = mixedMoment B node1012 node1012Labels := by
  calc
    mixedMoment B raw22804 raw22804Labels = mixedMoment B raw22804step0 raw22804step0Labels := by
      have hz : ∀ j, raw22804 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22804step0 = (fun i j => raw22804 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22804step0 raw22804; decide +kernel
      have hl : raw22804step0Labels = raw22804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22804 raw22804Labels permutation346 hz
    mixedMoment B raw22804step0 raw22804step0Labels = mixedMoment B raw22804step1 raw22804step1Labels := by
      have hz : ∀ j, raw22804step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22804step1 = (fun i j => raw22804step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22804step1 raw22804step0; decide +kernel
      have hl : raw22804step1Labels = raw22804step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22804step0 raw22804step0Labels permutation56 hz
    mixedMoment B raw22804step1 raw22804step1Labels = mixedMoment B raw22804step2 raw22804step2Labels := by
      have ha : raw22804step2 = (fun i j => raw22804step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22804step2 raw22804step1; decide +kernel
      have hl : raw22804step2Labels = raw22804step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22804step1 raw22804step1Labels permutation9 permutation6
    _ = mixedMoment B node1012 node1012Labels := by rfl

def raw22805 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22805Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22805step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22805step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22805step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22805 raw22805Labels = mixedMoment B node1204 node1204Labels := by
  calc
    mixedMoment B raw22805 raw22805Labels = mixedMoment B raw22805step0 raw22805step0Labels := by
      have hz : ∀ j, raw22805 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22805step0 = (fun i j => raw22805 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22805step0 raw22805; decide +kernel
      have hl : raw22805step0Labels = raw22805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22805 raw22805Labels permutation346 hz
    mixedMoment B raw22805step0 raw22805step0Labels = mixedMoment B raw22805step1 raw22805step1Labels := by
      have ha : raw22805step1 = (fun i j => raw22805step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22805step1 raw22805step0; decide +kernel
      have hl : raw22805step1Labels = raw22805step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22805step0 raw22805step0Labels permutation33 permutation6
    _ = mixedMoment B node1204 node1204Labels := by rfl

def raw22806 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22806Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22806step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22806step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22806 raw22806Labels = mixedMoment B node1204 node1204Labels := by
  calc
    mixedMoment B raw22806 raw22806Labels = mixedMoment B raw22806step0 raw22806step0Labels := by
      have hz : ∀ j, raw22806 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22806step0 = (fun i j => raw22806 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22806step0 raw22806; decide +kernel
      have hl : raw22806step0Labels = raw22806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22806 raw22806Labels permutation265 hz
    mixedMoment B raw22806step0 raw22806step0Labels = mixedMoment B raw22806step1 raw22806step1Labels := by
      have ha : raw22806step1 = (fun i j => raw22806step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22806step1 raw22806step0; decide +kernel
      have hl : raw22806step1Labels = raw22806step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22806step0 raw22806step0Labels permutation33 permutation6
    _ = mixedMoment B node1204 node1204Labels := by rfl

def raw22807 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22807Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 2, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22807step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22807step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22807step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22807step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw22807step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22807 raw22807Labels = mixedMoment B node1192 node1192Labels := by
  calc
    mixedMoment B raw22807 raw22807Labels = mixedMoment B raw22807step0 raw22807step0Labels := by
      have hz : ∀ j, raw22807 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22807step0 = (fun i j => raw22807 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22807step0 raw22807; decide +kernel
      have hl : raw22807step0Labels = raw22807Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22807 raw22807Labels permutation346 hz
    mixedMoment B raw22807step0 raw22807step0Labels = mixedMoment B raw22807step1 raw22807step1Labels := by
      have hz : ∀ j, raw22807step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22807step1 = (fun i j => raw22807step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22807step1 raw22807step0; decide +kernel
      have hl : raw22807step1Labels = raw22807step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22807step0 raw22807step0Labels permutation56 hz
    mixedMoment B raw22807step1 raw22807step1Labels = mixedMoment B raw22807step2 raw22807step2Labels := by
      have ha : raw22807step2 = (fun i j => raw22807step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22807step2 raw22807step1; decide +kernel
      have hl : raw22807step2Labels = raw22807step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22807step1 raw22807step1Labels permutation9 permutation6
    _ = mixedMoment B node1192 node1192Labels := by rfl

def raw22808 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw22808Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw22808step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22808step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw22808step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22808step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22808step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22808 raw22808Labels = mixedMoment B node1245 node1245Labels := by
  calc
    mixedMoment B raw22808 raw22808Labels = mixedMoment B raw22808step0 raw22808step0Labels := by
      have hz : ∀ j, raw22808 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22808step0 = (fun i j => raw22808 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22808step0 raw22808; decide +kernel
      have hl : raw22808step0Labels = raw22808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22808 raw22808Labels permutation346 hz
    mixedMoment B raw22808step0 raw22808step0Labels = mixedMoment B raw22808step1 raw22808step1Labels := by
      have hz : ∀ j, raw22808step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22808step1 = (fun i j => raw22808step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22808step1 raw22808step0; decide +kernel
      have hl : raw22808step1Labels = raw22808step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22808step0 raw22808step0Labels permutation56 hz
    mixedMoment B raw22808step1 raw22808step1Labels = mixedMoment B raw22808step2 raw22808step2Labels := by
      have ha : raw22808step2 = (fun i j => raw22808step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22808step2 raw22808step1; decide +kernel
      have hl : raw22808step2Labels = raw22808step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22808step1 raw22808step1Labels permutation9 permutation6
    _ = mixedMoment B node1245 node1245Labels := by rfl

def raw22809 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22809Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22809step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22809step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22809step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22809step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22809step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22809 raw22809Labels = mixedMoment B node1013 node1013Labels := by
  calc
    mixedMoment B raw22809 raw22809Labels = mixedMoment B raw22809step0 raw22809step0Labels := by
      have hz : ∀ j, raw22809 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22809step0 = (fun i j => raw22809 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22809step0 raw22809; decide +kernel
      have hl : raw22809step0Labels = raw22809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22809 raw22809Labels permutation346 hz
    mixedMoment B raw22809step0 raw22809step0Labels = mixedMoment B raw22809step1 raw22809step1Labels := by
      have hz : ∀ j, raw22809step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22809step1 = (fun i j => raw22809step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22809step1 raw22809step0; decide +kernel
      have hl : raw22809step1Labels = raw22809step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22809step0 raw22809step0Labels permutation56 hz
    mixedMoment B raw22809step1 raw22809step1Labels = mixedMoment B raw22809step2 raw22809step2Labels := by
      have ha : raw22809step2 = (fun i j => raw22809step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22809step2 raw22809step1; decide +kernel
      have hl : raw22809step2Labels = raw22809step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22809step1 raw22809step1Labels permutation8 permutation6
    _ = mixedMoment B node1013 node1013Labels := by rfl

def raw22810 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22810Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22810step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22810step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22810step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22810 raw22810Labels = mixedMoment B node1205 node1205Labels := by
  calc
    mixedMoment B raw22810 raw22810Labels = mixedMoment B raw22810step0 raw22810step0Labels := by
      have hz : ∀ j, raw22810 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22810step0 = (fun i j => raw22810 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22810step0 raw22810; decide +kernel
      have hl : raw22810step0Labels = raw22810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22810 raw22810Labels permutation346 hz
    mixedMoment B raw22810step0 raw22810step0Labels = mixedMoment B raw22810step1 raw22810step1Labels := by
      have ha : raw22810step1 = (fun i j => raw22810step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22810step1 raw22810step0; decide +kernel
      have hl : raw22810step1Labels = raw22810step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22810step0 raw22810step0Labels permutation32 permutation6
    _ = mixedMoment B node1205 node1205Labels := by rfl

def raw22811 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22811Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22811step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22811step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22811 raw22811Labels = mixedMoment B node1205 node1205Labels := by
  calc
    mixedMoment B raw22811 raw22811Labels = mixedMoment B raw22811step0 raw22811step0Labels := by
      have hz : ∀ j, raw22811 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22811step0 = (fun i j => raw22811 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22811step0 raw22811; decide +kernel
      have hl : raw22811step0Labels = raw22811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22811 raw22811Labels permutation265 hz
    mixedMoment B raw22811step0 raw22811step0Labels = mixedMoment B raw22811step1 raw22811step1Labels := by
      have ha : raw22811step1 = (fun i j => raw22811step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22811step1 raw22811step0; decide +kernel
      have hl : raw22811step1Labels = raw22811step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22811step0 raw22811step0Labels permutation32 permutation6
    _ = mixedMoment B node1205 node1205Labels := by rfl

def raw22812 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22812Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22812step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22812step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22812step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22812step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22812step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22812 raw22812Labels = mixedMoment B node1193 node1193Labels := by
  calc
    mixedMoment B raw22812 raw22812Labels = mixedMoment B raw22812step0 raw22812step0Labels := by
      have hz : ∀ j, raw22812 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22812step0 = (fun i j => raw22812 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22812step0 raw22812; decide +kernel
      have hl : raw22812step0Labels = raw22812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22812 raw22812Labels permutation346 hz
    mixedMoment B raw22812step0 raw22812step0Labels = mixedMoment B raw22812step1 raw22812step1Labels := by
      have hz : ∀ j, raw22812step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22812step1 = (fun i j => raw22812step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22812step1 raw22812step0; decide +kernel
      have hl : raw22812step1Labels = raw22812step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22812step0 raw22812step0Labels permutation56 hz
    mixedMoment B raw22812step1 raw22812step1Labels = mixedMoment B raw22812step2 raw22812step2Labels := by
      have ha : raw22812step2 = (fun i j => raw22812step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22812step2 raw22812step1; decide +kernel
      have hl : raw22812step2Labels = raw22812step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22812step1 raw22812step1Labels permutation8 permutation6
    _ = mixedMoment B node1193 node1193Labels := by rfl

def raw22813 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22813Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22813step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22813step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22813step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22813step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22813step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22813 raw22813Labels = mixedMoment B node1026 node1026Labels := by
  calc
    mixedMoment B raw22813 raw22813Labels = mixedMoment B raw22813step0 raw22813step0Labels := by
      have hz : ∀ j, raw22813 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22813step0 = (fun i j => raw22813 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22813step0 raw22813; decide +kernel
      have hl : raw22813step0Labels = raw22813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22813 raw22813Labels permutation346 hz
    mixedMoment B raw22813step0 raw22813step0Labels = mixedMoment B raw22813step1 raw22813step1Labels := by
      have ha : raw22813step1 = (fun i j => raw22813step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22813step1 raw22813step0; decide +kernel
      have hl : raw22813step1Labels = raw22813step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22813step0 raw22813step0Labels permutation32 permutation7
    mixedMoment B raw22813step1 raw22813step1Labels = mixedMoment B raw22813step2 raw22813step2Labels := by
      have ha : raw22813step2 = raw22813step1 := by apply Matrix.ext; unfold raw22813step2 raw22813step1; decide +kernel
      have hl : raw22813step1Labels = labelEmbedding1 ∘ raw22813step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22813step1 raw22813step1Labels raw22813step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1026 node1026Labels := by rfl

def raw22814 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22814Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22814step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22814step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22814step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22814step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22814step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22814 raw22814Labels = mixedMoment B node1026 node1026Labels := by
  calc
    mixedMoment B raw22814 raw22814Labels = mixedMoment B raw22814step0 raw22814step0Labels := by
      have hz : ∀ j, raw22814 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22814step0 = (fun i j => raw22814 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22814step0 raw22814; decide +kernel
      have hl : raw22814step0Labels = raw22814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22814 raw22814Labels permutation265 hz
    mixedMoment B raw22814step0 raw22814step0Labels = mixedMoment B raw22814step1 raw22814step1Labels := by
      have ha : raw22814step1 = (fun i j => raw22814step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22814step1 raw22814step0; decide +kernel
      have hl : raw22814step1Labels = raw22814step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22814step0 raw22814step0Labels permutation32 permutation7
    mixedMoment B raw22814step1 raw22814step1Labels = mixedMoment B raw22814step2 raw22814step2Labels := by
      have ha : raw22814step2 = raw22814step1 := by apply Matrix.ext; unfold raw22814step2 raw22814step1; decide +kernel
      have hl : raw22814step1Labels = labelEmbedding1 ∘ raw22814step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22814step1 raw22814step1Labels raw22814step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1026 node1026Labels := by rfl

def raw22815 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22815Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22815step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22815step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22815step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22815step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22815step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22815step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22815step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22815 raw22815Labels = mixedMoment B node1063 node1063Labels := by
  calc
    mixedMoment B raw22815 raw22815Labels = mixedMoment B raw22815step0 raw22815step0Labels := by
      have hz : ∀ j, raw22815 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22815step0 = (fun i j => raw22815 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22815step0 raw22815; decide +kernel
      have hl : raw22815step0Labels = raw22815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22815 raw22815Labels permutation346 hz
    mixedMoment B raw22815step0 raw22815step0Labels = mixedMoment B raw22815step1 raw22815step1Labels := by
      have hz : ∀ j, raw22815step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22815step1 = (fun i j => raw22815step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22815step1 raw22815step0; decide +kernel
      have hl : raw22815step1Labels = raw22815step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22815step0 raw22815step0Labels permutation56 hz
    mixedMoment B raw22815step1 raw22815step1Labels = mixedMoment B raw22815step2 raw22815step2Labels := by
      have ha : raw22815step2 = (fun i j => raw22815step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22815step2 raw22815step1; decide +kernel
      have hl : raw22815step2Labels = raw22815step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22815step1 raw22815step1Labels permutation8 permutation7
    mixedMoment B raw22815step2 raw22815step2Labels = mixedMoment B raw22815step3 raw22815step3Labels := by
      have ha : raw22815step3 = raw22815step2 := by apply Matrix.ext; unfold raw22815step3 raw22815step2; decide +kernel
      have hl : raw22815step2Labels = labelEmbedding1 ∘ raw22815step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22815step2 raw22815step2Labels raw22815step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1063 node1063Labels := by rfl

def raw22816 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22816Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22816step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22816step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22816step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22816step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22816step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22816step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22816step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22816 raw22816Labels = mixedMoment B node1050 node1050Labels := by
  calc
    mixedMoment B raw22816 raw22816Labels = mixedMoment B raw22816step0 raw22816step0Labels := by
      have hz : ∀ j, raw22816 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22816step0 = (fun i j => raw22816 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22816step0 raw22816; decide +kernel
      have hl : raw22816step0Labels = raw22816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22816 raw22816Labels permutation346 hz
    mixedMoment B raw22816step0 raw22816step0Labels = mixedMoment B raw22816step1 raw22816step1Labels := by
      have hz : ∀ j, raw22816step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22816step1 = (fun i j => raw22816step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22816step1 raw22816step0; decide +kernel
      have hl : raw22816step1Labels = raw22816step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22816step0 raw22816step0Labels permutation56 hz
    mixedMoment B raw22816step1 raw22816step1Labels = mixedMoment B raw22816step2 raw22816step2Labels := by
      have ha : raw22816step2 = (fun i j => raw22816step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22816step2 raw22816step1; decide +kernel
      have hl : raw22816step2Labels = raw22816step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22816step1 raw22816step1Labels permutation8 permutation7
    mixedMoment B raw22816step2 raw22816step2Labels = mixedMoment B raw22816step3 raw22816step3Labels := by
      have ha : raw22816step3 = raw22816step2 := by apply Matrix.ext; unfold raw22816step3 raw22816step2; decide +kernel
      have hl : raw22816step2Labels = labelEmbedding1 ∘ raw22816step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22816step2 raw22816step2Labels raw22816step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1050 node1050Labels := by rfl

def raw22817 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22817Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22817step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22817step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22817step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22817step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22817step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22817step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22817step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22817 raw22817Labels = mixedMoment B node1049 node1049Labels := by
  calc
    mixedMoment B raw22817 raw22817Labels = mixedMoment B raw22817step0 raw22817step0Labels := by
      have hz : ∀ j, raw22817 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22817step0 = (fun i j => raw22817 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22817step0 raw22817; decide +kernel
      have hl : raw22817step0Labels = raw22817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22817 raw22817Labels permutation346 hz
    mixedMoment B raw22817step0 raw22817step0Labels = mixedMoment B raw22817step1 raw22817step1Labels := by
      have hz : ∀ j, raw22817step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22817step1 = (fun i j => raw22817step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22817step1 raw22817step0; decide +kernel
      have hl : raw22817step1Labels = raw22817step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22817step0 raw22817step0Labels permutation56 hz
    mixedMoment B raw22817step1 raw22817step1Labels = mixedMoment B raw22817step2 raw22817step2Labels := by
      have ha : raw22817step2 = (fun i j => raw22817step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22817step2 raw22817step1; decide +kernel
      have hl : raw22817step2Labels = raw22817step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22817step1 raw22817step1Labels permutation8 permutation7
    mixedMoment B raw22817step2 raw22817step2Labels = mixedMoment B raw22817step3 raw22817step3Labels := by
      have ha : raw22817step3 = raw22817step2 := by apply Matrix.ext; unfold raw22817step3 raw22817step2; decide +kernel
      have hl : raw22817step2Labels = labelEmbedding1 ∘ raw22817step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22817step2 raw22817step2Labels raw22817step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1049 node1049Labels := by rfl

def raw22818 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22818Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22818step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22818step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22818step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22818step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22818 raw22818Labels = mixedMoment B node1401 node1401Labels := by
  calc
    mixedMoment B raw22818 raw22818Labels = mixedMoment B raw22818step0 raw22818step0Labels := by
      have hz : ∀ j, raw22818 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22818step0 = (fun i j => raw22818 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22818step0 raw22818; decide +kernel
      have hl : raw22818step0Labels = raw22818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22818 raw22818Labels permutation346 hz
    mixedMoment B raw22818step0 raw22818step0Labels = mixedMoment B raw22818step1 raw22818step1Labels := by
      have ha : raw22818step1 = (fun i j => raw22818step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22818step1 raw22818step0; decide +kernel
      have hl : raw22818step1Labels = raw22818step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22818step0 raw22818step0Labels permutation32 permutation7
    mixedMoment B raw22818step1 raw22818step1Labels = mixedMoment B raw22818step2 raw22818step2Labels := by
      have ha : raw22818step2 = raw22818step1 := by apply Matrix.ext; unfold raw22818step2 raw22818step1; decide +kernel
      have hl : raw22818step1Labels = labelEmbedding1 ∘ raw22818step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22818step1 raw22818step1Labels raw22818step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1401 node1401Labels := by rfl

def raw22819 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22819Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22819step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22819step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22819step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22819step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22819 raw22819Labels = mixedMoment B node1208 node1208Labels := by
  calc
    mixedMoment B raw22819 raw22819Labels = mixedMoment B raw22819step0 raw22819step0Labels := by
      have ha : raw22819step0 = (fun i j => raw22819 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22819step0 raw22819; decide +kernel
      have hl : raw22819step0Labels = raw22819Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22819 raw22819Labels permutation152 permutation7
    mixedMoment B raw22819step0 raw22819step0Labels = mixedMoment B raw22819step1 raw22819step1Labels := by
      have ha : raw22819step1 = raw22819step0 := by apply Matrix.ext; unfold raw22819step1 raw22819step0; decide +kernel
      have hl : raw22819step0Labels = labelEmbedding1 ∘ raw22819step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22819step0 raw22819step0Labels raw22819step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1208 node1208Labels := by rfl

def raw22820 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22820Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22820step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22820step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22820step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22820step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22820 raw22820Labels = mixedMoment B node1226 node1226Labels := by
  calc
    mixedMoment B raw22820 raw22820Labels = mixedMoment B raw22820step0 raw22820step0Labels := by
      have hz : ∀ j, raw22820 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22820step0 = (fun i j => raw22820 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22820step0 raw22820; decide +kernel
      have hl : raw22820step0Labels = raw22820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22820 raw22820Labels permutation346 hz
    mixedMoment B raw22820step0 raw22820step0Labels = mixedMoment B raw22820step1 raw22820step1Labels := by
      have ha : raw22820step1 = (fun i j => raw22820step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22820step1 raw22820step0; decide +kernel
      have hl : raw22820step1Labels = raw22820step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22820step0 raw22820step0Labels permutation32 permutation7
    mixedMoment B raw22820step1 raw22820step1Labels = mixedMoment B raw22820step2 raw22820step2Labels := by
      have ha : raw22820step2 = raw22820step1 := by apply Matrix.ext; unfold raw22820step2 raw22820step1; decide +kernel
      have hl : raw22820step1Labels = labelEmbedding1 ∘ raw22820step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22820step1 raw22820step1Labels raw22820step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1226 node1226Labels := by rfl

def raw22821 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22821Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22821step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22821step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22821step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22821step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22821step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22821 raw22821Labels = mixedMoment B node1220 node1220Labels := by
  calc
    mixedMoment B raw22821 raw22821Labels = mixedMoment B raw22821step0 raw22821step0Labels := by
      have hz : ∀ j, raw22821 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22821step0 = (fun i j => raw22821 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22821step0 raw22821; decide +kernel
      have hl : raw22821step0Labels = raw22821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22821 raw22821Labels permutation346 hz
    mixedMoment B raw22821step0 raw22821step0Labels = mixedMoment B raw22821step1 raw22821step1Labels := by
      have ha : raw22821step1 = (fun i j => raw22821step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22821step1 raw22821step0; decide +kernel
      have hl : raw22821step1Labels = raw22821step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22821step0 raw22821step0Labels permutation32 permutation7
    mixedMoment B raw22821step1 raw22821step1Labels = mixedMoment B raw22821step2 raw22821step2Labels := by
      have ha : raw22821step2 = raw22821step1 := by apply Matrix.ext; unfold raw22821step2 raw22821step1; decide +kernel
      have hl : raw22821step1Labels = labelEmbedding1 ∘ raw22821step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22821step1 raw22821step1Labels raw22821step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1220 node1220Labels := by rfl

def raw22822 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22822Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22822step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22822step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22822step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22822step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22822step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22822 raw22822Labels = mixedMoment B node1219 node1219Labels := by
  calc
    mixedMoment B raw22822 raw22822Labels = mixedMoment B raw22822step0 raw22822step0Labels := by
      have hz : ∀ j, raw22822 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22822step0 = (fun i j => raw22822 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22822step0 raw22822; decide +kernel
      have hl : raw22822step0Labels = raw22822Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22822 raw22822Labels permutation346 hz
    mixedMoment B raw22822step0 raw22822step0Labels = mixedMoment B raw22822step1 raw22822step1Labels := by
      have ha : raw22822step1 = (fun i j => raw22822step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22822step1 raw22822step0; decide +kernel
      have hl : raw22822step1Labels = raw22822step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22822step0 raw22822step0Labels permutation32 permutation7
    mixedMoment B raw22822step1 raw22822step1Labels = mixedMoment B raw22822step2 raw22822step2Labels := by
      have ha : raw22822step2 = raw22822step1 := by apply Matrix.ext; unfold raw22822step2 raw22822step1; decide +kernel
      have hl : raw22822step1Labels = labelEmbedding1 ∘ raw22822step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22822step1 raw22822step1Labels raw22822step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1219 node1219Labels := by rfl

def raw22823 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22823Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22823step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22823step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22823step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22823step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22823step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22823 raw22823Labels = mixedMoment B node1401 node1401Labels := by
  calc
    mixedMoment B raw22823 raw22823Labels = mixedMoment B raw22823step0 raw22823step0Labels := by
      have hz : ∀ j, raw22823 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22823step0 = (fun i j => raw22823 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22823step0 raw22823; decide +kernel
      have hl : raw22823step0Labels = raw22823Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22823 raw22823Labels permutation265 hz
    mixedMoment B raw22823step0 raw22823step0Labels = mixedMoment B raw22823step1 raw22823step1Labels := by
      have ha : raw22823step1 = (fun i j => raw22823step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22823step1 raw22823step0; decide +kernel
      have hl : raw22823step1Labels = raw22823step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22823step0 raw22823step0Labels permutation32 permutation7
    mixedMoment B raw22823step1 raw22823step1Labels = mixedMoment B raw22823step2 raw22823step2Labels := by
      have ha : raw22823step2 = raw22823step1 := by apply Matrix.ext; unfold raw22823step2 raw22823step1; decide +kernel
      have hl : raw22823step1Labels = labelEmbedding1 ∘ raw22823step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22823step1 raw22823step1Labels raw22823step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1401 node1401Labels := by rfl

def raw22824 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22824Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22824step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22824step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22824step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22824step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22824 raw22824Labels = mixedMoment B node1208 node1208Labels := by
  calc
    mixedMoment B raw22824 raw22824Labels = mixedMoment B raw22824step0 raw22824step0Labels := by
      have ha : raw22824step0 = (fun i j => raw22824 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22824step0 raw22824; decide +kernel
      have hl : raw22824step0Labels = raw22824Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22824 raw22824Labels permutation176 permutation7
    mixedMoment B raw22824step0 raw22824step0Labels = mixedMoment B raw22824step1 raw22824step1Labels := by
      have ha : raw22824step1 = raw22824step0 := by apply Matrix.ext; unfold raw22824step1 raw22824step0; decide +kernel
      have hl : raw22824step0Labels = labelEmbedding1 ∘ raw22824step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22824step0 raw22824step0Labels raw22824step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1208 node1208Labels := by rfl

def raw22825 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22825Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22825step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22825step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22825step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22825step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22825 raw22825Labels = mixedMoment B node1226 node1226Labels := by
  calc
    mixedMoment B raw22825 raw22825Labels = mixedMoment B raw22825step0 raw22825step0Labels := by
      have hz : ∀ j, raw22825 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22825step0 = (fun i j => raw22825 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22825step0 raw22825; decide +kernel
      have hl : raw22825step0Labels = raw22825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22825 raw22825Labels permutation265 hz
    mixedMoment B raw22825step0 raw22825step0Labels = mixedMoment B raw22825step1 raw22825step1Labels := by
      have ha : raw22825step1 = (fun i j => raw22825step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22825step1 raw22825step0; decide +kernel
      have hl : raw22825step1Labels = raw22825step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22825step0 raw22825step0Labels permutation32 permutation7
    mixedMoment B raw22825step1 raw22825step1Labels = mixedMoment B raw22825step2 raw22825step2Labels := by
      have ha : raw22825step2 = raw22825step1 := by apply Matrix.ext; unfold raw22825step2 raw22825step1; decide +kernel
      have hl : raw22825step1Labels = labelEmbedding1 ∘ raw22825step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22825step1 raw22825step1Labels raw22825step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1226 node1226Labels := by rfl

def raw22826 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22826Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22826step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22826step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22826step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22826step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22826step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22826 raw22826Labels = mixedMoment B node1220 node1220Labels := by
  calc
    mixedMoment B raw22826 raw22826Labels = mixedMoment B raw22826step0 raw22826step0Labels := by
      have hz : ∀ j, raw22826 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22826step0 = (fun i j => raw22826 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22826step0 raw22826; decide +kernel
      have hl : raw22826step0Labels = raw22826Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22826 raw22826Labels permutation265 hz
    mixedMoment B raw22826step0 raw22826step0Labels = mixedMoment B raw22826step1 raw22826step1Labels := by
      have ha : raw22826step1 = (fun i j => raw22826step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22826step1 raw22826step0; decide +kernel
      have hl : raw22826step1Labels = raw22826step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22826step0 raw22826step0Labels permutation32 permutation7
    mixedMoment B raw22826step1 raw22826step1Labels = mixedMoment B raw22826step2 raw22826step2Labels := by
      have ha : raw22826step2 = raw22826step1 := by apply Matrix.ext; unfold raw22826step2 raw22826step1; decide +kernel
      have hl : raw22826step1Labels = labelEmbedding1 ∘ raw22826step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22826step1 raw22826step1Labels raw22826step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1220 node1220Labels := by rfl

def raw22827 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22827Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22827step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22827step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22827step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22827step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22827step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22827 raw22827Labels = mixedMoment B node1219 node1219Labels := by
  calc
    mixedMoment B raw22827 raw22827Labels = mixedMoment B raw22827step0 raw22827step0Labels := by
      have hz : ∀ j, raw22827 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22827step0 = (fun i j => raw22827 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22827step0 raw22827; decide +kernel
      have hl : raw22827step0Labels = raw22827Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22827 raw22827Labels permutation265 hz
    mixedMoment B raw22827step0 raw22827step0Labels = mixedMoment B raw22827step1 raw22827step1Labels := by
      have ha : raw22827step1 = (fun i j => raw22827step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22827step1 raw22827step0; decide +kernel
      have hl : raw22827step1Labels = raw22827step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22827step0 raw22827step0Labels permutation32 permutation7
    mixedMoment B raw22827step1 raw22827step1Labels = mixedMoment B raw22827step2 raw22827step2Labels := by
      have ha : raw22827step2 = raw22827step1 := by apply Matrix.ext; unfold raw22827step2 raw22827step1; decide +kernel
      have hl : raw22827step1Labels = labelEmbedding1 ∘ raw22827step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22827step1 raw22827step1Labels raw22827step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1219 node1219Labels := by rfl

def raw22828 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22828Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22828step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22828step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22828step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22828step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![0, -2, 2], ![-1, -1, 2]]
def raw22828step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22828step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -2, 0], ![2, -1, -1]]
def raw22828step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22828step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -2, 0], ![2, -1, -1]]
def raw22828step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22828 raw22828Labels = mixedMoment B node1455 node1455Labels := by
  calc
    mixedMoment B raw22828 raw22828Labels = mixedMoment B raw22828step0 raw22828step0Labels := by
      have hz : ∀ j, raw22828 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22828step0 = (fun i j => raw22828 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22828step0 raw22828; decide +kernel
      have hl : raw22828step0Labels = raw22828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22828 raw22828Labels permutation434 hz
    mixedMoment B raw22828step0 raw22828step0Labels = mixedMoment B raw22828step1 raw22828step1Labels := by
      have hz : ∀ j, raw22828step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22828step1 = (fun i j => raw22828step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22828step1 raw22828step0; decide +kernel
      have hl : raw22828step1Labels = raw22828step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22828step0 raw22828step0Labels permutation80 hz
    mixedMoment B raw22828step1 raw22828step1Labels = mixedMoment B raw22828step2 raw22828step2Labels := by
      have hz : ∀ j, raw22828step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22828step2 = (fun i j => raw22828step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22828step2 raw22828step1; decide +kernel
      have hl : raw22828step2Labels = raw22828step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22828step1 raw22828step1Labels permutation14 hz
    mixedMoment B raw22828step2 raw22828step2Labels = mixedMoment B raw22828step3 raw22828step3Labels := by
      have ha : raw22828step3 = (fun i j => raw22828step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22828step3 raw22828step2; decide +kernel
      have hl : raw22828step3Labels = raw22828step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22828step2 raw22828step2Labels permutation2 permutation7
    mixedMoment B raw22828step3 raw22828step3Labels = mixedMoment B raw22828step4 raw22828step4Labels := by
      have ha : raw22828step4 = raw22828step3 := by apply Matrix.ext; unfold raw22828step4 raw22828step3; decide +kernel
      have hl : raw22828step3Labels = labelEmbedding1 ∘ raw22828step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22828step3 raw22828step3Labels raw22828step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1455 node1455Labels := by rfl

def raw22829 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22829Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22829step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22829step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22829step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22829step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22829step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22829step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22829step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22829 raw22829Labels = mixedMoment B node1274 node1274Labels := by
  calc
    mixedMoment B raw22829 raw22829Labels = mixedMoment B raw22829step0 raw22829step0Labels := by
      have hz : ∀ j, raw22829 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22829step0 = (fun i j => raw22829 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22829step0 raw22829; decide +kernel
      have hl : raw22829step0Labels = raw22829Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22829 raw22829Labels permutation434 hz
    mixedMoment B raw22829step0 raw22829step0Labels = mixedMoment B raw22829step1 raw22829step1Labels := by
      have hz : ∀ j, raw22829step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22829step1 = (fun i j => raw22829step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22829step1 raw22829step0; decide +kernel
      have hl : raw22829step1Labels = raw22829step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22829step0 raw22829step0Labels permutation80 hz
    mixedMoment B raw22829step1 raw22829step1Labels = mixedMoment B raw22829step2 raw22829step2Labels := by
      have ha : raw22829step2 = (fun i j => raw22829step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22829step2 raw22829step1; decide +kernel
      have hl : raw22829step2Labels = raw22829step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22829step1 raw22829step1Labels permutation8 permutation7
    mixedMoment B raw22829step2 raw22829step2Labels = mixedMoment B raw22829step3 raw22829step3Labels := by
      have ha : raw22829step3 = raw22829step2 := by apply Matrix.ext; unfold raw22829step3 raw22829step2; decide +kernel
      have hl : raw22829step2Labels = labelEmbedding1 ∘ raw22829step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22829step2 raw22829step2Labels raw22829step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1274 node1274Labels := by rfl

def raw22830 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22830Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22830step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22830step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw22830step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22830step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22830step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22830step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22830step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22830 raw22830Labels = mixedMoment B node1274 node1274Labels := by
  calc
    mixedMoment B raw22830 raw22830Labels = mixedMoment B raw22830step0 raw22830step0Labels := by
      have hz : ∀ j, raw22830 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22830step0 = (fun i j => raw22830 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22830step0 raw22830; decide +kernel
      have hl : raw22830step0Labels = raw22830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22830 raw22830Labels permutation434 hz
    mixedMoment B raw22830step0 raw22830step0Labels = mixedMoment B raw22830step1 raw22830step1Labels := by
      have hz : ∀ j, raw22830step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22830step1 = (fun i j => raw22830step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22830step1 raw22830step0; decide +kernel
      have hl : raw22830step1Labels = raw22830step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22830step0 raw22830step0Labels permutation56 hz
    mixedMoment B raw22830step1 raw22830step1Labels = mixedMoment B raw22830step2 raw22830step2Labels := by
      have ha : raw22830step2 = (fun i j => raw22830step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22830step2 raw22830step1; decide +kernel
      have hl : raw22830step2Labels = raw22830step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22830step1 raw22830step1Labels permutation8 permutation7
    mixedMoment B raw22830step2 raw22830step2Labels = mixedMoment B raw22830step3 raw22830step3Labels := by
      have ha : raw22830step3 = raw22830step2 := by apply Matrix.ext; unfold raw22830step3 raw22830step2; decide +kernel
      have hl : raw22830step2Labels = labelEmbedding1 ∘ raw22830step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22830step2 raw22830step2Labels raw22830step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1274 node1274Labels := by rfl

def raw22831 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22831Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22831step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22831step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22831step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22831step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, -1, 2], ![-1, -1, 2]]
def raw22831step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22831step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw22831step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22831step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw22831step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22831 raw22831Labels = mixedMoment B node1312 node1312Labels := by
  calc
    mixedMoment B raw22831 raw22831Labels = mixedMoment B raw22831step0 raw22831step0Labels := by
      have hz : ∀ j, raw22831 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22831step0 = (fun i j => raw22831 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22831step0 raw22831; decide +kernel
      have hl : raw22831step0Labels = raw22831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22831 raw22831Labels permutation434 hz
    mixedMoment B raw22831step0 raw22831step0Labels = mixedMoment B raw22831step1 raw22831step1Labels := by
      have hz : ∀ j, raw22831step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22831step1 = (fun i j => raw22831step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22831step1 raw22831step0; decide +kernel
      have hl : raw22831step1Labels = raw22831step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22831step0 raw22831step0Labels permutation80 hz
    mixedMoment B raw22831step1 raw22831step1Labels = mixedMoment B raw22831step2 raw22831step2Labels := by
      have hz : ∀ j, raw22831step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22831step2 = (fun i j => raw22831step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22831step2 raw22831step1; decide +kernel
      have hl : raw22831step2Labels = raw22831step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22831step1 raw22831step1Labels permutation14 hz
    mixedMoment B raw22831step2 raw22831step2Labels = mixedMoment B raw22831step3 raw22831step3Labels := by
      have ha : raw22831step3 = (fun i j => raw22831step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22831step3 raw22831step2; decide +kernel
      have hl : raw22831step3Labels = raw22831step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22831step2 raw22831step2Labels permutation2 permutation7
    mixedMoment B raw22831step3 raw22831step3Labels = mixedMoment B raw22831step4 raw22831step4Labels := by
      have ha : raw22831step4 = raw22831step3 := by apply Matrix.ext; unfold raw22831step4 raw22831step3; decide +kernel
      have hl : raw22831step3Labels = labelEmbedding1 ∘ raw22831step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22831step3 raw22831step3Labels raw22831step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1312 node1312Labels := by rfl

def raw22832 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22832Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22832step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22832step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw22832step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22832step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![0, -2, 2], ![-2, 0, 2]]
def raw22832step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22832step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw22832step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22832step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw22832step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22832 raw22832Labels = mixedMoment B node1311 node1311Labels := by
  calc
    mixedMoment B raw22832 raw22832Labels = mixedMoment B raw22832step0 raw22832step0Labels := by
      have hz : ∀ j, raw22832 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22832step0 = (fun i j => raw22832 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22832step0 raw22832; decide +kernel
      have hl : raw22832step0Labels = raw22832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22832 raw22832Labels permutation434 hz
    mixedMoment B raw22832step0 raw22832step0Labels = mixedMoment B raw22832step1 raw22832step1Labels := by
      have hz : ∀ j, raw22832step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22832step1 = (fun i j => raw22832step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22832step1 raw22832step0; decide +kernel
      have hl : raw22832step1Labels = raw22832step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22832step0 raw22832step0Labels permutation80 hz
    mixedMoment B raw22832step1 raw22832step1Labels = mixedMoment B raw22832step2 raw22832step2Labels := by
      have hz : ∀ j, raw22832step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22832step2 = (fun i j => raw22832step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22832step2 raw22832step1; decide +kernel
      have hl : raw22832step2Labels = raw22832step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22832step1 raw22832step1Labels permutation14 hz
    mixedMoment B raw22832step2 raw22832step2Labels = mixedMoment B raw22832step3 raw22832step3Labels := by
      have ha : raw22832step3 = (fun i j => raw22832step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22832step3 raw22832step2; decide +kernel
      have hl : raw22832step3Labels = raw22832step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22832step2 raw22832step2Labels permutation2 permutation7
    mixedMoment B raw22832step3 raw22832step3Labels = mixedMoment B raw22832step4 raw22832step4Labels := by
      have ha : raw22832step4 = raw22832step3 := by apply Matrix.ext; unfold raw22832step4 raw22832step3; decide +kernel
      have hl : raw22832step3Labels = labelEmbedding1 ∘ raw22832step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22832step3 raw22832step3Labels raw22832step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1311 node1311Labels := by rfl

def raw22833 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22833Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22833step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22833step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22833step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22833step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw22833step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22833step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw22833step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22833 raw22833Labels = mixedMoment B node1430 node1430Labels := by
  calc
    mixedMoment B raw22833 raw22833Labels = mixedMoment B raw22833step0 raw22833step0Labels := by
      have hz : ∀ j, raw22833 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22833step0 = (fun i j => raw22833 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22833step0 raw22833; decide +kernel
      have hl : raw22833step0Labels = raw22833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22833 raw22833Labels permutation346 hz
    mixedMoment B raw22833step0 raw22833step0Labels = mixedMoment B raw22833step1 raw22833step1Labels := by
      have hz : ∀ j, raw22833step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22833step1 = (fun i j => raw22833step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22833step1 raw22833step0; decide +kernel
      have hl : raw22833step1Labels = raw22833step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22833step0 raw22833step0Labels permutation56 hz
    mixedMoment B raw22833step1 raw22833step1Labels = mixedMoment B raw22833step2 raw22833step2Labels := by
      have ha : raw22833step2 = (fun i j => raw22833step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22833step2 raw22833step1; decide +kernel
      have hl : raw22833step2Labels = raw22833step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22833step1 raw22833step1Labels permutation8 permutation7
    mixedMoment B raw22833step2 raw22833step2Labels = mixedMoment B raw22833step3 raw22833step3Labels := by
      have ha : raw22833step3 = raw22833step2 := by apply Matrix.ext; unfold raw22833step3 raw22833step2; decide +kernel
      have hl : raw22833step2Labels = labelEmbedding1 ∘ raw22833step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22833step2 raw22833step2Labels raw22833step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1430 node1430Labels := by rfl

def raw22834 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22834Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22834step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22834step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw22834step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22834step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw22834step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22834 raw22834Labels = mixedMoment B node1253 node1253Labels := by
  calc
    mixedMoment B raw22834 raw22834Labels = mixedMoment B raw22834step0 raw22834step0Labels := by
      have hz : ∀ j, raw22834 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22834step0 = (fun i j => raw22834 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22834step0 raw22834; decide +kernel
      have hl : raw22834step0Labels = raw22834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22834 raw22834Labels permutation346 hz
    mixedMoment B raw22834step0 raw22834step0Labels = mixedMoment B raw22834step1 raw22834step1Labels := by
      have ha : raw22834step1 = (fun i j => raw22834step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22834step1 raw22834step0; decide +kernel
      have hl : raw22834step1Labels = raw22834step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22834step0 raw22834step0Labels permutation32 permutation7
    mixedMoment B raw22834step1 raw22834step1Labels = mixedMoment B raw22834step2 raw22834step2Labels := by
      have ha : raw22834step2 = raw22834step1 := by apply Matrix.ext; unfold raw22834step2 raw22834step1; decide +kernel
      have hl : raw22834step1Labels = labelEmbedding1 ∘ raw22834step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22834step1 raw22834step1Labels raw22834step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1253 node1253Labels := by rfl

def raw22835 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22835Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22835step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw22835step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22835step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw22835step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22835 raw22835Labels = mixedMoment B node1253 node1253Labels := by
  calc
    mixedMoment B raw22835 raw22835Labels = mixedMoment B raw22835step0 raw22835step0Labels := by
      have hz : ∀ j, raw22835 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22835step0 = (fun i j => raw22835 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22835step0 raw22835; decide +kernel
      have hl : raw22835step0Labels = raw22835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22835 raw22835Labels permutation265 hz
    mixedMoment B raw22835step0 raw22835step0Labels = mixedMoment B raw22835step1 raw22835step1Labels := by
      have ha : raw22835step1 = (fun i j => raw22835step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22835step1 raw22835step0; decide +kernel
      have hl : raw22835step1Labels = raw22835step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22835step0 raw22835step0Labels permutation32 permutation7
    mixedMoment B raw22835step1 raw22835step1Labels = mixedMoment B raw22835step2 raw22835step2Labels := by
      have ha : raw22835step2 = raw22835step1 := by apply Matrix.ext; unfold raw22835step2 raw22835step1; decide +kernel
      have hl : raw22835step1Labels = labelEmbedding1 ∘ raw22835step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22835step1 raw22835step1Labels raw22835step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1253 node1253Labels := by rfl

def raw22836 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22836Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 2, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22836step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22836step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw22836step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22836step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw22836step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22836step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw22836step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22836 raw22836Labels = mixedMoment B node1283 node1283Labels := by
  calc
    mixedMoment B raw22836 raw22836Labels = mixedMoment B raw22836step0 raw22836step0Labels := by
      have hz : ∀ j, raw22836 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22836step0 = (fun i j => raw22836 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22836step0 raw22836; decide +kernel
      have hl : raw22836step0Labels = raw22836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22836 raw22836Labels permutation346 hz
    mixedMoment B raw22836step0 raw22836step0Labels = mixedMoment B raw22836step1 raw22836step1Labels := by
      have hz : ∀ j, raw22836step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22836step1 = (fun i j => raw22836step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22836step1 raw22836step0; decide +kernel
      have hl : raw22836step1Labels = raw22836step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22836step0 raw22836step0Labels permutation56 hz
    mixedMoment B raw22836step1 raw22836step1Labels = mixedMoment B raw22836step2 raw22836step2Labels := by
      have ha : raw22836step2 = (fun i j => raw22836step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22836step2 raw22836step1; decide +kernel
      have hl : raw22836step2Labels = raw22836step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22836step1 raw22836step1Labels permutation8 permutation7
    mixedMoment B raw22836step2 raw22836step2Labels = mixedMoment B raw22836step3 raw22836step3Labels := by
      have ha : raw22836step3 = raw22836step2 := by apply Matrix.ext; unfold raw22836step3 raw22836step2; decide +kernel
      have hl : raw22836step2Labels = labelEmbedding1 ∘ raw22836step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22836step2 raw22836step2Labels raw22836step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1283 node1283Labels := by rfl

def raw22837 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw22837Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw22837step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22837step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw22837step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22837step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw22837step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22837step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw22837step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22837 raw22837Labels = mixedMoment B node1273 node1273Labels := by
  calc
    mixedMoment B raw22837 raw22837Labels = mixedMoment B raw22837step0 raw22837step0Labels := by
      have hz : ∀ j, raw22837 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22837step0 = (fun i j => raw22837 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22837step0 raw22837; decide +kernel
      have hl : raw22837step0Labels = raw22837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22837 raw22837Labels permutation346 hz
    mixedMoment B raw22837step0 raw22837step0Labels = mixedMoment B raw22837step1 raw22837step1Labels := by
      have hz : ∀ j, raw22837step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22837step1 = (fun i j => raw22837step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22837step1 raw22837step0; decide +kernel
      have hl : raw22837step1Labels = raw22837step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22837step0 raw22837step0Labels permutation56 hz
    mixedMoment B raw22837step1 raw22837step1Labels = mixedMoment B raw22837step2 raw22837step2Labels := by
      have ha : raw22837step2 = (fun i j => raw22837step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22837step2 raw22837step1; decide +kernel
      have hl : raw22837step2Labels = raw22837step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22837step1 raw22837step1Labels permutation8 permutation7
    mixedMoment B raw22837step2 raw22837step2Labels = mixedMoment B raw22837step3 raw22837step3Labels := by
      have ha : raw22837step3 = raw22837step2 := by apply Matrix.ext; unfold raw22837step3 raw22837step2; decide +kernel
      have hl : raw22837step2Labels = labelEmbedding1 ∘ raw22837step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22837step2 raw22837step2Labels raw22837step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1273 node1273Labels := by rfl

def raw22838 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22838Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22838step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22838step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22838step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22838step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw22838step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22838step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw22838step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22838 raw22838Labels = mixedMoment B node1431 node1431Labels := by
  calc
    mixedMoment B raw22838 raw22838Labels = mixedMoment B raw22838step0 raw22838step0Labels := by
      have hz : ∀ j, raw22838 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22838step0 = (fun i j => raw22838 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22838step0 raw22838; decide +kernel
      have hl : raw22838step0Labels = raw22838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22838 raw22838Labels permutation346 hz
    mixedMoment B raw22838step0 raw22838step0Labels = mixedMoment B raw22838step1 raw22838step1Labels := by
      have hz : ∀ j, raw22838step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22838step1 = (fun i j => raw22838step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22838step1 raw22838step0; decide +kernel
      have hl : raw22838step1Labels = raw22838step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22838step0 raw22838step0Labels permutation56 hz
    mixedMoment B raw22838step1 raw22838step1Labels = mixedMoment B raw22838step2 raw22838step2Labels := by
      have ha : raw22838step2 = (fun i j => raw22838step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22838step2 raw22838step1; decide +kernel
      have hl : raw22838step2Labels = raw22838step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22838step1 raw22838step1Labels permutation8 permutation7
    mixedMoment B raw22838step2 raw22838step2Labels = mixedMoment B raw22838step3 raw22838step3Labels := by
      have ha : raw22838step3 = raw22838step2 := by apply Matrix.ext; unfold raw22838step3 raw22838step2; decide +kernel
      have hl : raw22838step2Labels = labelEmbedding1 ∘ raw22838step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22838step2 raw22838step2Labels raw22838step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1431 node1431Labels := by rfl

def raw22839 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22839Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22839step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22839step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw22839step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22839step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw22839step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22839 raw22839Labels = mixedMoment B node1254 node1254Labels := by
  calc
    mixedMoment B raw22839 raw22839Labels = mixedMoment B raw22839step0 raw22839step0Labels := by
      have hz : ∀ j, raw22839 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22839step0 = (fun i j => raw22839 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22839step0 raw22839; decide +kernel
      have hl : raw22839step0Labels = raw22839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22839 raw22839Labels permutation346 hz
    mixedMoment B raw22839step0 raw22839step0Labels = mixedMoment B raw22839step1 raw22839step1Labels := by
      have ha : raw22839step1 = (fun i j => raw22839step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22839step1 raw22839step0; decide +kernel
      have hl : raw22839step1Labels = raw22839step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22839step0 raw22839step0Labels permutation32 permutation7
    mixedMoment B raw22839step1 raw22839step1Labels = mixedMoment B raw22839step2 raw22839step2Labels := by
      have ha : raw22839step2 = raw22839step1 := by apply Matrix.ext; unfold raw22839step2 raw22839step1; decide +kernel
      have hl : raw22839step1Labels = labelEmbedding1 ∘ raw22839step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22839step1 raw22839step1Labels raw22839step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1254 node1254Labels := by rfl

def raw22840 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22840Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22840step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw22840step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22840step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw22840step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22840 raw22840Labels = mixedMoment B node1254 node1254Labels := by
  calc
    mixedMoment B raw22840 raw22840Labels = mixedMoment B raw22840step0 raw22840step0Labels := by
      have hz : ∀ j, raw22840 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22840step0 = (fun i j => raw22840 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22840step0 raw22840; decide +kernel
      have hl : raw22840step0Labels = raw22840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22840 raw22840Labels permutation265 hz
    mixedMoment B raw22840step0 raw22840step0Labels = mixedMoment B raw22840step1 raw22840step1Labels := by
      have ha : raw22840step1 = (fun i j => raw22840step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22840step1 raw22840step0; decide +kernel
      have hl : raw22840step1Labels = raw22840step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22840step0 raw22840step0Labels permutation32 permutation7
    mixedMoment B raw22840step1 raw22840step1Labels = mixedMoment B raw22840step2 raw22840step2Labels := by
      have ha : raw22840step2 = raw22840step1 := by apply Matrix.ext; unfold raw22840step2 raw22840step1; decide +kernel
      have hl : raw22840step1Labels = labelEmbedding1 ∘ raw22840step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22840step1 raw22840step1Labels raw22840step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1254 node1254Labels := by rfl

def raw22841 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22841Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22841step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22841step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22841step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22841step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw22841step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22841step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw22841step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22841 raw22841Labels = mixedMoment B node1284 node1284Labels := by
  calc
    mixedMoment B raw22841 raw22841Labels = mixedMoment B raw22841step0 raw22841step0Labels := by
      have hz : ∀ j, raw22841 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22841step0 = (fun i j => raw22841 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22841step0 raw22841; decide +kernel
      have hl : raw22841step0Labels = raw22841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22841 raw22841Labels permutation346 hz
    mixedMoment B raw22841step0 raw22841step0Labels = mixedMoment B raw22841step1 raw22841step1Labels := by
      have hz : ∀ j, raw22841step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22841step1 = (fun i j => raw22841step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22841step1 raw22841step0; decide +kernel
      have hl : raw22841step1Labels = raw22841step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22841step0 raw22841step0Labels permutation56 hz
    mixedMoment B raw22841step1 raw22841step1Labels = mixedMoment B raw22841step2 raw22841step2Labels := by
      have ha : raw22841step2 = (fun i j => raw22841step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22841step2 raw22841step1; decide +kernel
      have hl : raw22841step2Labels = raw22841step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22841step1 raw22841step1Labels permutation8 permutation7
    mixedMoment B raw22841step2 raw22841step2Labels = mixedMoment B raw22841step3 raw22841step3Labels := by
      have ha : raw22841step3 = raw22841step2 := by apply Matrix.ext; unfold raw22841step3 raw22841step2; decide +kernel
      have hl : raw22841step2Labels = labelEmbedding1 ∘ raw22841step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22841step2 raw22841step2Labels raw22841step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1284 node1284Labels := by rfl

def raw22842 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22842Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22842step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22842step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22842step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw22842step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22842step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw22842step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22842step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22842 raw22842Labels = mixedMoment B node1274 node1274Labels := by
  calc
    mixedMoment B raw22842 raw22842Labels = mixedMoment B raw22842step0 raw22842step0Labels := by
      have hz : ∀ j, raw22842 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22842step0 = (fun i j => raw22842 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22842step0 raw22842; decide +kernel
      have hl : raw22842step0Labels = raw22842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22842 raw22842Labels permutation346 hz
    mixedMoment B raw22842step0 raw22842step0Labels = mixedMoment B raw22842step1 raw22842step1Labels := by
      have hz : ∀ j, raw22842step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22842step1 = (fun i j => raw22842step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22842step1 raw22842step0; decide +kernel
      have hl : raw22842step1Labels = raw22842step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22842step0 raw22842step0Labels permutation56 hz
    mixedMoment B raw22842step1 raw22842step1Labels = mixedMoment B raw22842step2 raw22842step2Labels := by
      have ha : raw22842step2 = (fun i j => raw22842step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22842step2 raw22842step1; decide +kernel
      have hl : raw22842step2Labels = raw22842step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22842step1 raw22842step1Labels permutation9 permutation7
    mixedMoment B raw22842step2 raw22842step2Labels = mixedMoment B raw22842step3 raw22842step3Labels := by
      have ha : raw22842step3 = raw22842step2 := by apply Matrix.ext; unfold raw22842step3 raw22842step2; decide +kernel
      have hl : raw22842step2Labels = labelEmbedding1 ∘ raw22842step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22842step2 raw22842step2Labels raw22842step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1274 node1274Labels := by rfl

def raw22843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw22843Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw22843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22843step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw22843step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22843step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw22843step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22843 raw22843Labels = mixedMoment B node1192 node1192Labels := by
  calc
    mixedMoment B raw22843 raw22843Labels = mixedMoment B raw22843step0 raw22843step0Labels := by
      have hz : ∀ j, raw22843 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22843step0 = (fun i j => raw22843 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22843step0 raw22843; decide +kernel
      have hl : raw22843step0Labels = raw22843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22843 raw22843Labels permutation346 hz
    mixedMoment B raw22843step0 raw22843step0Labels = mixedMoment B raw22843step1 raw22843step1Labels := by
      have hz : ∀ j, raw22843step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22843step1 = (fun i j => raw22843step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22843step1 raw22843step0; decide +kernel
      have hl : raw22843step1Labels = raw22843step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22843step0 raw22843step0Labels permutation56 hz
    mixedMoment B raw22843step1 raw22843step1Labels = mixedMoment B raw22843step2 raw22843step2Labels := by
      have ha : raw22843step2 = (fun i j => raw22843step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22843step2 raw22843step1; decide +kernel
      have hl : raw22843step2Labels = raw22843step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22843step1 raw22843step1Labels permutation9 permutation2
    _ = mixedMoment B node1192 node1192Labels := by rfl

def raw22844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw22844Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw22844step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw22844step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22844 raw22844Labels = mixedMoment B node2538 node2538Labels := by
  calc
    mixedMoment B raw22844 raw22844Labels = mixedMoment B raw22844step0 raw22844step0Labels := by
      have hz : ∀ j, raw22844 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22844step0 = (fun i j => raw22844 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22844step0 raw22844; decide +kernel
      have hl : raw22844step0Labels = raw22844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22844 raw22844Labels permutation346 hz
    mixedMoment B raw22844step0 raw22844step0Labels = mixedMoment B raw22844step1 raw22844step1Labels := by
      have ha : raw22844step1 = (fun i j => raw22844step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22844step1 raw22844step0; decide +kernel
      have hl : raw22844step1Labels = raw22844step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22844step0 raw22844step0Labels permutation33 permutation2
    _ = mixedMoment B node2538 node2538Labels := by rfl

def raw22845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw22845Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 1, -3], ![2, -1, -1]]
def raw22845step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw22845step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22845 raw22845Labels = mixedMoment B node2538 node2538Labels := by
  calc
    mixedMoment B raw22845 raw22845Labels = mixedMoment B raw22845step0 raw22845step0Labels := by
      have hz : ∀ j, raw22845 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22845step0 = (fun i j => raw22845 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22845step0 raw22845; decide +kernel
      have hl : raw22845step0Labels = raw22845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22845 raw22845Labels permutation265 hz
    mixedMoment B raw22845step0 raw22845step0Labels = mixedMoment B raw22845step1 raw22845step1Labels := by
      have ha : raw22845step1 = (fun i j => raw22845step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22845step1 raw22845step0; decide +kernel
      have hl : raw22845step1Labels = raw22845step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22845step0 raw22845step0Labels permutation33 permutation2
    _ = mixedMoment B node2538 node2538Labels := by rfl

def raw22846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![2, 1, -3], ![2, -1, -1]]
def raw22846Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, -1, 2], ![2, 1, -3], ![2, -1, -1]]
def raw22846step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22846step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, 1, -3], ![2, -1, -1]]
def raw22846step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22846step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw22846step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22846 raw22846Labels = mixedMoment B node2410 node2410Labels := by
  calc
    mixedMoment B raw22846 raw22846Labels = mixedMoment B raw22846step0 raw22846step0Labels := by
      have hz : ∀ j, raw22846 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22846step0 = (fun i j => raw22846 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22846step0 raw22846; decide +kernel
      have hl : raw22846step0Labels = raw22846Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22846 raw22846Labels permutation346 hz
    mixedMoment B raw22846step0 raw22846step0Labels = mixedMoment B raw22846step1 raw22846step1Labels := by
      have hz : ∀ j, raw22846step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22846step1 = (fun i j => raw22846step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22846step1 raw22846step0; decide +kernel
      have hl : raw22846step1Labels = raw22846step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22846step0 raw22846step0Labels permutation56 hz
    mixedMoment B raw22846step1 raw22846step1Labels = mixedMoment B raw22846step2 raw22846step2Labels := by
      have ha : raw22846step2 = (fun i j => raw22846step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22846step2 raw22846step1; decide +kernel
      have hl : raw22846step2Labels = raw22846step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22846step1 raw22846step1Labels permutation9 permutation2
    _ = mixedMoment B node2410 node2410Labels := by rfl

def raw22847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw22847Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw22847step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22847step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw22847step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22847 raw22847Labels = mixedMoment B node2687 node2687Labels := by
  calc
    mixedMoment B raw22847 raw22847Labels = mixedMoment B raw22847step0 raw22847step0Labels := by
      have hz : ∀ j, raw22847 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22847step0 = (fun i j => raw22847 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22847step0 raw22847; decide +kernel
      have hl : raw22847step0Labels = raw22847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22847 raw22847Labels permutation346 hz
    mixedMoment B raw22847step0 raw22847step0Labels = mixedMoment B raw22847step1 raw22847step1Labels := by
      have hz : ∀ j, raw22847step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22847step1 = (fun i j => raw22847step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22847step1 raw22847step0; decide +kernel
      have hl : raw22847step1Labels = raw22847step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22847step0 raw22847step0Labels permutation56 hz
    _ = mixedMoment B node2687 node2687Labels := by rfl

def raw22848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3], ![1, 0, -1]]
def raw22848Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3], ![1, 0, -1]]
def raw22848step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22848step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![2, 1, -3], ![1, 0, -1]]
def raw22848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22848step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw22848step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22848 raw22848Labels = mixedMoment B node2685 node2685Labels := by
  calc
    mixedMoment B raw22848 raw22848Labels = mixedMoment B raw22848step0 raw22848step0Labels := by
      have hz : ∀ j, raw22848 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22848step0 = (fun i j => raw22848 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22848step0 raw22848; decide +kernel
      have hl : raw22848step0Labels = raw22848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22848 raw22848Labels permutation346 hz
    mixedMoment B raw22848step0 raw22848step0Labels = mixedMoment B raw22848step1 raw22848step1Labels := by
      have hz : ∀ j, raw22848step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22848step1 = (fun i j => raw22848step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22848step1 raw22848step0; decide +kernel
      have hl : raw22848step1Labels = raw22848step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22848step0 raw22848step0Labels permutation56 hz
    mixedMoment B raw22848step1 raw22848step1Labels = mixedMoment B raw22848step2 raw22848step2Labels := by
      have ha : raw22848step2 = (fun i j => raw22848step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22848step2 raw22848step1; decide +kernel
      have hl : raw22848step2Labels = raw22848step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22848step1 raw22848step1Labels permutation9 permutation2
    _ = mixedMoment B node2685 node2685Labels := by rfl

def raw22849 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![-2, 2], ![3, -3], ![1, -1]]
def raw22849Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22849step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-2, 2], ![3, -3], ![1, -1]]
def raw22849step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22849step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![3, -3], ![1, -1]]
def raw22849step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22849step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw22849step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22849step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw22849step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22849 raw22849Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw22849 raw22849Labels = mixedMoment B raw22849step0 raw22849step0Labels := by
      have hz : ∀ j, raw22849 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22849step0 = (fun i j => raw22849 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22849step0 raw22849; decide +kernel
      have hl : raw22849step0Labels = raw22849Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22849 raw22849Labels permutation346 hz
    mixedMoment B raw22849step0 raw22849step0Labels = mixedMoment B raw22849step1 raw22849step1Labels := by
      have hz : ∀ j, raw22849step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22849step1 = (fun i j => raw22849step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22849step1 raw22849step0; decide +kernel
      have hl : raw22849step1Labels = raw22849step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22849step0 raw22849step0Labels permutation56 hz
    mixedMoment B raw22849step1 raw22849step1Labels = mixedMoment B raw22849step2 raw22849step2Labels := by
      have ha : raw22849step2 = (fun i j => raw22849step1 (permutation24 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22849step2 raw22849step1; decide +kernel
      have hl : raw22849step2Labels = raw22849step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22849step1 raw22849step1Labels permutation24 permutation0
    mixedMoment B raw22849step2 raw22849step2Labels = mixedMoment B raw22849step3 raw22849step3Labels := by
      have ha : raw22849step3 = -raw22849step2 := by apply Matrix.ext; change ∀ i j, raw22849step3 i j = -(raw22849step2 i j); unfold raw22849step3 raw22849step2; decide +kernel
      have hl : raw22849step3Labels = raw22849step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw22850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22850Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22850step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22850 raw22850Labels = mixedMoment B node2539 node2539Labels := by
  calc
    mixedMoment B raw22850 raw22850Labels = mixedMoment B raw22850step0 raw22850step0Labels := by
      have hz : ∀ j, raw22850 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22850step0 = (fun i j => raw22850 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22850step0 raw22850; decide +kernel
      have hl : raw22850step0Labels = raw22850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22850 raw22850Labels permutation346 hz
    _ = mixedMoment B node2539 node2539Labels := by rfl

def raw22851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22851Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22851step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22851 raw22851Labels = mixedMoment B node2539 node2539Labels := by
  calc
    mixedMoment B raw22851 raw22851Labels = mixedMoment B raw22851step0 raw22851step0Labels := by
      have hz : ∀ j, raw22851 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22851step0 = (fun i j => raw22851 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22851step0 raw22851; decide +kernel
      have hl : raw22851step0Labels = raw22851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22851 raw22851Labels permutation265 hz
    _ = mixedMoment B node2539 node2539Labels := by rfl

def raw22852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22852Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22852step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22852step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22852step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22852 raw22852Labels = mixedMoment B node2411 node2411Labels := by
  calc
    mixedMoment B raw22852 raw22852Labels = mixedMoment B raw22852step0 raw22852step0Labels := by
      have hz : ∀ j, raw22852 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22852step0 = (fun i j => raw22852 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22852step0 raw22852; decide +kernel
      have hl : raw22852step0Labels = raw22852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22852 raw22852Labels permutation346 hz
    mixedMoment B raw22852step0 raw22852step0Labels = mixedMoment B raw22852step1 raw22852step1Labels := by
      have hz : ∀ j, raw22852step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22852step1 = (fun i j => raw22852step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22852step1 raw22852step0; decide +kernel
      have hl : raw22852step1Labels = raw22852step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22852step0 raw22852step0Labels permutation56 hz
    _ = mixedMoment B node2411 node2411Labels := by rfl

def raw22853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]
def raw22853Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]
def raw22853step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22853step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]
def raw22853step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22853step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw22853step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22853 raw22853Labels = mixedMoment B node2686 node2686Labels := by
  calc
    mixedMoment B raw22853 raw22853Labels = mixedMoment B raw22853step0 raw22853step0Labels := by
      have hz : ∀ j, raw22853 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22853step0 = (fun i j => raw22853 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22853step0 raw22853; decide +kernel
      have hl : raw22853step0Labels = raw22853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22853 raw22853Labels permutation346 hz
    mixedMoment B raw22853step0 raw22853step0Labels = mixedMoment B raw22853step1 raw22853step1Labels := by
      have hz : ∀ j, raw22853step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22853step1 = (fun i j => raw22853step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22853step1 raw22853step0; decide +kernel
      have hl : raw22853step1Labels = raw22853step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22853step0 raw22853step0Labels permutation56 hz
    mixedMoment B raw22853step1 raw22853step1Labels = mixedMoment B raw22853step2 raw22853step2Labels := by
      have ha : raw22853step2 = (fun i j => raw22853step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22853step2 raw22853step1; decide +kernel
      have hl : raw22853step2Labels = raw22853step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22853step1 raw22853step1Labels permutation9 permutation2
    _ = mixedMoment B node2686 node2686Labels := by rfl

def raw22854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22854Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22854step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22854step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw22854step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22854 raw22854Labels = mixedMoment B node1099 node1099Labels := by
  calc
    mixedMoment B raw22854 raw22854Labels = mixedMoment B raw22854step0 raw22854step0Labels := by
      have hz : ∀ j, raw22854 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22854step0 = (fun i j => raw22854 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22854step0 raw22854; decide +kernel
      have hl : raw22854step0Labels = raw22854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22854 raw22854Labels permutation346 hz
    mixedMoment B raw22854step0 raw22854step0Labels = mixedMoment B raw22854step1 raw22854step1Labels := by
      have ha : raw22854step1 = (fun i j => raw22854step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22854step1 raw22854step0; decide +kernel
      have hl : raw22854step1Labels = raw22854step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22854step0 raw22854step0Labels permutation38 permutation2
    _ = mixedMoment B node1099 node1099Labels := by rfl

def raw22855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22855Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22855step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22855step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw22855step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22855 raw22855Labels = mixedMoment B node1099 node1099Labels := by
  calc
    mixedMoment B raw22855 raw22855Labels = mixedMoment B raw22855step0 raw22855step0Labels := by
      have hz : ∀ j, raw22855 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22855step0 = (fun i j => raw22855 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22855step0 raw22855; decide +kernel
      have hl : raw22855step0Labels = raw22855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22855 raw22855Labels permutation265 hz
    mixedMoment B raw22855step0 raw22855step0Labels = mixedMoment B raw22855step1 raw22855step1Labels := by
      have ha : raw22855step1 = (fun i j => raw22855step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22855step1 raw22855step0; decide +kernel
      have hl : raw22855step1Labels = raw22855step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22855step0 raw22855step0Labels permutation38 permutation2
    _ = mixedMoment B node1099 node1099Labels := by rfl

def raw22856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![3, -1, -2], ![2, 0, -2]]
def raw22856Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, -1, 2], ![3, -1, -2], ![2, 0, -2]]
def raw22856step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22856step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![3, -1, -2], ![2, 0, -2]]
def raw22856step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22856step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw22856step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22856 raw22856Labels = mixedMoment B node1104 node1104Labels := by
  calc
    mixedMoment B raw22856 raw22856Labels = mixedMoment B raw22856step0 raw22856step0Labels := by
      have hz : ∀ j, raw22856 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22856step0 = (fun i j => raw22856 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22856step0 raw22856; decide +kernel
      have hl : raw22856step0Labels = raw22856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22856 raw22856Labels permutation346 hz
    mixedMoment B raw22856step0 raw22856step0Labels = mixedMoment B raw22856step1 raw22856step1Labels := by
      have hz : ∀ j, raw22856step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22856step1 = (fun i j => raw22856step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22856step1 raw22856step0; decide +kernel
      have hl : raw22856step1Labels = raw22856step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22856step0 raw22856step0Labels permutation56 hz
    mixedMoment B raw22856step1 raw22856step1Labels = mixedMoment B raw22856step2 raw22856step2Labels := by
      have ha : raw22856step2 = (fun i j => raw22856step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22856step2 raw22856step1; decide +kernel
      have hl : raw22856step2Labels = raw22856step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22856step1 raw22856step1Labels permutation9 permutation2
    _ = mixedMoment B node1104 node1104Labels := by rfl

def raw22857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw22857Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw22857step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22857step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw22857step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22857 raw22857Labels = mixedMoment B node1104 node1104Labels := by
  calc
    mixedMoment B raw22857 raw22857Labels = mixedMoment B raw22857step0 raw22857step0Labels := by
      have hz : ∀ j, raw22857 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22857step0 = (fun i j => raw22857 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22857step0 raw22857; decide +kernel
      have hl : raw22857step0Labels = raw22857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22857 raw22857Labels permutation346 hz
    mixedMoment B raw22857step0 raw22857step0Labels = mixedMoment B raw22857step1 raw22857step1Labels := by
      have hz : ∀ j, raw22857step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22857step1 = (fun i j => raw22857step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22857step1 raw22857step0; decide +kernel
      have hl : raw22857step1Labels = raw22857step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22857step0 raw22857step0Labels permutation56 hz
    _ = mixedMoment B node1104 node1104Labels := by rfl

def raw22858 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22858Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22858step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22858step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22858step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22858step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw22858step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22858step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![2, 0, -2], ![2, 0, -2]]
def raw22858step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22858 raw22858Labels = mixedMoment B node3248 node3248Labels := by
  calc
    mixedMoment B raw22858 raw22858Labels = mixedMoment B raw22858step0 raw22858step0Labels := by
      have hz : ∀ j, raw22858 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22858step0 = (fun i j => raw22858 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22858step0 raw22858; decide +kernel
      have hl : raw22858step0Labels = raw22858Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22858 raw22858Labels permutation346 hz
    mixedMoment B raw22858step0 raw22858step0Labels = mixedMoment B raw22858step1 raw22858step1Labels := by
      have hz : ∀ j, raw22858step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22858step1 = (fun i j => raw22858step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22858step1 raw22858step0; decide +kernel
      have hl : raw22858step1Labels = raw22858step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22858step0 raw22858step0Labels permutation56 hz
    mixedMoment B raw22858step1 raw22858step1Labels = mixedMoment B raw22858step2 raw22858step2Labels := by
      have ha : raw22858step2 = (fun i j => raw22858step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22858step2 raw22858step1; decide +kernel
      have hl : raw22858step2Labels = raw22858step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22858step1 raw22858step1Labels permutation8 permutation4
    mixedMoment B raw22858step2 raw22858step2Labels = mixedMoment B raw22858step3 raw22858step3Labels := by
      have ha : raw22858step3 = -raw22858step2 := by apply Matrix.ext; change ∀ i j, raw22858step3 i j = -(raw22858step2 i j); unfold raw22858step3 raw22858step2; decide +kernel
      have hl : raw22858step3Labels = raw22858step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3248 node3248Labels := by rfl

def raw22859 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22859Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22859step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22859step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw22859step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22859step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw22859step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22859 raw22859Labels = mixedMoment B node1544 node1544Labels := by
  calc
    mixedMoment B raw22859 raw22859Labels = mixedMoment B raw22859step0 raw22859step0Labels := by
      have hz : ∀ j, raw22859 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22859step0 = (fun i j => raw22859 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22859step0 raw22859; decide +kernel
      have hl : raw22859step0Labels = raw22859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22859 raw22859Labels permutation346 hz
    mixedMoment B raw22859step0 raw22859step0Labels = mixedMoment B raw22859step1 raw22859step1Labels := by
      have ha : raw22859step1 = (fun i j => raw22859step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22859step1 raw22859step0; decide +kernel
      have hl : raw22859step1Labels = raw22859step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22859step0 raw22859step0Labels permutation38 permutation4
    mixedMoment B raw22859step1 raw22859step1Labels = mixedMoment B raw22859step2 raw22859step2Labels := by
      have ha : raw22859step2 = -raw22859step1 := by apply Matrix.ext; change ∀ i j, raw22859step2 i j = -(raw22859step1 i j); unfold raw22859step2 raw22859step1; decide +kernel
      have hl : raw22859step2Labels = raw22859step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1544 node1544Labels := by rfl

def raw22860 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22860Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22860step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw22860step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22860step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw22860step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22860 raw22860Labels = mixedMoment B node1544 node1544Labels := by
  calc
    mixedMoment B raw22860 raw22860Labels = mixedMoment B raw22860step0 raw22860step0Labels := by
      have hz : ∀ j, raw22860 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22860step0 = (fun i j => raw22860 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22860step0 raw22860; decide +kernel
      have hl : raw22860step0Labels = raw22860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22860 raw22860Labels permutation265 hz
    mixedMoment B raw22860step0 raw22860step0Labels = mixedMoment B raw22860step1 raw22860step1Labels := by
      have ha : raw22860step1 = (fun i j => raw22860step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22860step1 raw22860step0; decide +kernel
      have hl : raw22860step1Labels = raw22860step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22860step0 raw22860step0Labels permutation38 permutation4
    mixedMoment B raw22860step1 raw22860step1Labels = mixedMoment B raw22860step2 raw22860step2Labels := by
      have ha : raw22860step2 = -raw22860step1 := by apply Matrix.ext; change ∀ i j, raw22860step2 i j = -(raw22860step1 i j); unfold raw22860step2 raw22860step1; decide +kernel
      have hl : raw22860step2Labels = raw22860step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1544 node1544Labels := by rfl

def raw22861 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22861Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22861step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22861step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22861step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22861step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw22861step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22861step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw22861step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22861 raw22861Labels = mixedMoment B node1631 node1631Labels := by
  calc
    mixedMoment B raw22861 raw22861Labels = mixedMoment B raw22861step0 raw22861step0Labels := by
      have hz : ∀ j, raw22861 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22861step0 = (fun i j => raw22861 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22861step0 raw22861; decide +kernel
      have hl : raw22861step0Labels = raw22861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22861 raw22861Labels permutation346 hz
    mixedMoment B raw22861step0 raw22861step0Labels = mixedMoment B raw22861step1 raw22861step1Labels := by
      have hz : ∀ j, raw22861step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22861step1 = (fun i j => raw22861step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22861step1 raw22861step0; decide +kernel
      have hl : raw22861step1Labels = raw22861step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22861step0 raw22861step0Labels permutation56 hz
    mixedMoment B raw22861step1 raw22861step1Labels = mixedMoment B raw22861step2 raw22861step2Labels := by
      have ha : raw22861step2 = (fun i j => raw22861step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22861step2 raw22861step1; decide +kernel
      have hl : raw22861step2Labels = raw22861step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22861step1 raw22861step1Labels permutation8 permutation4
    mixedMoment B raw22861step2 raw22861step2Labels = mixedMoment B raw22861step3 raw22861step3Labels := by
      have ha : raw22861step3 = -raw22861step2 := by apply Matrix.ext; change ∀ i j, raw22861step3 i j = -(raw22861step2 i j); unfold raw22861step3 raw22861step2; decide +kernel
      have hl : raw22861step3Labels = raw22861step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1631 node1631Labels := by rfl

def raw22862 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -3, 2], ![0, -2, 2]]
def raw22862Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 2, 0], ![1, -3, 2], ![0, -2, 2]]
def raw22862step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22862step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 2, 0], ![1, -3, 2], ![0, -2, 2]]
def raw22862step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22862step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-2, 0, 2], ![-3, 1, 2]]
def raw22862step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22862step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22862step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22862 raw22862Labels = mixedMoment B node1549 node1549Labels := by
  calc
    mixedMoment B raw22862 raw22862Labels = mixedMoment B raw22862step0 raw22862step0Labels := by
      have hz : ∀ j, raw22862 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22862step0 = (fun i j => raw22862 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22862step0 raw22862; decide +kernel
      have hl : raw22862step0Labels = raw22862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22862 raw22862Labels permutation346 hz
    mixedMoment B raw22862step0 raw22862step0Labels = mixedMoment B raw22862step1 raw22862step1Labels := by
      have hz : ∀ j, raw22862step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22862step1 = (fun i j => raw22862step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22862step1 raw22862step0; decide +kernel
      have hl : raw22862step1Labels = raw22862step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22862step0 raw22862step0Labels permutation56 hz
    mixedMoment B raw22862step1 raw22862step1Labels = mixedMoment B raw22862step2 raw22862step2Labels := by
      have ha : raw22862step2 = (fun i j => raw22862step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22862step2 raw22862step1; decide +kernel
      have hl : raw22862step2Labels = raw22862step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22862step1 raw22862step1Labels permutation9 permutation4
    mixedMoment B raw22862step2 raw22862step2Labels = mixedMoment B raw22862step3 raw22862step3Labels := by
      have ha : raw22862step3 = -raw22862step2 := by apply Matrix.ext; change ∀ i j, raw22862step3 i j = -(raw22862step2 i j); unfold raw22862step3 raw22862step2; decide +kernel
      have hl : raw22862step3Labels = raw22862step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1549 node1549Labels := by rfl

def raw22863 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![1, -3, 2]]
def raw22863Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![1, -3, 2]]
def raw22863step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22863step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 2, 0], ![0, -2, 2], ![1, -3, 2]]
def raw22863step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22863step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-2, 0, 2], ![-3, 1, 2]]
def raw22863step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22863step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22863step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22863 raw22863Labels = mixedMoment B node1549 node1549Labels := by
  calc
    mixedMoment B raw22863 raw22863Labels = mixedMoment B raw22863step0 raw22863step0Labels := by
      have hz : ∀ j, raw22863 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22863step0 = (fun i j => raw22863 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22863step0 raw22863; decide +kernel
      have hl : raw22863step0Labels = raw22863Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22863 raw22863Labels permutation346 hz
    mixedMoment B raw22863step0 raw22863step0Labels = mixedMoment B raw22863step1 raw22863step1Labels := by
      have hz : ∀ j, raw22863step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22863step1 = (fun i j => raw22863step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22863step1 raw22863step0; decide +kernel
      have hl : raw22863step1Labels = raw22863step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22863step0 raw22863step0Labels permutation56 hz
    mixedMoment B raw22863step1 raw22863step1Labels = mixedMoment B raw22863step2 raw22863step2Labels := by
      have ha : raw22863step2 = (fun i j => raw22863step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22863step2 raw22863step1; decide +kernel
      have hl : raw22863step2Labels = raw22863step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22863step1 raw22863step1Labels permutation8 permutation4
    mixedMoment B raw22863step2 raw22863step2Labels = mixedMoment B raw22863step3 raw22863step3Labels := by
      have ha : raw22863step3 = -raw22863step2 := by apply Matrix.ext; change ∀ i j, raw22863step3 i j = -(raw22863step2 i j); unfold raw22863step3 raw22863step2; decide +kernel
      have hl : raw22863step3Labels = raw22863step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1549 node1549Labels := by rfl

def raw22864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw22864Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw22864step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22864step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22864step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22864 raw22864Labels = mixedMoment B node1204 node1204Labels := by
  calc
    mixedMoment B raw22864 raw22864Labels = mixedMoment B raw22864step0 raw22864step0Labels := by
      have hz : ∀ j, raw22864 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22864step0 = (fun i j => raw22864 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22864step0 raw22864; decide +kernel
      have hl : raw22864step0Labels = raw22864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22864 raw22864Labels permutation265 hz
    mixedMoment B raw22864step0 raw22864step0Labels = mixedMoment B raw22864step1 raw22864step1Labels := by
      have ha : raw22864step1 = (fun i j => raw22864step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22864step1 raw22864step0; decide +kernel
      have hl : raw22864step1Labels = raw22864step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22864step0 raw22864step0Labels permutation33 permutation2
    _ = mixedMoment B node1204 node1204Labels := by rfl

def raw22865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw22865Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22865step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22865 raw22865Labels = mixedMoment B node2540 node2540Labels := by
  calc
    mixedMoment B raw22865 raw22865Labels = mixedMoment B raw22865step0 raw22865step0Labels := by
      have ha : raw22865step0 = (fun i j => raw22865 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22865step0 raw22865; decide +kernel
      have hl : raw22865step0Labels = raw22865Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22865 raw22865Labels permutation153 permutation2
    _ = mixedMoment B node2540 node2540Labels := by rfl

def raw22866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw22866Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw22866step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22866step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22866 raw22866Labels = mixedMoment B node2467 node2467Labels := by
  calc
    mixedMoment B raw22866 raw22866Labels = mixedMoment B raw22866step0 raw22866step0Labels := by
      have hz : ∀ j, raw22866 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22866step0 = (fun i j => raw22866 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22866step0 raw22866; decide +kernel
      have hl : raw22866step0Labels = raw22866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22866 raw22866Labels permutation265 hz
    mixedMoment B raw22866step0 raw22866step0Labels = mixedMoment B raw22866step1 raw22866step1Labels := by
      have ha : raw22866step1 = (fun i j => raw22866step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22866step1 raw22866step0; decide +kernel
      have hl : raw22866step1Labels = raw22866step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22866step0 raw22866step0Labels permutation33 permutation2
    _ = mixedMoment B node2467 node2467Labels := by rfl

def raw22867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![2, 1, -3], ![2, -1, -1]]
def raw22867Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 0, 1], ![2, 1, -3], ![2, -1, -1]]
def raw22867step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw22867step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22867 raw22867Labels = mixedMoment B node2467 node2467Labels := by
  calc
    mixedMoment B raw22867 raw22867Labels = mixedMoment B raw22867step0 raw22867step0Labels := by
      have hz : ∀ j, raw22867 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22867step0 = (fun i j => raw22867 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22867step0 raw22867; decide +kernel
      have hl : raw22867step0Labels = raw22867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22867 raw22867Labels permutation265 hz
    mixedMoment B raw22867step0 raw22867step0Labels = mixedMoment B raw22867step1 raw22867step1Labels := by
      have ha : raw22867step1 = (fun i j => raw22867step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22867step1 raw22867step0; decide +kernel
      have hl : raw22867step1Labels = raw22867step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22867step0 raw22867step0Labels permutation39 permutation2
    _ = mixedMoment B node2467 node2467Labels := by rfl

def raw22868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw22868Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw22868step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22868 raw22868Labels = mixedMoment B node2706 node2706Labels := by
  calc
    mixedMoment B raw22868 raw22868Labels = mixedMoment B raw22868step0 raw22868step0Labels := by
      have hz : ∀ j, raw22868 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22868step0 = (fun i j => raw22868 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22868step0 raw22868; decide +kernel
      have hl : raw22868step0Labels = raw22868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22868 raw22868Labels permutation265 hz
    _ = mixedMoment B node2706 node2706Labels := by rfl

def raw22869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3], ![1, 0, -1]]
def raw22869Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3], ![1, 0, -1]]
def raw22869step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw22869step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22869 raw22869Labels = mixedMoment B node2704 node2704Labels := by
  calc
    mixedMoment B raw22869 raw22869Labels = mixedMoment B raw22869step0 raw22869step0Labels := by
      have hz : ∀ j, raw22869 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22869step0 = (fun i j => raw22869 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22869step0 raw22869; decide +kernel
      have hl : raw22869step0Labels = raw22869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22869 raw22869Labels permutation265 hz
    mixedMoment B raw22869step0 raw22869step0Labels = mixedMoment B raw22869step1 raw22869step1Labels := by
      have ha : raw22869step1 = (fun i j => raw22869step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22869step1 raw22869step0; decide +kernel
      have hl : raw22869step1Labels = raw22869step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22869step0 raw22869step0Labels permutation33 permutation2
    _ = mixedMoment B node2704 node2704Labels := by rfl

def raw22870 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![-1, 1], ![3, -3], ![1, -1]]
def raw22870Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22870step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![3, -3], ![1, -1]]
def raw22870step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22870step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw22870step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22870step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw22870step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22870 raw22870Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw22870 raw22870Labels = mixedMoment B raw22870step0 raw22870step0Labels := by
      have hz : ∀ j, raw22870 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22870step0 = (fun i j => raw22870 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22870step0 raw22870; decide +kernel
      have hl : raw22870step0Labels = raw22870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22870 raw22870Labels permutation265 hz
    mixedMoment B raw22870step0 raw22870step0Labels = mixedMoment B raw22870step1 raw22870step1Labels := by
      have ha : raw22870step1 = (fun i j => raw22870step0 (permutation125 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22870step1 raw22870step0; decide +kernel
      have hl : raw22870step1Labels = raw22870step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22870step0 raw22870step0Labels permutation125 permutation0
    mixedMoment B raw22870step1 raw22870step1Labels = mixedMoment B raw22870step2 raw22870step2Labels := by
      have ha : raw22870step2 = -raw22870step1 := by apply Matrix.ext; change ∀ i j, raw22870step2 i j = -(raw22870step1 i j); unfold raw22870step2 raw22870step1; decide +kernel
      have hl : raw22870step2Labels = raw22870step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw22871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22871Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22871 raw22871Labels = mixedMoment B node2541 node2541Labels := by
  calc
    _ = mixedMoment B node2541 node2541Labels := by rfl

def raw22872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22872Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22872 raw22872Labels = mixedMoment B node2468 node2468Labels := by
  calc
    mixedMoment B raw22872 raw22872Labels = mixedMoment B raw22872step0 raw22872step0Labels := by
      have hz : ∀ j, raw22872 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22872step0 = (fun i j => raw22872 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22872step0 raw22872; decide +kernel
      have hl : raw22872step0Labels = raw22872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22872 raw22872Labels permutation265 hz
    _ = mixedMoment B node2468 node2468Labels := by rfl

def raw22873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22873Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22873step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22873step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22873 raw22873Labels = mixedMoment B node2468 node2468Labels := by
  calc
    mixedMoment B raw22873 raw22873Labels = mixedMoment B raw22873step0 raw22873step0Labels := by
      have hz : ∀ j, raw22873 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22873step0 = (fun i j => raw22873 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22873step0 raw22873; decide +kernel
      have hl : raw22873step0Labels = raw22873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22873 raw22873Labels permutation265 hz
    mixedMoment B raw22873step0 raw22873step0Labels = mixedMoment B raw22873step1 raw22873step1Labels := by
      have ha : raw22873step1 = (fun i j => raw22873step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22873step1 raw22873step0; decide +kernel
      have hl : raw22873step1Labels = raw22873step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22873step0 raw22873step0Labels permutation38 permutation2
    _ = mixedMoment B node2468 node2468Labels := by rfl

def raw22874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw22874Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw22874step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22874step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw22874step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22874 raw22874Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw22874 raw22874Labels = mixedMoment B raw22874step0 raw22874step0Labels := by
      have hz : ∀ j, raw22874 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22874step0 = (fun i j => raw22874 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22874step0 raw22874; decide +kernel
      have hl : raw22874step0Labels = raw22874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22874 raw22874Labels permutation265 hz
    mixedMoment B raw22874step0 raw22874step0Labels = mixedMoment B raw22874step1 raw22874step1Labels := by
      have ha : raw22874step1 = (fun i j => raw22874step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22874step1 raw22874step0; decide +kernel
      have hl : raw22874step1Labels = raw22874step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22874step0 raw22874step0Labels permutation33 permutation2
    _ = mixedMoment B node2705 node2705Labels := by rfl

def raw22875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22875Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw22875step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22875 raw22875Labels = mixedMoment B node1106 node1106Labels := by
  calc
    mixedMoment B raw22875 raw22875Labels = mixedMoment B raw22875step0 raw22875step0Labels := by
      have ha : raw22875step0 = (fun i j => raw22875 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22875step0 raw22875; decide +kernel
      have hl : raw22875step0Labels = raw22875Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22875 raw22875Labels permutation182 permutation2
    _ = mixedMoment B node1106 node1106Labels := by rfl

def raw22876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22876Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22876step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22876 raw22876Labels = mixedMoment B node1124 node1124Labels := by
  calc
    mixedMoment B raw22876 raw22876Labels = mixedMoment B raw22876step0 raw22876step0Labels := by
      have hz : ∀ j, raw22876 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22876step0 = (fun i j => raw22876 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22876step0 raw22876; decide +kernel
      have hl : raw22876step0Labels = raw22876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22876 raw22876Labels permutation265 hz
    _ = mixedMoment B node1124 node1124Labels := by rfl

def raw22877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw22877Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw22877step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw22877step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22877 raw22877Labels = mixedMoment B node1110 node1110Labels := by
  calc
    mixedMoment B raw22877 raw22877Labels = mixedMoment B raw22877step0 raw22877step0Labels := by
      have hz : ∀ j, raw22877 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22877step0 = (fun i j => raw22877 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22877step0 raw22877; decide +kernel
      have hl : raw22877step0Labels = raw22877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22877 raw22877Labels permutation265 hz
    mixedMoment B raw22877step0 raw22877step0Labels = mixedMoment B raw22877step1 raw22877step1Labels := by
      have ha : raw22877step1 = (fun i j => raw22877step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22877step1 raw22877step0; decide +kernel
      have hl : raw22877step1Labels = raw22877step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22877step0 raw22877step0Labels permutation33 permutation2
    _ = mixedMoment B node1110 node1110Labels := by rfl

def raw22878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw22878Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw22878step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22878 raw22878Labels = mixedMoment B node1110 node1110Labels := by
  calc
    mixedMoment B raw22878 raw22878Labels = mixedMoment B raw22878step0 raw22878step0Labels := by
      have hz : ∀ j, raw22878 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22878step0 = (fun i j => raw22878 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22878step0 raw22878; decide +kernel
      have hl : raw22878step0Labels = raw22878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22878 raw22878Labels permutation265 hz
    _ = mixedMoment B node1110 node1110Labels := by rfl

def raw22879 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22879Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22879step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22879step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw22879step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22879step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw22879step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22879 raw22879Labels = mixedMoment B node3284 node3284Labels := by
  calc
    mixedMoment B raw22879 raw22879Labels = mixedMoment B raw22879step0 raw22879step0Labels := by
      have hz : ∀ j, raw22879 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22879step0 = (fun i j => raw22879 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22879step0 raw22879; decide +kernel
      have hl : raw22879step0Labels = raw22879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22879 raw22879Labels permutation265 hz
    mixedMoment B raw22879step0 raw22879step0Labels = mixedMoment B raw22879step1 raw22879step1Labels := by
      have ha : raw22879step1 = (fun i j => raw22879step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22879step1 raw22879step0; decide +kernel
      have hl : raw22879step1Labels = raw22879step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22879step0 raw22879step0Labels permutation32 permutation4
    mixedMoment B raw22879step1 raw22879step1Labels = mixedMoment B raw22879step2 raw22879step2Labels := by
      have ha : raw22879step2 = -raw22879step1 := by apply Matrix.ext; change ∀ i j, raw22879step2 i j = -(raw22879step1 i j); unfold raw22879step2 raw22879step1; decide +kernel
      have hl : raw22879step2Labels = raw22879step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3284 node3284Labels := by rfl

def raw22880 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw22880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22880step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw22880step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22880 raw22880Labels = mixedMoment B node1581 node1581Labels := by
  calc
    mixedMoment B raw22880 raw22880Labels = mixedMoment B raw22880step0 raw22880step0Labels := by
      have ha : raw22880step0 = (fun i j => raw22880 (permutation182 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22880step0 raw22880; decide +kernel
      have hl : raw22880step0Labels = raw22880Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22880 raw22880Labels permutation182 permutation4
    mixedMoment B raw22880step0 raw22880step0Labels = mixedMoment B raw22880step1 raw22880step1Labels := by
      have ha : raw22880step1 = -raw22880step0 := by apply Matrix.ext; change ∀ i j, raw22880step1 i j = -(raw22880step0 i j); unfold raw22880step1 raw22880step0; decide +kernel
      have hl : raw22880step1Labels = raw22880step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1581 node1581Labels := by rfl

def raw22881 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22881Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22881step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22881step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw22881step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22881step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw22881step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22881step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw22881step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22881 raw22881Labels = mixedMoment B node1631 node1631Labels := by
  calc
    mixedMoment B raw22881 raw22881Labels = mixedMoment B raw22881step0 raw22881step0Labels := by
      have hz : ∀ j, raw22881 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22881step0 = (fun i j => raw22881 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22881step0 raw22881; decide +kernel
      have hl : raw22881step0Labels = raw22881Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22881 raw22881Labels permutation434 hz
    mixedMoment B raw22881step0 raw22881step0Labels = mixedMoment B raw22881step1 raw22881step1Labels := by
      have hz : ∀ j, raw22881step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22881step1 = (fun i j => raw22881step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22881step1 raw22881step0; decide +kernel
      have hl : raw22881step1Labels = raw22881step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22881step0 raw22881step0Labels permutation56 hz
    mixedMoment B raw22881step1 raw22881step1Labels = mixedMoment B raw22881step2 raw22881step2Labels := by
      have ha : raw22881step2 = (fun i j => raw22881step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22881step2 raw22881step1; decide +kernel
      have hl : raw22881step2Labels = raw22881step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22881step1 raw22881step1Labels permutation8 permutation4
    mixedMoment B raw22881step2 raw22881step2Labels = mixedMoment B raw22881step3 raw22881step3Labels := by
      have ha : raw22881step3 = -raw22881step2 := by apply Matrix.ext; change ∀ i j, raw22881step3 i j = -(raw22881step2 i j); unfold raw22881step3 raw22881step2; decide +kernel
      have hl : raw22881step3Labels = raw22881step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1631 node1631Labels := by rfl

def raw22882 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2], ![0, -2, 2]]
def raw22882Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2], ![0, -2, 2]]
def raw22882step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-3, 1, 2]]
def raw22882step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22882step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22882step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22882 raw22882Labels = mixedMoment B node1585 node1585Labels := by
  calc
    mixedMoment B raw22882 raw22882Labels = mixedMoment B raw22882step0 raw22882step0Labels := by
      have hz : ∀ j, raw22882 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22882step0 = (fun i j => raw22882 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22882step0 raw22882; decide +kernel
      have hl : raw22882step0Labels = raw22882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22882 raw22882Labels permutation265 hz
    mixedMoment B raw22882step0 raw22882step0Labels = mixedMoment B raw22882step1 raw22882step1Labels := by
      have ha : raw22882step1 = (fun i j => raw22882step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22882step1 raw22882step0; decide +kernel
      have hl : raw22882step1Labels = raw22882step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22882step0 raw22882step0Labels permutation33 permutation4
    mixedMoment B raw22882step1 raw22882step1Labels = mixedMoment B raw22882step2 raw22882step2Labels := by
      have ha : raw22882step2 = -raw22882step1 := by apply Matrix.ext; change ∀ i j, raw22882step2 i j = -(raw22882step1 i j); unfold raw22882step2 raw22882step1; decide +kernel
      have hl : raw22882step2Labels = raw22882step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1585 node1585Labels := by rfl

def raw22883 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![1, -3, 2]]
def raw22883Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![1, -3, 2]]
def raw22883step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-3, 1, 2]]
def raw22883step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22883step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22883step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22883 raw22883Labels = mixedMoment B node1585 node1585Labels := by
  calc
    mixedMoment B raw22883 raw22883Labels = mixedMoment B raw22883step0 raw22883step0Labels := by
      have hz : ∀ j, raw22883 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22883step0 = (fun i j => raw22883 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22883step0 raw22883; decide +kernel
      have hl : raw22883step0Labels = raw22883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22883 raw22883Labels permutation265 hz
    mixedMoment B raw22883step0 raw22883step0Labels = mixedMoment B raw22883step1 raw22883step1Labels := by
      have ha : raw22883step1 = (fun i j => raw22883step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22883step1 raw22883step0; decide +kernel
      have hl : raw22883step1Labels = raw22883step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22883step0 raw22883step0Labels permutation32 permutation4
    mixedMoment B raw22883step1 raw22883step1Labels = mixedMoment B raw22883step2 raw22883step2Labels := by
      have ha : raw22883step2 = -raw22883step1 := by apply Matrix.ext; change ∀ i j, raw22883step2 i j = -(raw22883step1 i j); unfold raw22883step2 raw22883step1; decide +kernel
      have hl : raw22883step2Labels = raw22883step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1585 node1585Labels := by rfl

def raw22884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22884Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22884step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22884step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, 0, -2], ![2, -3, 1]]
def raw22884step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22884step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw22884step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22884 raw22884Labels = mixedMoment B node1062 node1062Labels := by
  calc
    mixedMoment B raw22884 raw22884Labels = mixedMoment B raw22884step0 raw22884step0Labels := by
      have hz : ∀ j, raw22884 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22884step0 = (fun i j => raw22884 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22884step0 raw22884; decide +kernel
      have hl : raw22884step0Labels = raw22884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22884 raw22884Labels permutation434 hz
    mixedMoment B raw22884step0 raw22884step0Labels = mixedMoment B raw22884step1 raw22884step1Labels := by
      have hz : ∀ j, raw22884step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22884step1 = (fun i j => raw22884step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22884step1 raw22884step0; decide +kernel
      have hl : raw22884step1Labels = raw22884step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22884step0 raw22884step0Labels permutation80 hz
    mixedMoment B raw22884step1 raw22884step1Labels = mixedMoment B raw22884step2 raw22884step2Labels := by
      have ha : raw22884step2 = (fun i j => raw22884step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22884step2 raw22884step1; decide +kernel
      have hl : raw22884step2Labels = raw22884step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22884step1 raw22884step1Labels permutation9 permutation2
    _ = mixedMoment B node1062 node1062Labels := by rfl

def raw22885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22885Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22885step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22885step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, 0, -2], ![2, -3, 1]]
def raw22885step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22885step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -3, 1], ![2, 0, -2]]
def raw22885step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22885 raw22885Labels = mixedMoment B node2137 node2137Labels := by
  calc
    mixedMoment B raw22885 raw22885Labels = mixedMoment B raw22885step0 raw22885step0Labels := by
      have hz : ∀ j, raw22885 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22885step0 = (fun i j => raw22885 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22885step0 raw22885; decide +kernel
      have hl : raw22885step0Labels = raw22885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22885 raw22885Labels permutation434 hz
    mixedMoment B raw22885step0 raw22885step0Labels = mixedMoment B raw22885step1 raw22885step1Labels := by
      have hz : ∀ j, raw22885step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22885step1 = (fun i j => raw22885step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22885step1 raw22885step0; decide +kernel
      have hl : raw22885step1Labels = raw22885step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22885step0 raw22885step0Labels permutation80 hz
    mixedMoment B raw22885step1 raw22885step1Labels = mixedMoment B raw22885step2 raw22885step2Labels := by
      have ha : raw22885step2 = (fun i j => raw22885step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22885step2 raw22885step1; decide +kernel
      have hl : raw22885step2Labels = raw22885step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22885step1 raw22885step1Labels permutation9 permutation2
    _ = mixedMoment B node2137 node2137Labels := by rfl

def raw22886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22886Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22886step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22886step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw22886step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22886 raw22886Labels = mixedMoment B node2038 node2038Labels := by
  calc
    mixedMoment B raw22886 raw22886Labels = mixedMoment B raw22886step0 raw22886step0Labels := by
      have hz : ∀ j, raw22886 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22886step0 = (fun i j => raw22886 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22886step0 raw22886; decide +kernel
      have hl : raw22886step0Labels = raw22886Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22886 raw22886Labels permutation434 hz
    mixedMoment B raw22886step0 raw22886step0Labels = mixedMoment B raw22886step1 raw22886step1Labels := by
      have ha : raw22886step1 = (fun i j => raw22886step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22886step1 raw22886step0; decide +kernel
      have hl : raw22886step1Labels = raw22886step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22886step0 raw22886step0Labels permutation39 permutation2
    _ = mixedMoment B node2038 node2038Labels := by rfl

def raw22887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22887Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22887step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw22887step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22887 raw22887Labels = mixedMoment B node2038 node2038Labels := by
  calc
    mixedMoment B raw22887 raw22887Labels = mixedMoment B raw22887step0 raw22887step0Labels := by
      have hz : ∀ j, raw22887 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22887step0 = (fun i j => raw22887 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22887step0 raw22887; decide +kernel
      have hl : raw22887step0Labels = raw22887Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22887 raw22887Labels permutation346 hz
    mixedMoment B raw22887step0 raw22887step0Labels = mixedMoment B raw22887step1 raw22887step1Labels := by
      have ha : raw22887step1 = (fun i j => raw22887step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22887step1 raw22887step0; decide +kernel
      have hl : raw22887step1Labels = raw22887step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22887step0 raw22887step0Labels permutation39 permutation2
    _ = mixedMoment B node2038 node2038Labels := by rfl

def raw22888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw22888Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw22888step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22888step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw22888step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22888 raw22888Labels = mixedMoment B node2280 node2280Labels := by
  calc
    mixedMoment B raw22888 raw22888Labels = mixedMoment B raw22888step0 raw22888step0Labels := by
      have hz : ∀ j, raw22888 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22888step0 = (fun i j => raw22888 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22888step0 raw22888; decide +kernel
      have hl : raw22888step0Labels = raw22888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22888 raw22888Labels permutation434 hz
    mixedMoment B raw22888step0 raw22888step0Labels = mixedMoment B raw22888step1 raw22888step1Labels := by
      have hz : ∀ j, raw22888step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22888step1 = (fun i j => raw22888step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22888step1 raw22888step0; decide +kernel
      have hl : raw22888step1Labels = raw22888step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22888step0 raw22888step0Labels permutation80 hz
    _ = mixedMoment B node2280 node2280Labels := by rfl

def raw22889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -2, 1]]
def raw22889Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2], ![1, -2, 1]]
def raw22889step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22889step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![2, 0, -2], ![1, -2, 1]]
def raw22889step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22889step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw22889step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22889 raw22889Labels = mixedMoment B node2276 node2276Labels := by
  calc
    mixedMoment B raw22889 raw22889Labels = mixedMoment B raw22889step0 raw22889step0Labels := by
      have hz : ∀ j, raw22889 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22889step0 = (fun i j => raw22889 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22889step0 raw22889; decide +kernel
      have hl : raw22889step0Labels = raw22889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22889 raw22889Labels permutation434 hz
    mixedMoment B raw22889step0 raw22889step0Labels = mixedMoment B raw22889step1 raw22889step1Labels := by
      have hz : ∀ j, raw22889step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22889step1 = (fun i j => raw22889step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22889step1 raw22889step0; decide +kernel
      have hl : raw22889step1Labels = raw22889step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22889step0 raw22889step0Labels permutation80 hz
    mixedMoment B raw22889step1 raw22889step1Labels = mixedMoment B raw22889step2 raw22889step2Labels := by
      have ha : raw22889step2 = (fun i j => raw22889step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22889step2 raw22889step1; decide +kernel
      have hl : raw22889step2Labels = raw22889step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22889step1 raw22889step1Labels permutation9 permutation2
    _ = mixedMoment B node2276 node2276Labels := by rfl

def raw22890 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![0, 0], ![2, -2], ![-1, 1]]
def raw22890Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22890step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![2, -2], ![-1, 1]]
def raw22890step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22890step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![2, -2], ![-1, 1]]
def raw22890step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22890step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw22890step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22890 raw22890Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw22890 raw22890Labels = mixedMoment B raw22890step0 raw22890step0Labels := by
      have hz : ∀ j, raw22890 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22890step0 = (fun i j => raw22890 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22890step0 raw22890; decide +kernel
      have hl : raw22890step0Labels = raw22890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22890 raw22890Labels permutation434 hz
    mixedMoment B raw22890step0 raw22890step0Labels = mixedMoment B raw22890step1 raw22890step1Labels := by
      have hz : ∀ j, raw22890step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22890step1 = (fun i j => raw22890step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22890step1 raw22890step0; decide +kernel
      have hl : raw22890step1Labels = raw22890step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22890step0 raw22890step0Labels permutation80 hz
    mixedMoment B raw22890step1 raw22890step1Labels = mixedMoment B raw22890step2 raw22890step2Labels := by
      have ha : raw22890step2 = (fun i j => raw22890step1 (permutation12 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22890step2 raw22890step1; decide +kernel
      have hl : raw22890step2Labels = raw22890step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22890step1 raw22890step1Labels permutation12 permutation0
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw22891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw22891Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw22891step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw22891step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22891 raw22891Labels = mixedMoment B node992 node992Labels := by
  calc
    mixedMoment B raw22891 raw22891Labels = mixedMoment B raw22891step0 raw22891step0Labels := by
      have hz : ∀ j, raw22891 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22891step0 = (fun i j => raw22891 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22891step0 raw22891; decide +kernel
      have hl : raw22891step0Labels = raw22891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22891 raw22891Labels permutation346 hz
    mixedMoment B raw22891step0 raw22891step0Labels = mixedMoment B raw22891step1 raw22891step1Labels := by
      have ha : raw22891step1 = (fun i j => raw22891step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22891step1 raw22891step0; decide +kernel
      have hl : raw22891step1Labels = raw22891step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22891step0 raw22891step0Labels permutation39 permutation2
    _ = mixedMoment B node992 node992Labels := by rfl

def raw22892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw22892Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw22892step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw22892step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22892 raw22892Labels = mixedMoment B node2122 node2122Labels := by
  calc
    mixedMoment B raw22892 raw22892Labels = mixedMoment B raw22892step0 raw22892step0Labels := by
      have hz : ∀ j, raw22892 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22892step0 = (fun i j => raw22892 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22892step0 raw22892; decide +kernel
      have hl : raw22892step0Labels = raw22892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22892 raw22892Labels permutation346 hz
    mixedMoment B raw22892step0 raw22892step0Labels = mixedMoment B raw22892step1 raw22892step1Labels := by
      have ha : raw22892step1 = (fun i j => raw22892step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22892step1 raw22892step0; decide +kernel
      have hl : raw22892step1Labels = raw22892step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22892step0 raw22892step0Labels permutation33 permutation2
    _ = mixedMoment B node2122 node2122Labels := by rfl

def raw22893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw22893Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22893step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw22893step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22893 raw22893Labels = mixedMoment B node1993 node1993Labels := by
  calc
    mixedMoment B raw22893 raw22893Labels = mixedMoment B raw22893step0 raw22893step0Labels := by
      have ha : raw22893step0 = (fun i j => raw22893 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22893step0 raw22893; decide +kernel
      have hl : raw22893step0Labels = raw22893Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22893 raw22893Labels permutation183 permutation2
    _ = mixedMoment B node1993 node1993Labels := by rfl

def raw22894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw22894Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw22894step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw22894step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22894 raw22894Labels = mixedMoment B node1928 node1928Labels := by
  calc
    mixedMoment B raw22894 raw22894Labels = mixedMoment B raw22894step0 raw22894step0Labels := by
      have hz : ∀ j, raw22894 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22894step0 = (fun i j => raw22894 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22894step0 raw22894; decide +kernel
      have hl : raw22894step0Labels = raw22894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22894 raw22894Labels permutation346 hz
    mixedMoment B raw22894step0 raw22894step0Labels = mixedMoment B raw22894step1 raw22894step1Labels := by
      have ha : raw22894step1 = (fun i j => raw22894step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22894step1 raw22894step0; decide +kernel
      have hl : raw22894step1Labels = raw22894step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22894step0 raw22894step0Labels permutation39 permutation2
    _ = mixedMoment B node1928 node1928Labels := by rfl

def raw22895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw22895Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw22895step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw22895step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22895 raw22895Labels = mixedMoment B node2217 node2217Labels := by
  calc
    mixedMoment B raw22895 raw22895Labels = mixedMoment B raw22895step0 raw22895step0Labels := by
      have hz : ∀ j, raw22895 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22895step0 = (fun i j => raw22895 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22895step0 raw22895; decide +kernel
      have hl : raw22895step0Labels = raw22895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22895 raw22895Labels permutation346 hz
    mixedMoment B raw22895step0 raw22895step0Labels = mixedMoment B raw22895step1 raw22895step1Labels := by
      have ha : raw22895step1 = (fun i j => raw22895step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22895step1 raw22895step0; decide +kernel
      have hl : raw22895step1Labels = raw22895step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22895step0 raw22895step0Labels permutation38 permutation2
    _ = mixedMoment B node2217 node2217Labels := by rfl

def raw22896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, -1, 0]]
def raw22896Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![2, 0, -2], ![1, -1, 0]]
def raw22896step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22896step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22896 raw22896Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw22896 raw22896Labels = mixedMoment B raw22896step0 raw22896step0Labels := by
      have hz : ∀ j, raw22896 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22896step0 = (fun i j => raw22896 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22896step0 raw22896; decide +kernel
      have hl : raw22896step0Labels = raw22896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22896 raw22896Labels permutation346 hz
    mixedMoment B raw22896step0 raw22896step0Labels = mixedMoment B raw22896step1 raw22896step1Labels := by
      have ha : raw22896step1 = (fun i j => raw22896step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22896step1 raw22896step0; decide +kernel
      have hl : raw22896step1Labels = raw22896step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22896step0 raw22896step0Labels permutation39 permutation2
    _ = mixedMoment B node2215 node2215Labels := by rfl

def raw22897 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![-1, 1], ![2, -2], ![0, 0]]
def raw22897Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22897step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![-1, 1], ![2, -2]]
def raw22897step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22897step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![-1, 1], ![2, -2]]
def raw22897step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22897step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw22897step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22897 raw22897Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw22897 raw22897Labels = mixedMoment B raw22897step0 raw22897step0Labels := by
      have hz : ∀ j, raw22897 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw22897step0 = (fun i j => raw22897 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw22897step0 raw22897; decide +kernel
      have hl : raw22897step0Labels = raw22897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22897 raw22897Labels permutation590 hz
    mixedMoment B raw22897step0 raw22897step0Labels = mixedMoment B raw22897step1 raw22897step1Labels := by
      have hz : ∀ j, raw22897step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22897step1 = (fun i j => raw22897step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22897step1 raw22897step0; decide +kernel
      have hl : raw22897step1Labels = raw22897step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22897step0 raw22897step0Labels permutation80 hz
    mixedMoment B raw22897step1 raw22897step1Labels = mixedMoment B raw22897step2 raw22897step2Labels := by
      have ha : raw22897step2 = (fun i j => raw22897step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22897step2 raw22897step1; decide +kernel
      have hl : raw22897step2Labels = raw22897step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22897step1 raw22897step1Labels permutation10 permutation0
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw22898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22898Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22898step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22898 raw22898Labels = mixedMoment B node2123 node2123Labels := by
  calc
    mixedMoment B raw22898 raw22898Labels = mixedMoment B raw22898step0 raw22898step0Labels := by
      have hz : ∀ j, raw22898 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22898step0 = (fun i j => raw22898 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22898step0 raw22898; decide +kernel
      have hl : raw22898step0Labels = raw22898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22898 raw22898Labels permutation346 hz
    _ = mixedMoment B node2123 node2123Labels := by rfl

def raw22899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22899Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22899step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw22899step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22899 raw22899Labels = mixedMoment B node1994 node1994Labels := by
  calc
    mixedMoment B raw22899 raw22899Labels = mixedMoment B raw22899step0 raw22899step0Labels := by
      have ha : raw22899step0 = (fun i j => raw22899 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22899step0 raw22899; decide +kernel
      have hl : raw22899step0Labels = raw22899Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22899 raw22899Labels permutation182 permutation2
    _ = mixedMoment B node1994 node1994Labels := by rfl

def raw22900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22900Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw22900step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22900step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw22900step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22900 raw22900Labels = mixedMoment B node1929 node1929Labels := by
  calc
    mixedMoment B raw22900 raw22900Labels = mixedMoment B raw22900step0 raw22900step0Labels := by
      have hz : ∀ j, raw22900 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22900step0 = (fun i j => raw22900 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22900step0 raw22900; decide +kernel
      have hl : raw22900step0Labels = raw22900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22900 raw22900Labels permutation346 hz
    mixedMoment B raw22900step0 raw22900step0Labels = mixedMoment B raw22900step1 raw22900step1Labels := by
      have ha : raw22900step1 = (fun i j => raw22900step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22900step1 raw22900step0; decide +kernel
      have hl : raw22900step1Labels = raw22900step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22900step0 raw22900step0Labels permutation38 permutation2
    _ = mixedMoment B node1929 node1929Labels := by rfl

def raw22901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw22901Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw22901step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw22901step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22901 raw22901Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw22901 raw22901Labels = mixedMoment B raw22901step0 raw22901step0Labels := by
      have hz : ∀ j, raw22901 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22901step0 = (fun i j => raw22901 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22901step0 raw22901; decide +kernel
      have hl : raw22901step0Labels = raw22901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22901 raw22901Labels permutation346 hz
    mixedMoment B raw22901step0 raw22901step0Labels = mixedMoment B raw22901step1 raw22901step1Labels := by
      have ha : raw22901step1 = (fun i j => raw22901step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22901step1 raw22901step0; decide +kernel
      have hl : raw22901step1Labels = raw22901step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22901step0 raw22901step0Labels permutation39 permutation2
    _ = mixedMoment B node2216 node2216Labels := by rfl

def raw22902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22902Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw22902step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw22902step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22902 raw22902Labels = mixedMoment B node1025 node1025Labels := by
  calc
    mixedMoment B raw22902 raw22902Labels = mixedMoment B raw22902step0 raw22902step0Labels := by
      have hz : ∀ j, raw22902 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22902step0 = (fun i j => raw22902 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22902step0 raw22902; decide +kernel
      have hl : raw22902step0Labels = raw22902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22902 raw22902Labels permutation434 hz
    mixedMoment B raw22902step0 raw22902step0Labels = mixedMoment B raw22902step1 raw22902step1Labels := by
      have ha : raw22902step1 = (fun i j => raw22902step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22902step1 raw22902step0; decide +kernel
      have hl : raw22902step1Labels = raw22902step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22902step0 raw22902step0Labels permutation33 permutation2
    _ = mixedMoment B node1025 node1025Labels := by rfl

def raw22903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22903Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw22903step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22903step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw22903step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22903 raw22903Labels = mixedMoment B node2093 node2093Labels := by
  calc
    mixedMoment B raw22903 raw22903Labels = mixedMoment B raw22903step0 raw22903step0Labels := by
      have hz : ∀ j, raw22903 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22903step0 = (fun i j => raw22903 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22903step0 raw22903; decide +kernel
      have hl : raw22903step0Labels = raw22903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22903 raw22903Labels permutation434 hz
    mixedMoment B raw22903step0 raw22903step0Labels = mixedMoment B raw22903step1 raw22903step1Labels := by
      have ha : raw22903step1 = (fun i j => raw22903step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22903step1 raw22903step0; decide +kernel
      have hl : raw22903step1Labels = raw22903step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22903step0 raw22903step0Labels permutation33 permutation2
    _ = mixedMoment B node2093 node2093Labels := by rfl

def raw22904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22904Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![2, 0, -2], ![2, -3, 1]]
def raw22904step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22904step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw22904step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22904 raw22904Labels = mixedMoment B node2093 node2093Labels := by
  calc
    mixedMoment B raw22904 raw22904Labels = mixedMoment B raw22904step0 raw22904step0Labels := by
      have hz : ∀ j, raw22904 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22904step0 = (fun i j => raw22904 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22904step0 raw22904; decide +kernel
      have hl : raw22904step0Labels = raw22904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22904 raw22904Labels permutation434 hz
    mixedMoment B raw22904step0 raw22904step0Labels = mixedMoment B raw22904step1 raw22904step1Labels := by
      have ha : raw22904step1 = (fun i j => raw22904step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22904step1 raw22904step0; decide +kernel
      have hl : raw22904step1Labels = raw22904step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22904step0 raw22904step0Labels permutation39 permutation2
    _ = mixedMoment B node2093 node2093Labels := by rfl

def raw22905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22905Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw22905step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22905 raw22905Labels = mixedMoment B node2011 node2011Labels := by
  calc
    mixedMoment B raw22905 raw22905Labels = mixedMoment B raw22905step0 raw22905step0Labels := by
      have ha : raw22905step0 = (fun i j => raw22905 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22905step0 raw22905; decide +kernel
      have hl : raw22905step0Labels = raw22905Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22905 raw22905Labels permutation201 permutation2
    _ = mixedMoment B node2011 node2011Labels := by rfl

def raw22906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw22906Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw22906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22906 raw22906Labels = mixedMoment B node2246 node2246Labels := by
  calc
    mixedMoment B raw22906 raw22906Labels = mixedMoment B raw22906step0 raw22906step0Labels := by
      have hz : ∀ j, raw22906 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22906step0 = (fun i j => raw22906 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22906step0 raw22906; decide +kernel
      have hl : raw22906step0Labels = raw22906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22906 raw22906Labels permutation434 hz
    _ = mixedMoment B node2246 node2246Labels := by rfl

def raw22907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -2, 1]]
def raw22907Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2], ![1, -2, 1]]
def raw22907step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw22907step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22907 raw22907Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw22907 raw22907Labels = mixedMoment B raw22907step0 raw22907step0Labels := by
      have hz : ∀ j, raw22907 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22907step0 = (fun i j => raw22907 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22907step0 raw22907; decide +kernel
      have hl : raw22907step0Labels = raw22907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22907 raw22907Labels permutation434 hz
    mixedMoment B raw22907step0 raw22907step0Labels = mixedMoment B raw22907step1 raw22907step1Labels := by
      have ha : raw22907step1 = (fun i j => raw22907step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22907step1 raw22907step0; decide +kernel
      have hl : raw22907step1Labels = raw22907step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22907step0 raw22907step0Labels permutation33 permutation2
    _ = mixedMoment B node2242 node2242Labels := by rfl

def raw22908 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![0, 0], ![2, -2], ![-1, 1]]
def raw22908Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22908step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![2, -2], ![-1, 1]]
def raw22908step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22908step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw22908step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22908 raw22908Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw22908 raw22908Labels = mixedMoment B raw22908step0 raw22908step0Labels := by
      have hz : ∀ j, raw22908 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22908step0 = (fun i j => raw22908 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22908step0 raw22908; decide +kernel
      have hl : raw22908step0Labels = raw22908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22908 raw22908Labels permutation434 hz
    mixedMoment B raw22908step0 raw22908step0Labels = mixedMoment B raw22908step1 raw22908step1Labels := by
      have ha : raw22908step1 = (fun i j => raw22908step0 (permutation50 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22908step1 raw22908step0; decide +kernel
      have hl : raw22908step1Labels = raw22908step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22908step0 raw22908step0Labels permutation50 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw22909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw22909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22909step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22909 raw22909Labels = mixedMoment B node973 node973Labels := by
  calc
    mixedMoment B raw22909 raw22909Labels = mixedMoment B raw22909step0 raw22909step0Labels := by
      have ha : raw22909step0 = (fun i j => raw22909 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22909step0 raw22909; decide +kernel
      have hl : raw22909step0Labels = raw22909Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22909 raw22909Labels permutation201 permutation2
    _ = mixedMoment B node973 node973Labels := by rfl

def raw22910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw22910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22910step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22910 raw22910Labels = mixedMoment B node2072 node2072Labels := by
  calc
    mixedMoment B raw22910 raw22910Labels = mixedMoment B raw22910step0 raw22910step0Labels := by
      have ha : raw22910step0 = (fun i j => raw22910 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22910step0 raw22910; decide +kernel
      have hl : raw22910step0Labels = raw22910Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22910 raw22910Labels permutation159 permutation2
    _ = mixedMoment B node2072 node2072Labels := by rfl

def raw22911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw22911Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22911 raw22911Labels = mixedMoment B node2072 node2072Labels := by
  calc
    mixedMoment B raw22911 raw22911Labels = mixedMoment B raw22911step0 raw22911step0Labels := by
      have ha : raw22911step0 = (fun i j => raw22911 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22911step0 raw22911; decide +kernel
      have hl : raw22911step0Labels = raw22911Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22911 raw22911Labels permutation183 permutation2
    _ = mixedMoment B node2072 node2072Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
