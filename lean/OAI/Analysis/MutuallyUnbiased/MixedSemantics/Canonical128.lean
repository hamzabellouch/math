import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw16384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16384Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16384step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16384step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16384step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16384 raw16384Labels = mixedMoment B node3946 node3946Labels := by
  calc
    mixedMoment B raw16384 raw16384Labels = mixedMoment B raw16384step0 raw16384step0Labels := by
      have ha : raw16384step0 = (fun i j => raw16384 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16384step0 raw16384; decide +kernel
      have hl : raw16384step0Labels = raw16384Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16384 raw16384Labels permutation688 permutation3
    mixedMoment B raw16384step0 raw16384step0Labels = mixedMoment B raw16384step1 raw16384step1Labels := by
      have ha : raw16384step1 = -raw16384step0 := by apply Matrix.ext; change ∀ i j, raw16384step1 i j = -(raw16384step0 i j); unfold raw16384step1 raw16384step0; decide +kernel
      have hl : raw16384step1Labels = raw16384step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3946 node3946Labels := by rfl

def raw16385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16385Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16385step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16385step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16385step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16385step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16385 raw16385Labels = mixedMoment B node3993 node3993Labels := by
  calc
    mixedMoment B raw16385 raw16385Labels = mixedMoment B raw16385step0 raw16385step0Labels := by
      have hz : ∀ j, raw16385 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16385step0 = (fun i j => raw16385 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16385step0 raw16385; decide +kernel
      have hl : raw16385step0Labels = raw16385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16385 raw16385Labels permutation346 hz
    mixedMoment B raw16385step0 raw16385step0Labels = mixedMoment B raw16385step1 raw16385step1Labels := by
      have ha : raw16385step1 = (fun i j => raw16385step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16385step1 raw16385step0; decide +kernel
      have hl : raw16385step1Labels = raw16385step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16385step0 raw16385step0Labels permutation145 permutation3
    mixedMoment B raw16385step1 raw16385step1Labels = mixedMoment B raw16385step2 raw16385step2Labels := by
      have ha : raw16385step2 = -raw16385step1 := by apply Matrix.ext; change ∀ i j, raw16385step2 i j = -(raw16385step1 i j); unfold raw16385step2 raw16385step1; decide +kernel
      have hl : raw16385step2Labels = raw16385step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3993 node3993Labels := by rfl

def raw16386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16386Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16386step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16386step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16386 raw16386Labels = mixedMoment B node4028 node4028Labels := by
  calc
    mixedMoment B raw16386 raw16386Labels = mixedMoment B raw16386step0 raw16386step0Labels := by
      have hz : ∀ j, raw16386 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16386step0 = (fun i j => raw16386 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16386step0 raw16386; decide +kernel
      have hl : raw16386step0Labels = raw16386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16386 raw16386Labels permutation346 hz
    mixedMoment B raw16386step0 raw16386step0Labels = mixedMoment B raw16386step1 raw16386step1Labels := by
      have ha : raw16386step1 = (fun i j => raw16386step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16386step1 raw16386step0; decide +kernel
      have hl : raw16386step1Labels = raw16386step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16386step0 raw16386step0Labels permutation33 permutation3
    _ = mixedMoment B node4028 node4028Labels := by rfl

def raw16387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw16387Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw16387step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16387step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw16387step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16387 raw16387Labels = mixedMoment B node2855 node2855Labels := by
  calc
    mixedMoment B raw16387 raw16387Labels = mixedMoment B raw16387step0 raw16387step0Labels := by
      have hz : ∀ j, raw16387 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16387step0 = (fun i j => raw16387 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16387step0 raw16387; decide +kernel
      have hl : raw16387step0Labels = raw16387Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16387 raw16387Labels permutation346 hz
    mixedMoment B raw16387step0 raw16387step0Labels = mixedMoment B raw16387step1 raw16387step1Labels := by
      have ha : raw16387step1 = (fun i j => raw16387step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16387step1 raw16387step0; decide +kernel
      have hl : raw16387step1Labels = raw16387step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16387step0 raw16387step0Labels permutation33 permutation3
    _ = mixedMoment B node2855 node2855Labels := by rfl

def raw16388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw16388Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw16388step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw16388step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16388step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw16388step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16388 raw16388Labels = mixedMoment B node3343 node3343Labels := by
  calc
    mixedMoment B raw16388 raw16388Labels = mixedMoment B raw16388step0 raw16388step0Labels := by
      have hz : ∀ j, raw16388 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16388step0 = (fun i j => raw16388 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16388step0 raw16388; decide +kernel
      have hl : raw16388step0Labels = raw16388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16388 raw16388Labels permutation346 hz
    mixedMoment B raw16388step0 raw16388step0Labels = mixedMoment B raw16388step1 raw16388step1Labels := by
      have ha : raw16388step1 = (fun i j => raw16388step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16388step1 raw16388step0; decide +kernel
      have hl : raw16388step1Labels = raw16388step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16388step0 raw16388step0Labels permutation126 permutation3
    mixedMoment B raw16388step1 raw16388step1Labels = mixedMoment B raw16388step2 raw16388step2Labels := by
      have ha : raw16388step2 = -raw16388step1 := by apply Matrix.ext; change ∀ i j, raw16388step2 i j = -(raw16388step1 i j); unfold raw16388step2 raw16388step1; decide +kernel
      have hl : raw16388step2Labels = raw16388step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3343 node3343Labels := by rfl

def raw16389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw16389Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16389step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16389step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16389step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16389 raw16389Labels = mixedMoment B node3342 node3342Labels := by
  calc
    mixedMoment B raw16389 raw16389Labels = mixedMoment B raw16389step0 raw16389step0Labels := by
      have ha : raw16389step0 = (fun i j => raw16389 (permutation589 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16389step0 raw16389; decide +kernel
      have hl : raw16389step0Labels = raw16389Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16389 raw16389Labels permutation589 permutation3
    mixedMoment B raw16389step0 raw16389step0Labels = mixedMoment B raw16389step1 raw16389step1Labels := by
      have ha : raw16389step1 = -raw16389step0 := by apply Matrix.ext; change ∀ i j, raw16389step1 i j = -(raw16389step0 i j); unfold raw16389step1 raw16389step0; decide +kernel
      have hl : raw16389step1Labels = raw16389step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3342 node3342Labels := by rfl

def raw16390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw16390Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw16390step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16390step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw16390step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16390step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16390step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16390 raw16390Labels = mixedMoment B node3359 node3359Labels := by
  calc
    mixedMoment B raw16390 raw16390Labels = mixedMoment B raw16390step0 raw16390step0Labels := by
      have hz : ∀ j, raw16390 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16390step0 = (fun i j => raw16390 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16390step0 raw16390; decide +kernel
      have hl : raw16390step0Labels = raw16390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16390 raw16390Labels permutation346 hz
    mixedMoment B raw16390step0 raw16390step0Labels = mixedMoment B raw16390step1 raw16390step1Labels := by
      have ha : raw16390step1 = (fun i j => raw16390step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16390step1 raw16390step0; decide +kernel
      have hl : raw16390step1Labels = raw16390step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16390step0 raw16390step0Labels permutation125 permutation3
    mixedMoment B raw16390step1 raw16390step1Labels = mixedMoment B raw16390step2 raw16390step2Labels := by
      have ha : raw16390step2 = -raw16390step1 := by apply Matrix.ext; change ∀ i j, raw16390step2 i j = -(raw16390step1 i j); unfold raw16390step2 raw16390step1; decide +kernel
      have hl : raw16390step2Labels = raw16390step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3359 node3359Labels := by rfl

def raw16391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw16391Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw16391step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16391step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16391step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16391step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16391step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16391 raw16391Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw16391 raw16391Labels = mixedMoment B raw16391step0 raw16391step0Labels := by
      have hz : ∀ j, raw16391 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16391step0 = (fun i j => raw16391 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16391step0 raw16391; decide +kernel
      have hl : raw16391step0Labels = raw16391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16391 raw16391Labels permutation346 hz
    mixedMoment B raw16391step0 raw16391step0Labels = mixedMoment B raw16391step1 raw16391step1Labels := by
      have ha : raw16391step1 = (fun i j => raw16391step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16391step1 raw16391step0; decide +kernel
      have hl : raw16391step1Labels = raw16391step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16391step0 raw16391step0Labels permutation127 permutation3
    mixedMoment B raw16391step1 raw16391step1Labels = mixedMoment B raw16391step2 raw16391step2Labels := by
      have ha : raw16391step2 = -raw16391step1 := by apply Matrix.ext; change ∀ i j, raw16391step2 i j = -(raw16391step1 i j); unfold raw16391step2 raw16391step1; decide +kernel
      have hl : raw16391step2Labels = raw16391step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw16392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw16392Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw16392step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16392step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw16392step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16392step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw16392step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16392 raw16392Labels = mixedMoment B node2386 node2386Labels := by
  calc
    mixedMoment B raw16392 raw16392Labels = mixedMoment B raw16392step0 raw16392step0Labels := by
      have hz : ∀ j, raw16392 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16392step0 = (fun i j => raw16392 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16392step0 raw16392; decide +kernel
      have hl : raw16392step0Labels = raw16392Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16392 raw16392Labels permutation346 hz
    mixedMoment B raw16392step0 raw16392step0Labels = mixedMoment B raw16392step1 raw16392step1Labels := by
      have ha : raw16392step1 = (fun i j => raw16392step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16392step1 raw16392step0; decide +kernel
      have hl : raw16392step1Labels = raw16392step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16392step0 raw16392step0Labels permutation151 permutation3
    mixedMoment B raw16392step1 raw16392step1Labels = mixedMoment B raw16392step2 raw16392step2Labels := by
      have ha : raw16392step2 = -raw16392step1 := by apply Matrix.ext; change ∀ i j, raw16392step2 i j = -(raw16392step1 i j); unfold raw16392step2 raw16392step1; decide +kernel
      have hl : raw16392step2Labels = raw16392step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2386 node2386Labels := by rfl

def raw16393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw16393Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw16393step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16393step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw16393step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16393step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw16393step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16393 raw16393Labels = mixedMoment B node2387 node2387Labels := by
  calc
    mixedMoment B raw16393 raw16393Labels = mixedMoment B raw16393step0 raw16393step0Labels := by
      have hz : ∀ j, raw16393 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16393step0 = (fun i j => raw16393 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16393step0 raw16393; decide +kernel
      have hl : raw16393step0Labels = raw16393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16393 raw16393Labels permutation346 hz
    mixedMoment B raw16393step0 raw16393step0Labels = mixedMoment B raw16393step1 raw16393step1Labels := by
      have ha : raw16393step1 = (fun i j => raw16393step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16393step1 raw16393step0; decide +kernel
      have hl : raw16393step1Labels = raw16393step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16393step0 raw16393step0Labels permutation150 permutation3
    mixedMoment B raw16393step1 raw16393step1Labels = mixedMoment B raw16393step2 raw16393step2Labels := by
      have ha : raw16393step2 = -raw16393step1 := by apply Matrix.ext; change ∀ i j, raw16393step2 i j = -(raw16393step1 i j); unfold raw16393step2 raw16393step1; decide +kernel
      have hl : raw16393step2Labels = raw16393step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2387 node2387Labels := by rfl

def raw16394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw16394Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16394step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16394step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16394step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16394 raw16394Labels = mixedMoment B node2384 node2384Labels := by
  calc
    mixedMoment B raw16394 raw16394Labels = mixedMoment B raw16394step0 raw16394step0Labels := by
      have ha : raw16394step0 = (fun i j => raw16394 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16394step0 raw16394; decide +kernel
      have hl : raw16394step0Labels = raw16394Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16394 raw16394Labels permutation688 permutation3
    mixedMoment B raw16394step0 raw16394step0Labels = mixedMoment B raw16394step1 raw16394step1Labels := by
      have ha : raw16394step1 = -raw16394step0 := by apply Matrix.ext; change ∀ i j, raw16394step1 i j = -(raw16394step0 i j); unfold raw16394step1 raw16394step0; decide +kernel
      have hl : raw16394step1Labels = raw16394step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2384 node2384Labels := by rfl

def raw16395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw16395Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw16395step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw16395step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16395step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16395step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16395 raw16395Labels = mixedMoment B node2406 node2406Labels := by
  calc
    mixedMoment B raw16395 raw16395Labels = mixedMoment B raw16395step0 raw16395step0Labels := by
      have hz : ∀ j, raw16395 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16395step0 = (fun i j => raw16395 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16395step0 raw16395; decide +kernel
      have hl : raw16395step0Labels = raw16395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16395 raw16395Labels permutation346 hz
    mixedMoment B raw16395step0 raw16395step0Labels = mixedMoment B raw16395step1 raw16395step1Labels := by
      have ha : raw16395step1 = (fun i j => raw16395step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16395step1 raw16395step0; decide +kernel
      have hl : raw16395step1Labels = raw16395step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16395step0 raw16395step0Labels permutation149 permutation3
    mixedMoment B raw16395step1 raw16395step1Labels = mixedMoment B raw16395step2 raw16395step2Labels := by
      have ha : raw16395step2 = -raw16395step1 := by apply Matrix.ext; change ∀ i j, raw16395step2 i j = -(raw16395step1 i j); unfold raw16395step2 raw16395step1; decide +kernel
      have hl : raw16395step2Labels = raw16395step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2406 node2406Labels := by rfl

def raw16396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw16396Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw16396step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16396step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16396step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16396step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16396step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16396 raw16396Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw16396 raw16396Labels = mixedMoment B raw16396step0 raw16396step0Labels := by
      have hz : ∀ j, raw16396 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16396step0 = (fun i j => raw16396 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16396step0 raw16396; decide +kernel
      have hl : raw16396step0Labels = raw16396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16396 raw16396Labels permutation346 hz
    mixedMoment B raw16396step0 raw16396step0Labels = mixedMoment B raw16396step1 raw16396step1Labels := by
      have ha : raw16396step1 = (fun i j => raw16396step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16396step1 raw16396step0; decide +kernel
      have hl : raw16396step1Labels = raw16396step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16396step0 raw16396step0Labels permutation151 permutation3
    mixedMoment B raw16396step1 raw16396step1Labels = mixedMoment B raw16396step2 raw16396step2Labels := by
      have ha : raw16396step2 = -raw16396step1 := by apply Matrix.ext; change ∀ i j, raw16396step2 i j = -(raw16396step1 i j); unfold raw16396step2 raw16396step1; decide +kernel
      have hl : raw16396step2Labels = raw16396step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2724 node2724Labels := by rfl

def raw16397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16397Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16397step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16397step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16397step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16397step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16397step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16397step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16397 raw16397Labels = mixedMoment B node2591 node2591Labels := by
  calc
    mixedMoment B raw16397 raw16397Labels = mixedMoment B raw16397step0 raw16397step0Labels := by
      have hz : ∀ j, raw16397 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16397step0 = (fun i j => raw16397 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16397step0 raw16397; decide +kernel
      have hl : raw16397step0Labels = raw16397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16397 raw16397Labels permutation346 hz
    mixedMoment B raw16397step0 raw16397step0Labels = mixedMoment B raw16397step1 raw16397step1Labels := by
      have ha : raw16397step1 = (fun i j => raw16397step0 (permutation63 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16397step1 raw16397step0; decide +kernel
      have hl : raw16397step1Labels = raw16397step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16397step0 raw16397step0Labels permutation63 permutation5
    mixedMoment B raw16397step1 raw16397step1Labels = mixedMoment B raw16397step2 raw16397step2Labels := by
      have ha : raw16397step2 = -raw16397step1 := by apply Matrix.ext; change ∀ i j, raw16397step2 i j = -(raw16397step1 i j); unfold raw16397step2 raw16397step1; decide +kernel
      have hl : raw16397step2Labels = raw16397step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16397step2 raw16397step2Labels = mixedMoment B raw16397step3 raw16397step3Labels := by
      have ha : raw16397step3 = raw16397step2 := by apply Matrix.ext; unfold raw16397step3 raw16397step2; decide +kernel
      have hl : raw16397step2Labels = labelEmbedding1 ∘ raw16397step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16397step2 raw16397step2Labels raw16397step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2591 node2591Labels := by rfl

def raw16398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16398Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16398step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16398step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16398step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16398 raw16398Labels = mixedMoment B node3947 node3947Labels := by
  calc
    mixedMoment B raw16398 raw16398Labels = mixedMoment B raw16398step0 raw16398step0Labels := by
      have ha : raw16398step0 = (fun i j => raw16398 (permutation574 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16398step0 raw16398; decide +kernel
      have hl : raw16398step0Labels = raw16398Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16398 raw16398Labels permutation574 permutation5
    mixedMoment B raw16398step0 raw16398step0Labels = mixedMoment B raw16398step1 raw16398step1Labels := by
      have ha : raw16398step1 = raw16398step0 := by apply Matrix.ext; unfold raw16398step1 raw16398step0; decide +kernel
      have hl : raw16398step0Labels = labelEmbedding1 ∘ raw16398step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16398step0 raw16398step0Labels raw16398step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3947 node3947Labels := by rfl

def raw16399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16399Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16399step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16399step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16399step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16399step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16399step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16399step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16399step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16399 raw16399Labels = mixedMoment B node3929 node3929Labels := by
  calc
    mixedMoment B raw16399 raw16399Labels = mixedMoment B raw16399step0 raw16399step0Labels := by
      have hz : ∀ j, raw16399 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16399step0 = (fun i j => raw16399 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16399step0 raw16399; decide +kernel
      have hl : raw16399step0Labels = raw16399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16399 raw16399Labels permutation346 hz
    mixedMoment B raw16399step0 raw16399step0Labels = mixedMoment B raw16399step1 raw16399step1Labels := by
      have ha : raw16399step1 = (fun i j => raw16399step0 (permutation63 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16399step1 raw16399step0; decide +kernel
      have hl : raw16399step1Labels = raw16399step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16399step0 raw16399step0Labels permutation63 permutation5
    mixedMoment B raw16399step1 raw16399step1Labels = mixedMoment B raw16399step2 raw16399step2Labels := by
      have ha : raw16399step2 = -raw16399step1 := by apply Matrix.ext; change ∀ i j, raw16399step2 i j = -(raw16399step1 i j); unfold raw16399step2 raw16399step1; decide +kernel
      have hl : raw16399step2Labels = raw16399step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16399step2 raw16399step2Labels = mixedMoment B raw16399step3 raw16399step3Labels := by
      have ha : raw16399step3 = raw16399step2 := by apply Matrix.ext; unfold raw16399step3 raw16399step2; decide +kernel
      have hl : raw16399step2Labels = labelEmbedding1 ∘ raw16399step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16399step2 raw16399step2Labels raw16399step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3929 node3929Labels := by rfl

def raw16400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16400Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16400step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16400step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16400step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16400step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16400step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16400step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16400 raw16400Labels = mixedMoment B node3997 node3997Labels := by
  calc
    mixedMoment B raw16400 raw16400Labels = mixedMoment B raw16400step0 raw16400step0Labels := by
      have hz : ∀ j, raw16400 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16400step0 = (fun i j => raw16400 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16400step0 raw16400; decide +kernel
      have hl : raw16400step0Labels = raw16400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16400 raw16400Labels permutation346 hz
    mixedMoment B raw16400step0 raw16400step0Labels = mixedMoment B raw16400step1 raw16400step1Labels := by
      have ha : raw16400step1 = (fun i j => raw16400step0 (permutation62 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16400step1 raw16400step0; decide +kernel
      have hl : raw16400step1Labels = raw16400step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16400step0 raw16400step0Labels permutation62 permutation5
    mixedMoment B raw16400step1 raw16400step1Labels = mixedMoment B raw16400step2 raw16400step2Labels := by
      have ha : raw16400step2 = -raw16400step1 := by apply Matrix.ext; change ∀ i j, raw16400step2 i j = -(raw16400step1 i j); unfold raw16400step2 raw16400step1; decide +kernel
      have hl : raw16400step2Labels = raw16400step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16400step2 raw16400step2Labels = mixedMoment B raw16400step3 raw16400step3Labels := by
      have ha : raw16400step3 = raw16400step2 := by apply Matrix.ext; unfold raw16400step3 raw16400step2; decide +kernel
      have hl : raw16400step2Labels = labelEmbedding1 ∘ raw16400step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16400step2 raw16400step2Labels raw16400step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3997 node3997Labels := by rfl

def raw16401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16401Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16401step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16401step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16401step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16401step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16401step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16401step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16401step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16401 raw16401Labels = mixedMoment B node3995 node3995Labels := by
  calc
    mixedMoment B raw16401 raw16401Labels = mixedMoment B raw16401step0 raw16401step0Labels := by
      have hz : ∀ j, raw16401 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16401step0 = (fun i j => raw16401 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16401step0 raw16401; decide +kernel
      have hl : raw16401step0Labels = raw16401Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16401 raw16401Labels permutation346 hz
    mixedMoment B raw16401step0 raw16401step0Labels = mixedMoment B raw16401step1 raw16401step1Labels := by
      have ha : raw16401step1 = (fun i j => raw16401step0 (permutation66 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16401step1 raw16401step0; decide +kernel
      have hl : raw16401step1Labels = raw16401step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16401step0 raw16401step0Labels permutation66 permutation5
    mixedMoment B raw16401step1 raw16401step1Labels = mixedMoment B raw16401step2 raw16401step2Labels := by
      have ha : raw16401step2 = -raw16401step1 := by apply Matrix.ext; change ∀ i j, raw16401step2 i j = -(raw16401step1 i j); unfold raw16401step2 raw16401step1; decide +kernel
      have hl : raw16401step2Labels = raw16401step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16401step2 raw16401step2Labels = mixedMoment B raw16401step3 raw16401step3Labels := by
      have ha : raw16401step3 = raw16401step2 := by apply Matrix.ext; unfold raw16401step3 raw16401step2; decide +kernel
      have hl : raw16401step2Labels = labelEmbedding1 ∘ raw16401step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16401step2 raw16401step2Labels raw16401step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3995 node3995Labels := by rfl

def raw16402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16402Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16402step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw16402step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16402step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16402step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16402step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16402step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16402 raw16402Labels = mixedMoment B node3580 node3580Labels := by
  calc
    mixedMoment B raw16402 raw16402Labels = mixedMoment B raw16402step0 raw16402step0Labels := by
      have hz : ∀ j, raw16402 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16402step0 = (fun i j => raw16402 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16402step0 raw16402; decide +kernel
      have hl : raw16402step0Labels = raw16402Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16402 raw16402Labels permutation346 hz
    mixedMoment B raw16402step0 raw16402step0Labels = mixedMoment B raw16402step1 raw16402step1Labels := by
      have ha : raw16402step1 = (fun i j => raw16402step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16402step1 raw16402step0; decide +kernel
      have hl : raw16402step1Labels = raw16402step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16402step0 raw16402step0Labels permutation44 permutation7
    mixedMoment B raw16402step1 raw16402step1Labels = mixedMoment B raw16402step2 raw16402step2Labels := by
      have ha : raw16402step2 = -raw16402step1 := by apply Matrix.ext; change ∀ i j, raw16402step2 i j = -(raw16402step1 i j); unfold raw16402step2 raw16402step1; decide +kernel
      have hl : raw16402step2Labels = raw16402step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16402step2 raw16402step2Labels = mixedMoment B raw16402step3 raw16402step3Labels := by
      have ha : raw16402step3 = raw16402step2 := by apply Matrix.ext; unfold raw16402step3 raw16402step2; decide +kernel
      have hl : raw16402step2Labels = labelEmbedding1 ∘ raw16402step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16402step2 raw16402step2Labels raw16402step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3580 node3580Labels := by rfl

def raw16403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16403Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16403step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw16403step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16403step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16403step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16403step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16403step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16403 raw16403Labels = mixedMoment B node3874 node3874Labels := by
  calc
    mixedMoment B raw16403 raw16403Labels = mixedMoment B raw16403step0 raw16403step0Labels := by
      have ha : raw16403step0 = (fun i j => raw16403 (permutation230 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16403step0 raw16403; decide +kernel
      have hl : raw16403step0Labels = raw16403Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16403 raw16403Labels permutation230 permutation7
    mixedMoment B raw16403step0 raw16403step0Labels = mixedMoment B raw16403step1 raw16403step1Labels := by
      have ha : raw16403step1 = -raw16403step0 := by apply Matrix.ext; change ∀ i j, raw16403step1 i j = -(raw16403step0 i j); unfold raw16403step1 raw16403step0; decide +kernel
      have hl : raw16403step1Labels = raw16403step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16403step1 raw16403step1Labels = mixedMoment B raw16403step2 raw16403step2Labels := by
      have ha : raw16403step2 = raw16403step1 := by apply Matrix.ext; unfold raw16403step2 raw16403step1; decide +kernel
      have hl : raw16403step1Labels = labelEmbedding1 ∘ raw16403step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16403step1 raw16403step1Labels raw16403step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3874 node3874Labels := by rfl

def raw16404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16404Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16404step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16404step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16404step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16404step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16404step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16404step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16404step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16404 raw16404Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw16404 raw16404Labels = mixedMoment B raw16404step0 raw16404step0Labels := by
      have hz : ∀ j, raw16404 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16404step0 = (fun i j => raw16404 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16404step0 raw16404; decide +kernel
      have hl : raw16404step0Labels = raw16404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16404 raw16404Labels permutation346 hz
    mixedMoment B raw16404step0 raw16404step0Labels = mixedMoment B raw16404step1 raw16404step1Labels := by
      have ha : raw16404step1 = (fun i j => raw16404step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16404step1 raw16404step0; decide +kernel
      have hl : raw16404step1Labels = raw16404step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16404step0 raw16404step0Labels permutation46 permutation7
    mixedMoment B raw16404step1 raw16404step1Labels = mixedMoment B raw16404step2 raw16404step2Labels := by
      have ha : raw16404step2 = -raw16404step1 := by apply Matrix.ext; change ∀ i j, raw16404step2 i j = -(raw16404step1 i j); unfold raw16404step2 raw16404step1; decide +kernel
      have hl : raw16404step2Labels = raw16404step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16404step2 raw16404step2Labels = mixedMoment B raw16404step3 raw16404step3Labels := by
      have ha : raw16404step3 = raw16404step2 := by apply Matrix.ext; unfold raw16404step3 raw16404step2; decide +kernel
      have hl : raw16404step2Labels = labelEmbedding1 ∘ raw16404step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16404step2 raw16404step2Labels raw16404step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3884 node3884Labels := by rfl

def raw16405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16405Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16405step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16405step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw16405step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16405step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16405step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16405step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16405step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16405 raw16405Labels = mixedMoment B node3858 node3858Labels := by
  calc
    mixedMoment B raw16405 raw16405Labels = mixedMoment B raw16405step0 raw16405step0Labels := by
      have hz : ∀ j, raw16405 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16405step0 = (fun i j => raw16405 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16405step0 raw16405; decide +kernel
      have hl : raw16405step0Labels = raw16405Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16405 raw16405Labels permutation346 hz
    mixedMoment B raw16405step0 raw16405step0Labels = mixedMoment B raw16405step1 raw16405step1Labels := by
      have ha : raw16405step1 = (fun i j => raw16405step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16405step1 raw16405step0; decide +kernel
      have hl : raw16405step1Labels = raw16405step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16405step0 raw16405step0Labels permutation44 permutation7
    mixedMoment B raw16405step1 raw16405step1Labels = mixedMoment B raw16405step2 raw16405step2Labels := by
      have ha : raw16405step2 = -raw16405step1 := by apply Matrix.ext; change ∀ i j, raw16405step2 i j = -(raw16405step1 i j); unfold raw16405step2 raw16405step1; decide +kernel
      have hl : raw16405step2Labels = raw16405step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16405step2 raw16405step2Labels = mixedMoment B raw16405step3 raw16405step3Labels := by
      have ha : raw16405step3 = raw16405step2 := by apply Matrix.ext; unfold raw16405step3 raw16405step2; decide +kernel
      have hl : raw16405step2Labels = labelEmbedding1 ∘ raw16405step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16405step2 raw16405step2Labels raw16405step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3858 node3858Labels := by rfl

def raw16406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16406Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16406step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16406step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw16406step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16406step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16406step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16406step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16406step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16406 raw16406Labels = mixedMoment B node3887 node3887Labels := by
  calc
    mixedMoment B raw16406 raw16406Labels = mixedMoment B raw16406step0 raw16406step0Labels := by
      have hz : ∀ j, raw16406 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16406step0 = (fun i j => raw16406 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16406step0 raw16406; decide +kernel
      have hl : raw16406step0Labels = raw16406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16406 raw16406Labels permutation346 hz
    mixedMoment B raw16406step0 raw16406step0Labels = mixedMoment B raw16406step1 raw16406step1Labels := by
      have ha : raw16406step1 = (fun i j => raw16406step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16406step1 raw16406step0; decide +kernel
      have hl : raw16406step1Labels = raw16406step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16406step0 raw16406step0Labels permutation44 permutation7
    mixedMoment B raw16406step1 raw16406step1Labels = mixedMoment B raw16406step2 raw16406step2Labels := by
      have ha : raw16406step2 = -raw16406step1 := by apply Matrix.ext; change ∀ i j, raw16406step2 i j = -(raw16406step1 i j); unfold raw16406step2 raw16406step1; decide +kernel
      have hl : raw16406step2Labels = raw16406step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16406step2 raw16406step2Labels = mixedMoment B raw16406step3 raw16406step3Labels := by
      have ha : raw16406step3 = raw16406step2 := by apply Matrix.ext; unfold raw16406step3 raw16406step2; decide +kernel
      have hl : raw16406step2Labels = labelEmbedding1 ∘ raw16406step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16406step2 raw16406step2Labels raw16406step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3887 node3887Labels := by rfl

def raw16407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16407Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16407step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16407step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16407step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16407step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16407step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16407 raw16407Labels = mixedMoment B node3568 node3568Labels := by
  calc
    mixedMoment B raw16407 raw16407Labels = mixedMoment B raw16407step0 raw16407step0Labels := by
      have ha : raw16407step0 = (fun i j => raw16407 (permutation230 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16407step0 raw16407; decide +kernel
      have hl : raw16407step0Labels = raw16407Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16407 raw16407Labels permutation230 permutation7
    mixedMoment B raw16407step0 raw16407step0Labels = mixedMoment B raw16407step1 raw16407step1Labels := by
      have ha : raw16407step1 = -raw16407step0 := by apply Matrix.ext; change ∀ i j, raw16407step1 i j = -(raw16407step0 i j); unfold raw16407step1 raw16407step0; decide +kernel
      have hl : raw16407step1Labels = raw16407step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16407step1 raw16407step1Labels = mixedMoment B raw16407step2 raw16407step2Labels := by
      have ha : raw16407step2 = raw16407step1 := by apply Matrix.ext; unfold raw16407step2 raw16407step1; decide +kernel
      have hl : raw16407step1Labels = labelEmbedding1 ∘ raw16407step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16407step1 raw16407step1Labels raw16407step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3568 node3568Labels := by rfl

def raw16408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16408Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16408step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16408step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16408step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16408step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16408step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16408 raw16408Labels = mixedMoment B node2537 node2537Labels := by
  calc
    mixedMoment B raw16408 raw16408Labels = mixedMoment B raw16408step0 raw16408step0Labels := by
      have ha : raw16408step0 = (fun i j => raw16408 (permutation306 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16408step0 raw16408; decide +kernel
      have hl : raw16408step0Labels = raw16408Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16408 raw16408Labels permutation306 permutation5
    mixedMoment B raw16408step0 raw16408step0Labels = mixedMoment B raw16408step1 raw16408step1Labels := by
      have ha : raw16408step1 = -raw16408step0 := by apply Matrix.ext; change ∀ i j, raw16408step1 i j = -(raw16408step0 i j); unfold raw16408step1 raw16408step0; decide +kernel
      have hl : raw16408step1Labels = raw16408step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16408step1 raw16408step1Labels = mixedMoment B raw16408step2 raw16408step2Labels := by
      have ha : raw16408step2 = raw16408step1 := by apply Matrix.ext; unfold raw16408step2 raw16408step1; decide +kernel
      have hl : raw16408step1Labels = labelEmbedding1 ∘ raw16408step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16408step1 raw16408step1Labels raw16408step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2537 node2537Labels := by rfl

def raw16409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16409Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16409step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 2, -1], ![-1, -1, 2]]
def raw16409step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16409step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw16409step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16409step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw16409step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16409 raw16409Labels = mixedMoment B node3879 node3879Labels := by
  calc
    mixedMoment B raw16409 raw16409Labels = mixedMoment B raw16409step0 raw16409step0Labels := by
      have ha : raw16409step0 = (fun i j => raw16409 (permutation230 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16409step0 raw16409; decide +kernel
      have hl : raw16409step0Labels = raw16409Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16409 raw16409Labels permutation230 permutation7
    mixedMoment B raw16409step0 raw16409step0Labels = mixedMoment B raw16409step1 raw16409step1Labels := by
      have ha : raw16409step1 = -raw16409step0 := by apply Matrix.ext; change ∀ i j, raw16409step1 i j = -(raw16409step0 i j); unfold raw16409step1 raw16409step0; decide +kernel
      have hl : raw16409step1Labels = raw16409step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16409step1 raw16409step1Labels = mixedMoment B raw16409step2 raw16409step2Labels := by
      have ha : raw16409step2 = raw16409step1 := by apply Matrix.ext; unfold raw16409step2 raw16409step1; decide +kernel
      have hl : raw16409step1Labels = labelEmbedding1 ∘ raw16409step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16409step1 raw16409step1Labels raw16409step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3879 node3879Labels := by rfl

def raw16410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16410Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16410step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16410step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16410step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16410step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16410step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16410 raw16410Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw16410 raw16410Labels = mixedMoment B raw16410step0 raw16410step0Labels := by
      have ha : raw16410step0 = (fun i j => raw16410 (permutation230 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16410step0 raw16410; decide +kernel
      have hl : raw16410step0Labels = raw16410Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16410 raw16410Labels permutation230 permutation7
    mixedMoment B raw16410step0 raw16410step0Labels = mixedMoment B raw16410step1 raw16410step1Labels := by
      have ha : raw16410step1 = -raw16410step0 := by apply Matrix.ext; change ∀ i j, raw16410step1 i j = -(raw16410step0 i j); unfold raw16410step1 raw16410step0; decide +kernel
      have hl : raw16410step1Labels = raw16410step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16410step1 raw16410step1Labels = mixedMoment B raw16410step2 raw16410step2Labels := by
      have ha : raw16410step2 = raw16410step1 := by apply Matrix.ext; unfold raw16410step2 raw16410step1; decide +kernel
      have hl : raw16410step1Labels = labelEmbedding1 ∘ raw16410step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16410step1 raw16410step1Labels raw16410step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw16411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16411Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw16411step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16411step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16411step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16411step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16411step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16411 raw16411Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw16411 raw16411Labels = mixedMoment B raw16411step0 raw16411step0Labels := by
      have ha : raw16411step0 = (fun i j => raw16411 (permutation230 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16411step0 raw16411; decide +kernel
      have hl : raw16411step0Labels = raw16411Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16411 raw16411Labels permutation230 permutation7
    mixedMoment B raw16411step0 raw16411step0Labels = mixedMoment B raw16411step1 raw16411step1Labels := by
      have ha : raw16411step1 = -raw16411step0 := by apply Matrix.ext; change ∀ i j, raw16411step1 i j = -(raw16411step0 i j); unfold raw16411step1 raw16411step0; decide +kernel
      have hl : raw16411step1Labels = raw16411step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16411step1 raw16411step1Labels = mixedMoment B raw16411step2 raw16411step2Labels := by
      have ha : raw16411step2 = raw16411step1 := by apply Matrix.ext; unfold raw16411step2 raw16411step1; decide +kernel
      have hl : raw16411step1Labels = labelEmbedding1 ∘ raw16411step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16411step1 raw16411step1Labels raw16411step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3880 node3880Labels := by rfl

def raw16412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16412Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16412step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16412step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16412step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16412step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16412step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16412step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16412step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16412 raw16412Labels = mixedMoment B node3578 node3578Labels := by
  calc
    mixedMoment B raw16412 raw16412Labels = mixedMoment B raw16412step0 raw16412step0Labels := by
      have hz : ∀ j, raw16412 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16412step0 = (fun i j => raw16412 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16412step0 raw16412; decide +kernel
      have hl : raw16412step0Labels = raw16412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16412 raw16412Labels permutation346 hz
    mixedMoment B raw16412step0 raw16412step0Labels = mixedMoment B raw16412step1 raw16412step1Labels := by
      have ha : raw16412step1 = (fun i j => raw16412step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16412step1 raw16412step0; decide +kernel
      have hl : raw16412step1Labels = raw16412step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16412step0 raw16412step0Labels permutation44 permutation7
    mixedMoment B raw16412step1 raw16412step1Labels = mixedMoment B raw16412step2 raw16412step2Labels := by
      have ha : raw16412step2 = -raw16412step1 := by apply Matrix.ext; change ∀ i j, raw16412step2 i j = -(raw16412step1 i j); unfold raw16412step2 raw16412step1; decide +kernel
      have hl : raw16412step2Labels = raw16412step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16412step2 raw16412step2Labels = mixedMoment B raw16412step3 raw16412step3Labels := by
      have ha : raw16412step3 = raw16412step2 := by apply Matrix.ext; unfold raw16412step3 raw16412step2; decide +kernel
      have hl : raw16412step2Labels = labelEmbedding1 ∘ raw16412step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16412step2 raw16412step2Labels raw16412step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3578 node3578Labels := by rfl

def raw16413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16413Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16413step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16413step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16413step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16413step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16413step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16413step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16413step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16413 raw16413Labels = mixedMoment B node2673 node2673Labels := by
  calc
    mixedMoment B raw16413 raw16413Labels = mixedMoment B raw16413step0 raw16413step0Labels := by
      have hz : ∀ j, raw16413 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16413step0 = (fun i j => raw16413 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16413step0 raw16413; decide +kernel
      have hl : raw16413step0Labels = raw16413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16413 raw16413Labels permutation346 hz
    mixedMoment B raw16413step0 raw16413step0Labels = mixedMoment B raw16413step1 raw16413step1Labels := by
      have ha : raw16413step1 = (fun i j => raw16413step0 (permutation57 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16413step1 raw16413step0; decide +kernel
      have hl : raw16413step1Labels = raw16413step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16413step0 raw16413step0Labels permutation57 permutation5
    mixedMoment B raw16413step1 raw16413step1Labels = mixedMoment B raw16413step2 raw16413step2Labels := by
      have ha : raw16413step2 = -raw16413step1 := by apply Matrix.ext; change ∀ i j, raw16413step2 i j = -(raw16413step1 i j); unfold raw16413step2 raw16413step1; decide +kernel
      have hl : raw16413step2Labels = raw16413step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16413step2 raw16413step2Labels = mixedMoment B raw16413step3 raw16413step3Labels := by
      have ha : raw16413step3 = raw16413step2 := by apply Matrix.ext; unfold raw16413step3 raw16413step2; decide +kernel
      have hl : raw16413step2Labels = labelEmbedding1 ∘ raw16413step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16413step2 raw16413step2Labels raw16413step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2673 node2673Labels := by rfl

def raw16414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16414Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16414step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16414step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16414step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16414step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16414step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16414 raw16414Labels = mixedMoment B node3873 node3873Labels := by
  calc
    mixedMoment B raw16414 raw16414Labels = mixedMoment B raw16414step0 raw16414step0Labels := by
      have ha : raw16414step0 = (fun i j => raw16414 (permutation230 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16414step0 raw16414; decide +kernel
      have hl : raw16414step0Labels = raw16414Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16414 raw16414Labels permutation230 permutation7
    mixedMoment B raw16414step0 raw16414step0Labels = mixedMoment B raw16414step1 raw16414step1Labels := by
      have ha : raw16414step1 = -raw16414step0 := by apply Matrix.ext; change ∀ i j, raw16414step1 i j = -(raw16414step0 i j); unfold raw16414step1 raw16414step0; decide +kernel
      have hl : raw16414step1Labels = raw16414step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16414step1 raw16414step1Labels = mixedMoment B raw16414step2 raw16414step2Labels := by
      have ha : raw16414step2 = raw16414step1 := by apply Matrix.ext; unfold raw16414step2 raw16414step1; decide +kernel
      have hl : raw16414step1Labels = labelEmbedding1 ∘ raw16414step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16414step1 raw16414step1Labels raw16414step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3873 node3873Labels := by rfl

def raw16415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16415Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16415step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16415step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16415step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16415step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16415step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16415step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16415step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16415 raw16415Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw16415 raw16415Labels = mixedMoment B raw16415step0 raw16415step0Labels := by
      have hz : ∀ j, raw16415 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16415step0 = (fun i j => raw16415 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16415step0 raw16415; decide +kernel
      have hl : raw16415step0Labels = raw16415Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16415 raw16415Labels permutation346 hz
    mixedMoment B raw16415step0 raw16415step0Labels = mixedMoment B raw16415step1 raw16415step1Labels := by
      have ha : raw16415step1 = (fun i j => raw16415step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16415step1 raw16415step0; decide +kernel
      have hl : raw16415step1Labels = raw16415step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16415step0 raw16415step0Labels permutation44 permutation7
    mixedMoment B raw16415step1 raw16415step1Labels = mixedMoment B raw16415step2 raw16415step2Labels := by
      have ha : raw16415step2 = -raw16415step1 := by apply Matrix.ext; change ∀ i j, raw16415step2 i j = -(raw16415step1 i j); unfold raw16415step2 raw16415step1; decide +kernel
      have hl : raw16415step2Labels = raw16415step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16415step2 raw16415step2Labels = mixedMoment B raw16415step3 raw16415step3Labels := by
      have ha : raw16415step3 = raw16415step2 := by apply Matrix.ext; unfold raw16415step3 raw16415step2; decide +kernel
      have hl : raw16415step2Labels = labelEmbedding1 ∘ raw16415step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16415step2 raw16415step2Labels raw16415step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3857 node3857Labels := by rfl

def raw16416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16416Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16416step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16416step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw16416step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16416step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16416step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16416step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16416step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16416 raw16416Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw16416 raw16416Labels = mixedMoment B raw16416step0 raw16416step0Labels := by
      have hz : ∀ j, raw16416 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16416step0 = (fun i j => raw16416 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16416step0 raw16416; decide +kernel
      have hl : raw16416step0Labels = raw16416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16416 raw16416Labels permutation346 hz
    mixedMoment B raw16416step0 raw16416step0Labels = mixedMoment B raw16416step1 raw16416step1Labels := by
      have ha : raw16416step1 = (fun i j => raw16416step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16416step1 raw16416step0; decide +kernel
      have hl : raw16416step1Labels = raw16416step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16416step0 raw16416step0Labels permutation44 permutation7
    mixedMoment B raw16416step1 raw16416step1Labels = mixedMoment B raw16416step2 raw16416step2Labels := by
      have ha : raw16416step2 = -raw16416step1 := by apply Matrix.ext; change ∀ i j, raw16416step2 i j = -(raw16416step1 i j); unfold raw16416step2 raw16416step1; decide +kernel
      have hl : raw16416step2Labels = raw16416step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16416step2 raw16416step2Labels = mixedMoment B raw16416step3 raw16416step3Labels := by
      have ha : raw16416step3 = raw16416step2 := by apply Matrix.ext; unfold raw16416step3 raw16416step2; decide +kernel
      have hl : raw16416step2Labels = labelEmbedding1 ∘ raw16416step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16416step2 raw16416step2Labels raw16416step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3885 node3885Labels := by rfl

def raw16417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw16417Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw16417step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16417step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw16417step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16417step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw16417step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16417 raw16417Labels = mixedMoment B node2401 node2401Labels := by
  calc
    mixedMoment B raw16417 raw16417Labels = mixedMoment B raw16417step0 raw16417step0Labels := by
      have hz : ∀ j, raw16417 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16417step0 = (fun i j => raw16417 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16417step0 raw16417; decide +kernel
      have hl : raw16417step0Labels = raw16417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16417 raw16417Labels permutation346 hz
    mixedMoment B raw16417step0 raw16417step0Labels = mixedMoment B raw16417step1 raw16417step1Labels := by
      have ha : raw16417step1 = (fun i j => raw16417step0 (permutation126 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16417step1 raw16417step0; decide +kernel
      have hl : raw16417step1Labels = raw16417step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16417step0 raw16417step0Labels permutation126 permutation5
    mixedMoment B raw16417step1 raw16417step1Labels = mixedMoment B raw16417step2 raw16417step2Labels := by
      have ha : raw16417step2 = raw16417step1 := by apply Matrix.ext; unfold raw16417step2 raw16417step1; decide +kernel
      have hl : raw16417step1Labels = labelEmbedding1 ∘ raw16417step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16417step1 raw16417step1Labels raw16417step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2401 node2401Labels := by rfl

def raw16418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw16418Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw16418step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw16418step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16418step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw16418step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16418 raw16418Labels = mixedMoment B node2391 node2391Labels := by
  calc
    mixedMoment B raw16418 raw16418Labels = mixedMoment B raw16418step0 raw16418step0Labels := by
      have hz : ∀ j, raw16418 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16418step0 = (fun i j => raw16418 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16418step0 raw16418; decide +kernel
      have hl : raw16418step0Labels = raw16418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16418 raw16418Labels permutation346 hz
    mixedMoment B raw16418step0 raw16418step0Labels = mixedMoment B raw16418step1 raw16418step1Labels := by
      have ha : raw16418step1 = (fun i j => raw16418step0 (permutation123 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16418step1 raw16418step0; decide +kernel
      have hl : raw16418step1Labels = raw16418step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16418step0 raw16418step0Labels permutation123 permutation5
    mixedMoment B raw16418step1 raw16418step1Labels = mixedMoment B raw16418step2 raw16418step2Labels := by
      have ha : raw16418step2 = raw16418step1 := by apply Matrix.ext; unfold raw16418step2 raw16418step1; decide +kernel
      have hl : raw16418step1Labels = labelEmbedding1 ∘ raw16418step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16418step1 raw16418step1Labels raw16418step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2391 node2391Labels := by rfl

def raw16419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw16419Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16419step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16419step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16419step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16419 raw16419Labels = mixedMoment B node2390 node2390Labels := by
  calc
    mixedMoment B raw16419 raw16419Labels = mixedMoment B raw16419step0 raw16419step0Labels := by
      have ha : raw16419step0 = (fun i j => raw16419 (permutation574 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16419step0 raw16419; decide +kernel
      have hl : raw16419step0Labels = raw16419Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16419 raw16419Labels permutation574 permutation5
    mixedMoment B raw16419step0 raw16419step0Labels = mixedMoment B raw16419step1 raw16419step1Labels := by
      have ha : raw16419step1 = raw16419step0 := by apply Matrix.ext; unfold raw16419step1 raw16419step0; decide +kernel
      have hl : raw16419step0Labels = labelEmbedding1 ∘ raw16419step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16419step0 raw16419step0Labels raw16419step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2390 node2390Labels := by rfl

def raw16420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw16420Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw16420step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw16420step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16420step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw16420step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16420 raw16420Labels = mixedMoment B node2395 node2395Labels := by
  calc
    mixedMoment B raw16420 raw16420Labels = mixedMoment B raw16420step0 raw16420step0Labels := by
      have hz : ∀ j, raw16420 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16420step0 = (fun i j => raw16420 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16420step0 raw16420; decide +kernel
      have hl : raw16420step0Labels = raw16420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16420 raw16420Labels permutation346 hz
    mixedMoment B raw16420step0 raw16420step0Labels = mixedMoment B raw16420step1 raw16420step1Labels := by
      have ha : raw16420step1 = (fun i j => raw16420step0 (permutation122 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16420step1 raw16420step0; decide +kernel
      have hl : raw16420step1Labels = raw16420step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16420step0 raw16420step0Labels permutation122 permutation5
    mixedMoment B raw16420step1 raw16420step1Labels = mixedMoment B raw16420step2 raw16420step2Labels := by
      have ha : raw16420step2 = raw16420step1 := by apply Matrix.ext; unfold raw16420step2 raw16420step1; decide +kernel
      have hl : raw16420step1Labels = labelEmbedding1 ∘ raw16420step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16420step1 raw16420step1Labels raw16420step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2395 node2395Labels := by rfl

def raw16421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw16421Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw16421step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16421step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16421step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16421step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16421step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16421 raw16421Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw16421 raw16421Labels = mixedMoment B raw16421step0 raw16421step0Labels := by
      have hz : ∀ j, raw16421 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16421step0 = (fun i j => raw16421 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16421step0 raw16421; decide +kernel
      have hl : raw16421step0Labels = raw16421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16421 raw16421Labels permutation346 hz
    mixedMoment B raw16421step0 raw16421step0Labels = mixedMoment B raw16421step1 raw16421step1Labels := by
      have ha : raw16421step1 = (fun i j => raw16421step0 (permutation123 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16421step1 raw16421step0; decide +kernel
      have hl : raw16421step1Labels = raw16421step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16421step0 raw16421step0Labels permutation123 permutation5
    mixedMoment B raw16421step1 raw16421step1Labels = mixedMoment B raw16421step2 raw16421step2Labels := by
      have ha : raw16421step2 = raw16421step1 := by apply Matrix.ext; unfold raw16421step2 raw16421step1; decide +kernel
      have hl : raw16421step1Labels = labelEmbedding1 ∘ raw16421step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16421step1 raw16421step1Labels raw16421step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2731 node2731Labels := by rfl

def raw16422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw16422Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw16422step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16422step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw16422step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16422step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw16422step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16422 raw16422Labels = mixedMoment B node3355 node3355Labels := by
  calc
    mixedMoment B raw16422 raw16422Labels = mixedMoment B raw16422step0 raw16422step0Labels := by
      have hz : ∀ j, raw16422 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16422step0 = (fun i j => raw16422 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16422step0 raw16422; decide +kernel
      have hl : raw16422step0Labels = raw16422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16422 raw16422Labels permutation346 hz
    mixedMoment B raw16422step0 raw16422step0Labels = mixedMoment B raw16422step1 raw16422step1Labels := by
      have ha : raw16422step1 = (fun i j => raw16422step0 (permutation150 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16422step1 raw16422step0; decide +kernel
      have hl : raw16422step1Labels = raw16422step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16422step0 raw16422step0Labels permutation150 permutation5
    mixedMoment B raw16422step1 raw16422step1Labels = mixedMoment B raw16422step2 raw16422step2Labels := by
      have ha : raw16422step2 = raw16422step1 := by apply Matrix.ext; unfold raw16422step2 raw16422step1; decide +kernel
      have hl : raw16422step1Labels = labelEmbedding1 ∘ raw16422step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16422step1 raw16422step1Labels raw16422step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3355 node3355Labels := by rfl

def raw16423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw16423Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw16423step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16423step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-2, 1, 1], ![-2, -1, 3]]
def raw16423step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16423step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw16423step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16423step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw16423step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16423 raw16423Labels = mixedMoment B node2538 node2538Labels := by
  calc
    mixedMoment B raw16423 raw16423Labels = mixedMoment B raw16423step0 raw16423step0Labels := by
      have hz : ∀ j, raw16423 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16423step0 = (fun i j => raw16423 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16423step0 raw16423; decide +kernel
      have hl : raw16423step0Labels = raw16423Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16423 raw16423Labels permutation346 hz
    mixedMoment B raw16423step0 raw16423step0Labels = mixedMoment B raw16423step1 raw16423step1Labels := by
      have ha : raw16423step1 = (fun i j => raw16423step0 (permutation62 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16423step1 raw16423step0; decide +kernel
      have hl : raw16423step1Labels = raw16423step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16423step0 raw16423step0Labels permutation62 permutation5
    mixedMoment B raw16423step1 raw16423step1Labels = mixedMoment B raw16423step2 raw16423step2Labels := by
      have ha : raw16423step2 = -raw16423step1 := by apply Matrix.ext; change ∀ i j, raw16423step2 i j = -(raw16423step1 i j); unfold raw16423step2 raw16423step1; decide +kernel
      have hl : raw16423step2Labels = raw16423step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16423step2 raw16423step2Labels = mixedMoment B raw16423step3 raw16423step3Labels := by
      have ha : raw16423step3 = raw16423step2 := by apply Matrix.ext; unfold raw16423step3 raw16423step2; decide +kernel
      have hl : raw16423step2Labels = labelEmbedding1 ∘ raw16423step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16423step2 raw16423step2Labels raw16423step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2538 node2538Labels := by rfl

def raw16424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw16424Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16424step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16424step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16424step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16424 raw16424Labels = mixedMoment B node3346 node3346Labels := by
  calc
    mixedMoment B raw16424 raw16424Labels = mixedMoment B raw16424step0 raw16424step0Labels := by
      have ha : raw16424step0 = (fun i j => raw16424 (permutation670 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16424step0 raw16424; decide +kernel
      have hl : raw16424step0Labels = raw16424Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16424 raw16424Labels permutation670 permutation5
    mixedMoment B raw16424step0 raw16424step0Labels = mixedMoment B raw16424step1 raw16424step1Labels := by
      have ha : raw16424step1 = raw16424step0 := by apply Matrix.ext; unfold raw16424step1 raw16424step0; decide +kernel
      have hl : raw16424step0Labels = labelEmbedding1 ∘ raw16424step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16424step0 raw16424step0Labels raw16424step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3346 node3346Labels := by rfl

def raw16425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw16425Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw16425step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw16425step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16425step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw16425step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16425 raw16425Labels = mixedMoment B node3349 node3349Labels := by
  calc
    mixedMoment B raw16425 raw16425Labels = mixedMoment B raw16425step0 raw16425step0Labels := by
      have hz : ∀ j, raw16425 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16425step0 = (fun i j => raw16425 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16425step0 raw16425; decide +kernel
      have hl : raw16425step0Labels = raw16425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16425 raw16425Labels permutation346 hz
    mixedMoment B raw16425step0 raw16425step0Labels = mixedMoment B raw16425step1 raw16425step1Labels := by
      have ha : raw16425step1 = (fun i j => raw16425step0 (permutation146 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16425step1 raw16425step0; decide +kernel
      have hl : raw16425step1Labels = raw16425step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16425step0 raw16425step0Labels permutation146 permutation5
    mixedMoment B raw16425step1 raw16425step1Labels = mixedMoment B raw16425step2 raw16425step2Labels := by
      have ha : raw16425step2 = raw16425step1 := by apply Matrix.ext; unfold raw16425step2 raw16425step1; decide +kernel
      have hl : raw16425step1Labels = labelEmbedding1 ∘ raw16425step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16425step1 raw16425step1Labels raw16425step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3349 node3349Labels := by rfl

def raw16426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw16426Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw16426step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16426step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16426step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16426step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16426step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16426 raw16426Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw16426 raw16426Labels = mixedMoment B raw16426step0 raw16426step0Labels := by
      have hz : ∀ j, raw16426 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16426step0 = (fun i j => raw16426 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16426step0 raw16426; decide +kernel
      have hl : raw16426step0Labels = raw16426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16426 raw16426Labels permutation346 hz
    mixedMoment B raw16426step0 raw16426step0Labels = mixedMoment B raw16426step1 raw16426step1Labels := by
      have ha : raw16426step1 = (fun i j => raw16426step0 (permutation147 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16426step1 raw16426step0; decide +kernel
      have hl : raw16426step1Labels = raw16426step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16426step0 raw16426step0Labels permutation147 permutation5
    mixedMoment B raw16426step1 raw16426step1Labels = mixedMoment B raw16426step2 raw16426step2Labels := by
      have ha : raw16426step2 = raw16426step1 := by apply Matrix.ext; unfold raw16426step2 raw16426step1; decide +kernel
      have hl : raw16426step1Labels = labelEmbedding1 ∘ raw16426step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16426step1 raw16426step1Labels raw16426step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

def raw16427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16427Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16427step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16427 raw16427Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw16427 raw16427Labels = mixedMoment B raw16427step0 raw16427step0Labels := by
      have hz : ∀ j, raw16427 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16427step0 = (fun i j => raw16427 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16427step0 raw16427; decide +kernel
      have hl : raw16427step0Labels = raw16427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16427 raw16427Labels permutation346 hz
    _ = mixedMoment B node3881 node3881Labels := by rfl

def raw16428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16428Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16428step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16428step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16428step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16428step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16428step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16428 raw16428Labels = mixedMoment B node2955 node2955Labels := by
  calc
    mixedMoment B raw16428 raw16428Labels = mixedMoment B raw16428step0 raw16428step0Labels := by
      have hz : ∀ j, raw16428 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16428step0 = (fun i j => raw16428 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16428step0 raw16428; decide +kernel
      have hl : raw16428step0Labels = raw16428Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16428 raw16428Labels permutation346 hz
    mixedMoment B raw16428step0 raw16428step0Labels = mixedMoment B raw16428step1 raw16428step1Labels := by
      have ha : raw16428step1 = (fun i j => raw16428step0 (permutation66 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16428step1 raw16428step0; decide +kernel
      have hl : raw16428step1Labels = raw16428step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16428step0 raw16428step0Labels permutation66 permutation4
    mixedMoment B raw16428step1 raw16428step1Labels = mixedMoment B raw16428step2 raw16428step2Labels := by
      have ha : raw16428step2 = -raw16428step1 := by apply Matrix.ext; change ∀ i j, raw16428step2 i j = -(raw16428step1 i j); unfold raw16428step2 raw16428step1; decide +kernel
      have hl : raw16428step2Labels = raw16428step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2955 node2955Labels := by rfl

def raw16429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16429Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16429step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16429 raw16429Labels = mixedMoment B node3947 node3947Labels := by
  calc
    mixedMoment B raw16429 raw16429Labels = mixedMoment B raw16429step0 raw16429step0Labels := by
      have ha : raw16429step0 = (fun i j => raw16429 (permutation528 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16429step0 raw16429; decide +kernel
      have hl : raw16429step0Labels = raw16429Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16429 raw16429Labels permutation528 permutation4
    _ = mixedMoment B node3947 node3947Labels := by rfl

def raw16430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16430Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16430step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16430step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16430step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16430step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16430 raw16430Labels = mixedMoment B node3929 node3929Labels := by
  calc
    mixedMoment B raw16430 raw16430Labels = mixedMoment B raw16430step0 raw16430step0Labels := by
      have hz : ∀ j, raw16430 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16430step0 = (fun i j => raw16430 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16430step0 raw16430; decide +kernel
      have hl : raw16430step0Labels = raw16430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16430 raw16430Labels permutation346 hz
    mixedMoment B raw16430step0 raw16430step0Labels = mixedMoment B raw16430step1 raw16430step1Labels := by
      have ha : raw16430step1 = (fun i j => raw16430step0 (permutation66 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16430step1 raw16430step0; decide +kernel
      have hl : raw16430step1Labels = raw16430step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16430step0 raw16430step0Labels permutation66 permutation4
    mixedMoment B raw16430step1 raw16430step1Labels = mixedMoment B raw16430step2 raw16430step2Labels := by
      have ha : raw16430step2 = -raw16430step1 := by apply Matrix.ext; change ∀ i j, raw16430step2 i j = -(raw16430step1 i j); unfold raw16430step2 raw16430step1; decide +kernel
      have hl : raw16430step2Labels = raw16430step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3929 node3929Labels := by rfl

def raw16431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16431Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16431step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16431step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16431step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16431step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16431 raw16431Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw16431 raw16431Labels = mixedMoment B raw16431step0 raw16431step0Labels := by
      have hz : ∀ j, raw16431 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16431step0 = (fun i j => raw16431 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16431step0 raw16431; decide +kernel
      have hl : raw16431step0Labels = raw16431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16431 raw16431Labels permutation346 hz
    mixedMoment B raw16431step0 raw16431step0Labels = mixedMoment B raw16431step1 raw16431step1Labels := by
      have ha : raw16431step1 = (fun i j => raw16431step0 (permutation67 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16431step1 raw16431step0; decide +kernel
      have hl : raw16431step1Labels = raw16431step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16431step0 raw16431step0Labels permutation67 permutation4
    mixedMoment B raw16431step1 raw16431step1Labels = mixedMoment B raw16431step2 raw16431step2Labels := by
      have ha : raw16431step2 = -raw16431step1 := by apply Matrix.ext; change ∀ i j, raw16431step2 i j = -(raw16431step1 i j); unfold raw16431step2 raw16431step1; decide +kernel
      have hl : raw16431step2Labels = raw16431step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw16432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16432Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16432step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16432step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16432step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16432 raw16432Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw16432 raw16432Labels = mixedMoment B raw16432step0 raw16432step0Labels := by
      have hz : ∀ j, raw16432 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16432step0 = (fun i j => raw16432 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16432step0 raw16432; decide +kernel
      have hl : raw16432step0Labels = raw16432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16432 raw16432Labels permutation346 hz
    mixedMoment B raw16432step0 raw16432step0Labels = mixedMoment B raw16432step1 raw16432step1Labels := by
      have ha : raw16432step1 = (fun i j => raw16432step0 (permutation109 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16432step1 raw16432step0; decide +kernel
      have hl : raw16432step1Labels = raw16432step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16432step0 raw16432step0Labels permutation109 permutation4
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw16433 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![1, -1], ![-1, 1], ![1, -1]]
def raw16433Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16433step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![-1, 1], ![1, -1]]
def raw16433step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw16433step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw16433step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical16433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16433 raw16433Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw16433 raw16433Labels = mixedMoment B raw16433step0 raw16433step0Labels := by
      have hz : ∀ j, raw16433 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16433step0 = (fun i j => raw16433 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16433step0 raw16433; decide +kernel
      have hl : raw16433step0Labels = raw16433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16433 raw16433Labels permutation346 hz
    mixedMoment B raw16433step0 raw16433step0Labels = mixedMoment B raw16433step1 raw16433step1Labels := by
      have ha : raw16433step1 = (fun i j => raw16433step0 (permutation44 i) (permutation0 j)) := by apply Matrix.ext; unfold raw16433step1 raw16433step0; decide +kernel
      have hl : raw16433step1Labels = raw16433step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16433step0 raw16433step0Labels permutation44 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw16434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16434Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 1, 1]]
def raw16434step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16434step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw16434step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16434 raw16434Labels = mixedMoment B node2944 node2944Labels := by
  calc
    mixedMoment B raw16434 raw16434Labels = mixedMoment B raw16434step0 raw16434step0Labels := by
      have ha : raw16434step0 = (fun i j => raw16434 (permutation309 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16434step0 raw16434; decide +kernel
      have hl : raw16434step0Labels = raw16434Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16434 raw16434Labels permutation309 permutation4
    mixedMoment B raw16434step0 raw16434step0Labels = mixedMoment B raw16434step1 raw16434step1Labels := by
      have ha : raw16434step1 = -raw16434step0 := by apply Matrix.ext; change ∀ i j, raw16434step1 i j = -(raw16434step0 i j); unfold raw16434step1 raw16434step0; decide +kernel
      have hl : raw16434step1Labels = raw16434step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2944 node2944Labels := by rfl

def raw16435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16435Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16435step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw16435step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16435step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16435step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16435 raw16435Labels = mixedMoment B node3092 node3092Labels := by
  calc
    mixedMoment B raw16435 raw16435Labels = mixedMoment B raw16435step0 raw16435step0Labels := by
      have hz : ∀ j, raw16435 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16435step0 = (fun i j => raw16435 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16435step0 raw16435; decide +kernel
      have hl : raw16435step0Labels = raw16435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16435 raw16435Labels permutation346 hz
    mixedMoment B raw16435step0 raw16435step0Labels = mixedMoment B raw16435step1 raw16435step1Labels := by
      have ha : raw16435step1 = (fun i j => raw16435step0 (permutation63 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16435step1 raw16435step0; decide +kernel
      have hl : raw16435step1Labels = raw16435step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16435step0 raw16435step0Labels permutation63 permutation4
    mixedMoment B raw16435step1 raw16435step1Labels = mixedMoment B raw16435step2 raw16435step2Labels := by
      have ha : raw16435step2 = -raw16435step1 := by apply Matrix.ext; change ∀ i j, raw16435step2 i j = -(raw16435step1 i j); unfold raw16435step2 raw16435step1; decide +kernel
      have hl : raw16435step2Labels = raw16435step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3092 node3092Labels := by rfl

def raw16436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw16436Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw16436step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16436step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-3, 2, 1]]
def raw16436step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16436step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw16436step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16436 raw16436Labels = mixedMoment B node2946 node2946Labels := by
  calc
    mixedMoment B raw16436 raw16436Labels = mixedMoment B raw16436step0 raw16436step0Labels := by
      have hz : ∀ j, raw16436 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16436step0 = (fun i j => raw16436 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16436step0 raw16436; decide +kernel
      have hl : raw16436step0Labels = raw16436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16436 raw16436Labels permutation346 hz
    mixedMoment B raw16436step0 raw16436step0Labels = mixedMoment B raw16436step1 raw16436step1Labels := by
      have ha : raw16436step1 = (fun i j => raw16436step0 (permutation63 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16436step1 raw16436step0; decide +kernel
      have hl : raw16436step1Labels = raw16436step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16436step0 raw16436step0Labels permutation63 permutation4
    mixedMoment B raw16436step1 raw16436step1Labels = mixedMoment B raw16436step2 raw16436step2Labels := by
      have ha : raw16436step2 = -raw16436step1 := by apply Matrix.ext; change ∀ i j, raw16436step2 i j = -(raw16436step1 i j); unfold raw16436step2 raw16436step1; decide +kernel
      have hl : raw16436step2Labels = raw16436step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2946 node2946Labels := by rfl

def raw16437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw16437Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw16437step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16437step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -2, 2], ![-2, 3, -1], ![-2, 1, 1]]
def raw16437step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16437step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw16437step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16437 raw16437Labels = mixedMoment B node2949 node2949Labels := by
  calc
    mixedMoment B raw16437 raw16437Labels = mixedMoment B raw16437step0 raw16437step0Labels := by
      have hz : ∀ j, raw16437 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16437step0 = (fun i j => raw16437 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16437step0 raw16437; decide +kernel
      have hl : raw16437step0Labels = raw16437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16437 raw16437Labels permutation346 hz
    mixedMoment B raw16437step0 raw16437step0Labels = mixedMoment B raw16437step1 raw16437step1Labels := by
      have ha : raw16437step1 = (fun i j => raw16437step0 (permutation63 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16437step1 raw16437step0; decide +kernel
      have hl : raw16437step1Labels = raw16437step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16437step0 raw16437step0Labels permutation63 permutation4
    mixedMoment B raw16437step1 raw16437step1Labels = mixedMoment B raw16437step2 raw16437step2Labels := by
      have ha : raw16437step2 = -raw16437step1 := by apply Matrix.ext; change ∀ i j, raw16437step2 i j = -(raw16437step1 i j); unfold raw16437step2 raw16437step1; decide +kernel
      have hl : raw16437step2Labels = raw16437step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2949 node2949Labels := by rfl

def raw16438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16438Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16438step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16438step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16438step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16438 raw16438Labels = mixedMoment B node2633 node2633Labels := by
  calc
    mixedMoment B raw16438 raw16438Labels = mixedMoment B raw16438step0 raw16438step0Labels := by
      have hz : ∀ j, raw16438 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16438step0 = (fun i j => raw16438 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16438step0 raw16438; decide +kernel
      have hl : raw16438step0Labels = raw16438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16438 raw16438Labels permutation346 hz
    mixedMoment B raw16438step0 raw16438step0Labels = mixedMoment B raw16438step1 raw16438step1Labels := by
      have ha : raw16438step1 = (fun i j => raw16438step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16438step1 raw16438step0; decide +kernel
      have hl : raw16438step1Labels = raw16438step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16438step0 raw16438step0Labels permutation34 permutation2
    _ = mixedMoment B node2633 node2633Labels := by rfl

def raw16439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16439Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16439step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16439step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16439 raw16439Labels = mixedMoment B node3827 node3827Labels := by
  calc
    mixedMoment B raw16439 raw16439Labels = mixedMoment B raw16439step0 raw16439step0Labels := by
      have ha : raw16439step0 = (fun i j => raw16439 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16439step0 raw16439; decide +kernel
      have hl : raw16439step0Labels = raw16439Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16439 raw16439Labels permutation178 permutation2
    _ = mixedMoment B node3827 node3827Labels := by rfl

def raw16440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16440Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16440step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16440 raw16440Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw16440 raw16440Labels = mixedMoment B raw16440step0 raw16440step0Labels := by
      have hz : ∀ j, raw16440 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16440step0 = (fun i j => raw16440 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16440step0 raw16440; decide +kernel
      have hl : raw16440step0Labels = raw16440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16440 raw16440Labels permutation346 hz
    mixedMoment B raw16440step0 raw16440step0Labels = mixedMoment B raw16440step1 raw16440step1Labels := by
      have ha : raw16440step1 = (fun i j => raw16440step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16440step1 raw16440step0; decide +kernel
      have hl : raw16440step1Labels = raw16440step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16440step0 raw16440step0Labels permutation34 permutation2
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw16441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16441Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16441step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16441 raw16441Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw16441 raw16441Labels = mixedMoment B raw16441step0 raw16441step0Labels := by
      have hz : ∀ j, raw16441 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16441step0 = (fun i j => raw16441 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16441step0 raw16441; decide +kernel
      have hl : raw16441step0Labels = raw16441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16441 raw16441Labels permutation346 hz
    mixedMoment B raw16441step0 raw16441step0Labels = mixedMoment B raw16441step1 raw16441step1Labels := by
      have ha : raw16441step1 = (fun i j => raw16441step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16441step1 raw16441step0; decide +kernel
      have hl : raw16441step1Labels = raw16441step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16441step0 raw16441step0Labels permutation34 permutation2
    _ = mixedMoment B node3885 node3885Labels := by rfl

def raw16442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16442Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16442step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16442step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16442 raw16442Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw16442 raw16442Labels = mixedMoment B raw16442step0 raw16442step0Labels := by
      have hz : ∀ j, raw16442 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16442step0 = (fun i j => raw16442 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16442step0 raw16442; decide +kernel
      have hl : raw16442step0Labels = raw16442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16442 raw16442Labels permutation346 hz
    mixedMoment B raw16442step0 raw16442step0Labels = mixedMoment B raw16442step1 raw16442step1Labels := by
      have ha : raw16442step1 = (fun i j => raw16442step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16442step1 raw16442step0; decide +kernel
      have hl : raw16442step1Labels = raw16442step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16442step0 raw16442step0Labels permutation56 permutation2
    _ = mixedMoment B node5428 node5428Labels := by rfl

def raw16443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16443Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16443step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16443step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16443step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16443step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16443 raw16443Labels = mixedMoment B node5471 node5471Labels := by
  calc
    mixedMoment B raw16443 raw16443Labels = mixedMoment B raw16443step0 raw16443step0Labels := by
      have ha : raw16443step0 = (fun i j => raw16443 (permutation572 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16443step0 raw16443; decide +kernel
      have hl : raw16443step0Labels = raw16443Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16443 raw16443Labels permutation572 permutation7
    mixedMoment B raw16443step0 raw16443step0Labels = mixedMoment B raw16443step1 raw16443step1Labels := by
      have ha : raw16443step1 = raw16443step0 := by apply Matrix.ext; unfold raw16443step1 raw16443step0; decide +kernel
      have hl : raw16443step0Labels = labelEmbedding10 ∘ raw16443step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16443step0 raw16443step0Labels raw16443step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5471 node5471Labels := by rfl

def raw16444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16444Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16444step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16444step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16444step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16444step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16444 raw16444Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw16444 raw16444Labels = mixedMoment B raw16444step0 raw16444step0Labels := by
      have hz : ∀ j, raw16444 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16444step0 = (fun i j => raw16444 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16444step0 raw16444; decide +kernel
      have hl : raw16444step0Labels = raw16444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16444 raw16444Labels permutation346 hz
    mixedMoment B raw16444step0 raw16444step0Labels = mixedMoment B raw16444step1 raw16444step1Labels := by
      have ha : raw16444step1 = (fun i j => raw16444step0 (permutation123 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16444step1 raw16444step0; decide +kernel
      have hl : raw16444step1Labels = raw16444step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16444step0 raw16444step0Labels permutation123 permutation7
    mixedMoment B raw16444step1 raw16444step1Labels = mixedMoment B raw16444step2 raw16444step2Labels := by
      have ha : raw16444step2 = raw16444step1 := by apply Matrix.ext; unfold raw16444step2 raw16444step1; decide +kernel
      have hl : raw16444step1Labels = labelEmbedding10 ∘ raw16444step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16444step1 raw16444step1Labels raw16444step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw16445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16445Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16445step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16445step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16445step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16445step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16445step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16445step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16445 raw16445Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw16445 raw16445Labels = mixedMoment B raw16445step0 raw16445step0Labels := by
      have hz : ∀ j, raw16445 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16445step0 = (fun i j => raw16445 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16445step0 raw16445; decide +kernel
      have hl : raw16445step0Labels = raw16445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16445 raw16445Labels permutation346 hz
    mixedMoment B raw16445step0 raw16445step0Labels = mixedMoment B raw16445step1 raw16445step1Labels := by
      have ha : raw16445step1 = (fun i j => raw16445step0 (permutation109 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16445step1 raw16445step0; decide +kernel
      have hl : raw16445step1Labels = raw16445step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16445step0 raw16445step0Labels permutation109 permutation4
    mixedMoment B raw16445step1 raw16445step1Labels = mixedMoment B raw16445step2 raw16445step2Labels := by
      have ha : raw16445step2 = -raw16445step1 := by apply Matrix.ext; change ∀ i j, raw16445step2 i j = -(raw16445step1 i j); unfold raw16445step2 raw16445step1; decide +kernel
      have hl : raw16445step2Labels = raw16445step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16445step2 raw16445step2Labels = mixedMoment B raw16445step3 raw16445step3Labels := by
      have ha : raw16445step3 = raw16445step2 := by apply Matrix.ext; unfold raw16445step3 raw16445step2; decide +kernel
      have hl : raw16445step2Labels = labelEmbedding7 ∘ raw16445step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16445step2 raw16445step2Labels raw16445step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw16446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16446Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16446step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16446step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw16446step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw16446step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16446step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw16446step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16446step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16446 raw16446Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw16446 raw16446Labels = mixedMoment B raw16446step0 raw16446step0Labels := by
      have hz : ∀ j, raw16446 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16446step0 = (fun i j => raw16446 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16446step0 raw16446; decide +kernel
      have hl : raw16446step0Labels = raw16446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16446 raw16446Labels permutation346 hz
    mixedMoment B raw16446step0 raw16446step0Labels = mixedMoment B raw16446step1 raw16446step1Labels := by
      have ha : raw16446step1 = (fun i j => raw16446step0 (permutation63 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16446step1 raw16446step0; decide +kernel
      have hl : raw16446step1Labels = raw16446step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16446step0 raw16446step0Labels permutation63 permutation6
    mixedMoment B raw16446step1 raw16446step1Labels = mixedMoment B raw16446step2 raw16446step2Labels := by
      have ha : raw16446step2 = -raw16446step1 := by apply Matrix.ext; change ∀ i j, raw16446step2 i j = -(raw16446step1 i j); unfold raw16446step2 raw16446step1; decide +kernel
      have hl : raw16446step2Labels = raw16446step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16446step2 raw16446step2Labels = mixedMoment B raw16446step3 raw16446step3Labels := by
      have ha : raw16446step3 = raw16446step2 := by apply Matrix.ext; unfold raw16446step3 raw16446step2; decide +kernel
      have hl : raw16446step2Labels = labelEmbedding9 ∘ raw16446step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16446step2 raw16446step2Labels raw16446step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw16447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16447Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16447step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16447step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16447step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16447step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16447step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16447step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16447step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16447 raw16447Labels = mixedMoment B node4867 node4867Labels := by
  calc
    mixedMoment B raw16447 raw16447Labels = mixedMoment B raw16447step0 raw16447step0Labels := by
      have hz : ∀ j, raw16447 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16447step0 = (fun i j => raw16447 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16447step0 raw16447; decide +kernel
      have hl : raw16447step0Labels = raw16447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16447 raw16447Labels permutation346 hz
    mixedMoment B raw16447step0 raw16447step0Labels = mixedMoment B raw16447step1 raw16447step1Labels := by
      have ha : raw16447step1 = (fun i j => raw16447step0 (permutation47 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16447step1 raw16447step0; decide +kernel
      have hl : raw16447step1Labels = raw16447step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16447step0 raw16447step0Labels permutation47 permutation5
    mixedMoment B raw16447step1 raw16447step1Labels = mixedMoment B raw16447step2 raw16447step2Labels := by
      have ha : raw16447step2 = -raw16447step1 := by apply Matrix.ext; change ∀ i j, raw16447step2 i j = -(raw16447step1 i j); unfold raw16447step2 raw16447step1; decide +kernel
      have hl : raw16447step2Labels = raw16447step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16447step2 raw16447step2Labels = mixedMoment B raw16447step3 raw16447step3Labels := by
      have ha : raw16447step3 = raw16447step2 := by apply Matrix.ext; unfold raw16447step3 raw16447step2; decide +kernel
      have hl : raw16447step2Labels = labelEmbedding8 ∘ raw16447step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16447step2 raw16447step2Labels raw16447step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4867 node4867Labels := by rfl

def raw16448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16448Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16448step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16448step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16448step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16448 raw16448Labels = mixedMoment B node5402 node5402Labels := by
  calc
    mixedMoment B raw16448 raw16448Labels = mixedMoment B raw16448step0 raw16448step0Labels := by
      have ha : raw16448step0 = (fun i j => raw16448 (permutation319 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16448step0 raw16448; decide +kernel
      have hl : raw16448step0Labels = raw16448Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16448 raw16448Labels permutation319 permutation4
    mixedMoment B raw16448step0 raw16448step0Labels = mixedMoment B raw16448step1 raw16448step1Labels := by
      have ha : raw16448step1 = raw16448step0 := by apply Matrix.ext; unfold raw16448step1 raw16448step0; decide +kernel
      have hl : raw16448step0Labels = labelEmbedding7 ∘ raw16448step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16448step0 raw16448step0Labels raw16448step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5402 node5402Labels := by rfl

def raw16449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16449Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16449step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16449step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16449step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16449step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16449 raw16449Labels = mixedMoment B node5436 node5436Labels := by
  calc
    mixedMoment B raw16449 raw16449Labels = mixedMoment B raw16449step0 raw16449step0Labels := by
      have hz : ∀ j, raw16449 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16449step0 = (fun i j => raw16449 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16449step0 raw16449; decide +kernel
      have hl : raw16449step0Labels = raw16449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16449 raw16449Labels permutation346 hz
    mixedMoment B raw16449step0 raw16449step0Labels = mixedMoment B raw16449step1 raw16449step1Labels := by
      have ha : raw16449step1 = (fun i j => raw16449step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16449step1 raw16449step0; decide +kernel
      have hl : raw16449step1Labels = raw16449step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16449step0 raw16449step0Labels permutation38 permutation3
    mixedMoment B raw16449step1 raw16449step1Labels = mixedMoment B raw16449step2 raw16449step2Labels := by
      have ha : raw16449step2 = raw16449step1 := by apply Matrix.ext; unfold raw16449step2 raw16449step1; decide +kernel
      have hl : raw16449step1Labels = labelEmbedding6 ∘ raw16449step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16449step1 raw16449step1Labels raw16449step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5436 node5436Labels := by rfl

def raw16450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16450Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16450step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16450step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16450step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16450step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16450step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16450step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16450 raw16450Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw16450 raw16450Labels = mixedMoment B raw16450step0 raw16450step0Labels := by
      have hz : ∀ j, raw16450 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16450step0 = (fun i j => raw16450 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16450step0 raw16450; decide +kernel
      have hl : raw16450step0Labels = raw16450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16450 raw16450Labels permutation346 hz
    mixedMoment B raw16450step0 raw16450step0Labels = mixedMoment B raw16450step1 raw16450step1Labels := by
      have ha : raw16450step1 = (fun i j => raw16450step0 (permutation109 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16450step1 raw16450step0; decide +kernel
      have hl : raw16450step1Labels = raw16450step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16450step0 raw16450step0Labels permutation109 permutation4
    mixedMoment B raw16450step1 raw16450step1Labels = mixedMoment B raw16450step2 raw16450step2Labels := by
      have ha : raw16450step2 = -raw16450step1 := by apply Matrix.ext; change ∀ i j, raw16450step2 i j = -(raw16450step1 i j); unfold raw16450step2 raw16450step1; decide +kernel
      have hl : raw16450step2Labels = raw16450step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16450step2 raw16450step2Labels = mixedMoment B raw16450step3 raw16450step3Labels := by
      have ha : raw16450step3 = raw16450step2 := by apply Matrix.ext; unfold raw16450step3 raw16450step2; decide +kernel
      have hl : raw16450step2Labels = labelEmbedding7 ∘ raw16450step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16450step2 raw16450step2Labels raw16450step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw16451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16451Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16451step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16451step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16451step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16451step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16451step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16451 raw16451Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw16451 raw16451Labels = mixedMoment B raw16451step0 raw16451step0Labels := by
      have hz : ∀ j, raw16451 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16451step0 = (fun i j => raw16451 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16451step0 raw16451; decide +kernel
      have hl : raw16451step0Labels = raw16451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16451 raw16451Labels permutation346 hz
    mixedMoment B raw16451step0 raw16451step0Labels = mixedMoment B raw16451step1 raw16451step1Labels := by
      have ha : raw16451step1 = (fun i j => raw16451step0 (permutation67 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16451step1 raw16451step0; decide +kernel
      have hl : raw16451step1Labels = raw16451step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16451step0 raw16451step0Labels permutation67 permutation4
    mixedMoment B raw16451step1 raw16451step1Labels = mixedMoment B raw16451step2 raw16451step2Labels := by
      have ha : raw16451step2 = raw16451step1 := by apply Matrix.ext; unfold raw16451step2 raw16451step1; decide +kernel
      have hl : raw16451step1Labels = labelEmbedding7 ∘ raw16451step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16451step1 raw16451step1Labels raw16451step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw16452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16452Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16452step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16452step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16452step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16452step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16452 raw16452Labels = mixedMoment B node4849 node4849Labels := by
  calc
    mixedMoment B raw16452 raw16452Labels = mixedMoment B raw16452step0 raw16452step0Labels := by
      have ha : raw16452step0 = (fun i j => raw16452 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16452step0 raw16452; decide +kernel
      have hl : raw16452step0Labels = raw16452Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16452 raw16452Labels permutation160 permutation3
    mixedMoment B raw16452step0 raw16452step0Labels = mixedMoment B raw16452step1 raw16452step1Labels := by
      have ha : raw16452step1 = raw16452step0 := by apply Matrix.ext; unfold raw16452step1 raw16452step0; decide +kernel
      have hl : raw16452step0Labels = labelEmbedding6 ∘ raw16452step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16452step0 raw16452step0Labels raw16452step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4849 node4849Labels := by rfl

def raw16453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16453Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16453step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16453step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16453 raw16453Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw16453 raw16453Labels = mixedMoment B raw16453step0 raw16453step0Labels := by
      have ha : raw16453step0 = (fun i j => raw16453 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16453step0 raw16453; decide +kernel
      have hl : raw16453step0Labels = raw16453Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16453 raw16453Labels permutation271 permutation2
    _ = mixedMoment B node5379 node5379Labels := by rfl

def raw16454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16454Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16454step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16454step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16454step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16454step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16454 raw16454Labels = mixedMoment B node5421 node5421Labels := by
  calc
    mixedMoment B raw16454 raw16454Labels = mixedMoment B raw16454step0 raw16454step0Labels := by
      have ha : raw16454step0 = (fun i j => raw16454 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16454step0 raw16454; decide +kernel
      have hl : raw16454step0Labels = raw16454Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16454 raw16454Labels permutation202 permutation3
    mixedMoment B raw16454step0 raw16454step0Labels = mixedMoment B raw16454step1 raw16454step1Labels := by
      have ha : raw16454step1 = raw16454step0 := by apply Matrix.ext; unfold raw16454step1 raw16454step0; decide +kernel
      have hl : raw16454step0Labels = labelEmbedding6 ∘ raw16454step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16454step0 raw16454step0Labels raw16454step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5421 node5421Labels := by rfl

def raw16455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16455Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16455step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16455step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16455step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16455step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16455step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16455step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16455 raw16455Labels = mixedMoment B node5382 node5382Labels := by
  calc
    mixedMoment B raw16455 raw16455Labels = mixedMoment B raw16455step0 raw16455step0Labels := by
      have ha : raw16455step0 = (fun i j => raw16455 (permutation528 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16455step0 raw16455; decide +kernel
      have hl : raw16455step0Labels = raw16455Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16455 raw16455Labels permutation528 permutation4
    mixedMoment B raw16455step0 raw16455step0Labels = mixedMoment B raw16455step1 raw16455step1Labels := by
      have ha : raw16455step1 = -raw16455step0 := by apply Matrix.ext; change ∀ i j, raw16455step1 i j = -(raw16455step0 i j); unfold raw16455step1 raw16455step0; decide +kernel
      have hl : raw16455step1Labels = raw16455step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16455step1 raw16455step1Labels = mixedMoment B raw16455step2 raw16455step2Labels := by
      have ha : raw16455step2 = raw16455step1 := by apply Matrix.ext; unfold raw16455step2 raw16455step1; decide +kernel
      have hl : raw16455step1Labels = labelEmbedding7 ∘ raw16455step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16455step1 raw16455step1Labels raw16455step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5382 node5382Labels := by rfl

def raw16456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16456Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16456step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16456step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16456step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16456step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16456 raw16456Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw16456 raw16456Labels = mixedMoment B raw16456step0 raw16456step0Labels := by
      have ha : raw16456step0 = (fun i j => raw16456 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16456step0 raw16456; decide +kernel
      have hl : raw16456step0Labels = raw16456Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16456 raw16456Labels permutation161 permutation3
    mixedMoment B raw16456step0 raw16456step0Labels = mixedMoment B raw16456step1 raw16456step1Labels := by
      have ha : raw16456step1 = raw16456step0 := by apply Matrix.ext; unfold raw16456step1 raw16456step0; decide +kernel
      have hl : raw16456step0Labels = labelEmbedding6 ∘ raw16456step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16456step0 raw16456step0Labels raw16456step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

def raw16457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16457Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16457step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16457step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16457step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16457step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16457step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16457 raw16457Labels = mixedMoment B node4861 node4861Labels := by
  calc
    mixedMoment B raw16457 raw16457Labels = mixedMoment B raw16457step0 raw16457step0Labels := by
      have hz : ∀ j, raw16457 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16457step0 = (fun i j => raw16457 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16457step0 raw16457; decide +kernel
      have hl : raw16457step0Labels = raw16457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16457 raw16457Labels permutation346 hz
    mixedMoment B raw16457step0 raw16457step0Labels = mixedMoment B raw16457step1 raw16457step1Labels := by
      have ha : raw16457step1 = (fun i j => raw16457step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16457step1 raw16457step0; decide +kernel
      have hl : raw16457step1Labels = raw16457step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16457step0 raw16457step0Labels permutation34 permutation3
    mixedMoment B raw16457step1 raw16457step1Labels = mixedMoment B raw16457step2 raw16457step2Labels := by
      have ha : raw16457step2 = raw16457step1 := by apply Matrix.ext; unfold raw16457step2 raw16457step1; decide +kernel
      have hl : raw16457step1Labels = labelEmbedding6 ∘ raw16457step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16457step1 raw16457step1Labels raw16457step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4861 node4861Labels := by rfl

def raw16458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16458Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16458step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16458step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16458step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16458 raw16458Labels = mixedMoment B node5385 node5385Labels := by
  calc
    mixedMoment B raw16458 raw16458Labels = mixedMoment B raw16458step0 raw16458step0Labels := by
      have hz : ∀ j, raw16458 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16458step0 = (fun i j => raw16458 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16458step0 raw16458; decide +kernel
      have hl : raw16458step0Labels = raw16458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16458 raw16458Labels permutation346 hz
    mixedMoment B raw16458step0 raw16458step0Labels = mixedMoment B raw16458step1 raw16458step1Labels := by
      have ha : raw16458step1 = (fun i j => raw16458step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16458step1 raw16458step0; decide +kernel
      have hl : raw16458step1Labels = raw16458step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16458step0 raw16458step0Labels permutation56 permutation2
    _ = mixedMoment B node5385 node5385Labels := by rfl

def raw16459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16459Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16459step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16459step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16459step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16459 raw16459Labels = mixedMoment B node5399 node5399Labels := by
  calc
    mixedMoment B raw16459 raw16459Labels = mixedMoment B raw16459step0 raw16459step0Labels := by
      have ha : raw16459step0 = (fun i j => raw16459 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16459step0 raw16459; decide +kernel
      have hl : raw16459step0Labels = raw16459Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16459 raw16459Labels permutation178 permutation3
    mixedMoment B raw16459step0 raw16459step0Labels = mixedMoment B raw16459step1 raw16459step1Labels := by
      have ha : raw16459step1 = raw16459step0 := by apply Matrix.ext; unfold raw16459step1 raw16459step0; decide +kernel
      have hl : raw16459step0Labels = labelEmbedding6 ∘ raw16459step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16459step0 raw16459step0Labels raw16459step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5399 node5399Labels := by rfl

def raw16460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16460Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16460step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16460step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16460step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16460step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16460step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16460step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16460step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16460 raw16460Labels = mixedMoment B node5385 node5385Labels := by
  calc
    mixedMoment B raw16460 raw16460Labels = mixedMoment B raw16460step0 raw16460step0Labels := by
      have hz : ∀ j, raw16460 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16460step0 = (fun i j => raw16460 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16460step0 raw16460; decide +kernel
      have hl : raw16460step0Labels = raw16460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16460 raw16460Labels permutation346 hz
    mixedMoment B raw16460step0 raw16460step0Labels = mixedMoment B raw16460step1 raw16460step1Labels := by
      have ha : raw16460step1 = (fun i j => raw16460step0 (permutation108 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16460step1 raw16460step0; decide +kernel
      have hl : raw16460step1Labels = raw16460step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16460step0 raw16460step0Labels permutation108 permutation4
    mixedMoment B raw16460step1 raw16460step1Labels = mixedMoment B raw16460step2 raw16460step2Labels := by
      have ha : raw16460step2 = -raw16460step1 := by apply Matrix.ext; change ∀ i j, raw16460step2 i j = -(raw16460step1 i j); unfold raw16460step2 raw16460step1; decide +kernel
      have hl : raw16460step2Labels = raw16460step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16460step2 raw16460step2Labels = mixedMoment B raw16460step3 raw16460step3Labels := by
      have ha : raw16460step3 = raw16460step2 := by apply Matrix.ext; unfold raw16460step3 raw16460step2; decide +kernel
      have hl : raw16460step2Labels = labelEmbedding7 ∘ raw16460step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16460step2 raw16460step2Labels raw16460step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5385 node5385Labels := by rfl

def raw16461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16461Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16461step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16461step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16461step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16461step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16461step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16461step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16461step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16461 raw16461Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw16461 raw16461Labels = mixedMoment B raw16461step0 raw16461step0Labels := by
      have hz : ∀ j, raw16461 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16461step0 = (fun i j => raw16461 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16461step0 raw16461; decide +kernel
      have hl : raw16461step0Labels = raw16461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16461 raw16461Labels permutation346 hz
    mixedMoment B raw16461step0 raw16461step0Labels = mixedMoment B raw16461step1 raw16461step1Labels := by
      have ha : raw16461step1 = (fun i j => raw16461step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16461step1 raw16461step0; decide +kernel
      have hl : raw16461step1Labels = raw16461step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16461step0 raw16461step0Labels permutation48 permutation5
    mixedMoment B raw16461step1 raw16461step1Labels = mixedMoment B raw16461step2 raw16461step2Labels := by
      have ha : raw16461step2 = -raw16461step1 := by apply Matrix.ext; change ∀ i j, raw16461step2 i j = -(raw16461step1 i j); unfold raw16461step2 raw16461step1; decide +kernel
      have hl : raw16461step2Labels = raw16461step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16461step2 raw16461step2Labels = mixedMoment B raw16461step3 raw16461step3Labels := by
      have ha : raw16461step3 = raw16461step2 := by apply Matrix.ext; unfold raw16461step3 raw16461step2; decide +kernel
      have hl : raw16461step2Labels = labelEmbedding8 ∘ raw16461step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16461step2 raw16461step2Labels raw16461step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw16462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16462Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16462step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16462step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16462step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16462step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16462 raw16462Labels = mixedMoment B node4856 node4856Labels := by
  calc
    mixedMoment B raw16462 raw16462Labels = mixedMoment B raw16462step0 raw16462step0Labels := by
      have hz : ∀ j, raw16462 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16462step0 = (fun i j => raw16462 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16462step0 raw16462; decide +kernel
      have hl : raw16462step0Labels = raw16462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16462 raw16462Labels permutation346 hz
    mixedMoment B raw16462step0 raw16462step0Labels = mixedMoment B raw16462step1 raw16462step1Labels := by
      have ha : raw16462step1 = (fun i j => raw16462step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16462step1 raw16462step0; decide +kernel
      have hl : raw16462step1Labels = raw16462step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16462step0 raw16462step0Labels permutation32 permutation3
    mixedMoment B raw16462step1 raw16462step1Labels = mixedMoment B raw16462step2 raw16462step2Labels := by
      have ha : raw16462step2 = raw16462step1 := by apply Matrix.ext; unfold raw16462step2 raw16462step1; decide +kernel
      have hl : raw16462step1Labels = labelEmbedding6 ∘ raw16462step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16462step1 raw16462step1Labels raw16462step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4856 node4856Labels := by rfl

def raw16463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16463Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16463step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16463step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw16463step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16463step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw16463step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16463 raw16463Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw16463 raw16463Labels = mixedMoment B raw16463step0 raw16463step0Labels := by
      have hz : ∀ j, raw16463 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16463step0 = (fun i j => raw16463 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16463step0 raw16463; decide +kernel
      have hl : raw16463step0Labels = raw16463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16463 raw16463Labels permutation346 hz
    mixedMoment B raw16463step0 raw16463step0Labels = mixedMoment B raw16463step1 raw16463step1Labels := by
      have ha : raw16463step1 = (fun i j => raw16463step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16463step1 raw16463step0; decide +kernel
      have hl : raw16463step1Labels = raw16463step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16463step0 raw16463step0Labels permutation126 permutation2
    mixedMoment B raw16463step1 raw16463step1Labels = mixedMoment B raw16463step2 raw16463step2Labels := by
      have ha : raw16463step2 = -raw16463step1 := by apply Matrix.ext; change ∀ i j, raw16463step2 i j = -(raw16463step1 i j); unfold raw16463step2 raw16463step1; decide +kernel
      have hl : raw16463step2Labels = raw16463step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw16464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16464Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16464step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16464step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16464step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16464 raw16464Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw16464 raw16464Labels = mixedMoment B raw16464step0 raw16464step0Labels := by
      have ha : raw16464step0 = (fun i j => raw16464 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16464step0 raw16464; decide +kernel
      have hl : raw16464step0Labels = raw16464Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16464 raw16464Labels permutation589 permutation2
    mixedMoment B raw16464step0 raw16464step0Labels = mixedMoment B raw16464step1 raw16464step1Labels := by
      have ha : raw16464step1 = -raw16464step0 := by apply Matrix.ext; change ∀ i j, raw16464step1 i j = -(raw16464step0 i j); unfold raw16464step1 raw16464step0; decide +kernel
      have hl : raw16464step1Labels = raw16464step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5353 node5353Labels := by rfl

def raw16465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16465Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16465step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16465step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16465step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16465step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16465step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16465 raw16465Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw16465 raw16465Labels = mixedMoment B raw16465step0 raw16465step0Labels := by
      have hz : ∀ j, raw16465 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16465step0 = (fun i j => raw16465 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16465step0 raw16465; decide +kernel
      have hl : raw16465step0Labels = raw16465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16465 raw16465Labels permutation346 hz
    mixedMoment B raw16465step0 raw16465step0Labels = mixedMoment B raw16465step1 raw16465step1Labels := by
      have ha : raw16465step1 = (fun i j => raw16465step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16465step1 raw16465step0; decide +kernel
      have hl : raw16465step1Labels = raw16465step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16465step0 raw16465step0Labels permutation127 permutation2
    mixedMoment B raw16465step1 raw16465step1Labels = mixedMoment B raw16465step2 raw16465step2Labels := by
      have ha : raw16465step2 = -raw16465step1 := by apply Matrix.ext; change ∀ i j, raw16465step2 i j = -(raw16465step1 i j); unfold raw16465step2 raw16465step1; decide +kernel
      have hl : raw16465step2Labels = raw16465step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5370 node5370Labels := by rfl

def raw16466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw16466Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw16466step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16466step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16466step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16466step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16466step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16466 raw16466Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw16466 raw16466Labels = mixedMoment B raw16466step0 raw16466step0Labels := by
      have hz : ∀ j, raw16466 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16466step0 = (fun i j => raw16466 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16466step0 raw16466; decide +kernel
      have hl : raw16466step0Labels = raw16466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16466 raw16466Labels permutation346 hz
    mixedMoment B raw16466step0 raw16466step0Labels = mixedMoment B raw16466step1 raw16466step1Labels := by
      have ha : raw16466step1 = (fun i j => raw16466step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16466step1 raw16466step0; decide +kernel
      have hl : raw16466step1Labels = raw16466step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16466step0 raw16466step0Labels permutation127 permutation2
    mixedMoment B raw16466step1 raw16466step1Labels = mixedMoment B raw16466step2 raw16466step2Labels := by
      have ha : raw16466step2 = -raw16466step1 := by apply Matrix.ext; change ∀ i j, raw16466step2 i j = -(raw16466step1 i j); unfold raw16466step2 raw16466step1; decide +kernel
      have hl : raw16466step2Labels = raw16466step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw16467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16467step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16467step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw16467step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16467step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw16467step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16467 raw16467Labels = mixedMoment B node4850 node4850Labels := by
  calc
    mixedMoment B raw16467 raw16467Labels = mixedMoment B raw16467step0 raw16467step0Labels := by
      have hz : ∀ j, raw16467 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16467step0 = (fun i j => raw16467 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16467step0 raw16467; decide +kernel
      have hl : raw16467step0Labels = raw16467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16467 raw16467Labels permutation346 hz
    mixedMoment B raw16467step0 raw16467step0Labels = mixedMoment B raw16467step1 raw16467step1Labels := by
      have ha : raw16467step1 = (fun i j => raw16467step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16467step1 raw16467step0; decide +kernel
      have hl : raw16467step1Labels = raw16467step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16467step0 raw16467step0Labels permutation32 permutation3
    mixedMoment B raw16467step1 raw16467step1Labels = mixedMoment B raw16467step2 raw16467step2Labels := by
      have ha : raw16467step2 = raw16467step1 := by apply Matrix.ext; unfold raw16467step2 raw16467step1; decide +kernel
      have hl : raw16467step1Labels = labelEmbedding6 ∘ raw16467step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16467step1 raw16467step1Labels raw16467step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4850 node4850Labels := by rfl

def raw16468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16468Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16468step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16468step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw16468step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16468step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw16468step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16468step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw16468step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16468 raw16468Labels = mixedMoment B node5188 node5188Labels := by
  calc
    mixedMoment B raw16468 raw16468Labels = mixedMoment B raw16468step0 raw16468step0Labels := by
      have hz : ∀ j, raw16468 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16468step0 = (fun i j => raw16468 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16468step0 raw16468; decide +kernel
      have hl : raw16468step0Labels = raw16468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16468 raw16468Labels permutation346 hz
    mixedMoment B raw16468step0 raw16468step0Labels = mixedMoment B raw16468step1 raw16468step1Labels := by
      have ha : raw16468step1 = (fun i j => raw16468step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16468step1 raw16468step0; decide +kernel
      have hl : raw16468step1Labels = raw16468step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16468step0 raw16468step0Labels permutation151 permutation3
    mixedMoment B raw16468step1 raw16468step1Labels = mixedMoment B raw16468step2 raw16468step2Labels := by
      have ha : raw16468step2 = -raw16468step1 := by apply Matrix.ext; change ∀ i j, raw16468step2 i j = -(raw16468step1 i j); unfold raw16468step2 raw16468step1; decide +kernel
      have hl : raw16468step2Labels = raw16468step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16468step2 raw16468step2Labels = mixedMoment B raw16468step3 raw16468step3Labels := by
      have ha : raw16468step3 = raw16468step2 := by apply Matrix.ext; unfold raw16468step3 raw16468step2; decide +kernel
      have hl : raw16468step2Labels = labelEmbedding6 ∘ raw16468step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16468step2 raw16468step2Labels raw16468step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5188 node5188Labels := by rfl

def raw16469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16469step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16469step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16469step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16469step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16469step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16469 raw16469Labels = mixedMoment B node5183 node5183Labels := by
  calc
    mixedMoment B raw16469 raw16469Labels = mixedMoment B raw16469step0 raw16469step0Labels := by
      have ha : raw16469step0 = (fun i j => raw16469 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16469step0 raw16469; decide +kernel
      have hl : raw16469step0Labels = raw16469Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16469 raw16469Labels permutation686 permutation3
    mixedMoment B raw16469step0 raw16469step0Labels = mixedMoment B raw16469step1 raw16469step1Labels := by
      have ha : raw16469step1 = -raw16469step0 := by apply Matrix.ext; change ∀ i j, raw16469step1 i j = -(raw16469step0 i j); unfold raw16469step1 raw16469step0; decide +kernel
      have hl : raw16469step1Labels = raw16469step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16469step1 raw16469step1Labels = mixedMoment B raw16469step2 raw16469step2Labels := by
      have ha : raw16469step2 = raw16469step1 := by apply Matrix.ext; unfold raw16469step2 raw16469step1; decide +kernel
      have hl : raw16469step1Labels = labelEmbedding6 ∘ raw16469step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16469step1 raw16469step1Labels raw16469step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5183 node5183Labels := by rfl

def raw16470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16470step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16470step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw16470step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16470step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16470step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16470step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16470step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16470 raw16470Labels = mixedMoment B node5198 node5198Labels := by
  calc
    mixedMoment B raw16470 raw16470Labels = mixedMoment B raw16470step0 raw16470step0Labels := by
      have hz : ∀ j, raw16470 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16470step0 = (fun i j => raw16470 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16470step0 raw16470; decide +kernel
      have hl : raw16470step0Labels = raw16470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16470 raw16470Labels permutation346 hz
    mixedMoment B raw16470step0 raw16470step0Labels = mixedMoment B raw16470step1 raw16470step1Labels := by
      have ha : raw16470step1 = (fun i j => raw16470step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16470step1 raw16470step0; decide +kernel
      have hl : raw16470step1Labels = raw16470step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16470step0 raw16470step0Labels permutation149 permutation3
    mixedMoment B raw16470step1 raw16470step1Labels = mixedMoment B raw16470step2 raw16470step2Labels := by
      have ha : raw16470step2 = -raw16470step1 := by apply Matrix.ext; change ∀ i j, raw16470step2 i j = -(raw16470step1 i j); unfold raw16470step2 raw16470step1; decide +kernel
      have hl : raw16470step2Labels = raw16470step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16470step2 raw16470step2Labels = mixedMoment B raw16470step3 raw16470step3Labels := by
      have ha : raw16470step3 = raw16470step2 := by apply Matrix.ext; unfold raw16470step3 raw16470step2; decide +kernel
      have hl : raw16470step2Labels = labelEmbedding6 ∘ raw16470step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16470step2 raw16470step2Labels raw16470step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5198 node5198Labels := by rfl

def raw16471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw16471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw16471step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16471step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw16471step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16471step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw16471step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16471step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw16471step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16471 raw16471Labels = mixedMoment B node5264 node5264Labels := by
  calc
    mixedMoment B raw16471 raw16471Labels = mixedMoment B raw16471step0 raw16471step0Labels := by
      have hz : ∀ j, raw16471 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16471step0 = (fun i j => raw16471 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16471step0 raw16471; decide +kernel
      have hl : raw16471step0Labels = raw16471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16471 raw16471Labels permutation346 hz
    mixedMoment B raw16471step0 raw16471step0Labels = mixedMoment B raw16471step1 raw16471step1Labels := by
      have ha : raw16471step1 = (fun i j => raw16471step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16471step1 raw16471step0; decide +kernel
      have hl : raw16471step1Labels = raw16471step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16471step0 raw16471step0Labels permutation145 permutation3
    mixedMoment B raw16471step1 raw16471step1Labels = mixedMoment B raw16471step2 raw16471step2Labels := by
      have ha : raw16471step2 = -raw16471step1 := by apply Matrix.ext; change ∀ i j, raw16471step2 i j = -(raw16471step1 i j); unfold raw16471step2 raw16471step1; decide +kernel
      have hl : raw16471step2Labels = raw16471step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16471step2 raw16471step2Labels = mixedMoment B raw16471step3 raw16471step3Labels := by
      have ha : raw16471step3 = raw16471step2 := by apply Matrix.ext; unfold raw16471step3 raw16471step2; decide +kernel
      have hl : raw16471step2Labels = labelEmbedding6 ∘ raw16471step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16471step2 raw16471step2Labels raw16471step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5264 node5264Labels := by rfl

def raw16472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16472Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16472step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16472step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw16472step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16472step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw16472step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16472 raw16472Labels = mixedMoment B node4003 node4003Labels := by
  calc
    mixedMoment B raw16472 raw16472Labels = mixedMoment B raw16472step0 raw16472step0Labels := by
      have hz : ∀ j, raw16472 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16472step0 = (fun i j => raw16472 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16472step0 raw16472; decide +kernel
      have hl : raw16472step0Labels = raw16472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16472 raw16472Labels permutation346 hz
    mixedMoment B raw16472step0 raw16472step0Labels = mixedMoment B raw16472step1 raw16472step1Labels := by
      have ha : raw16472step1 = (fun i j => raw16472step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16472step1 raw16472step0; decide +kernel
      have hl : raw16472step1Labels = raw16472step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16472step0 raw16472step0Labels permutation150 permutation3
    mixedMoment B raw16472step1 raw16472step1Labels = mixedMoment B raw16472step2 raw16472step2Labels := by
      have ha : raw16472step2 = -raw16472step1 := by apply Matrix.ext; change ∀ i j, raw16472step2 i j = -(raw16472step1 i j); unfold raw16472step2 raw16472step1; decide +kernel
      have hl : raw16472step2Labels = raw16472step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4003 node4003Labels := by rfl

def raw16473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16473Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16473step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16473step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16473step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16473 raw16473Labels = mixedMoment B node3976 node3976Labels := by
  calc
    mixedMoment B raw16473 raw16473Labels = mixedMoment B raw16473step0 raw16473step0Labels := by
      have ha : raw16473step0 = (fun i j => raw16473 (permutation306 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16473step0 raw16473; decide +kernel
      have hl : raw16473step0Labels = raw16473Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16473 raw16473Labels permutation306 permutation6
    mixedMoment B raw16473step0 raw16473step0Labels = mixedMoment B raw16473step1 raw16473step1Labels := by
      have ha : raw16473step1 = -raw16473step0 := by apply Matrix.ext; change ∀ i j, raw16473step1 i j = -(raw16473step0 i j); unfold raw16473step1 raw16473step0; decide +kernel
      have hl : raw16473step1Labels = raw16473step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3976 node3976Labels := by rfl

def raw16474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16474Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16474step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16474step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16474step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16474step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16474step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16474 raw16474Labels = mixedMoment B node3995 node3995Labels := by
  calc
    mixedMoment B raw16474 raw16474Labels = mixedMoment B raw16474step0 raw16474step0Labels := by
      have hz : ∀ j, raw16474 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16474step0 = (fun i j => raw16474 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16474step0 raw16474; decide +kernel
      have hl : raw16474step0Labels = raw16474Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16474 raw16474Labels permutation346 hz
    mixedMoment B raw16474step0 raw16474step0Labels = mixedMoment B raw16474step1 raw16474step1Labels := by
      have ha : raw16474step1 = (fun i j => raw16474step0 (permutation63 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16474step1 raw16474step0; decide +kernel
      have hl : raw16474step1Labels = raw16474step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16474step0 raw16474step0Labels permutation63 permutation6
    mixedMoment B raw16474step1 raw16474step1Labels = mixedMoment B raw16474step2 raw16474step2Labels := by
      have ha : raw16474step2 = -raw16474step1 := by apply Matrix.ext; change ∀ i j, raw16474step2 i j = -(raw16474step1 i j); unfold raw16474step2 raw16474step1; decide +kernel
      have hl : raw16474step2Labels = raw16474step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3995 node3995Labels := by rfl

def raw16475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16475Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16475step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16475step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16475step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16475 raw16475Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw16475 raw16475Labels = mixedMoment B raw16475step0 raw16475step0Labels := by
      have hz : ∀ j, raw16475 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16475step0 = (fun i j => raw16475 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16475step0 raw16475; decide +kernel
      have hl : raw16475step0Labels = raw16475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16475 raw16475Labels permutation346 hz
    mixedMoment B raw16475step0 raw16475step0Labels = mixedMoment B raw16475step1 raw16475step1Labels := by
      have ha : raw16475step1 = (fun i j => raw16475step0 (permutation123 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16475step1 raw16475step0; decide +kernel
      have hl : raw16475step1Labels = raw16475step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16475step0 raw16475step0Labels permutation123 permutation6
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw16476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16476Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16476step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16476step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw16476step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16476step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16476step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16476 raw16476Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw16476 raw16476Labels = mixedMoment B raw16476step0 raw16476step0Labels := by
      have hz : ∀ j, raw16476 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16476step0 = (fun i j => raw16476 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16476step0 raw16476; decide +kernel
      have hl : raw16476step0Labels = raw16476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16476 raw16476Labels permutation346 hz
    mixedMoment B raw16476step0 raw16476step0Labels = mixedMoment B raw16476step1 raw16476step1Labels := by
      have ha : raw16476step1 = (fun i j => raw16476step0 (permutation63 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16476step1 raw16476step0; decide +kernel
      have hl : raw16476step1Labels = raw16476step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16476step0 raw16476step0Labels permutation63 permutation6
    mixedMoment B raw16476step1 raw16476step1Labels = mixedMoment B raw16476step2 raw16476step2Labels := by
      have ha : raw16476step2 = -raw16476step1 := by apply Matrix.ext; change ∀ i j, raw16476step2 i j = -(raw16476step1 i j); unfold raw16476step2 raw16476step1; decide +kernel
      have hl : raw16476step2Labels = raw16476step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3981 node3981Labels := by rfl

def raw16477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16477Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16477step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16477step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16477step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16477 raw16477Labels = mixedMoment B node2251 node2251Labels := by
  calc
    mixedMoment B raw16477 raw16477Labels = mixedMoment B raw16477step0 raw16477step0Labels := by
      have hz : ∀ j, raw16477 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16477step0 = (fun i j => raw16477 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16477step0 raw16477; decide +kernel
      have hl : raw16477step0Labels = raw16477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16477 raw16477Labels permutation346 hz
    mixedMoment B raw16477step0 raw16477step0Labels = mixedMoment B raw16477step1 raw16477step1Labels := by
      have ha : raw16477step1 = (fun i j => raw16477step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16477step1 raw16477step0; decide +kernel
      have hl : raw16477step1Labels = raw16477step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16477step0 raw16477step0Labels permutation38 permutation3
    _ = mixedMoment B node2251 node2251Labels := by rfl

def raw16478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16478Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16478step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16478step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16478 raw16478Labels = mixedMoment B node3802 node3802Labels := by
  calc
    mixedMoment B raw16478 raw16478Labels = mixedMoment B raw16478step0 raw16478step0Labels := by
      have ha : raw16478step0 = (fun i j => raw16478 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16478step0 raw16478; decide +kernel
      have hl : raw16478step0Labels = raw16478Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16478 raw16478Labels permutation182 permutation3
    _ = mixedMoment B node3802 node3802Labels := by rfl

def raw16479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16479Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16479step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16479step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16479step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16479 raw16479Labels = mixedMoment B node3854 node3854Labels := by
  calc
    mixedMoment B raw16479 raw16479Labels = mixedMoment B raw16479step0 raw16479step0Labels := by
      have hz : ∀ j, raw16479 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16479step0 = (fun i j => raw16479 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16479step0 raw16479; decide +kernel
      have hl : raw16479step0Labels = raw16479Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16479 raw16479Labels permutation346 hz
    mixedMoment B raw16479step0 raw16479step0Labels = mixedMoment B raw16479step1 raw16479step1Labels := by
      have ha : raw16479step1 = (fun i j => raw16479step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16479step1 raw16479step0; decide +kernel
      have hl : raw16479step1Labels = raw16479step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16479step0 raw16479step0Labels permutation38 permutation3
    _ = mixedMoment B node3854 node3854Labels := by rfl

def raw16480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16480Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16480step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16480step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw16480step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16480step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw16480step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16480 raw16480Labels = mixedMoment B node3811 node3811Labels := by
  calc
    mixedMoment B raw16480 raw16480Labels = mixedMoment B raw16480step0 raw16480step0Labels := by
      have hz : ∀ j, raw16480 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16480step0 = (fun i j => raw16480 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16480step0 raw16480; decide +kernel
      have hl : raw16480step0Labels = raw16480Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16480 raw16480Labels permutation346 hz
    mixedMoment B raw16480step0 raw16480step0Labels = mixedMoment B raw16480step1 raw16480step1Labels := by
      have ha : raw16480step1 = (fun i j => raw16480step0 (permutation63 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16480step1 raw16480step0; decide +kernel
      have hl : raw16480step1Labels = raw16480step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16480step0 raw16480step0Labels permutation63 permutation6
    mixedMoment B raw16480step1 raw16480step1Labels = mixedMoment B raw16480step2 raw16480step2Labels := by
      have ha : raw16480step2 = -raw16480step1 := by apply Matrix.ext; change ∀ i j, raw16480step2 i j = -(raw16480step1 i j); unfold raw16480step2 raw16480step1; decide +kernel
      have hl : raw16480step2Labels = raw16480step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3811 node3811Labels := by rfl

def raw16481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16481Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16481step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16481step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw16481step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16481step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16481step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16481 raw16481Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw16481 raw16481Labels = mixedMoment B raw16481step0 raw16481step0Labels := by
      have hz : ∀ j, raw16481 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16481step0 = (fun i j => raw16481 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16481step0 raw16481; decide +kernel
      have hl : raw16481step0Labels = raw16481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16481 raw16481Labels permutation346 hz
    mixedMoment B raw16481step0 raw16481step0Labels = mixedMoment B raw16481step1 raw16481step1Labels := by
      have ha : raw16481step1 = (fun i j => raw16481step0 (permutation63 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16481step1 raw16481step0; decide +kernel
      have hl : raw16481step1Labels = raw16481step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16481step0 raw16481step0Labels permutation63 permutation6
    mixedMoment B raw16481step1 raw16481step1Labels = mixedMoment B raw16481step2 raw16481step2Labels := by
      have ha : raw16481step2 = -raw16481step1 := by apply Matrix.ext; change ∀ i j, raw16481step2 i j = -(raw16481step1 i j); unfold raw16481step2 raw16481step1; decide +kernel
      have hl : raw16481step2Labels = raw16481step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3813 node3813Labels := by rfl

def raw16482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16482Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16482step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16482 raw16482Labels = mixedMoment B node2086 node2086Labels := by
  calc
    mixedMoment B raw16482 raw16482Labels = mixedMoment B raw16482step0 raw16482step0Labels := by
      have ha : raw16482step0 = (fun i j => raw16482 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16482step0 raw16482; decide +kernel
      have hl : raw16482step0Labels = raw16482Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16482 raw16482Labels permutation160 permutation3
    _ = mixedMoment B node2086 node2086Labels := by rfl

def raw16483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16483Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16483step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16483step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16483 raw16483Labels = mixedMoment B node3724 node3724Labels := by
  calc
    mixedMoment B raw16483 raw16483Labels = mixedMoment B raw16483step0 raw16483step0Labels := by
      have ha : raw16483step0 = (fun i j => raw16483 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16483step0 raw16483; decide +kernel
      have hl : raw16483step0Labels = raw16483Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16483 raw16483Labels permutation160 permutation3
    _ = mixedMoment B node3724 node3724Labels := by rfl

def raw16484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16484Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16484step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16484 raw16484Labels = mixedMoment B node3827 node3827Labels := by
  calc
    mixedMoment B raw16484 raw16484Labels = mixedMoment B raw16484step0 raw16484step0Labels := by
      have ha : raw16484step0 = (fun i j => raw16484 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16484step0 raw16484; decide +kernel
      have hl : raw16484step0Labels = raw16484Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16484 raw16484Labels permutation202 permutation3
    _ = mixedMoment B node3827 node3827Labels := by rfl

def raw16485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16485Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16485step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16485 raw16485Labels = mixedMoment B node3866 node3866Labels := by
  calc
    mixedMoment B raw16485 raw16485Labels = mixedMoment B raw16485step0 raw16485step0Labels := by
      have ha : raw16485step0 = (fun i j => raw16485 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16485step0 raw16485; decide +kernel
      have hl : raw16485step0Labels = raw16485Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16485 raw16485Labels permutation166 permutation3
    _ = mixedMoment B node3866 node3866Labels := by rfl

def raw16486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16486Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16486step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16486 raw16486Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw16486 raw16486Labels = mixedMoment B raw16486step0 raw16486step0Labels := by
      have ha : raw16486step0 = (fun i j => raw16486 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16486step0 raw16486; decide +kernel
      have hl : raw16486step0Labels = raw16486Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16486 raw16486Labels permutation161 permutation3
    _ = mixedMoment B node3880 node3880Labels := by rfl

def raw16487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16487Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16487step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16487step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16487 raw16487Labels = mixedMoment B node2102 node2102Labels := by
  calc
    mixedMoment B raw16487 raw16487Labels = mixedMoment B raw16487step0 raw16487step0Labels := by
      have hz : ∀ j, raw16487 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16487step0 = (fun i j => raw16487 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16487step0 raw16487; decide +kernel
      have hl : raw16487step0Labels = raw16487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16487 raw16487Labels permutation346 hz
    mixedMoment B raw16487step0 raw16487step0Labels = mixedMoment B raw16487step1 raw16487step1Labels := by
      have ha : raw16487step1 = (fun i j => raw16487step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16487step1 raw16487step0; decide +kernel
      have hl : raw16487step1Labels = raw16487step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16487step0 raw16487step0Labels permutation34 permutation3
    _ = mixedMoment B node2102 node2102Labels := by rfl

def raw16488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16488Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16488step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16488step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16488 raw16488Labels = mixedMoment B node3733 node3733Labels := by
  calc
    mixedMoment B raw16488 raw16488Labels = mixedMoment B raw16488step0 raw16488step0Labels := by
      have hz : ∀ j, raw16488 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16488step0 = (fun i j => raw16488 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16488step0 raw16488; decide +kernel
      have hl : raw16488step0Labels = raw16488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16488 raw16488Labels permutation346 hz
    mixedMoment B raw16488step0 raw16488step0Labels = mixedMoment B raw16488step1 raw16488step1Labels := by
      have ha : raw16488step1 = (fun i j => raw16488step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16488step1 raw16488step0; decide +kernel
      have hl : raw16488step1Labels = raw16488step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16488step0 raw16488step0Labels permutation34 permutation3
    _ = mixedMoment B node3733 node3733Labels := by rfl

def raw16489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16489Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16489step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16489step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16489 raw16489Labels = mixedMoment B node3785 node3785Labels := by
  calc
    mixedMoment B raw16489 raw16489Labels = mixedMoment B raw16489step0 raw16489step0Labels := by
      have ha : raw16489step0 = (fun i j => raw16489 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16489step0 raw16489; decide +kernel
      have hl : raw16489step0Labels = raw16489Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16489 raw16489Labels permutation178 permutation3
    _ = mixedMoment B node3785 node3785Labels := by rfl

def raw16490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16490Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16490step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw16490step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16490 raw16490Labels = mixedMoment B node3868 node3868Labels := by
  calc
    mixedMoment B raw16490 raw16490Labels = mixedMoment B raw16490step0 raw16490step0Labels := by
      have hz : ∀ j, raw16490 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16490step0 = (fun i j => raw16490 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16490step0 raw16490; decide +kernel
      have hl : raw16490step0Labels = raw16490Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16490 raw16490Labels permutation346 hz
    mixedMoment B raw16490step0 raw16490step0Labels = mixedMoment B raw16490step1 raw16490step1Labels := by
      have ha : raw16490step1 = (fun i j => raw16490step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16490step1 raw16490step0; decide +kernel
      have hl : raw16490step1Labels = raw16490step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16490step0 raw16490step0Labels permutation34 permutation3
    _ = mixedMoment B node3868 node3868Labels := by rfl

def raw16491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16491Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16491step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16491step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16491 raw16491Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw16491 raw16491Labels = mixedMoment B raw16491step0 raw16491step0Labels := by
      have hz : ∀ j, raw16491 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16491step0 = (fun i j => raw16491 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16491step0 raw16491; decide +kernel
      have hl : raw16491step0Labels = raw16491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16491 raw16491Labels permutation346 hz
    mixedMoment B raw16491step0 raw16491step0Labels = mixedMoment B raw16491step1 raw16491step1Labels := by
      have ha : raw16491step1 = (fun i j => raw16491step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16491step1 raw16491step0; decide +kernel
      have hl : raw16491step1Labels = raw16491step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16491step0 raw16491step0Labels permutation35 permutation3
    _ = mixedMoment B node3884 node3884Labels := by rfl

def raw16492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16492Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16492step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16492 raw16492Labels = mixedMoment B node2094 node2094Labels := by
  calc
    mixedMoment B raw16492 raw16492Labels = mixedMoment B raw16492step0 raw16492step0Labels := by
      have hz : ∀ j, raw16492 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16492step0 = (fun i j => raw16492 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16492step0 raw16492; decide +kernel
      have hl : raw16492step0Labels = raw16492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16492 raw16492Labels permutation346 hz
    mixedMoment B raw16492step0 raw16492step0Labels = mixedMoment B raw16492step1 raw16492step1Labels := by
      have ha : raw16492step1 = (fun i j => raw16492step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16492step1 raw16492step0; decide +kernel
      have hl : raw16492step1Labels = raw16492step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16492step0 raw16492step0Labels permutation32 permutation3
    _ = mixedMoment B node2094 node2094Labels := by rfl

def raw16493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16493Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16493step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16493step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16493 raw16493Labels = mixedMoment B node3728 node3728Labels := by
  calc
    mixedMoment B raw16493 raw16493Labels = mixedMoment B raw16493step0 raw16493step0Labels := by
      have hz : ∀ j, raw16493 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16493step0 = (fun i j => raw16493 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16493step0 raw16493; decide +kernel
      have hl : raw16493step0Labels = raw16493Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16493 raw16493Labels permutation346 hz
    mixedMoment B raw16493step0 raw16493step0Labels = mixedMoment B raw16493step1 raw16493step1Labels := by
      have ha : raw16493step1 = (fun i j => raw16493step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16493step1 raw16493step0; decide +kernel
      have hl : raw16493step1Labels = raw16493step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16493step0 raw16493step0Labels permutation32 permutation3
    _ = mixedMoment B node3728 node3728Labels := by rfl

def raw16494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16494Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16494step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16494step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16494 raw16494Labels = mixedMoment B node3783 node3783Labels := by
  calc
    mixedMoment B raw16494 raw16494Labels = mixedMoment B raw16494step0 raw16494step0Labels := by
      have ha : raw16494step0 = (fun i j => raw16494 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16494step0 raw16494; decide +kernel
      have hl : raw16494step0Labels = raw16494Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16494 raw16494Labels permutation176 permutation3
    _ = mixedMoment B node3783 node3783Labels := by rfl

def raw16495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16495Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw16495step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16495step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16495 raw16495Labels = mixedMoment B node3831 node3831Labels := by
  calc
    mixedMoment B raw16495 raw16495Labels = mixedMoment B raw16495step0 raw16495step0Labels := by
      have hz : ∀ j, raw16495 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16495step0 = (fun i j => raw16495 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16495step0 raw16495; decide +kernel
      have hl : raw16495step0Labels = raw16495Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16495 raw16495Labels permutation346 hz
    mixedMoment B raw16495step0 raw16495step0Labels = mixedMoment B raw16495step1 raw16495step1Labels := by
      have ha : raw16495step1 = (fun i j => raw16495step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16495step1 raw16495step0; decide +kernel
      have hl : raw16495step1Labels = raw16495step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16495step0 raw16495step0Labels permutation38 permutation3
    _ = mixedMoment B node3831 node3831Labels := by rfl

def raw16496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw16496Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw16496step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16496step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16496 raw16496Labels = mixedMoment B node3883 node3883Labels := by
  calc
    mixedMoment B raw16496 raw16496Labels = mixedMoment B raw16496step0 raw16496step0Labels := by
      have hz : ∀ j, raw16496 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16496step0 = (fun i j => raw16496 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16496step0 raw16496; decide +kernel
      have hl : raw16496step0Labels = raw16496Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16496 raw16496Labels permutation346 hz
    mixedMoment B raw16496step0 raw16496step0Labels = mixedMoment B raw16496step1 raw16496step1Labels := by
      have ha : raw16496step1 = (fun i j => raw16496step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16496step1 raw16496step0; decide +kernel
      have hl : raw16496step1Labels = raw16496step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16496step0 raw16496step0Labels permutation33 permutation3
    _ = mixedMoment B node3883 node3883Labels := by rfl

def raw16497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16497Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16497step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw16497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16497 raw16497Labels = mixedMoment B node2087 node2087Labels := by
  calc
    mixedMoment B raw16497 raw16497Labels = mixedMoment B raw16497step0 raw16497step0Labels := by
      have hz : ∀ j, raw16497 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16497step0 = (fun i j => raw16497 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16497step0 raw16497; decide +kernel
      have hl : raw16497step0Labels = raw16497Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16497 raw16497Labels permutation346 hz
    mixedMoment B raw16497step0 raw16497step0Labels = mixedMoment B raw16497step1 raw16497step1Labels := by
      have ha : raw16497step1 = (fun i j => raw16497step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16497step1 raw16497step0; decide +kernel
      have hl : raw16497step1Labels = raw16497step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16497step0 raw16497step0Labels permutation32 permutation3
    _ = mixedMoment B node2087 node2087Labels := by rfl

def raw16498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16498Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16498step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw16498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16498step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw16498step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16498 raw16498Labels = mixedMoment B node2620 node2620Labels := by
  calc
    mixedMoment B raw16498 raw16498Labels = mixedMoment B raw16498step0 raw16498step0Labels := by
      have hz : ∀ j, raw16498 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16498step0 = (fun i j => raw16498 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16498step0 raw16498; decide +kernel
      have hl : raw16498step0Labels = raw16498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16498 raw16498Labels permutation346 hz
    mixedMoment B raw16498step0 raw16498step0Labels = mixedMoment B raw16498step1 raw16498step1Labels := by
      have ha : raw16498step1 = (fun i j => raw16498step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16498step1 raw16498step0; decide +kernel
      have hl : raw16498step1Labels = raw16498step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16498step0 raw16498step0Labels permutation151 permutation3
    mixedMoment B raw16498step1 raw16498step1Labels = mixedMoment B raw16498step2 raw16498step2Labels := by
      have ha : raw16498step2 = -raw16498step1 := by apply Matrix.ext; change ∀ i j, raw16498step2 i j = -(raw16498step1 i j); unfold raw16498step2 raw16498step1; decide +kernel
      have hl : raw16498step2Labels = raw16498step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2620 node2620Labels := by rfl

def raw16499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16499Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16499step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16499step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16499step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16499 raw16499Labels = mixedMoment B node2613 node2613Labels := by
  calc
    mixedMoment B raw16499 raw16499Labels = mixedMoment B raw16499step0 raw16499step0Labels := by
      have ha : raw16499step0 = (fun i j => raw16499 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16499step0 raw16499; decide +kernel
      have hl : raw16499step0Labels = raw16499Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16499 raw16499Labels permutation686 permutation3
    mixedMoment B raw16499step0 raw16499step0Labels = mixedMoment B raw16499step1 raw16499step1Labels := by
      have ha : raw16499step1 = -raw16499step0 := by apply Matrix.ext; change ∀ i j, raw16499step1 i j = -(raw16499step0 i j); unfold raw16499step1 raw16499step0; decide +kernel
      have hl : raw16499step1Labels = raw16499step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2613 node2613Labels := by rfl

def raw16500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16500Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16500step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16500step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw16500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16500step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16500step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16500 raw16500Labels = mixedMoment B node2632 node2632Labels := by
  calc
    mixedMoment B raw16500 raw16500Labels = mixedMoment B raw16500step0 raw16500step0Labels := by
      have hz : ∀ j, raw16500 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16500step0 = (fun i j => raw16500 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16500step0 raw16500; decide +kernel
      have hl : raw16500step0Labels = raw16500Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16500 raw16500Labels permutation346 hz
    mixedMoment B raw16500step0 raw16500step0Labels = mixedMoment B raw16500step1 raw16500step1Labels := by
      have ha : raw16500step1 = (fun i j => raw16500step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16500step1 raw16500step0; decide +kernel
      have hl : raw16500step1Labels = raw16500step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16500step0 raw16500step0Labels permutation149 permutation3
    mixedMoment B raw16500step1 raw16500step1Labels = mixedMoment B raw16500step2 raw16500step2Labels := by
      have ha : raw16500step2 = -raw16500step1 := by apply Matrix.ext; change ∀ i j, raw16500step2 i j = -(raw16500step1 i j); unfold raw16500step2 raw16500step1; decide +kernel
      have hl : raw16500step2Labels = raw16500step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2632 node2632Labels := by rfl

def raw16501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw16501Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw16501step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16501step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw16501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16501step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw16501step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16501 raw16501Labels = mixedMoment B node2729 node2729Labels := by
  calc
    mixedMoment B raw16501 raw16501Labels = mixedMoment B raw16501step0 raw16501step0Labels := by
      have hz : ∀ j, raw16501 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16501step0 = (fun i j => raw16501 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16501step0 raw16501; decide +kernel
      have hl : raw16501step0Labels = raw16501Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16501 raw16501Labels permutation346 hz
    mixedMoment B raw16501step0 raw16501step0Labels = mixedMoment B raw16501step1 raw16501step1Labels := by
      have ha : raw16501step1 = (fun i j => raw16501step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16501step1 raw16501step0; decide +kernel
      have hl : raw16501step1Labels = raw16501step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16501step0 raw16501step0Labels permutation145 permutation3
    mixedMoment B raw16501step1 raw16501step1Labels = mixedMoment B raw16501step2 raw16501step2Labels := by
      have ha : raw16501step2 = -raw16501step1 := by apply Matrix.ext; change ∀ i j, raw16501step2 i j = -(raw16501step1 i j); unfold raw16501step2 raw16501step1; decide +kernel
      have hl : raw16501step2Labels = raw16501step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2729 node2729Labels := by rfl

def raw16502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16502Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16502step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16502step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16502step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16502step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16502step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16502step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16502 raw16502Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw16502 raw16502Labels = mixedMoment B raw16502step0 raw16502step0Labels := by
      have hz : ∀ j, raw16502 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16502step0 = (fun i j => raw16502 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16502step0 raw16502; decide +kernel
      have hl : raw16502step0Labels = raw16502Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16502 raw16502Labels permutation346 hz
    mixedMoment B raw16502step0 raw16502step0Labels = mixedMoment B raw16502step1 raw16502step1Labels := by
      have ha : raw16502step1 = (fun i j => raw16502step0 (permutation63 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16502step1 raw16502step0; decide +kernel
      have hl : raw16502step1Labels = raw16502step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16502step0 raw16502step0Labels permutation63 permutation7
    mixedMoment B raw16502step1 raw16502step1Labels = mixedMoment B raw16502step2 raw16502step2Labels := by
      have ha : raw16502step2 = -raw16502step1 := by apply Matrix.ext; change ∀ i j, raw16502step2 i j = -(raw16502step1 i j); unfold raw16502step2 raw16502step1; decide +kernel
      have hl : raw16502step2Labels = raw16502step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16502step2 raw16502step2Labels = mixedMoment B raw16502step3 raw16502step3Labels := by
      have ha : raw16502step3 = raw16502step2 := by apply Matrix.ext; unfold raw16502step3 raw16502step2; decide +kernel
      have hl : raw16502step2Labels = labelEmbedding1 ∘ raw16502step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16502step2 raw16502step2Labels raw16502step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3845 node3845Labels := by rfl

def raw16503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16503Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16503step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16503step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16503step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16503step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16503 raw16503Labels = mixedMoment B node3953 node3953Labels := by
  calc
    mixedMoment B raw16503 raw16503Labels = mixedMoment B raw16503step0 raw16503step0Labels := by
      have ha : raw16503step0 = (fun i j => raw16503 (permutation572 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16503step0 raw16503; decide +kernel
      have hl : raw16503step0Labels = raw16503Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16503 raw16503Labels permutation572 permutation7
    mixedMoment B raw16503step0 raw16503step0Labels = mixedMoment B raw16503step1 raw16503step1Labels := by
      have ha : raw16503step1 = raw16503step0 := by apply Matrix.ext; unfold raw16503step1 raw16503step0; decide +kernel
      have hl : raw16503step0Labels = labelEmbedding1 ∘ raw16503step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16503step0 raw16503step0Labels raw16503step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3953 node3953Labels := by rfl

def raw16504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16504Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16504step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16504step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16504step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16504step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16504step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16504 raw16504Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw16504 raw16504Labels = mixedMoment B raw16504step0 raw16504step0Labels := by
      have hz : ∀ j, raw16504 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16504step0 = (fun i j => raw16504 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16504step0 raw16504; decide +kernel
      have hl : raw16504step0Labels = raw16504Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16504 raw16504Labels permutation346 hz
    mixedMoment B raw16504step0 raw16504step0Labels = mixedMoment B raw16504step1 raw16504step1Labels := by
      have ha : raw16504step1 = (fun i j => raw16504step0 (permutation123 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16504step1 raw16504step0; decide +kernel
      have hl : raw16504step1Labels = raw16504step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16504step0 raw16504step0Labels permutation123 permutation7
    mixedMoment B raw16504step1 raw16504step1Labels = mixedMoment B raw16504step2 raw16504step2Labels := by
      have ha : raw16504step2 = raw16504step1 := by apply Matrix.ext; unfold raw16504step2 raw16504step1; decide +kernel
      have hl : raw16504step1Labels = labelEmbedding1 ∘ raw16504step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16504step1 raw16504step1Labels raw16504step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw16505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16505Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16505step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16505step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16505step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16505step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16505step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16505step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16505step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16505 raw16505Labels = mixedMoment B node3993 node3993Labels := by
  calc
    mixedMoment B raw16505 raw16505Labels = mixedMoment B raw16505step0 raw16505step0Labels := by
      have hz : ∀ j, raw16505 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16505step0 = (fun i j => raw16505 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16505step0 raw16505; decide +kernel
      have hl : raw16505step0Labels = raw16505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16505 raw16505Labels permutation346 hz
    mixedMoment B raw16505step0 raw16505step0Labels = mixedMoment B raw16505step1 raw16505step1Labels := by
      have ha : raw16505step1 = (fun i j => raw16505step0 (permutation63 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16505step1 raw16505step0; decide +kernel
      have hl : raw16505step1Labels = raw16505step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16505step0 raw16505step0Labels permutation63 permutation7
    mixedMoment B raw16505step1 raw16505step1Labels = mixedMoment B raw16505step2 raw16505step2Labels := by
      have ha : raw16505step2 = -raw16505step1 := by apply Matrix.ext; change ∀ i j, raw16505step2 i j = -(raw16505step1 i j); unfold raw16505step2 raw16505step1; decide +kernel
      have hl : raw16505step2Labels = raw16505step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16505step2 raw16505step2Labels = mixedMoment B raw16505step3 raw16505step3Labels := by
      have ha : raw16505step3 = raw16505step2 := by apply Matrix.ext; unfold raw16505step3 raw16505step2; decide +kernel
      have hl : raw16505step2Labels = labelEmbedding1 ∘ raw16505step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16505step2 raw16505step2Labels raw16505step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3993 node3993Labels := by rfl

def raw16506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16506Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16506step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16506step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16506step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16506step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16506step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16506 raw16506Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw16506 raw16506Labels = mixedMoment B raw16506step0 raw16506step0Labels := by
      have hz : ∀ j, raw16506 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16506step0 = (fun i j => raw16506 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16506step0 raw16506; decide +kernel
      have hl : raw16506step0Labels = raw16506Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16506 raw16506Labels permutation346 hz
    mixedMoment B raw16506step0 raw16506step0Labels = mixedMoment B raw16506step1 raw16506step1Labels := by
      have ha : raw16506step1 = (fun i j => raw16506step0 (permutation123 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16506step1 raw16506step0; decide +kernel
      have hl : raw16506step1Labels = raw16506step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16506step0 raw16506step0Labels permutation123 permutation7
    mixedMoment B raw16506step1 raw16506step1Labels = mixedMoment B raw16506step2 raw16506step2Labels := by
      have ha : raw16506step2 = raw16506step1 := by apply Matrix.ext; unfold raw16506step2 raw16506step1; decide +kernel
      have hl : raw16506step1Labels = labelEmbedding1 ∘ raw16506step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16506step1 raw16506step1Labels raw16506step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3981 node3981Labels := by rfl

def raw16507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16507Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16507step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16507step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16507step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16507step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16507step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16507step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16507 raw16507Labels = mixedMoment B node2108 node2108Labels := by
  calc
    mixedMoment B raw16507 raw16507Labels = mixedMoment B raw16507step0 raw16507step0Labels := by
      have hz : ∀ j, raw16507 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16507step0 = (fun i j => raw16507 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16507step0 raw16507; decide +kernel
      have hl : raw16507step0Labels = raw16507Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16507 raw16507Labels permutation346 hz
    mixedMoment B raw16507step0 raw16507step0Labels = mixedMoment B raw16507step1 raw16507step1Labels := by
      have ha : raw16507step1 = (fun i j => raw16507step0 (permutation47 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16507step1 raw16507step0; decide +kernel
      have hl : raw16507step1Labels = raw16507step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16507step0 raw16507step0Labels permutation47 permutation5
    mixedMoment B raw16507step1 raw16507step1Labels = mixedMoment B raw16507step2 raw16507step2Labels := by
      have ha : raw16507step2 = -raw16507step1 := by apply Matrix.ext; change ∀ i j, raw16507step2 i j = -(raw16507step1 i j); unfold raw16507step2 raw16507step1; decide +kernel
      have hl : raw16507step2Labels = raw16507step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16507step2 raw16507step2Labels = mixedMoment B raw16507step3 raw16507step3Labels := by
      have ha : raw16507step3 = raw16507step2 := by apply Matrix.ext; unfold raw16507step3 raw16507step2; decide +kernel
      have hl : raw16507step2Labels = labelEmbedding1 ∘ raw16507step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16507step2 raw16507step2Labels raw16507step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2108 node2108Labels := by rfl

def raw16508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16508Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16508step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16508step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16508step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16508step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16508step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16508 raw16508Labels = mixedMoment B node3788 node3788Labels := by
  calc
    mixedMoment B raw16508 raw16508Labels = mixedMoment B raw16508step0 raw16508step0Labels := by
      have ha : raw16508step0 = (fun i j => raw16508 (permutation191 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16508step0 raw16508; decide +kernel
      have hl : raw16508step0Labels = raw16508Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16508 raw16508Labels permutation191 permutation5
    mixedMoment B raw16508step0 raw16508step0Labels = mixedMoment B raw16508step1 raw16508step1Labels := by
      have ha : raw16508step1 = -raw16508step0 := by apply Matrix.ext; change ∀ i j, raw16508step1 i j = -(raw16508step0 i j); unfold raw16508step1 raw16508step0; decide +kernel
      have hl : raw16508step1Labels = raw16508step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16508step1 raw16508step1Labels = mixedMoment B raw16508step2 raw16508step2Labels := by
      have ha : raw16508step2 = raw16508step1 := by apply Matrix.ext; unfold raw16508step2 raw16508step1; decide +kernel
      have hl : raw16508step1Labels = labelEmbedding1 ∘ raw16508step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16508step1 raw16508step1Labels raw16508step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3788 node3788Labels := by rfl

def raw16509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16509Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16509step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16509step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16509step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16509step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16509step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16509step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16509step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16509 raw16509Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw16509 raw16509Labels = mixedMoment B raw16509step0 raw16509step0Labels := by
      have hz : ∀ j, raw16509 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16509step0 = (fun i j => raw16509 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16509step0 raw16509; decide +kernel
      have hl : raw16509step0Labels = raw16509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16509 raw16509Labels permutation346 hz
    mixedMoment B raw16509step0 raw16509step0Labels = mixedMoment B raw16509step1 raw16509step1Labels := by
      have ha : raw16509step1 = (fun i j => raw16509step0 (permutation47 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16509step1 raw16509step0; decide +kernel
      have hl : raw16509step1Labels = raw16509step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16509step0 raw16509step0Labels permutation47 permutation5
    mixedMoment B raw16509step1 raw16509step1Labels = mixedMoment B raw16509step2 raw16509step2Labels := by
      have ha : raw16509step2 = -raw16509step1 := by apply Matrix.ext; change ∀ i j, raw16509step2 i j = -(raw16509step1 i j); unfold raw16509step2 raw16509step1; decide +kernel
      have hl : raw16509step2Labels = raw16509step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16509step2 raw16509step2Labels = mixedMoment B raw16509step3 raw16509step3Labels := by
      have ha : raw16509step3 = raw16509step2 := by apply Matrix.ext; unfold raw16509step3 raw16509step2; decide +kernel
      have hl : raw16509step2Labels = labelEmbedding1 ∘ raw16509step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16509step2 raw16509step2Labels raw16509step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3877 node3877Labels := by rfl

def raw16510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16510Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw16510step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16510step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16510step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16510step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16510step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16510step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16510step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16510 raw16510Labels = mixedMoment B node3738 node3738Labels := by
  calc
    mixedMoment B raw16510 raw16510Labels = mixedMoment B raw16510step0 raw16510step0Labels := by
      have hz : ∀ j, raw16510 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16510step0 = (fun i j => raw16510 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16510step0 raw16510; decide +kernel
      have hl : raw16510step0Labels = raw16510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16510 raw16510Labels permutation346 hz
    mixedMoment B raw16510step0 raw16510step0Labels = mixedMoment B raw16510step1 raw16510step1Labels := by
      have ha : raw16510step1 = (fun i j => raw16510step0 (permutation47 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16510step1 raw16510step0; decide +kernel
      have hl : raw16510step1Labels = raw16510step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16510step0 raw16510step0Labels permutation47 permutation5
    mixedMoment B raw16510step1 raw16510step1Labels = mixedMoment B raw16510step2 raw16510step2Labels := by
      have ha : raw16510step2 = -raw16510step1 := by apply Matrix.ext; change ∀ i j, raw16510step2 i j = -(raw16510step1 i j); unfold raw16510step2 raw16510step1; decide +kernel
      have hl : raw16510step2Labels = raw16510step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16510step2 raw16510step2Labels = mixedMoment B raw16510step3 raw16510step3Labels := by
      have ha : raw16510step3 = raw16510step2 := by apply Matrix.ext; unfold raw16510step3 raw16510step2; decide +kernel
      have hl : raw16510step2Labels = labelEmbedding1 ∘ raw16510step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16510step2 raw16510step2Labels raw16510step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3738 node3738Labels := by rfl

def raw16511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16511Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw16511step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw16511step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16511step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16511step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16511step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16511step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16511 raw16511Labels = mixedMoment B node3883 node3883Labels := by
  calc
    mixedMoment B raw16511 raw16511Labels = mixedMoment B raw16511step0 raw16511step0Labels := by
      have hz : ∀ j, raw16511 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16511step0 = (fun i j => raw16511 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16511step0 raw16511; decide +kernel
      have hl : raw16511step0Labels = raw16511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16511 raw16511Labels permutation346 hz
    mixedMoment B raw16511step0 raw16511step0Labels = mixedMoment B raw16511step1 raw16511step1Labels := by
      have ha : raw16511step1 = (fun i j => raw16511step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16511step1 raw16511step0; decide +kernel
      have hl : raw16511step1Labels = raw16511step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16511step0 raw16511step0Labels permutation49 permutation5
    mixedMoment B raw16511step1 raw16511step1Labels = mixedMoment B raw16511step2 raw16511step2Labels := by
      have ha : raw16511step2 = -raw16511step1 := by apply Matrix.ext; change ∀ i j, raw16511step2 i j = -(raw16511step1 i j); unfold raw16511step2 raw16511step1; decide +kernel
      have hl : raw16511step2Labels = raw16511step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16511step2 raw16511step2Labels = mixedMoment B raw16511step3 raw16511step3Labels := by
      have ha : raw16511step3 = raw16511step2 := by apply Matrix.ext; unfold raw16511step3 raw16511step2; decide +kernel
      have hl : raw16511step2Labels = labelEmbedding1 ∘ raw16511step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16511step2 raw16511step2Labels raw16511step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3883 node3883Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
