import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw33664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33664step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw33664step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33664 raw33664Labels = mixedMoment B node4867 node4867Labels := by
  calc
    mixedMoment B raw33664 raw33664Labels = mixedMoment B raw33664step0 raw33664step0Labels := by
      have hz : ∀ j, raw33664 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33664step0 = (fun i j => raw33664 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33664step0 raw33664; decide +kernel
      have hl : raw33664step0Labels = raw33664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33664 raw33664Labels permutation346 hz
    mixedMoment B raw33664step0 raw33664step0Labels = mixedMoment B raw33664step1 raw33664step1Labels := by
      have ha : raw33664step1 = (fun i j => raw33664step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33664step1 raw33664step0; decide +kernel
      have hl : raw33664step1Labels = raw33664step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33664step0 raw33664step0Labels permutation35 permutation2
    _ = mixedMoment B node4867 node4867Labels := by rfl

def raw33665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33665 raw33665Labels = mixedMoment B node4700 node4700Labels := by
  calc
    mixedMoment B raw33665 raw33665Labels = mixedMoment B raw33665step0 raw33665step0Labels := by
      have hz : ∀ j, raw33665 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33665step0 = (fun i j => raw33665 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33665step0 raw33665; decide +kernel
      have hl : raw33665step0Labels = raw33665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33665 raw33665Labels permutation346 hz
    _ = mixedMoment B node4700 node4700Labels := by rfl

def raw33666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33666step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33666step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33666 raw33666Labels = mixedMoment B node4773 node4773Labels := by
  calc
    mixedMoment B raw33666 raw33666Labels = mixedMoment B raw33666step0 raw33666step0Labels := by
      have ha : raw33666step0 = (fun i j => raw33666 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33666step0 raw33666; decide +kernel
      have hl : raw33666step0Labels = raw33666Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33666 raw33666Labels permutation176 permutation2
    _ = mixedMoment B node4773 node4773Labels := by rfl

def raw33667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw33667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw33667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw33667step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33667 raw33667Labels = mixedMoment B node4867 node4867Labels := by
  calc
    mixedMoment B raw33667 raw33667Labels = mixedMoment B raw33667step0 raw33667step0Labels := by
      have hz : ∀ j, raw33667 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33667step0 = (fun i j => raw33667 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33667step0 raw33667; decide +kernel
      have hl : raw33667step0Labels = raw33667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33667 raw33667Labels permutation346 hz
    mixedMoment B raw33667step0 raw33667step0Labels = mixedMoment B raw33667step1 raw33667step1Labels := by
      have ha : raw33667step1 = (fun i j => raw33667step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33667step1 raw33667step0; decide +kernel
      have hl : raw33667step1Labels = raw33667step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33667step0 raw33667step0Labels permutation33 permutation2
    _ = mixedMoment B node4867 node4867Labels := by rfl

def raw33668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33668 raw33668Labels = mixedMoment B node4697 node4697Labels := by
  calc
    mixedMoment B raw33668 raw33668Labels = mixedMoment B raw33668step0 raw33668step0Labels := by
      have hz : ∀ j, raw33668 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33668step0 = (fun i j => raw33668 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33668step0 raw33668; decide +kernel
      have hl : raw33668step0Labels = raw33668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33668 raw33668Labels permutation346 hz
    _ = mixedMoment B node4697 node4697Labels := by rfl

def raw33669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33669step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33669 raw33669Labels = mixedMoment B node4771 node4771Labels := by
  calc
    mixedMoment B raw33669 raw33669Labels = mixedMoment B raw33669step0 raw33669step0Labels := by
      have ha : raw33669step0 = (fun i j => raw33669 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33669step0 raw33669; decide +kernel
      have hl : raw33669step0Labels = raw33669Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33669 raw33669Labels permutation176 permutation2
    _ = mixedMoment B node4771 node4771Labels := by rfl

def raw33670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw33670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33670step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33670step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw33670step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33670 raw33670Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw33670 raw33670Labels = mixedMoment B raw33670step0 raw33670step0Labels := by
      have hz : ∀ j, raw33670 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33670step0 = (fun i j => raw33670 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33670step0 raw33670; decide +kernel
      have hl : raw33670step0Labels = raw33670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33670 raw33670Labels permutation520 hz
    mixedMoment B raw33670step0 raw33670step0Labels = mixedMoment B raw33670step1 raw33670step1Labels := by
      have hz : ∀ j, raw33670step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33670step1 = (fun i j => raw33670step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33670step1 raw33670step0; decide +kernel
      have hl : raw33670step1Labels = raw33670step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33670step0 raw33670step0Labels permutation80 hz
    _ = mixedMoment B node4868 node4868Labels := by rfl

def raw33671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33671Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33671step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, -2, 3], ![-2, 2, 0]]
def raw33671step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33671step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw33671step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33671 raw33671Labels = mixedMoment B node3079 node3079Labels := by
  calc
    mixedMoment B raw33671 raw33671Labels = mixedMoment B raw33671step0 raw33671step0Labels := by
      have hz : ∀ j, raw33671 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33671step0 = (fun i j => raw33671 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33671step0 raw33671; decide +kernel
      have hl : raw33671step0Labels = raw33671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33671 raw33671Labels permutation346 hz
    mixedMoment B raw33671step0 raw33671step0Labels = mixedMoment B raw33671step1 raw33671step1Labels := by
      have ha : raw33671step1 = (fun i j => raw33671step0 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33671step1 raw33671step0; decide +kernel
      have hl : raw33671step1Labels = raw33671step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33671step0 raw33671step0Labels permutation40 permutation6
    mixedMoment B raw33671step1 raw33671step1Labels = mixedMoment B raw33671step2 raw33671step2Labels := by
      have ha : raw33671step2 = -raw33671step1 := by apply Matrix.ext; change ∀ i j, raw33671step2 i j = -(raw33671step1 i j); unfold raw33671step2 raw33671step1; decide +kernel
      have hl : raw33671step2Labels = raw33671step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3079 node3079Labels := by rfl

def raw33672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33672Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33672step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw33672step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33672step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33672step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33672 raw33672Labels = mixedMoment B node3066 node3066Labels := by
  calc
    mixedMoment B raw33672 raw33672Labels = mixedMoment B raw33672step0 raw33672step0Labels := by
      have ha : raw33672step0 = (fun i j => raw33672 (permutation214 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33672step0 raw33672; decide +kernel
      have hl : raw33672step0Labels = raw33672Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33672 raw33672Labels permutation214 permutation6
    mixedMoment B raw33672step0 raw33672step0Labels = mixedMoment B raw33672step1 raw33672step1Labels := by
      have ha : raw33672step1 = -raw33672step0 := by apply Matrix.ext; change ∀ i j, raw33672step1 i j = -(raw33672step0 i j); unfold raw33672step1 raw33672step0; decide +kernel
      have hl : raw33672step1Labels = raw33672step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3066 node3066Labels := by rfl

def raw33673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33673Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33673step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33673step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33673step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33673step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw33673step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33673step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw33673step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33673 raw33673Labels = mixedMoment B node3103 node3103Labels := by
  calc
    mixedMoment B raw33673 raw33673Labels = mixedMoment B raw33673step0 raw33673step0Labels := by
      have hz : ∀ j, raw33673 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33673step0 = (fun i j => raw33673 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33673step0 raw33673; decide +kernel
      have hl : raw33673step0Labels = raw33673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33673 raw33673Labels permutation434 hz
    mixedMoment B raw33673step0 raw33673step0Labels = mixedMoment B raw33673step1 raw33673step1Labels := by
      have hz : ∀ j, raw33673step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33673step1 = (fun i j => raw33673step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33673step1 raw33673step0; decide +kernel
      have hl : raw33673step1Labels = raw33673step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33673step0 raw33673step0Labels permutation80 hz
    mixedMoment B raw33673step1 raw33673step1Labels = mixedMoment B raw33673step2 raw33673step2Labels := by
      have ha : raw33673step2 = (fun i j => raw33673step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33673step2 raw33673step1; decide +kernel
      have hl : raw33673step2Labels = raw33673step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33673step1 raw33673step1Labels permutation10 permutation6
    mixedMoment B raw33673step2 raw33673step2Labels = mixedMoment B raw33673step3 raw33673step3Labels := by
      have ha : raw33673step3 = -raw33673step2 := by apply Matrix.ext; change ∀ i j, raw33673step3 i j = -(raw33673step2 i j); unfold raw33673step3 raw33673step2; decide +kernel
      have hl : raw33673step3Labels = raw33673step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3103 node3103Labels := by rfl

def raw33674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33674Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33674step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33674step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33674step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33674step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw33674step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33674step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw33674step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33674 raw33674Labels = mixedMoment B node3103 node3103Labels := by
  calc
    mixedMoment B raw33674 raw33674Labels = mixedMoment B raw33674step0 raw33674step0Labels := by
      have hz : ∀ j, raw33674 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33674step0 = (fun i j => raw33674 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33674step0 raw33674; decide +kernel
      have hl : raw33674step0Labels = raw33674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33674 raw33674Labels permutation520 hz
    mixedMoment B raw33674step0 raw33674step0Labels = mixedMoment B raw33674step1 raw33674step1Labels := by
      have hz : ∀ j, raw33674step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33674step1 = (fun i j => raw33674step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33674step1 raw33674step0; decide +kernel
      have hl : raw33674step1Labels = raw33674step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33674step0 raw33674step0Labels permutation80 hz
    mixedMoment B raw33674step1 raw33674step1Labels = mixedMoment B raw33674step2 raw33674step2Labels := by
      have ha : raw33674step2 = (fun i j => raw33674step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33674step2 raw33674step1; decide +kernel
      have hl : raw33674step2Labels = raw33674step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33674step1 raw33674step1Labels permutation10 permutation6
    mixedMoment B raw33674step2 raw33674step2Labels = mixedMoment B raw33674step3 raw33674step3Labels := by
      have ha : raw33674step3 = -raw33674step2 := by apply Matrix.ext; change ∀ i j, raw33674step3 i j = -(raw33674step2 i j); unfold raw33674step3 raw33674step2; decide +kernel
      have hl : raw33674step3Labels = raw33674step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3103 node3103Labels := by rfl

def raw33675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33675Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33675step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw33675step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33675step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw33675step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33675 raw33675Labels = mixedMoment B node3078 node3078Labels := by
  calc
    mixedMoment B raw33675 raw33675Labels = mixedMoment B raw33675step0 raw33675step0Labels := by
      have hz : ∀ j, raw33675 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33675step0 = (fun i j => raw33675 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33675step0 raw33675; decide +kernel
      have hl : raw33675step0Labels = raw33675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33675 raw33675Labels permutation346 hz
    mixedMoment B raw33675step0 raw33675step0Labels = mixedMoment B raw33675step1 raw33675step1Labels := by
      have ha : raw33675step1 = (fun i j => raw33675step0 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33675step1 raw33675step0; decide +kernel
      have hl : raw33675step1Labels = raw33675step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33675step0 raw33675step0Labels permutation40 permutation6
    mixedMoment B raw33675step1 raw33675step1Labels = mixedMoment B raw33675step2 raw33675step2Labels := by
      have ha : raw33675step2 = -raw33675step1 := by apply Matrix.ext; change ∀ i j, raw33675step2 i j = -(raw33675step1 i j); unfold raw33675step2 raw33675step1; decide +kernel
      have hl : raw33675step2Labels = raw33675step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3078 node3078Labels := by rfl

def raw33676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33676Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33676step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33676step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33676 raw33676Labels = mixedMoment B node3130 node3130Labels := by
  calc
    mixedMoment B raw33676 raw33676Labels = mixedMoment B raw33676step0 raw33676step0Labels := by
      have ha : raw33676step0 = (fun i j => raw33676 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33676step0 raw33676; decide +kernel
      have hl : raw33676step0Labels = raw33676Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33676 raw33676Labels permutation152 permutation3
    _ = mixedMoment B node3130 node3130Labels := by rfl

def raw33677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33677Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33677step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33677step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33677 raw33677Labels = mixedMoment B node3185 node3185Labels := by
  calc
    mixedMoment B raw33677 raw33677Labels = mixedMoment B raw33677step0 raw33677step0Labels := by
      have hz : ∀ j, raw33677 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33677step0 = (fun i j => raw33677 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33677step0 raw33677; decide +kernel
      have hl : raw33677step0Labels = raw33677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33677 raw33677Labels permutation434 hz
    mixedMoment B raw33677step0 raw33677step0Labels = mixedMoment B raw33677step1 raw33677step1Labels := by
      have ha : raw33677step1 = (fun i j => raw33677step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33677step1 raw33677step0; decide +kernel
      have hl : raw33677step1Labels = raw33677step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33677step0 raw33677step0Labels permutation32 permutation3
    _ = mixedMoment B node3185 node3185Labels := by rfl

def raw33678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33678Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33678step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33678step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33678 raw33678Labels = mixedMoment B node3185 node3185Labels := by
  calc
    mixedMoment B raw33678 raw33678Labels = mixedMoment B raw33678step0 raw33678step0Labels := by
      have hz : ∀ j, raw33678 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33678step0 = (fun i j => raw33678 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33678step0 raw33678; decide +kernel
      have hl : raw33678step0Labels = raw33678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33678 raw33678Labels permutation520 hz
    mixedMoment B raw33678step0 raw33678step0Labels = mixedMoment B raw33678step1 raw33678step1Labels := by
      have ha : raw33678step1 = (fun i j => raw33678step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33678step1 raw33678step0; decide +kernel
      have hl : raw33678step1Labels = raw33678step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33678step0 raw33678step0Labels permutation32 permutation3
    _ = mixedMoment B node3185 node3185Labels := by rfl

def raw33679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33679Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33679step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33679step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33679 raw33679Labels = mixedMoment B node3179 node3179Labels := by
  calc
    mixedMoment B raw33679 raw33679Labels = mixedMoment B raw33679step0 raw33679step0Labels := by
      have ha : raw33679step0 = (fun i j => raw33679 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33679step0 raw33679; decide +kernel
      have hl : raw33679step0Labels = raw33679Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33679 raw33679Labels permutation170 permutation3
    _ = mixedMoment B node3179 node3179Labels := by rfl

def raw33680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33680Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33680step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33680step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33680 raw33680Labels = mixedMoment B node3131 node3131Labels := by
  calc
    mixedMoment B raw33680 raw33680Labels = mixedMoment B raw33680step0 raw33680step0Labels := by
      have hz : ∀ j, raw33680 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33680step0 = (fun i j => raw33680 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33680step0 raw33680; decide +kernel
      have hl : raw33680step0Labels = raw33680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33680 raw33680Labels permutation346 hz
    mixedMoment B raw33680step0 raw33680step0Labels = mixedMoment B raw33680step1 raw33680step1Labels := by
      have ha : raw33680step1 = (fun i j => raw33680step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33680step1 raw33680step0; decide +kernel
      have hl : raw33680step1Labels = raw33680step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33680step0 raw33680step0Labels permutation35 permutation3
    _ = mixedMoment B node3131 node3131Labels := by rfl

def raw33681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33681Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33681step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33681step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33681 raw33681Labels = mixedMoment B node3163 node3163Labels := by
  calc
    mixedMoment B raw33681 raw33681Labels = mixedMoment B raw33681step0 raw33681step0Labels := by
      have ha : raw33681step0 = (fun i j => raw33681 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33681step0 raw33681; decide +kernel
      have hl : raw33681step0Labels = raw33681Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33681 raw33681Labels permutation155 permutation3
    _ = mixedMoment B node3163 node3163Labels := by rfl

def raw33682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33682Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33682step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33682step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33682step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33682step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw33682step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33682 raw33682Labels = mixedMoment B node3187 node3187Labels := by
  calc
    mixedMoment B raw33682 raw33682Labels = mixedMoment B raw33682step0 raw33682step0Labels := by
      have hz : ∀ j, raw33682 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33682step0 = (fun i j => raw33682 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33682step0 raw33682; decide +kernel
      have hl : raw33682step0Labels = raw33682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33682 raw33682Labels permutation520 hz
    mixedMoment B raw33682step0 raw33682step0Labels = mixedMoment B raw33682step1 raw33682step1Labels := by
      have hz : ∀ j, raw33682step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33682step1 = (fun i j => raw33682step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33682step1 raw33682step0; decide +kernel
      have hl : raw33682step1Labels = raw33682step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33682step0 raw33682step0Labels permutation80 hz
    mixedMoment B raw33682step1 raw33682step1Labels = mixedMoment B raw33682step2 raw33682step2Labels := by
      have ha : raw33682step2 = (fun i j => raw33682step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33682step2 raw33682step1; decide +kernel
      have hl : raw33682step2Labels = raw33682step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33682step1 raw33682step1Labels permutation9 permutation3
    _ = mixedMoment B node3187 node3187Labels := by rfl

def raw33683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33683Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33683step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33683step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33683 raw33683Labels = mixedMoment B node3180 node3180Labels := by
  calc
    mixedMoment B raw33683 raw33683Labels = mixedMoment B raw33683step0 raw33683step0Labels := by
      have hz : ∀ j, raw33683 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33683step0 = (fun i j => raw33683 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33683step0 raw33683; decide +kernel
      have hl : raw33683step0Labels = raw33683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33683 raw33683Labels permutation346 hz
    mixedMoment B raw33683step0 raw33683step0Labels = mixedMoment B raw33683step1 raw33683step1Labels := by
      have ha : raw33683step1 = (fun i j => raw33683step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33683step1 raw33683step0; decide +kernel
      have hl : raw33683step1Labels = raw33683step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33683step0 raw33683step0Labels permutation37 permutation3
    _ = mixedMoment B node3180 node3180Labels := by rfl

def raw33684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33684Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33684step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33684step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33684 raw33684Labels = mixedMoment B node3131 node3131Labels := by
  calc
    mixedMoment B raw33684 raw33684Labels = mixedMoment B raw33684step0 raw33684step0Labels := by
      have hz : ∀ j, raw33684 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33684step0 = (fun i j => raw33684 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33684step0 raw33684; decide +kernel
      have hl : raw33684step0Labels = raw33684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33684 raw33684Labels permutation346 hz
    mixedMoment B raw33684step0 raw33684step0Labels = mixedMoment B raw33684step1 raw33684step1Labels := by
      have ha : raw33684step1 = (fun i j => raw33684step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33684step1 raw33684step0; decide +kernel
      have hl : raw33684step1Labels = raw33684step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33684step0 raw33684step0Labels permutation33 permutation3
    _ = mixedMoment B node3131 node3131Labels := by rfl

def raw33685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33685Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33685step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33685step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33685 raw33685Labels = mixedMoment B node3163 node3163Labels := by
  calc
    mixedMoment B raw33685 raw33685Labels = mixedMoment B raw33685step0 raw33685step0Labels := by
      have ha : raw33685step0 = (fun i j => raw33685 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33685step0 raw33685; decide +kernel
      have hl : raw33685step0Labels = raw33685Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33685 raw33685Labels permutation153 permutation3
    _ = mixedMoment B node3163 node3163Labels := by rfl

def raw33686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33686Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33686step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33686step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33686step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33686step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw33686step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33686 raw33686Labels = mixedMoment B node3187 node3187Labels := by
  calc
    mixedMoment B raw33686 raw33686Labels = mixedMoment B raw33686step0 raw33686step0Labels := by
      have hz : ∀ j, raw33686 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33686step0 = (fun i j => raw33686 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33686step0 raw33686; decide +kernel
      have hl : raw33686step0Labels = raw33686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33686 raw33686Labels permutation434 hz
    mixedMoment B raw33686step0 raw33686step0Labels = mixedMoment B raw33686step1 raw33686step1Labels := by
      have hz : ∀ j, raw33686step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33686step1 = (fun i j => raw33686step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33686step1 raw33686step0; decide +kernel
      have hl : raw33686step1Labels = raw33686step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33686step0 raw33686step0Labels permutation80 hz
    mixedMoment B raw33686step1 raw33686step1Labels = mixedMoment B raw33686step2 raw33686step2Labels := by
      have ha : raw33686step2 = (fun i j => raw33686step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33686step2 raw33686step1; decide +kernel
      have hl : raw33686step2Labels = raw33686step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33686step1 raw33686step1Labels permutation9 permutation3
    _ = mixedMoment B node3187 node3187Labels := by rfl

def raw33687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw33687Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw33687step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33687step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33687 raw33687Labels = mixedMoment B node3180 node3180Labels := by
  calc
    mixedMoment B raw33687 raw33687Labels = mixedMoment B raw33687step0 raw33687step0Labels := by
      have hz : ∀ j, raw33687 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33687step0 = (fun i j => raw33687 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33687step0 raw33687; decide +kernel
      have hl : raw33687step0Labels = raw33687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33687 raw33687Labels permutation346 hz
    mixedMoment B raw33687step0 raw33687step0Labels = mixedMoment B raw33687step1 raw33687step1Labels := by
      have ha : raw33687step1 = (fun i j => raw33687step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33687step1 raw33687step0; decide +kernel
      have hl : raw33687step1Labels = raw33687step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33687step0 raw33687step0Labels permutation36 permutation3
    _ = mixedMoment B node3180 node3180Labels := by rfl

def raw33688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33688Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33688step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![1, 0, -1], ![-2, -1, 3], ![-3, 3, 0]]
def raw33688step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33688step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw33688step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33688 raw33688Labels = mixedMoment B node2899 node2899Labels := by
  calc
    mixedMoment B raw33688 raw33688Labels = mixedMoment B raw33688step0 raw33688step0Labels := by
      have hz : ∀ j, raw33688 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33688step0 = (fun i j => raw33688 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33688step0 raw33688; decide +kernel
      have hl : raw33688step0Labels = raw33688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33688 raw33688Labels permutation346 hz
    mixedMoment B raw33688step0 raw33688step0Labels = mixedMoment B raw33688step1 raw33688step1Labels := by
      have ha : raw33688step1 = (fun i j => raw33688step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33688step1 raw33688step0; decide +kernel
      have hl : raw33688step1Labels = raw33688step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33688step0 raw33688step0Labels permutation145 permutation3
    mixedMoment B raw33688step1 raw33688step1Labels = mixedMoment B raw33688step2 raw33688step2Labels := by
      have ha : raw33688step2 = -raw33688step1 := by apply Matrix.ext; change ∀ i j, raw33688step2 i j = -(raw33688step1 i j); unfold raw33688step2 raw33688step1; decide +kernel
      have hl : raw33688step2Labels = raw33688step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2899 node2899Labels := by rfl

def raw33689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33689Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33689step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw33689step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33689step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw33689step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33689 raw33689Labels = mixedMoment B node2895 node2895Labels := by
  calc
    mixedMoment B raw33689 raw33689Labels = mixedMoment B raw33689step0 raw33689step0Labels := by
      have ha : raw33689step0 = (fun i j => raw33689 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33689step0 raw33689; decide +kernel
      have hl : raw33689step0Labels = raw33689Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33689 raw33689Labels permutation664 permutation3
    mixedMoment B raw33689step0 raw33689step0Labels = mixedMoment B raw33689step1 raw33689step1Labels := by
      have ha : raw33689step1 = -raw33689step0 := by apply Matrix.ext; change ∀ i j, raw33689step1 i j = -(raw33689step0 i j); unfold raw33689step1 raw33689step0; decide +kernel
      have hl : raw33689step1Labels = raw33689step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2895 node2895Labels := by rfl

def raw33690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw33690Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33690step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33690step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw33690step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33690step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![-1, -1, 2], ![-3, 3, 0]]
def raw33690step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33690step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw33690step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33690 raw33690Labels = mixedMoment B node2966 node2966Labels := by
  calc
    mixedMoment B raw33690 raw33690Labels = mixedMoment B raw33690step0 raw33690step0Labels := by
      have hz : ∀ j, raw33690 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33690step0 = (fun i j => raw33690 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33690step0 raw33690; decide +kernel
      have hl : raw33690step0Labels = raw33690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33690 raw33690Labels permutation520 hz
    mixedMoment B raw33690step0 raw33690step0Labels = mixedMoment B raw33690step1 raw33690step1Labels := by
      have hz : ∀ j, raw33690step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33690step1 = (fun i j => raw33690step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33690step1 raw33690step0; decide +kernel
      have hl : raw33690step1Labels = raw33690step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33690step0 raw33690step0Labels permutation80 hz
    mixedMoment B raw33690step1 raw33690step1Labels = mixedMoment B raw33690step2 raw33690step2Labels := by
      have ha : raw33690step2 = (fun i j => raw33690step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33690step2 raw33690step1; decide +kernel
      have hl : raw33690step2Labels = raw33690step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33690step1 raw33690step1Labels permutation31 permutation3
    mixedMoment B raw33690step2 raw33690step2Labels = mixedMoment B raw33690step3 raw33690step3Labels := by
      have ha : raw33690step3 = -raw33690step2 := by apply Matrix.ext; change ∀ i j, raw33690step3 i j = -(raw33690step2 i j); unfold raw33690step3 raw33690step2; decide +kernel
      have hl : raw33690step3Labels = raw33690step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2966 node2966Labels := by rfl

def raw33691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33691Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33691step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-2, 0, 2]]
def raw33691step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33691step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw33691step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33691step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw33691step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33691 raw33691Labels = mixedMoment B node2748 node2748Labels := by
  calc
    mixedMoment B raw33691 raw33691Labels = mixedMoment B raw33691step0 raw33691step0Labels := by
      have hz : ∀ j, raw33691 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33691step0 = (fun i j => raw33691 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33691step0 raw33691; decide +kernel
      have hl : raw33691step0Labels = raw33691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33691 raw33691Labels permutation346 hz
    mixedMoment B raw33691step0 raw33691step0Labels = mixedMoment B raw33691step1 raw33691step1Labels := by
      have ha : raw33691step1 = (fun i j => raw33691step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33691step1 raw33691step0; decide +kernel
      have hl : raw33691step1Labels = raw33691step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33691step0 raw33691step0Labels permutation40 permutation7
    mixedMoment B raw33691step1 raw33691step1Labels = mixedMoment B raw33691step2 raw33691step2Labels := by
      have ha : raw33691step2 = -raw33691step1 := by apply Matrix.ext; change ∀ i j, raw33691step2 i j = -(raw33691step1 i j); unfold raw33691step2 raw33691step1; decide +kernel
      have hl : raw33691step2Labels = raw33691step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33691step2 raw33691step2Labels = mixedMoment B raw33691step3 raw33691step3Labels := by
      have ha : raw33691step3 = raw33691step2 := by apply Matrix.ext; unfold raw33691step3 raw33691step2; decide +kernel
      have hl : raw33691step2Labels = labelEmbedding1 ∘ raw33691step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33691step2 raw33691step2Labels raw33691step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2748 node2748Labels := by rfl

def raw33692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33692Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33692step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw33692step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33692step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33692step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33692step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33692step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33692 raw33692Labels = mixedMoment B node2708 node2708Labels := by
  calc
    mixedMoment B raw33692 raw33692Labels = mixedMoment B raw33692step0 raw33692step0Labels := by
      have ha : raw33692step0 = (fun i j => raw33692 (permutation184 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33692step0 raw33692; decide +kernel
      have hl : raw33692step0Labels = raw33692Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33692 raw33692Labels permutation184 permutation7
    mixedMoment B raw33692step0 raw33692step0Labels = mixedMoment B raw33692step1 raw33692step1Labels := by
      have ha : raw33692step1 = -raw33692step0 := by apply Matrix.ext; change ∀ i j, raw33692step1 i j = -(raw33692step0 i j); unfold raw33692step1 raw33692step0; decide +kernel
      have hl : raw33692step1Labels = raw33692step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33692step1 raw33692step1Labels = mixedMoment B raw33692step2 raw33692step2Labels := by
      have ha : raw33692step2 = raw33692step1 := by apply Matrix.ext; unfold raw33692step2 raw33692step1; decide +kernel
      have hl : raw33692step1Labels = labelEmbedding1 ∘ raw33692step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33692step1 raw33692step1Labels raw33692step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2708 node2708Labels := by rfl

def raw33693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33693Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33693step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33693step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33693step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33693step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw33693step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33693step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33693step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33693step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33693step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33693 raw33693Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw33693 raw33693Labels = mixedMoment B raw33693step0 raw33693step0Labels := by
      have hz : ∀ j, raw33693 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33693step0 = (fun i j => raw33693 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33693step0 raw33693; decide +kernel
      have hl : raw33693step0Labels = raw33693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33693 raw33693Labels permutation434 hz
    mixedMoment B raw33693step0 raw33693step0Labels = mixedMoment B raw33693step1 raw33693step1Labels := by
      have hz : ∀ j, raw33693step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33693step1 = (fun i j => raw33693step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33693step1 raw33693step0; decide +kernel
      have hl : raw33693step1Labels = raw33693step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33693step0 raw33693step0Labels permutation80 hz
    mixedMoment B raw33693step1 raw33693step1Labels = mixedMoment B raw33693step2 raw33693step2Labels := by
      have ha : raw33693step2 = (fun i j => raw33693step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33693step2 raw33693step1; decide +kernel
      have hl : raw33693step2Labels = raw33693step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33693step1 raw33693step1Labels permutation10 permutation7
    mixedMoment B raw33693step2 raw33693step2Labels = mixedMoment B raw33693step3 raw33693step3Labels := by
      have ha : raw33693step3 = -raw33693step2 := by apply Matrix.ext; change ∀ i j, raw33693step3 i j = -(raw33693step2 i j); unfold raw33693step3 raw33693step2; decide +kernel
      have hl : raw33693step3Labels = raw33693step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33693step3 raw33693step3Labels = mixedMoment B raw33693step4 raw33693step4Labels := by
      have ha : raw33693step4 = raw33693step3 := by apply Matrix.ext; unfold raw33693step4 raw33693step3; decide +kernel
      have hl : raw33693step3Labels = labelEmbedding1 ∘ raw33693step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33693step3 raw33693step3Labels raw33693step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2765 node2765Labels := by rfl

def raw33694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33694Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33694step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33694step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33694step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33694step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw33694step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33694step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33694step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33694step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33694step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33694 raw33694Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw33694 raw33694Labels = mixedMoment B raw33694step0 raw33694step0Labels := by
      have hz : ∀ j, raw33694 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33694step0 = (fun i j => raw33694 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33694step0 raw33694; decide +kernel
      have hl : raw33694step0Labels = raw33694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33694 raw33694Labels permutation520 hz
    mixedMoment B raw33694step0 raw33694step0Labels = mixedMoment B raw33694step1 raw33694step1Labels := by
      have hz : ∀ j, raw33694step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33694step1 = (fun i j => raw33694step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33694step1 raw33694step0; decide +kernel
      have hl : raw33694step1Labels = raw33694step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33694step0 raw33694step0Labels permutation80 hz
    mixedMoment B raw33694step1 raw33694step1Labels = mixedMoment B raw33694step2 raw33694step2Labels := by
      have ha : raw33694step2 = (fun i j => raw33694step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33694step2 raw33694step1; decide +kernel
      have hl : raw33694step2Labels = raw33694step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33694step1 raw33694step1Labels permutation10 permutation7
    mixedMoment B raw33694step2 raw33694step2Labels = mixedMoment B raw33694step3 raw33694step3Labels := by
      have ha : raw33694step3 = -raw33694step2 := by apply Matrix.ext; change ∀ i j, raw33694step3 i j = -(raw33694step2 i j); unfold raw33694step3 raw33694step2; decide +kernel
      have hl : raw33694step3Labels = raw33694step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33694step3 raw33694step3Labels = mixedMoment B raw33694step4 raw33694step4Labels := by
      have ha : raw33694step4 = raw33694step3 := by apply Matrix.ext; unfold raw33694step4 raw33694step3; decide +kernel
      have hl : raw33694step3Labels = labelEmbedding1 ∘ raw33694step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33694step3 raw33694step3Labels raw33694step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2765 node2765Labels := by rfl

def raw33695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33695Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33695step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw33695step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33695step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw33695step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33695step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw33695step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33695 raw33695Labels = mixedMoment B node2751 node2751Labels := by
  calc
    mixedMoment B raw33695 raw33695Labels = mixedMoment B raw33695step0 raw33695step0Labels := by
      have hz : ∀ j, raw33695 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33695step0 = (fun i j => raw33695 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33695step0 raw33695; decide +kernel
      have hl : raw33695step0Labels = raw33695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33695 raw33695Labels permutation346 hz
    mixedMoment B raw33695step0 raw33695step0Labels = mixedMoment B raw33695step1 raw33695step1Labels := by
      have ha : raw33695step1 = (fun i j => raw33695step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33695step1 raw33695step0; decide +kernel
      have hl : raw33695step1Labels = raw33695step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33695step0 raw33695step0Labels permutation40 permutation7
    mixedMoment B raw33695step1 raw33695step1Labels = mixedMoment B raw33695step2 raw33695step2Labels := by
      have ha : raw33695step2 = -raw33695step1 := by apply Matrix.ext; change ∀ i j, raw33695step2 i j = -(raw33695step1 i j); unfold raw33695step2 raw33695step1; decide +kernel
      have hl : raw33695step2Labels = raw33695step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33695step2 raw33695step2Labels = mixedMoment B raw33695step3 raw33695step3Labels := by
      have ha : raw33695step3 = raw33695step2 := by apply Matrix.ext; unfold raw33695step3 raw33695step2; decide +kernel
      have hl : raw33695step2Labels = labelEmbedding1 ∘ raw33695step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33695step2 raw33695step2Labels raw33695step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2751 node2751Labels := by rfl

def raw33696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33696Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-2, 0, 2]]
def raw33696step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33696step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw33696step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33696step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw33696step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33696 raw33696Labels = mixedMoment B node2231 node2231Labels := by
  calc
    mixedMoment B raw33696 raw33696Labels = mixedMoment B raw33696step0 raw33696step0Labels := by
      have ha : raw33696step0 = (fun i j => raw33696 (permutation184 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33696step0 raw33696; decide +kernel
      have hl : raw33696step0Labels = raw33696Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33696 raw33696Labels permutation184 permutation7
    mixedMoment B raw33696step0 raw33696step0Labels = mixedMoment B raw33696step1 raw33696step1Labels := by
      have ha : raw33696step1 = -raw33696step0 := by apply Matrix.ext; change ∀ i j, raw33696step1 i j = -(raw33696step0 i j); unfold raw33696step1 raw33696step0; decide +kernel
      have hl : raw33696step1Labels = raw33696step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33696step1 raw33696step1Labels = mixedMoment B raw33696step2 raw33696step2Labels := by
      have ha : raw33696step2 = raw33696step1 := by apply Matrix.ext; unfold raw33696step2 raw33696step1; decide +kernel
      have hl : raw33696step1Labels = labelEmbedding1 ∘ raw33696step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33696step1 raw33696step1Labels raw33696step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2231 node2231Labels := by rfl

def raw33697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33697Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33697step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw33697step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33697step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33697step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33697step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33697step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33697 raw33697Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw33697 raw33697Labels = mixedMoment B raw33697step0 raw33697step0Labels := by
      have hz : ∀ j, raw33697 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33697step0 = (fun i j => raw33697 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33697step0 raw33697; decide +kernel
      have hl : raw33697step0Labels = raw33697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33697 raw33697Labels permutation434 hz
    mixedMoment B raw33697step0 raw33697step0Labels = mixedMoment B raw33697step1 raw33697step1Labels := by
      have ha : raw33697step1 = (fun i j => raw33697step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33697step1 raw33697step0; decide +kernel
      have hl : raw33697step1Labels = raw33697step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33697step0 raw33697step0Labels permutation40 permutation7
    mixedMoment B raw33697step1 raw33697step1Labels = mixedMoment B raw33697step2 raw33697step2Labels := by
      have ha : raw33697step2 = -raw33697step1 := by apply Matrix.ext; change ∀ i j, raw33697step2 i j = -(raw33697step1 i j); unfold raw33697step2 raw33697step1; decide +kernel
      have hl : raw33697step2Labels = raw33697step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33697step2 raw33697step2Labels = mixedMoment B raw33697step3 raw33697step3Labels := by
      have ha : raw33697step3 = raw33697step2 := by apply Matrix.ext; unfold raw33697step3 raw33697step2; decide +kernel
      have hl : raw33697step2Labels = labelEmbedding1 ∘ raw33697step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33697step2 raw33697step2Labels raw33697step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2242 node2242Labels := by rfl

def raw33698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33698Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33698step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw33698step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33698step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33698step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33698step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33698step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33698 raw33698Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw33698 raw33698Labels = mixedMoment B raw33698step0 raw33698step0Labels := by
      have hz : ∀ j, raw33698 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33698step0 = (fun i j => raw33698 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33698step0 raw33698; decide +kernel
      have hl : raw33698step0Labels = raw33698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33698 raw33698Labels permutation520 hz
    mixedMoment B raw33698step0 raw33698step0Labels = mixedMoment B raw33698step1 raw33698step1Labels := by
      have ha : raw33698step1 = (fun i j => raw33698step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33698step1 raw33698step0; decide +kernel
      have hl : raw33698step1Labels = raw33698step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33698step0 raw33698step0Labels permutation40 permutation7
    mixedMoment B raw33698step1 raw33698step1Labels = mixedMoment B raw33698step2 raw33698step2Labels := by
      have ha : raw33698step2 = -raw33698step1 := by apply Matrix.ext; change ∀ i j, raw33698step2 i j = -(raw33698step1 i j); unfold raw33698step2 raw33698step1; decide +kernel
      have hl : raw33698step2Labels = raw33698step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33698step2 raw33698step2Labels = mixedMoment B raw33698step3 raw33698step3Labels := by
      have ha : raw33698step3 = raw33698step2 := by apply Matrix.ext; unfold raw33698step3 raw33698step2; decide +kernel
      have hl : raw33698step2Labels = labelEmbedding1 ∘ raw33698step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33698step2 raw33698step2Labels raw33698step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2242 node2242Labels := by rfl

def raw33699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33699Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33699step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw33699step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33699step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw33699step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33699step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw33699step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33699 raw33699Labels = mixedMoment B node2232 node2232Labels := by
  calc
    mixedMoment B raw33699 raw33699Labels = mixedMoment B raw33699step0 raw33699step0Labels := by
      have ha : raw33699step0 = (fun i j => raw33699 (permutation184 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33699step0 raw33699; decide +kernel
      have hl : raw33699step0Labels = raw33699Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33699 raw33699Labels permutation184 permutation7
    mixedMoment B raw33699step0 raw33699step0Labels = mixedMoment B raw33699step1 raw33699step1Labels := by
      have ha : raw33699step1 = -raw33699step0 := by apply Matrix.ext; change ∀ i j, raw33699step1 i j = -(raw33699step0 i j); unfold raw33699step1 raw33699step0; decide +kernel
      have hl : raw33699step1Labels = raw33699step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33699step1 raw33699step1Labels = mixedMoment B raw33699step2 raw33699step2Labels := by
      have ha : raw33699step2 = raw33699step1 := by apply Matrix.ext; unfold raw33699step2 raw33699step1; decide +kernel
      have hl : raw33699step1Labels = labelEmbedding1 ∘ raw33699step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33699step1 raw33699step1Labels raw33699step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2232 node2232Labels := by rfl

def raw33700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33700Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33700step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 3, -2], ![-2, 0, 2]]
def raw33700step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33700step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw33700step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33700step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw33700step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33700 raw33700Labels = mixedMoment B node2249 node2249Labels := by
  calc
    mixedMoment B raw33700 raw33700Labels = mixedMoment B raw33700step0 raw33700step0Labels := by
      have hz : ∀ j, raw33700 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33700step0 = (fun i j => raw33700 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33700step0 raw33700; decide +kernel
      have hl : raw33700step0Labels = raw33700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33700 raw33700Labels permutation346 hz
    mixedMoment B raw33700step0 raw33700step0Labels = mixedMoment B raw33700step1 raw33700step1Labels := by
      have ha : raw33700step1 = (fun i j => raw33700step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33700step1 raw33700step0; decide +kernel
      have hl : raw33700step1Labels = raw33700step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33700step0 raw33700step0Labels permutation46 permutation7
    mixedMoment B raw33700step1 raw33700step1Labels = mixedMoment B raw33700step2 raw33700step2Labels := by
      have ha : raw33700step2 = -raw33700step1 := by apply Matrix.ext; change ∀ i j, raw33700step2 i j = -(raw33700step1 i j); unfold raw33700step2 raw33700step1; decide +kernel
      have hl : raw33700step2Labels = raw33700step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33700step2 raw33700step2Labels = mixedMoment B raw33700step3 raw33700step3Labels := by
      have ha : raw33700step3 = raw33700step2 := by apply Matrix.ext; unfold raw33700step3 raw33700step2; decide +kernel
      have hl : raw33700step2Labels = labelEmbedding1 ∘ raw33700step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33700step2 raw33700step2Labels raw33700step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2249 node2249Labels := by rfl

def raw33701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33701Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33701step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw33701step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33701step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw33701step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33701step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw33701step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33701 raw33701Labels = mixedMoment B node2194 node2194Labels := by
  calc
    mixedMoment B raw33701 raw33701Labels = mixedMoment B raw33701step0 raw33701step0Labels := by
      have ha : raw33701step0 = (fun i j => raw33701 (permutation190 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33701step0 raw33701; decide +kernel
      have hl : raw33701step0Labels = raw33701Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33701 raw33701Labels permutation190 permutation7
    mixedMoment B raw33701step0 raw33701step0Labels = mixedMoment B raw33701step1 raw33701step1Labels := by
      have ha : raw33701step1 = -raw33701step0 := by apply Matrix.ext; change ∀ i j, raw33701step1 i j = -(raw33701step0 i j); unfold raw33701step1 raw33701step0; decide +kernel
      have hl : raw33701step1Labels = raw33701step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33701step1 raw33701step1Labels = mixedMoment B raw33701step2 raw33701step2Labels := by
      have ha : raw33701step2 = raw33701step1 := by apply Matrix.ext; unfold raw33701step2 raw33701step1; decide +kernel
      have hl : raw33701step1Labels = labelEmbedding1 ∘ raw33701step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33701step1 raw33701step1Labels raw33701step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2194 node2194Labels := by rfl

def raw33702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33702Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33702step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33702step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33702step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33702step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw33702step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33702step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw33702step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33702step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw33702step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33702 raw33702Labels = mixedMoment B node2276 node2276Labels := by
  calc
    mixedMoment B raw33702 raw33702Labels = mixedMoment B raw33702step0 raw33702step0Labels := by
      have hz : ∀ j, raw33702 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33702step0 = (fun i j => raw33702 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33702step0 raw33702; decide +kernel
      have hl : raw33702step0Labels = raw33702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33702 raw33702Labels permutation520 hz
    mixedMoment B raw33702step0 raw33702step0Labels = mixedMoment B raw33702step1 raw33702step1Labels := by
      have hz : ∀ j, raw33702step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33702step1 = (fun i j => raw33702step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33702step1 raw33702step0; decide +kernel
      have hl : raw33702step1Labels = raw33702step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33702step0 raw33702step0Labels permutation80 hz
    mixedMoment B raw33702step1 raw33702step1Labels = mixedMoment B raw33702step2 raw33702step2Labels := by
      have ha : raw33702step2 = (fun i j => raw33702step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33702step2 raw33702step1; decide +kernel
      have hl : raw33702step2Labels = raw33702step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33702step1 raw33702step1Labels permutation10 permutation7
    mixedMoment B raw33702step2 raw33702step2Labels = mixedMoment B raw33702step3 raw33702step3Labels := by
      have ha : raw33702step3 = -raw33702step2 := by apply Matrix.ext; change ∀ i j, raw33702step3 i j = -(raw33702step2 i j); unfold raw33702step3 raw33702step2; decide +kernel
      have hl : raw33702step3Labels = raw33702step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33702step3 raw33702step3Labels = mixedMoment B raw33702step4 raw33702step4Labels := by
      have ha : raw33702step4 = raw33702step3 := by apply Matrix.ext; unfold raw33702step4 raw33702step3; decide +kernel
      have hl : raw33702step3Labels = labelEmbedding1 ∘ raw33702step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33702step3 raw33702step3Labels raw33702step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2276 node2276Labels := by rfl

def raw33703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33703Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33703step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw33703step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33703step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw33703step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33703step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw33703step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33703 raw33703Labels = mixedMoment B node2251 node2251Labels := by
  calc
    mixedMoment B raw33703 raw33703Labels = mixedMoment B raw33703step0 raw33703step0Labels := by
      have hz : ∀ j, raw33703 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33703step0 = (fun i j => raw33703 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33703step0 raw33703; decide +kernel
      have hl : raw33703step0Labels = raw33703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33703 raw33703Labels permutation346 hz
    mixedMoment B raw33703step0 raw33703step0Labels = mixedMoment B raw33703step1 raw33703step1Labels := by
      have ha : raw33703step1 = (fun i j => raw33703step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33703step1 raw33703step0; decide +kernel
      have hl : raw33703step1Labels = raw33703step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33703step0 raw33703step0Labels permutation46 permutation7
    mixedMoment B raw33703step1 raw33703step1Labels = mixedMoment B raw33703step2 raw33703step2Labels := by
      have ha : raw33703step2 = -raw33703step1 := by apply Matrix.ext; change ∀ i j, raw33703step2 i j = -(raw33703step1 i j); unfold raw33703step2 raw33703step1; decide +kernel
      have hl : raw33703step2Labels = raw33703step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33703step2 raw33703step2Labels = mixedMoment B raw33703step3 raw33703step3Labels := by
      have ha : raw33703step3 = raw33703step2 := by apply Matrix.ext; unfold raw33703step3 raw33703step2; decide +kernel
      have hl : raw33703step2Labels = labelEmbedding1 ∘ raw33703step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33703step2 raw33703step2Labels raw33703step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2251 node2251Labels := by rfl

def raw33704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33704Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33704step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 3, -2], ![-2, 0, 2]]
def raw33704step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33704step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw33704step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33704step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw33704step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33704 raw33704Labels = mixedMoment B node2249 node2249Labels := by
  calc
    mixedMoment B raw33704 raw33704Labels = mixedMoment B raw33704step0 raw33704step0Labels := by
      have hz : ∀ j, raw33704 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33704step0 = (fun i j => raw33704 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33704step0 raw33704; decide +kernel
      have hl : raw33704step0Labels = raw33704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33704 raw33704Labels permutation346 hz
    mixedMoment B raw33704step0 raw33704step0Labels = mixedMoment B raw33704step1 raw33704step1Labels := by
      have ha : raw33704step1 = (fun i j => raw33704step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33704step1 raw33704step0; decide +kernel
      have hl : raw33704step1Labels = raw33704step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33704step0 raw33704step0Labels permutation40 permutation7
    mixedMoment B raw33704step1 raw33704step1Labels = mixedMoment B raw33704step2 raw33704step2Labels := by
      have ha : raw33704step2 = -raw33704step1 := by apply Matrix.ext; change ∀ i j, raw33704step2 i j = -(raw33704step1 i j); unfold raw33704step2 raw33704step1; decide +kernel
      have hl : raw33704step2Labels = raw33704step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33704step2 raw33704step2Labels = mixedMoment B raw33704step3 raw33704step3Labels := by
      have ha : raw33704step3 = raw33704step2 := by apply Matrix.ext; unfold raw33704step3 raw33704step2; decide +kernel
      have hl : raw33704step2Labels = labelEmbedding1 ∘ raw33704step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33704step2 raw33704step2Labels raw33704step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2249 node2249Labels := by rfl

def raw33705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33705Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33705step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw33705step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33705step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw33705step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33705step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw33705step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33705 raw33705Labels = mixedMoment B node2194 node2194Labels := by
  calc
    mixedMoment B raw33705 raw33705Labels = mixedMoment B raw33705step0 raw33705step0Labels := by
      have ha : raw33705step0 = (fun i j => raw33705 (permutation184 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33705step0 raw33705; decide +kernel
      have hl : raw33705step0Labels = raw33705Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33705 raw33705Labels permutation184 permutation7
    mixedMoment B raw33705step0 raw33705step0Labels = mixedMoment B raw33705step1 raw33705step1Labels := by
      have ha : raw33705step1 = -raw33705step0 := by apply Matrix.ext; change ∀ i j, raw33705step1 i j = -(raw33705step0 i j); unfold raw33705step1 raw33705step0; decide +kernel
      have hl : raw33705step1Labels = raw33705step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33705step1 raw33705step1Labels = mixedMoment B raw33705step2 raw33705step2Labels := by
      have ha : raw33705step2 = raw33705step1 := by apply Matrix.ext; unfold raw33705step2 raw33705step1; decide +kernel
      have hl : raw33705step1Labels = labelEmbedding1 ∘ raw33705step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33705step1 raw33705step1Labels raw33705step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2194 node2194Labels := by rfl

def raw33706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33706Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33706step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33706step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33706step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33706step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw33706step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33706step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw33706step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33706step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw33706step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33706 raw33706Labels = mixedMoment B node2276 node2276Labels := by
  calc
    mixedMoment B raw33706 raw33706Labels = mixedMoment B raw33706step0 raw33706step0Labels := by
      have hz : ∀ j, raw33706 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33706step0 = (fun i j => raw33706 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33706step0 raw33706; decide +kernel
      have hl : raw33706step0Labels = raw33706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33706 raw33706Labels permutation434 hz
    mixedMoment B raw33706step0 raw33706step0Labels = mixedMoment B raw33706step1 raw33706step1Labels := by
      have hz : ∀ j, raw33706step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33706step1 = (fun i j => raw33706step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33706step1 raw33706step0; decide +kernel
      have hl : raw33706step1Labels = raw33706step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33706step0 raw33706step0Labels permutation80 hz
    mixedMoment B raw33706step1 raw33706step1Labels = mixedMoment B raw33706step2 raw33706step2Labels := by
      have ha : raw33706step2 = (fun i j => raw33706step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33706step2 raw33706step1; decide +kernel
      have hl : raw33706step2Labels = raw33706step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33706step1 raw33706step1Labels permutation10 permutation7
    mixedMoment B raw33706step2 raw33706step2Labels = mixedMoment B raw33706step3 raw33706step3Labels := by
      have ha : raw33706step3 = -raw33706step2 := by apply Matrix.ext; change ∀ i j, raw33706step3 i j = -(raw33706step2 i j); unfold raw33706step3 raw33706step2; decide +kernel
      have hl : raw33706step3Labels = raw33706step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33706step3 raw33706step3Labels = mixedMoment B raw33706step4 raw33706step4Labels := by
      have ha : raw33706step4 = raw33706step3 := by apply Matrix.ext; unfold raw33706step4 raw33706step3; decide +kernel
      have hl : raw33706step3Labels = labelEmbedding1 ∘ raw33706step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33706step3 raw33706step3Labels raw33706step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2276 node2276Labels := by rfl

def raw33707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw33707Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw33707step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw33707step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw33707step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33707step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw33707step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33707 raw33707Labels = mixedMoment B node2251 node2251Labels := by
  calc
    mixedMoment B raw33707 raw33707Labels = mixedMoment B raw33707step0 raw33707step0Labels := by
      have hz : ∀ j, raw33707 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33707step0 = (fun i j => raw33707 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33707step0 raw33707; decide +kernel
      have hl : raw33707step0Labels = raw33707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33707 raw33707Labels permutation346 hz
    mixedMoment B raw33707step0 raw33707step0Labels = mixedMoment B raw33707step1 raw33707step1Labels := by
      have ha : raw33707step1 = (fun i j => raw33707step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33707step1 raw33707step0; decide +kernel
      have hl : raw33707step1Labels = raw33707step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33707step0 raw33707step0Labels permutation40 permutation7
    mixedMoment B raw33707step1 raw33707step1Labels = mixedMoment B raw33707step2 raw33707step2Labels := by
      have ha : raw33707step2 = -raw33707step1 := by apply Matrix.ext; change ∀ i j, raw33707step2 i j = -(raw33707step1 i j); unfold raw33707step2 raw33707step1; decide +kernel
      have hl : raw33707step2Labels = raw33707step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33707step2 raw33707step2Labels = mixedMoment B raw33707step3 raw33707step3Labels := by
      have ha : raw33707step3 = raw33707step2 := by apply Matrix.ext; unfold raw33707step3 raw33707step2; decide +kernel
      have hl : raw33707step2Labels = labelEmbedding1 ∘ raw33707step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33707step2 raw33707step2Labels raw33707step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2251 node2251Labels := by rfl

def raw33708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33708Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33708step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-2, -1, 3]]
def raw33708step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33708step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw33708step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33708step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw33708step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33708 raw33708Labels = mixedMoment B node2239 node2239Labels := by
  calc
    mixedMoment B raw33708 raw33708Labels = mixedMoment B raw33708step0 raw33708step0Labels := by
      have hz : ∀ j, raw33708 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33708step0 = (fun i j => raw33708 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33708step0 raw33708; decide +kernel
      have hl : raw33708step0Labels = raw33708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33708 raw33708Labels permutation346 hz
    mixedMoment B raw33708step0 raw33708step0Labels = mixedMoment B raw33708step1 raw33708step1Labels := by
      have ha : raw33708step1 = (fun i j => raw33708step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33708step1 raw33708step0; decide +kernel
      have hl : raw33708step1Labels = raw33708step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33708step0 raw33708step0Labels permutation40 permutation7
    mixedMoment B raw33708step1 raw33708step1Labels = mixedMoment B raw33708step2 raw33708step2Labels := by
      have ha : raw33708step2 = -raw33708step1 := by apply Matrix.ext; change ∀ i j, raw33708step2 i j = -(raw33708step1 i j); unfold raw33708step2 raw33708step1; decide +kernel
      have hl : raw33708step2Labels = raw33708step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33708step2 raw33708step2Labels = mixedMoment B raw33708step3 raw33708step3Labels := by
      have ha : raw33708step3 = raw33708step2 := by apply Matrix.ext; unfold raw33708step3 raw33708step2; decide +kernel
      have hl : raw33708step2Labels = labelEmbedding1 ∘ raw33708step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33708step2 raw33708step2Labels raw33708step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2239 node2239Labels := by rfl

def raw33709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33709Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33709step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw33709step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33709step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw33709step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33709step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw33709step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33709 raw33709Labels = mixedMoment B node2189 node2189Labels := by
  calc
    mixedMoment B raw33709 raw33709Labels = mixedMoment B raw33709step0 raw33709step0Labels := by
      have ha : raw33709step0 = (fun i j => raw33709 (permutation184 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33709step0 raw33709; decide +kernel
      have hl : raw33709step0Labels = raw33709Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33709 raw33709Labels permutation184 permutation7
    mixedMoment B raw33709step0 raw33709step0Labels = mixedMoment B raw33709step1 raw33709step1Labels := by
      have ha : raw33709step1 = -raw33709step0 := by apply Matrix.ext; change ∀ i j, raw33709step1 i j = -(raw33709step0 i j); unfold raw33709step1 raw33709step0; decide +kernel
      have hl : raw33709step1Labels = raw33709step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33709step1 raw33709step1Labels = mixedMoment B raw33709step2 raw33709step2Labels := by
      have ha : raw33709step2 = raw33709step1 := by apply Matrix.ext; unfold raw33709step2 raw33709step1; decide +kernel
      have hl : raw33709step1Labels = labelEmbedding1 ∘ raw33709step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33709step1 raw33709step1Labels raw33709step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2189 node2189Labels := by rfl

def raw33710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw33710Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33710step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33710step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw33710step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33710step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw33710step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33710step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw33710step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33710step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw33710step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33710 raw33710Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw33710 raw33710Labels = mixedMoment B raw33710step0 raw33710step0Labels := by
      have hz : ∀ j, raw33710 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33710step0 = (fun i j => raw33710 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33710step0 raw33710; decide +kernel
      have hl : raw33710step0Labels = raw33710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33710 raw33710Labels permutation520 hz
    mixedMoment B raw33710step0 raw33710step0Labels = mixedMoment B raw33710step1 raw33710step1Labels := by
      have hz : ∀ j, raw33710step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33710step1 = (fun i j => raw33710step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33710step1 raw33710step0; decide +kernel
      have hl : raw33710step1Labels = raw33710step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33710step0 raw33710step0Labels permutation80 hz
    mixedMoment B raw33710step1 raw33710step1Labels = mixedMoment B raw33710step2 raw33710step2Labels := by
      have ha : raw33710step2 = (fun i j => raw33710step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33710step2 raw33710step1; decide +kernel
      have hl : raw33710step2Labels = raw33710step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33710step1 raw33710step1Labels permutation10 permutation7
    mixedMoment B raw33710step2 raw33710step2Labels = mixedMoment B raw33710step3 raw33710step3Labels := by
      have ha : raw33710step3 = -raw33710step2 := by apply Matrix.ext; change ∀ i j, raw33710step3 i j = -(raw33710step2 i j); unfold raw33710step3 raw33710step2; decide +kernel
      have hl : raw33710step3Labels = raw33710step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33710step3 raw33710step3Labels = mixedMoment B raw33710step4 raw33710step4Labels := by
      have ha : raw33710step4 = raw33710step3 := by apply Matrix.ext; unfold raw33710step4 raw33710step3; decide +kernel
      have hl : raw33710step3Labels = labelEmbedding1 ∘ raw33710step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33710step3 raw33710step3Labels raw33710step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2261 node2261Labels := by rfl

def raw33711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33711Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33711step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33711step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw33711step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33711step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33711step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33711 raw33711Labels = mixedMoment B node3050 node3050Labels := by
  calc
    mixedMoment B raw33711 raw33711Labels = mixedMoment B raw33711step0 raw33711step0Labels := by
      have hz : ∀ j, raw33711 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33711step0 = (fun i j => raw33711 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33711step0 raw33711; decide +kernel
      have hl : raw33711step0Labels = raw33711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33711 raw33711Labels permutation346 hz
    mixedMoment B raw33711step0 raw33711step0Labels = mixedMoment B raw33711step1 raw33711step1Labels := by
      have ha : raw33711step1 = (fun i j => raw33711step0 (permutation77 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33711step1 raw33711step0; decide +kernel
      have hl : raw33711step1Labels = raw33711step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33711step0 raw33711step0Labels permutation77 permutation4
    mixedMoment B raw33711step1 raw33711step1Labels = mixedMoment B raw33711step2 raw33711step2Labels := by
      have ha : raw33711step2 = -raw33711step1 := by apply Matrix.ext; change ∀ i j, raw33711step2 i j = -(raw33711step1 i j); unfold raw33711step2 raw33711step1; decide +kernel
      have hl : raw33711step2Labels = raw33711step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3050 node3050Labels := by rfl

def raw33712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33712Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33712 raw33712Labels = mixedMoment B node1821 node1821Labels := by
  calc
    _ = mixedMoment B node1821 node1821Labels := by rfl

def raw33713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33713Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33713step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33713step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33713step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33713 raw33713Labels = mixedMoment B node1826 node1826Labels := by
  calc
    mixedMoment B raw33713 raw33713Labels = mixedMoment B raw33713step0 raw33713step0Labels := by
      have hz : ∀ j, raw33713 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33713step0 = (fun i j => raw33713 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33713step0 raw33713; decide +kernel
      have hl : raw33713step0Labels = raw33713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33713 raw33713Labels permutation346 hz
    mixedMoment B raw33713step0 raw33713step0Labels = mixedMoment B raw33713step1 raw33713step1Labels := by
      have ha : raw33713step1 = (fun i j => raw33713step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33713step1 raw33713step0; decide +kernel
      have hl : raw33713step1Labels = raw33713step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33713step0 raw33713step0Labels permutation34 permutation2
    _ = mixedMoment B node1826 node1826Labels := by rfl

def raw33714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33714Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33714step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33714 raw33714Labels = mixedMoment B node1826 node1826Labels := by
  calc
    mixedMoment B raw33714 raw33714Labels = mixedMoment B raw33714step0 raw33714step0Labels := by
      have hz : ∀ j, raw33714 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33714step0 = (fun i j => raw33714 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33714step0 raw33714; decide +kernel
      have hl : raw33714step0Labels = raw33714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33714 raw33714Labels permutation346 hz
    _ = mixedMoment B node1826 node1826Labels := by rfl

def raw33715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33715Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33715step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33715 raw33715Labels = mixedMoment B node1823 node1823Labels := by
  calc
    mixedMoment B raw33715 raw33715Labels = mixedMoment B raw33715step0 raw33715step0Labels := by
      have hz : ∀ j, raw33715 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33715step0 = (fun i j => raw33715 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33715step0 raw33715; decide +kernel
      have hl : raw33715step0Labels = raw33715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33715 raw33715Labels permutation346 hz
    _ = mixedMoment B node1823 node1823Labels := by rfl

def raw33716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33716Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33716step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33716 raw33716Labels = mixedMoment B node2106 node2106Labels := by
  calc
    mixedMoment B raw33716 raw33716Labels = mixedMoment B raw33716step0 raw33716step0Labels := by
      have hz : ∀ j, raw33716 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33716step0 = (fun i j => raw33716 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33716step0 raw33716; decide +kernel
      have hl : raw33716step0Labels = raw33716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33716 raw33716Labels permutation434 hz
    _ = mixedMoment B node2106 node2106Labels := by rfl

def raw33717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33717Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33717step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33717 raw33717Labels = mixedMoment B node2106 node2106Labels := by
  calc
    mixedMoment B raw33717 raw33717Labels = mixedMoment B raw33717step0 raw33717step0Labels := by
      have hz : ∀ j, raw33717 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33717step0 = (fun i j => raw33717 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33717step0 raw33717; decide +kernel
      have hl : raw33717step0Labels = raw33717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33717 raw33717Labels permutation520 hz
    _ = mixedMoment B node2106 node2106Labels := by rfl

def raw33718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33718Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33718 raw33718Labels = mixedMoment B node2104 node2104Labels := by
  calc
    _ = mixedMoment B node2104 node2104Labels := by rfl

def raw33719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33719Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33719step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw33719step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33719step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33719step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33719step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33719step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33719 raw33719Labels = mixedMoment B node4255 node4255Labels := by
  calc
    mixedMoment B raw33719 raw33719Labels = mixedMoment B raw33719step0 raw33719step0Labels := by
      have hz : ∀ j, raw33719 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33719step0 = (fun i j => raw33719 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33719step0 raw33719; decide +kernel
      have hl : raw33719step0Labels = raw33719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33719 raw33719Labels permutation346 hz
    mixedMoment B raw33719step0 raw33719step0Labels = mixedMoment B raw33719step1 raw33719step1Labels := by
      have ha : raw33719step1 = (fun i j => raw33719step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33719step1 raw33719step0; decide +kernel
      have hl : raw33719step1Labels = raw33719step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33719step0 raw33719step0Labels permutation40 permutation5
    mixedMoment B raw33719step1 raw33719step1Labels = mixedMoment B raw33719step2 raw33719step2Labels := by
      have ha : raw33719step2 = -raw33719step1 := by apply Matrix.ext; change ∀ i j, raw33719step2 i j = -(raw33719step1 i j); unfold raw33719step2 raw33719step1; decide +kernel
      have hl : raw33719step2Labels = raw33719step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33719step2 raw33719step2Labels = mixedMoment B raw33719step3 raw33719step3Labels := by
      have ha : raw33719step3 = raw33719step2 := by apply Matrix.ext; unfold raw33719step3 raw33719step2; decide +kernel
      have hl : raw33719step2Labels = labelEmbedding8 ∘ raw33719step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33719step2 raw33719step2Labels raw33719step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4255 node4255Labels := by rfl

def raw33720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33720Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33720step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw33720step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33720step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33720step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33720step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33720step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33720 raw33720Labels = mixedMoment B node4731 node4731Labels := by
  calc
    mixedMoment B raw33720 raw33720Labels = mixedMoment B raw33720step0 raw33720step0Labels := by
      have ha : raw33720step0 = (fun i j => raw33720 (permutation184 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33720step0 raw33720; decide +kernel
      have hl : raw33720step0Labels = raw33720Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33720 raw33720Labels permutation184 permutation5
    mixedMoment B raw33720step0 raw33720step0Labels = mixedMoment B raw33720step1 raw33720step1Labels := by
      have ha : raw33720step1 = -raw33720step0 := by apply Matrix.ext; change ∀ i j, raw33720step1 i j = -(raw33720step0 i j); unfold raw33720step1 raw33720step0; decide +kernel
      have hl : raw33720step1Labels = raw33720step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33720step1 raw33720step1Labels = mixedMoment B raw33720step2 raw33720step2Labels := by
      have ha : raw33720step2 = raw33720step1 := by apply Matrix.ext; unfold raw33720step2 raw33720step1; decide +kernel
      have hl : raw33720step1Labels = labelEmbedding8 ∘ raw33720step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33720step1 raw33720step1Labels raw33720step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4731 node4731Labels := by rfl

def raw33721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33721Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33721step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw33721step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33721step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33721step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33721step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33721step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33721 raw33721Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw33721 raw33721Labels = mixedMoment B raw33721step0 raw33721step0Labels := by
      have hz : ∀ j, raw33721 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33721step0 = (fun i j => raw33721 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33721step0 raw33721; decide +kernel
      have hl : raw33721step0Labels = raw33721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33721 raw33721Labels permutation346 hz
    mixedMoment B raw33721step0 raw33721step0Labels = mixedMoment B raw33721step1 raw33721step1Labels := by
      have ha : raw33721step1 = (fun i j => raw33721step0 (permutation46 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33721step1 raw33721step0; decide +kernel
      have hl : raw33721step1Labels = raw33721step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33721step0 raw33721step0Labels permutation46 permutation5
    mixedMoment B raw33721step1 raw33721step1Labels = mixedMoment B raw33721step2 raw33721step2Labels := by
      have ha : raw33721step2 = -raw33721step1 := by apply Matrix.ext; change ∀ i j, raw33721step2 i j = -(raw33721step1 i j); unfold raw33721step2 raw33721step1; decide +kernel
      have hl : raw33721step2Labels = raw33721step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33721step2 raw33721step2Labels = mixedMoment B raw33721step3 raw33721step3Labels := by
      have ha : raw33721step3 = raw33721step2 := by apply Matrix.ext; unfold raw33721step3 raw33721step2; decide +kernel
      have hl : raw33721step2Labels = labelEmbedding8 ∘ raw33721step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33721step2 raw33721step2Labels raw33721step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

def raw33722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33722step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33722step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33722step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33722step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33722 raw33722Labels = mixedMoment B node4230 node4230Labels := by
  calc
    mixedMoment B raw33722 raw33722Labels = mixedMoment B raw33722step0 raw33722step0Labels := by
      have ha : raw33722step0 = (fun i j => raw33722 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33722step0 raw33722; decide +kernel
      have hl : raw33722step0Labels = raw33722Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33722 raw33722Labels permutation160 permutation3
    mixedMoment B raw33722step0 raw33722step0Labels = mixedMoment B raw33722step1 raw33722step1Labels := by
      have ha : raw33722step1 = raw33722step0 := by apply Matrix.ext; unfold raw33722step1 raw33722step0; decide +kernel
      have hl : raw33722step0Labels = labelEmbedding6 ∘ raw33722step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33722step0 raw33722step0Labels raw33722step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4230 node4230Labels := by rfl

def raw33723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33723Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33723step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33723step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33723step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33723step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33723 raw33723Labels = mixedMoment B node4676 node4676Labels := by
  calc
    mixedMoment B raw33723 raw33723Labels = mixedMoment B raw33723step0 raw33723step0Labels := by
      have ha : raw33723step0 = (fun i j => raw33723 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33723step0 raw33723; decide +kernel
      have hl : raw33723step0Labels = raw33723Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33723 raw33723Labels permutation160 permutation3
    mixedMoment B raw33723step0 raw33723step0Labels = mixedMoment B raw33723step1 raw33723step1Labels := by
      have ha : raw33723step1 = raw33723step0 := by apply Matrix.ext; unfold raw33723step1 raw33723step0; decide +kernel
      have hl : raw33723step0Labels = labelEmbedding6 ∘ raw33723step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33723step0 raw33723step0Labels raw33723step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4676 node4676Labels := by rfl

def raw33724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33724Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33724step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33724step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33724step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33724step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33724step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33724step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33724 raw33724Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw33724 raw33724Labels = mixedMoment B raw33724step0 raw33724step0Labels := by
      have ha : raw33724step0 = (fun i j => raw33724 (permutation234 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33724step0 raw33724; decide +kernel
      have hl : raw33724step0Labels = raw33724Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33724 raw33724Labels permutation234 permutation5
    mixedMoment B raw33724step0 raw33724step0Labels = mixedMoment B raw33724step1 raw33724step1Labels := by
      have ha : raw33724step1 = -raw33724step0 := by apply Matrix.ext; change ∀ i j, raw33724step1 i j = -(raw33724step0 i j); unfold raw33724step1 raw33724step0; decide +kernel
      have hl : raw33724step1Labels = raw33724step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33724step1 raw33724step1Labels = mixedMoment B raw33724step2 raw33724step2Labels := by
      have ha : raw33724step2 = raw33724step1 := by apply Matrix.ext; unfold raw33724step2 raw33724step1; decide +kernel
      have hl : raw33724step1Labels = labelEmbedding8 ∘ raw33724step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33724step1 raw33724step1Labels raw33724step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

def raw33725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33725Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33725step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33725step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33725step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33725step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33725 raw33725Labels = mixedMoment B node4234 node4234Labels := by
  calc
    mixedMoment B raw33725 raw33725Labels = mixedMoment B raw33725step0 raw33725step0Labels := by
      have hz : ∀ j, raw33725 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33725step0 = (fun i j => raw33725 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33725step0 raw33725; decide +kernel
      have hl : raw33725step0Labels = raw33725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33725 raw33725Labels permutation346 hz
    mixedMoment B raw33725step0 raw33725step0Labels = mixedMoment B raw33725step1 raw33725step1Labels := by
      have ha : raw33725step1 = (fun i j => raw33725step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33725step1 raw33725step0; decide +kernel
      have hl : raw33725step1Labels = raw33725step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33725step0 raw33725step0Labels permutation34 permutation3
    mixedMoment B raw33725step1 raw33725step1Labels = mixedMoment B raw33725step2 raw33725step2Labels := by
      have ha : raw33725step2 = raw33725step1 := by apply Matrix.ext; unfold raw33725step2 raw33725step1; decide +kernel
      have hl : raw33725step1Labels = labelEmbedding6 ∘ raw33725step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33725step1 raw33725step1Labels raw33725step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4234 node4234Labels := by rfl

def raw33726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33726Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33726step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33726step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33726step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33726step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33726 raw33726Labels = mixedMoment B node4684 node4684Labels := by
  calc
    mixedMoment B raw33726 raw33726Labels = mixedMoment B raw33726step0 raw33726step0Labels := by
      have hz : ∀ j, raw33726 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33726step0 = (fun i j => raw33726 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33726step0 raw33726; decide +kernel
      have hl : raw33726step0Labels = raw33726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33726 raw33726Labels permutation346 hz
    mixedMoment B raw33726step0 raw33726step0Labels = mixedMoment B raw33726step1 raw33726step1Labels := by
      have ha : raw33726step1 = (fun i j => raw33726step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33726step1 raw33726step0; decide +kernel
      have hl : raw33726step1Labels = raw33726step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33726step0 raw33726step0Labels permutation34 permutation3
    mixedMoment B raw33726step1 raw33726step1Labels = mixedMoment B raw33726step2 raw33726step2Labels := by
      have ha : raw33726step2 = raw33726step1 := by apply Matrix.ext; unfold raw33726step2 raw33726step1; decide +kernel
      have hl : raw33726step1Labels = labelEmbedding6 ∘ raw33726step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33726step1 raw33726step1Labels raw33726step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4684 node4684Labels := by rfl

def raw33727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33727Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33727step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33727step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33727step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33727step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33727 raw33727Labels = mixedMoment B node4722 node4722Labels := by
  calc
    mixedMoment B raw33727 raw33727Labels = mixedMoment B raw33727step0 raw33727step0Labels := by
      have ha : raw33727step0 = (fun i j => raw33727 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33727step0 raw33727; decide +kernel
      have hl : raw33727step0Labels = raw33727Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33727 raw33727Labels permutation178 permutation3
    mixedMoment B raw33727step0 raw33727step0Labels = mixedMoment B raw33727step1 raw33727step1Labels := by
      have ha : raw33727step1 = raw33727step0 := by apply Matrix.ext; unfold raw33727step1 raw33727step0; decide +kernel
      have hl : raw33727step0Labels = labelEmbedding6 ∘ raw33727step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33727step0 raw33727step0Labels raw33727step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4722 node4722Labels := by rfl

def raw33728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33728Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33728step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw33728step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33728step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw33728step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33728step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw33728step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33728 raw33728Labels = mixedMoment B node4828 node4828Labels := by
  calc
    mixedMoment B raw33728 raw33728Labels = mixedMoment B raw33728step0 raw33728step0Labels := by
      have hz : ∀ j, raw33728 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33728step0 = (fun i j => raw33728 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33728step0 raw33728; decide +kernel
      have hl : raw33728step0Labels = raw33728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33728 raw33728Labels permutation346 hz
    mixedMoment B raw33728step0 raw33728step0Labels = mixedMoment B raw33728step1 raw33728step1Labels := by
      have ha : raw33728step1 = (fun i j => raw33728step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33728step1 raw33728step0; decide +kernel
      have hl : raw33728step1Labels = raw33728step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33728step0 raw33728step0Labels permutation44 permutation5
    mixedMoment B raw33728step1 raw33728step1Labels = mixedMoment B raw33728step2 raw33728step2Labels := by
      have ha : raw33728step2 = -raw33728step1 := by apply Matrix.ext; change ∀ i j, raw33728step2 i j = -(raw33728step1 i j); unfold raw33728step2 raw33728step1; decide +kernel
      have hl : raw33728step2Labels = raw33728step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33728step2 raw33728step2Labels = mixedMoment B raw33728step3 raw33728step3Labels := by
      have ha : raw33728step3 = raw33728step2 := by apply Matrix.ext; unfold raw33728step3 raw33728step2; decide +kernel
      have hl : raw33728step2Labels = labelEmbedding8 ∘ raw33728step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33728step2 raw33728step2Labels raw33728step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4828 node4828Labels := by rfl

def raw33729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33729Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33729step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33729step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33729step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33729 raw33729Labels = mixedMoment B node4234 node4234Labels := by
  calc
    mixedMoment B raw33729 raw33729Labels = mixedMoment B raw33729step0 raw33729step0Labels := by
      have hz : ∀ j, raw33729 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33729step0 = (fun i j => raw33729 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33729step0 raw33729; decide +kernel
      have hl : raw33729step0Labels = raw33729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33729 raw33729Labels permutation346 hz
    mixedMoment B raw33729step0 raw33729step0Labels = mixedMoment B raw33729step1 raw33729step1Labels := by
      have ha : raw33729step1 = (fun i j => raw33729step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33729step1 raw33729step0; decide +kernel
      have hl : raw33729step1Labels = raw33729step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33729step0 raw33729step0Labels permutation32 permutation3
    mixedMoment B raw33729step1 raw33729step1Labels = mixedMoment B raw33729step2 raw33729step2Labels := by
      have ha : raw33729step2 = raw33729step1 := by apply Matrix.ext; unfold raw33729step2 raw33729step1; decide +kernel
      have hl : raw33729step1Labels = labelEmbedding6 ∘ raw33729step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33729step1 raw33729step1Labels raw33729step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4234 node4234Labels := by rfl

def raw33730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33730Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33730step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33730step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33730step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33730step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33730 raw33730Labels = mixedMoment B node4684 node4684Labels := by
  calc
    mixedMoment B raw33730 raw33730Labels = mixedMoment B raw33730step0 raw33730step0Labels := by
      have hz : ∀ j, raw33730 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33730step0 = (fun i j => raw33730 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33730step0 raw33730; decide +kernel
      have hl : raw33730step0Labels = raw33730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33730 raw33730Labels permutation346 hz
    mixedMoment B raw33730step0 raw33730step0Labels = mixedMoment B raw33730step1 raw33730step1Labels := by
      have ha : raw33730step1 = (fun i j => raw33730step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33730step1 raw33730step0; decide +kernel
      have hl : raw33730step1Labels = raw33730step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33730step0 raw33730step0Labels permutation32 permutation3
    mixedMoment B raw33730step1 raw33730step1Labels = mixedMoment B raw33730step2 raw33730step2Labels := by
      have ha : raw33730step2 = raw33730step1 := by apply Matrix.ext; unfold raw33730step2 raw33730step1; decide +kernel
      have hl : raw33730step1Labels = labelEmbedding6 ∘ raw33730step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33730step1 raw33730step1Labels raw33730step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4684 node4684Labels := by rfl

def raw33731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33731Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33731step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33731step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33731step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33731 raw33731Labels = mixedMoment B node4722 node4722Labels := by
  calc
    mixedMoment B raw33731 raw33731Labels = mixedMoment B raw33731step0 raw33731step0Labels := by
      have ha : raw33731step0 = (fun i j => raw33731 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33731step0 raw33731; decide +kernel
      have hl : raw33731step0Labels = raw33731Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33731 raw33731Labels permutation176 permutation3
    mixedMoment B raw33731step0 raw33731step0Labels = mixedMoment B raw33731step1 raw33731step1Labels := by
      have ha : raw33731step1 = raw33731step0 := by apply Matrix.ext; unfold raw33731step1 raw33731step0; decide +kernel
      have hl : raw33731step0Labels = labelEmbedding6 ∘ raw33731step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33731step0 raw33731step0Labels raw33731step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4722 node4722Labels := by rfl

def raw33732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33732Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33732step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw33732step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33732step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw33732step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33732 raw33732Labels = mixedMoment B node4231 node4231Labels := by
  calc
    mixedMoment B raw33732 raw33732Labels = mixedMoment B raw33732step0 raw33732step0Labels := by
      have hz : ∀ j, raw33732 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33732step0 = (fun i j => raw33732 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33732step0 raw33732; decide +kernel
      have hl : raw33732step0Labels = raw33732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33732 raw33732Labels permutation346 hz
    mixedMoment B raw33732step0 raw33732step0Labels = mixedMoment B raw33732step1 raw33732step1Labels := by
      have ha : raw33732step1 = (fun i j => raw33732step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33732step1 raw33732step0; decide +kernel
      have hl : raw33732step1Labels = raw33732step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33732step0 raw33732step0Labels permutation32 permutation3
    mixedMoment B raw33732step1 raw33732step1Labels = mixedMoment B raw33732step2 raw33732step2Labels := by
      have ha : raw33732step2 = raw33732step1 := by apply Matrix.ext; unfold raw33732step2 raw33732step1; decide +kernel
      have hl : raw33732step1Labels = labelEmbedding6 ∘ raw33732step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33732step1 raw33732step1Labels raw33732step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4231 node4231Labels := by rfl

def raw33733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33733Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33733step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw33733step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33733step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw33733step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33733 raw33733Labels = mixedMoment B node4678 node4678Labels := by
  calc
    mixedMoment B raw33733 raw33733Labels = mixedMoment B raw33733step0 raw33733step0Labels := by
      have hz : ∀ j, raw33733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33733step0 = (fun i j => raw33733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33733step0 raw33733; decide +kernel
      have hl : raw33733step0Labels = raw33733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33733 raw33733Labels permutation346 hz
    mixedMoment B raw33733step0 raw33733step0Labels = mixedMoment B raw33733step1 raw33733step1Labels := by
      have ha : raw33733step1 = (fun i j => raw33733step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33733step1 raw33733step0; decide +kernel
      have hl : raw33733step1Labels = raw33733step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33733step0 raw33733step0Labels permutation32 permutation3
    mixedMoment B raw33733step1 raw33733step1Labels = mixedMoment B raw33733step2 raw33733step2Labels := by
      have ha : raw33733step2 = raw33733step1 := by apply Matrix.ext; unfold raw33733step2 raw33733step1; decide +kernel
      have hl : raw33733step1Labels = labelEmbedding6 ∘ raw33733step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33733step1 raw33733step1Labels raw33733step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4678 node4678Labels := by rfl

def raw33734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33734Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33734step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw33734step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33734step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw33734step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33734 raw33734Labels = mixedMoment B node4720 node4720Labels := by
  calc
    mixedMoment B raw33734 raw33734Labels = mixedMoment B raw33734step0 raw33734step0Labels := by
      have ha : raw33734step0 = (fun i j => raw33734 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33734step0 raw33734; decide +kernel
      have hl : raw33734step0Labels = raw33734Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33734 raw33734Labels permutation176 permutation3
    mixedMoment B raw33734step0 raw33734step0Labels = mixedMoment B raw33734step1 raw33734step1Labels := by
      have ha : raw33734step1 = raw33734step0 := by apply Matrix.ext; unfold raw33734step1 raw33734step0; decide +kernel
      have hl : raw33734step0Labels = labelEmbedding6 ∘ raw33734step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33734step0 raw33734step0Labels raw33734step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4720 node4720Labels := by rfl

def raw33735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw33735Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw33735step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 0, 3]]
def raw33735step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33735step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw33735step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33735step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw33735step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33735 raw33735Labels = mixedMoment B node4800 node4800Labels := by
  calc
    mixedMoment B raw33735 raw33735Labels = mixedMoment B raw33735step0 raw33735step0Labels := by
      have hz : ∀ j, raw33735 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33735step0 = (fun i j => raw33735 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33735step0 raw33735; decide +kernel
      have hl : raw33735step0Labels = raw33735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33735 raw33735Labels permutation346 hz
    mixedMoment B raw33735step0 raw33735step0Labels = mixedMoment B raw33735step1 raw33735step1Labels := by
      have ha : raw33735step1 = (fun i j => raw33735step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33735step1 raw33735step0; decide +kernel
      have hl : raw33735step1Labels = raw33735step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33735step0 raw33735step0Labels permutation145 permutation3
    mixedMoment B raw33735step1 raw33735step1Labels = mixedMoment B raw33735step2 raw33735step2Labels := by
      have ha : raw33735step2 = -raw33735step1 := by apply Matrix.ext; change ∀ i j, raw33735step2 i j = -(raw33735step1 i j); unfold raw33735step2 raw33735step1; decide +kernel
      have hl : raw33735step2Labels = raw33735step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33735step2 raw33735step2Labels = mixedMoment B raw33735step3 raw33735step3Labels := by
      have ha : raw33735step3 = raw33735step2 := by apply Matrix.ext; unfold raw33735step3 raw33735step2; decide +kernel
      have hl : raw33735step2Labels = labelEmbedding6 ∘ raw33735step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33735step2 raw33735step2Labels raw33735step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4800 node4800Labels := by rfl

def raw33736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33736Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33736step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33736step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33736step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33736 raw33736Labels = mixedMoment B node3736 node3736Labels := by
  calc
    mixedMoment B raw33736 raw33736Labels = mixedMoment B raw33736step0 raw33736step0Labels := by
      have hz : ∀ j, raw33736 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33736step0 = (fun i j => raw33736 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33736step0 raw33736; decide +kernel
      have hl : raw33736step0Labels = raw33736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33736 raw33736Labels permutation346 hz
    mixedMoment B raw33736step0 raw33736step0Labels = mixedMoment B raw33736step1 raw33736step1Labels := by
      have ha : raw33736step1 = (fun i j => raw33736step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33736step1 raw33736step0; decide +kernel
      have hl : raw33736step1Labels = raw33736step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33736step0 raw33736step0Labels permutation32 permutation3
    _ = mixedMoment B node3736 node3736Labels := by rfl

def raw33737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33737Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33737step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33737step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33737 raw33737Labels = mixedMoment B node3786 node3786Labels := by
  calc
    mixedMoment B raw33737 raw33737Labels = mixedMoment B raw33737step0 raw33737step0Labels := by
      have ha : raw33737step0 = (fun i j => raw33737 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33737step0 raw33737; decide +kernel
      have hl : raw33737step0Labels = raw33737Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33737 raw33737Labels permutation176 permutation3
    _ = mixedMoment B node3786 node3786Labels := by rfl

def raw33738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33738Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33738step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw33738step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33738step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33738step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33738 raw33738Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw33738 raw33738Labels = mixedMoment B raw33738step0 raw33738step0Labels := by
      have hz : ∀ j, raw33738 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33738step0 = (fun i j => raw33738 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33738step0 raw33738; decide +kernel
      have hl : raw33738step0Labels = raw33738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33738 raw33738Labels permutation346 hz
    mixedMoment B raw33738step0 raw33738step0Labels = mixedMoment B raw33738step1 raw33738step1Labels := by
      have ha : raw33738step1 = (fun i j => raw33738step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33738step1 raw33738step0; decide +kernel
      have hl : raw33738step1Labels = raw33738step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33738step0 raw33738step0Labels permutation151 permutation3
    mixedMoment B raw33738step1 raw33738step1Labels = mixedMoment B raw33738step2 raw33738step2Labels := by
      have ha : raw33738step2 = -raw33738step1 := by apply Matrix.ext; change ∀ i j, raw33738step2 i j = -(raw33738step1 i j); unfold raw33738step2 raw33738step1; decide +kernel
      have hl : raw33738step2Labels = raw33738step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw33739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33739Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33739step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw33739step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33739step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33739 raw33739Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw33739 raw33739Labels = mixedMoment B raw33739step0 raw33739step0Labels := by
      have hz : ∀ j, raw33739 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33739step0 = (fun i j => raw33739 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33739step0 raw33739; decide +kernel
      have hl : raw33739step0Labels = raw33739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33739 raw33739Labels permutation346 hz
    mixedMoment B raw33739step0 raw33739step0Labels = mixedMoment B raw33739step1 raw33739step1Labels := by
      have ha : raw33739step1 = (fun i j => raw33739step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33739step1 raw33739step0; decide +kernel
      have hl : raw33739step1Labels = raw33739step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33739step0 raw33739step0Labels permutation145 permutation3
    mixedMoment B raw33739step1 raw33739step1Labels = mixedMoment B raw33739step2 raw33739step2Labels := by
      have ha : raw33739step2 = -raw33739step1 := by apply Matrix.ext; change ∀ i j, raw33739step2 i j = -(raw33739step1 i j); unfold raw33739step2 raw33739step1; decide +kernel
      have hl : raw33739step2Labels = raw33739step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw33740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33740Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33740step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33740step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33740 raw33740Labels = mixedMoment B node3887 node3887Labels := by
  calc
    mixedMoment B raw33740 raw33740Labels = mixedMoment B raw33740step0 raw33740step0Labels := by
      have hz : ∀ j, raw33740 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33740step0 = (fun i j => raw33740 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33740step0 raw33740; decide +kernel
      have hl : raw33740step0Labels = raw33740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33740 raw33740Labels permutation346 hz
    mixedMoment B raw33740step0 raw33740step0Labels = mixedMoment B raw33740step1 raw33740step1Labels := by
      have ha : raw33740step1 = (fun i j => raw33740step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33740step1 raw33740step0; decide +kernel
      have hl : raw33740step1Labels = raw33740step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33740step0 raw33740step0Labels permutation32 permutation3
    _ = mixedMoment B node3887 node3887Labels := by rfl

def raw33741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33741Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33741step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33741step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33741step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33741 raw33741Labels = mixedMoment B node823 node823Labels := by
  calc
    mixedMoment B raw33741 raw33741Labels = mixedMoment B raw33741step0 raw33741step0Labels := by
      have hz : ∀ j, raw33741 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33741step0 = (fun i j => raw33741 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33741step0 raw33741; decide +kernel
      have hl : raw33741step0Labels = raw33741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33741 raw33741Labels permutation346 hz
    mixedMoment B raw33741step0 raw33741step0Labels = mixedMoment B raw33741step1 raw33741step1Labels := by
      have ha : raw33741step1 = (fun i j => raw33741step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33741step1 raw33741step0; decide +kernel
      have hl : raw33741step1Labels = raw33741step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33741step0 raw33741step0Labels permutation32 permutation3
    _ = mixedMoment B node823 node823Labels := by rfl

def raw33742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33742Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33742step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33742 raw33742Labels = mixedMoment B node1921 node1921Labels := by
  calc
    mixedMoment B raw33742 raw33742Labels = mixedMoment B raw33742step0 raw33742step0Labels := by
      have ha : raw33742step0 = (fun i j => raw33742 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33742step0 raw33742; decide +kernel
      have hl : raw33742step0Labels = raw33742Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33742 raw33742Labels permutation176 permutation3
    _ = mixedMoment B node1921 node1921Labels := by rfl

def raw33743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33743Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33743step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw33743step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33743 raw33743Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw33743 raw33743Labels = mixedMoment B raw33743step0 raw33743step0Labels := by
      have hz : ∀ j, raw33743 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33743step0 = (fun i j => raw33743 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33743step0 raw33743; decide +kernel
      have hl : raw33743step0Labels = raw33743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33743 raw33743Labels permutation346 hz
    mixedMoment B raw33743step0 raw33743step0Labels = mixedMoment B raw33743step1 raw33743step1Labels := by
      have ha : raw33743step1 = (fun i j => raw33743step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33743step1 raw33743step0; decide +kernel
      have hl : raw33743step1Labels = raw33743step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33743step0 raw33743step0Labels permutation38 permutation3
    _ = mixedMoment B node2215 node2215Labels := by rfl

def raw33744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33744Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33744step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw33744step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33744 raw33744Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw33744 raw33744Labels = mixedMoment B raw33744step0 raw33744step0Labels := by
      have hz : ∀ j, raw33744 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33744step0 = (fun i j => raw33744 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33744step0 raw33744; decide +kernel
      have hl : raw33744step0Labels = raw33744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33744 raw33744Labels permutation346 hz
    mixedMoment B raw33744step0 raw33744step0Labels = mixedMoment B raw33744step1 raw33744step1Labels := by
      have ha : raw33744step1 = (fun i j => raw33744step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33744step1 raw33744step0; decide +kernel
      have hl : raw33744step1Labels = raw33744step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33744step0 raw33744step0Labels permutation44 permutation3
    _ = mixedMoment B node2215 node2215Labels := by rfl

def raw33745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33745Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33745step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw33745step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33745 raw33745Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw33745 raw33745Labels = mixedMoment B raw33745step0 raw33745step0Labels := by
      have hz : ∀ j, raw33745 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33745step0 = (fun i j => raw33745 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33745step0 raw33745; decide +kernel
      have hl : raw33745step0Labels = raw33745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33745 raw33745Labels permutation346 hz
    mixedMoment B raw33745step0 raw33745step0Labels = mixedMoment B raw33745step1 raw33745step1Labels := by
      have ha : raw33745step1 = (fun i j => raw33745step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33745step1 raw33745step0; decide +kernel
      have hl : raw33745step1Labels = raw33745step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33745step0 raw33745step0Labels permutation32 permutation3
    _ = mixedMoment B node2277 node2277Labels := by rfl

def raw33746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33746Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33746step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33746 raw33746Labels = mixedMoment B node730 node730Labels := by
  calc
    mixedMoment B raw33746 raw33746Labels = mixedMoment B raw33746step0 raw33746step0Labels := by
      have ha : raw33746step0 = (fun i j => raw33746 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33746step0 raw33746; decide +kernel
      have hl : raw33746step0Labels = raw33746Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33746 raw33746Labels permutation160 permutation3
    _ = mixedMoment B node730 node730Labels := by rfl

def raw33747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33747Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33747step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33747 raw33747Labels = mixedMoment B node1802 node1802Labels := by
  calc
    mixedMoment B raw33747 raw33747Labels = mixedMoment B raw33747step0 raw33747step0Labels := by
      have ha : raw33747step0 = (fun i j => raw33747 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33747step0 raw33747; decide +kernel
      have hl : raw33747step0Labels = raw33747Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33747 raw33747Labels permutation160 permutation3
    _ = mixedMoment B node1802 node1802Labels := by rfl

def raw33748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33748Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33748step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33748step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33748 raw33748Labels = mixedMoment B node2075 node2075Labels := by
  calc
    mixedMoment B raw33748 raw33748Labels = mixedMoment B raw33748step0 raw33748step0Labels := by
      have ha : raw33748step0 = (fun i j => raw33748 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33748step0 raw33748; decide +kernel
      have hl : raw33748step0Labels = raw33748Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33748 raw33748Labels permutation160 permutation3
    _ = mixedMoment B node2075 node2075Labels := by rfl

def raw33749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33749Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33749step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33749step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33749 raw33749Labels = mixedMoment B node2075 node2075Labels := by
  calc
    mixedMoment B raw33749 raw33749Labels = mixedMoment B raw33749step0 raw33749step0Labels := by
      have ha : raw33749step0 = (fun i j => raw33749 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33749step0 raw33749; decide +kernel
      have hl : raw33749step0Labels = raw33749Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33749 raw33749Labels permutation166 permutation3
    _ = mixedMoment B node2075 node2075Labels := by rfl

def raw33750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33750Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33750step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33750 raw33750Labels = mixedMoment B node2105 node2105Labels := by
  calc
    mixedMoment B raw33750 raw33750Labels = mixedMoment B raw33750step0 raw33750step0Labels := by
      have ha : raw33750step0 = (fun i j => raw33750 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33750step0 raw33750; decide +kernel
      have hl : raw33750step0Labels = raw33750Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33750 raw33750Labels permutation160 permutation3
    _ = mixedMoment B node2105 node2105Labels := by rfl

def raw33751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33751Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33751step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33751step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33751 raw33751Labels = mixedMoment B node734 node734Labels := by
  calc
    mixedMoment B raw33751 raw33751Labels = mixedMoment B raw33751step0 raw33751step0Labels := by
      have hz : ∀ j, raw33751 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33751step0 = (fun i j => raw33751 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33751step0 raw33751; decide +kernel
      have hl : raw33751step0Labels = raw33751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33751 raw33751Labels permutation346 hz
    mixedMoment B raw33751step0 raw33751step0Labels = mixedMoment B raw33751step1 raw33751step1Labels := by
      have ha : raw33751step1 = (fun i j => raw33751step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33751step1 raw33751step0; decide +kernel
      have hl : raw33751step1Labels = raw33751step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33751step0 raw33751step0Labels permutation34 permutation3
    _ = mixedMoment B node734 node734Labels := by rfl

def raw33752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33752Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33752step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33752step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33752 raw33752Labels = mixedMoment B node1810 node1810Labels := by
  calc
    mixedMoment B raw33752 raw33752Labels = mixedMoment B raw33752step0 raw33752step0Labels := by
      have hz : ∀ j, raw33752 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33752step0 = (fun i j => raw33752 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33752step0 raw33752; decide +kernel
      have hl : raw33752step0Labels = raw33752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33752 raw33752Labels permutation346 hz
    mixedMoment B raw33752step0 raw33752step0Labels = mixedMoment B raw33752step1 raw33752step1Labels := by
      have ha : raw33752step1 = (fun i j => raw33752step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33752step1 raw33752step0; decide +kernel
      have hl : raw33752step1Labels = raw33752step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33752step0 raw33752step0Labels permutation34 permutation3
    _ = mixedMoment B node1810 node1810Labels := by rfl

def raw33753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33753Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33753step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33753 raw33753Labels = mixedMoment B node1876 node1876Labels := by
  calc
    mixedMoment B raw33753 raw33753Labels = mixedMoment B raw33753step0 raw33753step0Labels := by
      have ha : raw33753step0 = (fun i j => raw33753 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33753step0 raw33753; decide +kernel
      have hl : raw33753step0Labels = raw33753Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33753 raw33753Labels permutation178 permutation3
    _ = mixedMoment B node1876 node1876Labels := by rfl

def raw33754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33754Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33754step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw33754step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33754 raw33754Labels = mixedMoment B node2082 node2082Labels := by
  calc
    mixedMoment B raw33754 raw33754Labels = mixedMoment B raw33754step0 raw33754step0Labels := by
      have hz : ∀ j, raw33754 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33754step0 = (fun i j => raw33754 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33754step0 raw33754; decide +kernel
      have hl : raw33754step0Labels = raw33754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33754 raw33754Labels permutation346 hz
    mixedMoment B raw33754step0 raw33754step0Labels = mixedMoment B raw33754step1 raw33754step1Labels := by
      have ha : raw33754step1 = (fun i j => raw33754step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33754step1 raw33754step0; decide +kernel
      have hl : raw33754step1Labels = raw33754step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33754step0 raw33754step0Labels permutation34 permutation3
    _ = mixedMoment B node2082 node2082Labels := by rfl

def raw33755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33755Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33755step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33755step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33755 raw33755Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw33755 raw33755Labels = mixedMoment B raw33755step0 raw33755step0Labels := by
      have hz : ∀ j, raw33755 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33755step0 = (fun i j => raw33755 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33755step0 raw33755; decide +kernel
      have hl : raw33755step0Labels = raw33755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33755 raw33755Labels permutation346 hz
    mixedMoment B raw33755step0 raw33755step0Labels = mixedMoment B raw33755step1 raw33755step1Labels := by
      have ha : raw33755step1 = (fun i j => raw33755step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33755step1 raw33755step0; decide +kernel
      have hl : raw33755step1Labels = raw33755step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33755step0 raw33755step0Labels permutation35 permutation3
    _ = mixedMoment B node2107 node2107Labels := by rfl

def raw33756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33756Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33756step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33756step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33756 raw33756Labels = mixedMoment B node734 node734Labels := by
  calc
    mixedMoment B raw33756 raw33756Labels = mixedMoment B raw33756step0 raw33756step0Labels := by
      have hz : ∀ j, raw33756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33756step0 = (fun i j => raw33756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33756step0 raw33756; decide +kernel
      have hl : raw33756step0Labels = raw33756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33756 raw33756Labels permutation346 hz
    mixedMoment B raw33756step0 raw33756step0Labels = mixedMoment B raw33756step1 raw33756step1Labels := by
      have ha : raw33756step1 = (fun i j => raw33756step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33756step1 raw33756step0; decide +kernel
      have hl : raw33756step1Labels = raw33756step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33756step0 raw33756step0Labels permutation32 permutation3
    _ = mixedMoment B node734 node734Labels := by rfl

def raw33757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33757Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33757step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33757step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33757 raw33757Labels = mixedMoment B node1810 node1810Labels := by
  calc
    mixedMoment B raw33757 raw33757Labels = mixedMoment B raw33757step0 raw33757step0Labels := by
      have hz : ∀ j, raw33757 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33757step0 = (fun i j => raw33757 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33757step0 raw33757; decide +kernel
      have hl : raw33757step0Labels = raw33757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33757 raw33757Labels permutation346 hz
    mixedMoment B raw33757step0 raw33757step0Labels = mixedMoment B raw33757step1 raw33757step1Labels := by
      have ha : raw33757step1 = (fun i j => raw33757step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33757step1 raw33757step0; decide +kernel
      have hl : raw33757step1Labels = raw33757step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33757step0 raw33757step0Labels permutation32 permutation3
    _ = mixedMoment B node1810 node1810Labels := by rfl

def raw33758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33758Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33758step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33758 raw33758Labels = mixedMoment B node1876 node1876Labels := by
  calc
    mixedMoment B raw33758 raw33758Labels = mixedMoment B raw33758step0 raw33758step0Labels := by
      have ha : raw33758step0 = (fun i j => raw33758 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33758step0 raw33758; decide +kernel
      have hl : raw33758step0Labels = raw33758Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33758 raw33758Labels permutation176 permutation3
    _ = mixedMoment B node1876 node1876Labels := by rfl

def raw33759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33759Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33759step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw33759step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33759 raw33759Labels = mixedMoment B node2082 node2082Labels := by
  calc
    mixedMoment B raw33759 raw33759Labels = mixedMoment B raw33759step0 raw33759step0Labels := by
      have hz : ∀ j, raw33759 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33759step0 = (fun i j => raw33759 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33759step0 raw33759; decide +kernel
      have hl : raw33759step0Labels = raw33759Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33759 raw33759Labels permutation346 hz
    mixedMoment B raw33759step0 raw33759step0Labels = mixedMoment B raw33759step1 raw33759step1Labels := by
      have ha : raw33759step1 = (fun i j => raw33759step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33759step1 raw33759step0; decide +kernel
      have hl : raw33759step1Labels = raw33759step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33759step0 raw33759step0Labels permutation32 permutation3
    _ = mixedMoment B node2082 node2082Labels := by rfl

def raw33760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw33760Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw33760step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33760step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33760 raw33760Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw33760 raw33760Labels = mixedMoment B raw33760step0 raw33760step0Labels := by
      have hz : ∀ j, raw33760 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33760step0 = (fun i j => raw33760 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33760step0 raw33760; decide +kernel
      have hl : raw33760step0Labels = raw33760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33760 raw33760Labels permutation346 hz
    mixedMoment B raw33760step0 raw33760step0Labels = mixedMoment B raw33760step1 raw33760step1Labels := by
      have ha : raw33760step1 = (fun i j => raw33760step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33760step1 raw33760step0; decide +kernel
      have hl : raw33760step1Labels = raw33760step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33760step0 raw33760step0Labels permutation33 permutation3
    _ = mixedMoment B node2107 node2107Labels := by rfl

def raw33761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33761Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33761step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw33761step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33761 raw33761Labels = mixedMoment B node731 node731Labels := by
  calc
    mixedMoment B raw33761 raw33761Labels = mixedMoment B raw33761step0 raw33761step0Labels := by
      have hz : ∀ j, raw33761 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33761step0 = (fun i j => raw33761 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33761step0 raw33761; decide +kernel
      have hl : raw33761step0Labels = raw33761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33761 raw33761Labels permutation346 hz
    mixedMoment B raw33761step0 raw33761step0Labels = mixedMoment B raw33761step1 raw33761step1Labels := by
      have ha : raw33761step1 = (fun i j => raw33761step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33761step1 raw33761step0; decide +kernel
      have hl : raw33761step1Labels = raw33761step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33761step0 raw33761step0Labels permutation32 permutation3
    _ = mixedMoment B node731 node731Labels := by rfl

def raw33762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33762Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33762step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw33762step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33762 raw33762Labels = mixedMoment B node1804 node1804Labels := by
  calc
    mixedMoment B raw33762 raw33762Labels = mixedMoment B raw33762step0 raw33762step0Labels := by
      have hz : ∀ j, raw33762 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33762step0 = (fun i j => raw33762 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33762step0 raw33762; decide +kernel
      have hl : raw33762step0Labels = raw33762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33762 raw33762Labels permutation346 hz
    mixedMoment B raw33762step0 raw33762step0Labels = mixedMoment B raw33762step1 raw33762step1Labels := by
      have ha : raw33762step1 = (fun i j => raw33762step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33762step1 raw33762step0; decide +kernel
      have hl : raw33762step1Labels = raw33762step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33762step0 raw33762step0Labels permutation32 permutation3
    _ = mixedMoment B node1804 node1804Labels := by rfl

def raw33763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33763Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw33763step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33763 raw33763Labels = mixedMoment B node1874 node1874Labels := by
  calc
    mixedMoment B raw33763 raw33763Labels = mixedMoment B raw33763step0 raw33763step0Labels := by
      have ha : raw33763step0 = (fun i j => raw33763 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33763step0 raw33763; decide +kernel
      have hl : raw33763step0Labels = raw33763Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33763 raw33763Labels permutation176 permutation3
    _ = mixedMoment B node1874 node1874Labels := by rfl

def raw33764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33764Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33764step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 0, 3]]
def raw33764step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33764step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw33764step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33764 raw33764Labels = mixedMoment B node2018 node2018Labels := by
  calc
    mixedMoment B raw33764 raw33764Labels = mixedMoment B raw33764step0 raw33764step0Labels := by
      have hz : ∀ j, raw33764 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33764step0 = (fun i j => raw33764 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33764step0 raw33764; decide +kernel
      have hl : raw33764step0Labels = raw33764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33764 raw33764Labels permutation346 hz
    mixedMoment B raw33764step0 raw33764step0Labels = mixedMoment B raw33764step1 raw33764step1Labels := by
      have ha : raw33764step1 = (fun i j => raw33764step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33764step1 raw33764step0; decide +kernel
      have hl : raw33764step1Labels = raw33764step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33764step0 raw33764step0Labels permutation151 permutation3
    mixedMoment B raw33764step1 raw33764step1Labels = mixedMoment B raw33764step2 raw33764step2Labels := by
      have ha : raw33764step2 = -raw33764step1 := by apply Matrix.ext; change ∀ i j, raw33764step2 i j = -(raw33764step1 i j); unfold raw33764step2 raw33764step1; decide +kernel
      have hl : raw33764step2Labels = raw33764step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2018 node2018Labels := by rfl

def raw33765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw33765Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw33765step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 0, 3]]
def raw33765step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33765step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw33765step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33765 raw33765Labels = mixedMoment B node2018 node2018Labels := by
  calc
    mixedMoment B raw33765 raw33765Labels = mixedMoment B raw33765step0 raw33765step0Labels := by
      have hz : ∀ j, raw33765 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33765step0 = (fun i j => raw33765 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33765step0 raw33765; decide +kernel
      have hl : raw33765step0Labels = raw33765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33765 raw33765Labels permutation346 hz
    mixedMoment B raw33765step0 raw33765step0Labels = mixedMoment B raw33765step1 raw33765step1Labels := by
      have ha : raw33765step1 = (fun i j => raw33765step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33765step1 raw33765step0; decide +kernel
      have hl : raw33765step1Labels = raw33765step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33765step0 raw33765step0Labels permutation145 permutation3
    mixedMoment B raw33765step1 raw33765step1Labels = mixedMoment B raw33765step2 raw33765step2Labels := by
      have ha : raw33765step2 = -raw33765step1 := by apply Matrix.ext; change ∀ i j, raw33765step2 i j = -(raw33765step1 i j); unfold raw33765step2 raw33765step1; decide +kernel
      have hl : raw33765step2Labels = raw33765step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2018 node2018Labels := by rfl

def raw33766 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33766step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33766step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33766step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33766step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33766 raw33766Labels = mixedMoment B node5198 node5198Labels := by
  calc
    mixedMoment B raw33766 raw33766Labels = mixedMoment B raw33766step0 raw33766step0Labels := by
      have hz : ∀ j, raw33766 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33766step0 = (fun i j => raw33766 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33766step0 raw33766; decide +kernel
      have hl : raw33766step0Labels = raw33766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33766 raw33766Labels permutation346 hz
    mixedMoment B raw33766step0 raw33766step0Labels = mixedMoment B raw33766step1 raw33766step1Labels := by
      have ha : raw33766step1 = (fun i j => raw33766step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33766step1 raw33766step0; decide +kernel
      have hl : raw33766step1Labels = raw33766step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33766step0 raw33766step0Labels permutation32 permutation6
    mixedMoment B raw33766step1 raw33766step1Labels = mixedMoment B raw33766step2 raw33766step2Labels := by
      have ha : raw33766step2 = raw33766step1 := by apply Matrix.ext; unfold raw33766step2 raw33766step1; decide +kernel
      have hl : raw33766step1Labels = labelEmbedding9 ∘ raw33766step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33766step1 raw33766step1Labels raw33766step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5198 node5198Labels := by rfl

def raw33767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw33767step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33767step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw33767step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33767step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw33767step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33767 raw33767Labels = mixedMoment B node4443 node4443Labels := by
  calc
    mixedMoment B raw33767 raw33767Labels = mixedMoment B raw33767step0 raw33767step0Labels := by
      have hz : ∀ j, raw33767 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33767step0 = (fun i j => raw33767 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33767step0 raw33767; decide +kernel
      have hl : raw33767step0Labels = raw33767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33767 raw33767Labels permutation346 hz
    mixedMoment B raw33767step0 raw33767step0Labels = mixedMoment B raw33767step1 raw33767step1Labels := by
      have ha : raw33767step1 = (fun i j => raw33767step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33767step1 raw33767step0; decide +kernel
      have hl : raw33767step1Labels = raw33767step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33767step0 raw33767step0Labels permutation40 permutation4
    mixedMoment B raw33767step1 raw33767step1Labels = mixedMoment B raw33767step2 raw33767step2Labels := by
      have ha : raw33767step2 = -raw33767step1 := by apply Matrix.ext; change ∀ i j, raw33767step2 i j = -(raw33767step1 i j); unfold raw33767step2 raw33767step1; decide +kernel
      have hl : raw33767step2Labels = raw33767step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33767step2 raw33767step2Labels = mixedMoment B raw33767step3 raw33767step3Labels := by
      have ha : raw33767step3 = raw33767step2 := by apply Matrix.ext; unfold raw33767step3 raw33767step2; decide +kernel
      have hl : raw33767step2Labels = labelEmbedding7 ∘ raw33767step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33767step2 raw33767step2Labels raw33767step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4443 node4443Labels := by rfl

def raw33768 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw33768step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33768step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw33768step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33768step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw33768step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33768 raw33768Labels = mixedMoment B node4794 node4794Labels := by
  calc
    mixedMoment B raw33768 raw33768Labels = mixedMoment B raw33768step0 raw33768step0Labels := by
      have ha : raw33768step0 = (fun i j => raw33768 (permutation184 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33768step0 raw33768; decide +kernel
      have hl : raw33768step0Labels = raw33768Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33768 raw33768Labels permutation184 permutation4
    mixedMoment B raw33768step0 raw33768step0Labels = mixedMoment B raw33768step1 raw33768step1Labels := by
      have ha : raw33768step1 = -raw33768step0 := by apply Matrix.ext; change ∀ i j, raw33768step1 i j = -(raw33768step0 i j); unfold raw33768step1 raw33768step0; decide +kernel
      have hl : raw33768step1Labels = raw33768step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33768step1 raw33768step1Labels = mixedMoment B raw33768step2 raw33768step2Labels := by
      have ha : raw33768step2 = raw33768step1 := by apply Matrix.ext; unfold raw33768step2 raw33768step1; decide +kernel
      have hl : raw33768step1Labels = labelEmbedding7 ∘ raw33768step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33768step1 raw33768step1Labels raw33768step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4794 node4794Labels := by rfl

def raw33769 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33769step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw33769step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33769step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw33769step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33769step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw33769step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33769 raw33769Labels = mixedMoment B node4855 node4855Labels := by
  calc
    mixedMoment B raw33769 raw33769Labels = mixedMoment B raw33769step0 raw33769step0Labels := by
      have hz : ∀ j, raw33769 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33769step0 = (fun i j => raw33769 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33769step0 raw33769; decide +kernel
      have hl : raw33769step0Labels = raw33769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33769 raw33769Labels permutation346 hz
    mixedMoment B raw33769step0 raw33769step0Labels = mixedMoment B raw33769step1 raw33769step1Labels := by
      have ha : raw33769step1 = (fun i j => raw33769step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33769step1 raw33769step0; decide +kernel
      have hl : raw33769step1Labels = raw33769step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33769step0 raw33769step0Labels permutation40 permutation4
    mixedMoment B raw33769step1 raw33769step1Labels = mixedMoment B raw33769step2 raw33769step2Labels := by
      have ha : raw33769step2 = -raw33769step1 := by apply Matrix.ext; change ∀ i j, raw33769step2 i j = -(raw33769step1 i j); unfold raw33769step2 raw33769step1; decide +kernel
      have hl : raw33769step2Labels = raw33769step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33769step2 raw33769step2Labels = mixedMoment B raw33769step3 raw33769step3Labels := by
      have ha : raw33769step3 = raw33769step2 := by apply Matrix.ext; unfold raw33769step3 raw33769step2; decide +kernel
      have hl : raw33769step2Labels = labelEmbedding7 ∘ raw33769step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33769step2 raw33769step2Labels raw33769step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4855 node4855Labels := by rfl

def raw33770 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw33770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw33770step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw33770step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33770step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw33770step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33770step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw33770step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33770 raw33770Labels = mixedMoment B node4855 node4855Labels := by
  calc
    mixedMoment B raw33770 raw33770Labels = mixedMoment B raw33770step0 raw33770step0Labels := by
      have hz : ∀ j, raw33770 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33770step0 = (fun i j => raw33770 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33770step0 raw33770; decide +kernel
      have hl : raw33770step0Labels = raw33770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33770 raw33770Labels permutation346 hz
    mixedMoment B raw33770step0 raw33770step0Labels = mixedMoment B raw33770step1 raw33770step1Labels := by
      have ha : raw33770step1 = (fun i j => raw33770step0 (permutation46 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33770step1 raw33770step0; decide +kernel
      have hl : raw33770step1Labels = raw33770step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33770step0 raw33770step0Labels permutation46 permutation4
    mixedMoment B raw33770step1 raw33770step1Labels = mixedMoment B raw33770step2 raw33770step2Labels := by
      have ha : raw33770step2 = -raw33770step1 := by apply Matrix.ext; change ∀ i j, raw33770step2 i j = -(raw33770step1 i j); unfold raw33770step2 raw33770step1; decide +kernel
      have hl : raw33770step2Labels = raw33770step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33770step2 raw33770step2Labels = mixedMoment B raw33770step3 raw33770step3Labels := by
      have ha : raw33770step3 = raw33770step2 := by apply Matrix.ext; unfold raw33770step3 raw33770step2; decide +kernel
      have hl : raw33770step2Labels = labelEmbedding7 ∘ raw33770step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33770step2 raw33770step2Labels raw33770step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4855 node4855Labels := by rfl

def raw33771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw33771step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33771step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33771step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33771step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33771step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33771 raw33771Labels = mixedMoment B node4435 node4435Labels := by
  calc
    mixedMoment B raw33771 raw33771Labels = mixedMoment B raw33771step0 raw33771step0Labels := by
      have ha : raw33771step0 = (fun i j => raw33771 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33771step0 raw33771; decide +kernel
      have hl : raw33771step0Labels = raw33771Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33771 raw33771Labels permutation212 permutation4
    mixedMoment B raw33771step0 raw33771step0Labels = mixedMoment B raw33771step1 raw33771step1Labels := by
      have ha : raw33771step1 = -raw33771step0 := by apply Matrix.ext; change ∀ i j, raw33771step1 i j = -(raw33771step0 i j); unfold raw33771step1 raw33771step0; decide +kernel
      have hl : raw33771step1Labels = raw33771step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33771step1 raw33771step1Labels = mixedMoment B raw33771step2 raw33771step2Labels := by
      have ha : raw33771step2 = raw33771step1 := by apply Matrix.ext; unfold raw33771step2 raw33771step1; decide +kernel
      have hl : raw33771step1Labels = labelEmbedding7 ∘ raw33771step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33771step1 raw33771step1Labels raw33771step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4435 node4435Labels := by rfl

def raw33772 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33772step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw33772step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33772step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33772step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33772step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33772step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33772 raw33772Labels = mixedMoment B node4848 node4848Labels := by
  calc
    mixedMoment B raw33772 raw33772Labels = mixedMoment B raw33772step0 raw33772step0Labels := by
      have ha : raw33772step0 = (fun i j => raw33772 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33772step0 raw33772; decide +kernel
      have hl : raw33772step0Labels = raw33772Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33772 raw33772Labels permutation212 permutation4
    mixedMoment B raw33772step0 raw33772step0Labels = mixedMoment B raw33772step1 raw33772step1Labels := by
      have ha : raw33772step1 = -raw33772step0 := by apply Matrix.ext; change ∀ i j, raw33772step1 i j = -(raw33772step0 i j); unfold raw33772step1 raw33772step0; decide +kernel
      have hl : raw33772step1Labels = raw33772step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33772step1 raw33772step1Labels = mixedMoment B raw33772step2 raw33772step2Labels := by
      have ha : raw33772step2 = raw33772step1 := by apply Matrix.ext; unfold raw33772step2 raw33772step1; decide +kernel
      have hl : raw33772step1Labels = labelEmbedding7 ∘ raw33772step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33772step1 raw33772step1Labels raw33772step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4848 node4848Labels := by rfl

def raw33773 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw33773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw33773step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33773step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33773step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33773step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw33773step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33773 raw33773Labels = mixedMoment B node4848 node4848Labels := by
  calc
    mixedMoment B raw33773 raw33773Labels = mixedMoment B raw33773step0 raw33773step0Labels := by
      have ha : raw33773step0 = (fun i j => raw33773 (permutation234 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33773step0 raw33773; decide +kernel
      have hl : raw33773step0Labels = raw33773Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33773 raw33773Labels permutation234 permutation4
    mixedMoment B raw33773step0 raw33773step0Labels = mixedMoment B raw33773step1 raw33773step1Labels := by
      have ha : raw33773step1 = -raw33773step0 := by apply Matrix.ext; change ∀ i j, raw33773step1 i j = -(raw33773step0 i j); unfold raw33773step1 raw33773step0; decide +kernel
      have hl : raw33773step1Labels = raw33773step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33773step1 raw33773step1Labels = mixedMoment B raw33773step2 raw33773step2Labels := by
      have ha : raw33773step2 = raw33773step1 := by apply Matrix.ext; unfold raw33773step2 raw33773step1; decide +kernel
      have hl : raw33773step1Labels = labelEmbedding7 ∘ raw33773step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33773step1 raw33773step1Labels raw33773step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4848 node4848Labels := by rfl

def raw33774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33774step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33774step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33774step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33774step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33774step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33774step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33774 raw33774Labels = mixedMoment B node4452 node4452Labels := by
  calc
    mixedMoment B raw33774 raw33774Labels = mixedMoment B raw33774step0 raw33774step0Labels := by
      have hz : ∀ j, raw33774 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33774step0 = (fun i j => raw33774 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33774step0 raw33774; decide +kernel
      have hl : raw33774step0Labels = raw33774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33774 raw33774Labels permutation346 hz
    mixedMoment B raw33774step0 raw33774step0Labels = mixedMoment B raw33774step1 raw33774step1Labels := by
      have ha : raw33774step1 = (fun i j => raw33774step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33774step1 raw33774step0; decide +kernel
      have hl : raw33774step1Labels = raw33774step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33774step0 raw33774step0Labels permutation38 permutation4
    mixedMoment B raw33774step1 raw33774step1Labels = mixedMoment B raw33774step2 raw33774step2Labels := by
      have ha : raw33774step2 = -raw33774step1 := by apply Matrix.ext; change ∀ i j, raw33774step2 i j = -(raw33774step1 i j); unfold raw33774step2 raw33774step1; decide +kernel
      have hl : raw33774step2Labels = raw33774step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33774step2 raw33774step2Labels = mixedMoment B raw33774step3 raw33774step3Labels := by
      have ha : raw33774step3 = raw33774step2 := by apply Matrix.ext; unfold raw33774step3 raw33774step2; decide +kernel
      have hl : raw33774step2Labels = labelEmbedding7 ∘ raw33774step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33774step2 raw33774step2Labels raw33774step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4452 node4452Labels := by rfl

def raw33775 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33775step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33775step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33775step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33775 raw33775Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw33775 raw33775Labels = mixedMoment B raw33775step0 raw33775step0Labels := by
      have hz : ∀ j, raw33775 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33775step0 = (fun i j => raw33775 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33775step0 raw33775; decide +kernel
      have hl : raw33775step0Labels = raw33775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33775 raw33775Labels permutation346 hz
    mixedMoment B raw33775step0 raw33775step0Labels = mixedMoment B raw33775step1 raw33775step1Labels := by
      have ha : raw33775step1 = (fun i j => raw33775step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33775step1 raw33775step0; decide +kernel
      have hl : raw33775step1Labels = raw33775step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33775step0 raw33775step0Labels permutation32 permutation6
    mixedMoment B raw33775step1 raw33775step1Labels = mixedMoment B raw33775step2 raw33775step2Labels := by
      have ha : raw33775step2 = raw33775step1 := by apply Matrix.ext; unfold raw33775step2 raw33775step1; decide +kernel
      have hl : raw33775step1Labels = labelEmbedding9 ∘ raw33775step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33775step1 raw33775step1Labels raw33775step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4834 node4834Labels := by rfl

def raw33776 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33776step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33776step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33776step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33776step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33776step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33776step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33776 raw33776Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw33776 raw33776Labels = mixedMoment B raw33776step0 raw33776step0Labels := by
      have ha : raw33776step0 = (fun i j => raw33776 (permutation182 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33776step0 raw33776; decide +kernel
      have hl : raw33776step0Labels = raw33776Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33776 raw33776Labels permutation182 permutation4
    mixedMoment B raw33776step0 raw33776step0Labels = mixedMoment B raw33776step1 raw33776step1Labels := by
      have ha : raw33776step1 = -raw33776step0 := by apply Matrix.ext; change ∀ i j, raw33776step1 i j = -(raw33776step0 i j); unfold raw33776step1 raw33776step0; decide +kernel
      have hl : raw33776step1Labels = raw33776step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33776step1 raw33776step1Labels = mixedMoment B raw33776step2 raw33776step2Labels := by
      have ha : raw33776step2 = raw33776step1 := by apply Matrix.ext; unfold raw33776step2 raw33776step1; decide +kernel
      have hl : raw33776step1Labels = labelEmbedding7 ∘ raw33776step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33776step1 raw33776step1Labels raw33776step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

def raw33777 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33777step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33777step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33777step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33777step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33777step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33777step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33777 raw33777Labels = mixedMoment B node4860 node4860Labels := by
  calc
    mixedMoment B raw33777 raw33777Labels = mixedMoment B raw33777step0 raw33777step0Labels := by
      have hz : ∀ j, raw33777 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33777step0 = (fun i j => raw33777 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33777step0 raw33777; decide +kernel
      have hl : raw33777step0Labels = raw33777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33777 raw33777Labels permutation346 hz
    mixedMoment B raw33777step0 raw33777step0Labels = mixedMoment B raw33777step1 raw33777step1Labels := by
      have ha : raw33777step1 = (fun i j => raw33777step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33777step1 raw33777step0; decide +kernel
      have hl : raw33777step1Labels = raw33777step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33777step0 raw33777step0Labels permutation38 permutation4
    mixedMoment B raw33777step1 raw33777step1Labels = mixedMoment B raw33777step2 raw33777step2Labels := by
      have ha : raw33777step2 = -raw33777step1 := by apply Matrix.ext; change ∀ i j, raw33777step2 i j = -(raw33777step1 i j); unfold raw33777step2 raw33777step1; decide +kernel
      have hl : raw33777step2Labels = raw33777step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33777step2 raw33777step2Labels = mixedMoment B raw33777step3 raw33777step3Labels := by
      have ha : raw33777step3 = raw33777step2 := by apply Matrix.ext; unfold raw33777step3 raw33777step2; decide +kernel
      have hl : raw33777step2Labels = labelEmbedding7 ∘ raw33777step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33777step2 raw33777step2Labels raw33777step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4860 node4860Labels := by rfl

def raw33778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw33778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw33778step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33778step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw33778step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33778step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw33778step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33778step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw33778step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33778 raw33778Labels = mixedMoment B node4437 node4437Labels := by
  calc
    mixedMoment B raw33778 raw33778Labels = mixedMoment B raw33778step0 raw33778step0Labels := by
      have hz : ∀ j, raw33778 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33778step0 = (fun i j => raw33778 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33778step0 raw33778; decide +kernel
      have hl : raw33778step0Labels = raw33778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33778 raw33778Labels permutation346 hz
    mixedMoment B raw33778step0 raw33778step0Labels = mixedMoment B raw33778step1 raw33778step1Labels := by
      have ha : raw33778step1 = (fun i j => raw33778step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33778step1 raw33778step0; decide +kernel
      have hl : raw33778step1Labels = raw33778step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33778step0 raw33778step0Labels permutation40 permutation4
    mixedMoment B raw33778step1 raw33778step1Labels = mixedMoment B raw33778step2 raw33778step2Labels := by
      have ha : raw33778step2 = -raw33778step1 := by apply Matrix.ext; change ∀ i j, raw33778step2 i j = -(raw33778step1 i j); unfold raw33778step2 raw33778step1; decide +kernel
      have hl : raw33778step2Labels = raw33778step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33778step2 raw33778step2Labels = mixedMoment B raw33778step3 raw33778step3Labels := by
      have ha : raw33778step3 = raw33778step2 := by apply Matrix.ext; unfold raw33778step3 raw33778step2; decide +kernel
      have hl : raw33778step2Labels = labelEmbedding7 ∘ raw33778step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33778step2 raw33778step2Labels raw33778step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4437 node4437Labels := by rfl

def raw33779 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw33779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw33779step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33779step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33779step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33779step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33779 raw33779Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw33779 raw33779Labels = mixedMoment B raw33779step0 raw33779step0Labels := by
      have hz : ∀ j, raw33779 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33779step0 = (fun i j => raw33779 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33779step0 raw33779; decide +kernel
      have hl : raw33779step0Labels = raw33779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33779 raw33779Labels permutation346 hz
    mixedMoment B raw33779step0 raw33779step0Labels = mixedMoment B raw33779step1 raw33779step1Labels := by
      have ha : raw33779step1 = (fun i j => raw33779step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33779step1 raw33779step0; decide +kernel
      have hl : raw33779step1Labels = raw33779step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33779step0 raw33779step0Labels permutation32 permutation6
    mixedMoment B raw33779step1 raw33779step1Labels = mixedMoment B raw33779step2 raw33779step2Labels := by
      have ha : raw33779step2 = raw33779step1 := by apply Matrix.ext; unfold raw33779step2 raw33779step1; decide +kernel
      have hl : raw33779step1Labels = labelEmbedding9 ∘ raw33779step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33779step1 raw33779step1Labels raw33779step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4832 node4832Labels := by rfl

def raw33780 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw33780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33780step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw33780step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33780step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw33780step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33780step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw33780step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33780 raw33780Labels = mixedMoment B node4791 node4791Labels := by
  calc
    mixedMoment B raw33780 raw33780Labels = mixedMoment B raw33780step0 raw33780step0Labels := by
      have ha : raw33780step0 = (fun i j => raw33780 (permutation184 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33780step0 raw33780; decide +kernel
      have hl : raw33780step0Labels = raw33780Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33780 raw33780Labels permutation184 permutation4
    mixedMoment B raw33780step0 raw33780step0Labels = mixedMoment B raw33780step1 raw33780step1Labels := by
      have ha : raw33780step1 = -raw33780step0 := by apply Matrix.ext; change ∀ i j, raw33780step1 i j = -(raw33780step0 i j); unfold raw33780step1 raw33780step0; decide +kernel
      have hl : raw33780step1Labels = raw33780step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33780step1 raw33780step1Labels = mixedMoment B raw33780step2 raw33780step2Labels := by
      have ha : raw33780step2 = raw33780step1 := by apply Matrix.ext; unfold raw33780step2 raw33780step1; decide +kernel
      have hl : raw33780step1Labels = labelEmbedding7 ∘ raw33780step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33780step1 raw33780step1Labels raw33780step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4791 node4791Labels := by rfl

def raw33781 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw33781Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw33781step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33781step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw33781step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33781step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw33781step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33781step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw33781step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33781 raw33781Labels = mixedMoment B node4850 node4850Labels := by
  calc
    mixedMoment B raw33781 raw33781Labels = mixedMoment B raw33781step0 raw33781step0Labels := by
      have hz : ∀ j, raw33781 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33781step0 = (fun i j => raw33781 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33781step0 raw33781; decide +kernel
      have hl : raw33781step0Labels = raw33781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33781 raw33781Labels permutation346 hz
    mixedMoment B raw33781step0 raw33781step0Labels = mixedMoment B raw33781step1 raw33781step1Labels := by
      have ha : raw33781step1 = (fun i j => raw33781step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33781step1 raw33781step0; decide +kernel
      have hl : raw33781step1Labels = raw33781step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33781step0 raw33781step0Labels permutation40 permutation4
    mixedMoment B raw33781step1 raw33781step1Labels = mixedMoment B raw33781step2 raw33781step2Labels := by
      have ha : raw33781step2 = -raw33781step1 := by apply Matrix.ext; change ∀ i j, raw33781step2 i j = -(raw33781step1 i j); unfold raw33781step2 raw33781step1; decide +kernel
      have hl : raw33781step2Labels = raw33781step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33781step2 raw33781step2Labels = mixedMoment B raw33781step3 raw33781step3Labels := by
      have ha : raw33781step3 = raw33781step2 := by apply Matrix.ext; unfold raw33781step3 raw33781step2; decide +kernel
      have hl : raw33781step2Labels = labelEmbedding7 ∘ raw33781step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33781step2 raw33781step2Labels raw33781step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4850 node4850Labels := by rfl

def raw33782 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw33782Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw33782step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33782step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw33782step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33782step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw33782step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33782step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw33782step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33782 raw33782Labels = mixedMoment B node4850 node4850Labels := by
  calc
    mixedMoment B raw33782 raw33782Labels = mixedMoment B raw33782step0 raw33782step0Labels := by
      have hz : ∀ j, raw33782 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33782step0 = (fun i j => raw33782 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33782step0 raw33782; decide +kernel
      have hl : raw33782step0Labels = raw33782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33782 raw33782Labels permutation346 hz
    mixedMoment B raw33782step0 raw33782step0Labels = mixedMoment B raw33782step1 raw33782step1Labels := by
      have ha : raw33782step1 = (fun i j => raw33782step0 (permutation46 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33782step1 raw33782step0; decide +kernel
      have hl : raw33782step1Labels = raw33782step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33782step0 raw33782step0Labels permutation46 permutation4
    mixedMoment B raw33782step1 raw33782step1Labels = mixedMoment B raw33782step2 raw33782step2Labels := by
      have ha : raw33782step2 = -raw33782step1 := by apply Matrix.ext; change ∀ i j, raw33782step2 i j = -(raw33782step1 i j); unfold raw33782step2 raw33782step1; decide +kernel
      have hl : raw33782step2Labels = raw33782step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33782step2 raw33782step2Labels = mixedMoment B raw33782step3 raw33782step3Labels := by
      have ha : raw33782step3 = raw33782step2 := by apply Matrix.ext; unfold raw33782step3 raw33782step2; decide +kernel
      have hl : raw33782step2Labels = labelEmbedding7 ∘ raw33782step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33782step2 raw33782step2Labels raw33782step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4850 node4850Labels := by rfl

def raw33783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33783Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33783step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw33783step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33783step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw33783step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33783 raw33783Labels = mixedMoment B node3070 node3070Labels := by
  calc
    mixedMoment B raw33783 raw33783Labels = mixedMoment B raw33783step0 raw33783step0Labels := by
      have ha : raw33783step0 = (fun i j => raw33783 (permutation317 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33783step0 raw33783; decide +kernel
      have hl : raw33783step0Labels = raw33783Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33783 raw33783Labels permutation317 permutation4
    mixedMoment B raw33783step0 raw33783step0Labels = mixedMoment B raw33783step1 raw33783step1Labels := by
      have ha : raw33783step1 = -raw33783step0 := by apply Matrix.ext; change ∀ i j, raw33783step1 i j = -(raw33783step0 i j); unfold raw33783step1 raw33783step0; decide +kernel
      have hl : raw33783step1Labels = raw33783step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3070 node3070Labels := by rfl

def raw33784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33784Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33784step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33784step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33784 raw33784Labels = mixedMoment B node3446 node3446Labels := by
  calc
    mixedMoment B raw33784 raw33784Labels = mixedMoment B raw33784step0 raw33784step0Labels := by
      have ha : raw33784step0 = (fun i j => raw33784 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33784step0 raw33784; decide +kernel
      have hl : raw33784step0Labels = raw33784Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33784 raw33784Labels permutation176 permutation2
    _ = mixedMoment B node3446 node3446Labels := by rfl

def raw33785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33785Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33785 raw33785Labels = mixedMoment B node3558 node3558Labels := by
  calc
    _ = mixedMoment B node3558 node3558Labels := by rfl

def raw33786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw33786Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33786step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33786 raw33786Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw33786 raw33786Labels = mixedMoment B raw33786step0 raw33786step0Labels := by
      have ha : raw33786step0 = (fun i j => raw33786 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33786step0 raw33786; decide +kernel
      have hl : raw33786step0Labels = raw33786Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33786 raw33786Labels permutation154 permutation2
    _ = mixedMoment B node3558 node3558Labels := by rfl

def raw33787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33787Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33787 raw33787Labels = mixedMoment B node3563 node3563Labels := by
  calc
    _ = mixedMoment B node3563 node3563Labels := by rfl

def raw33788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33788Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33788step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33788 raw33788Labels = mixedMoment B node1879 node1879Labels := by
  calc
    mixedMoment B raw33788 raw33788Labels = mixedMoment B raw33788step0 raw33788step0Labels := by
      have ha : raw33788step0 = (fun i j => raw33788 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33788step0 raw33788; decide +kernel
      have hl : raw33788step0Labels = raw33788Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33788 raw33788Labels permutation178 permutation2
    _ = mixedMoment B node1879 node1879Labels := by rfl

def raw33789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33789Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33789step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33789 raw33789Labels = mixedMoment B node1879 node1879Labels := by
  calc
    mixedMoment B raw33789 raw33789Labels = mixedMoment B raw33789step0 raw33789step0Labels := by
      have ha : raw33789step0 = (fun i j => raw33789 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33789step0 raw33789; decide +kernel
      have hl : raw33789step0Labels = raw33789Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33789 raw33789Labels permutation176 permutation2
    _ = mixedMoment B node1879 node1879Labels := by rfl

def raw33790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33790Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33790step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33790 raw33790Labels = mixedMoment B node1877 node1877Labels := by
  calc
    mixedMoment B raw33790 raw33790Labels = mixedMoment B raw33790step0 raw33790step0Labels := by
      have ha : raw33790step0 = (fun i j => raw33790 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33790step0 raw33790; decide +kernel
      have hl : raw33790step0Labels = raw33790Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33790 raw33790Labels permutation176 permutation2
    _ = mixedMoment B node1877 node1877Labels := by rfl

def raw33791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33791Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33791step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33791step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33791step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33791step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33791step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33791 raw33791Labels = mixedMoment B node5231 node5231Labels := by
  calc
    mixedMoment B raw33791 raw33791Labels = mixedMoment B raw33791step0 raw33791step0Labels := by
      have ha : raw33791step0 = (fun i j => raw33791 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33791step0 raw33791; decide +kernel
      have hl : raw33791step0Labels = raw33791Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33791 raw33791Labels permutation170 permutation7
    mixedMoment B raw33791step0 raw33791step0Labels = mixedMoment B raw33791step1 raw33791step1Labels := by
      have ha : raw33791step1 = -raw33791step0 := by apply Matrix.ext; change ∀ i j, raw33791step1 i j = -(raw33791step0 i j); unfold raw33791step1 raw33791step0; decide +kernel
      have hl : raw33791step1Labels = raw33791step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33791step1 raw33791step1Labels = mixedMoment B raw33791step2 raw33791step2Labels := by
      have ha : raw33791step2 = raw33791step1 := by apply Matrix.ext; unfold raw33791step2 raw33791step1; decide +kernel
      have hl : raw33791step1Labels = labelEmbedding10 ∘ raw33791step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33791step1 raw33791step1Labels raw33791step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5231 node5231Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
