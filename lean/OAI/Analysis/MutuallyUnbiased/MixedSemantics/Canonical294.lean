import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw37632 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -4, 3]]
def raw37632Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![1, -4, 3]]
def raw37632step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37632step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 1, -4]]
def raw37632step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37632 raw37632Labels = mixedMoment B node968 node968Labels := by
  calc
    mixedMoment B raw37632 raw37632Labels = mixedMoment B raw37632step0 raw37632step0Labels := by
      have hz : ∀ j, raw37632 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37632step0 = (fun i j => raw37632 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37632step0 raw37632; decide +kernel
      have hl : raw37632step0Labels = raw37632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37632 raw37632Labels permutation346 hz
    mixedMoment B raw37632step0 raw37632step0Labels = mixedMoment B raw37632step1 raw37632step1Labels := by
      have ha : raw37632step1 = (fun i j => raw37632step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37632step1 raw37632step0; decide +kernel
      have hl : raw37632step1Labels = raw37632step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37632step0 raw37632step0Labels permutation145 permutation4
    _ = mixedMoment B node968 node968Labels := by rfl

def raw37633 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37633Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37633step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37633step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37633step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37633step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37633 raw37633Labels = mixedMoment B node840 node840Labels := by
  calc
    mixedMoment B raw37633 raw37633Labels = mixedMoment B raw37633step0 raw37633step0Labels := by
      have hz : ∀ j, raw37633 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37633step0 = (fun i j => raw37633 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37633step0 raw37633; decide +kernel
      have hl : raw37633step0Labels = raw37633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37633 raw37633Labels permutation346 hz
    mixedMoment B raw37633step0 raw37633step0Labels = mixedMoment B raw37633step1 raw37633step1Labels := by
      have ha : raw37633step1 = (fun i j => raw37633step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37633step1 raw37633step0; decide +kernel
      have hl : raw37633step1Labels = raw37633step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37633step0 raw37633step0Labels permutation32 permutation4
    mixedMoment B raw37633step1 raw37633step1Labels = mixedMoment B raw37633step2 raw37633step2Labels := by
      have ha : raw37633step2 = -raw37633step1 := by apply Matrix.ext; change ∀ i j, raw37633step2 i j = -(raw37633step1 i j); unfold raw37633step2 raw37633step1; decide +kernel
      have hl : raw37633step2Labels = raw37633step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node840 node840Labels := by rfl

def raw37634 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37634Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![1, -2, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37634step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw37634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37634step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw37634step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37634 raw37634Labels = mixedMoment B node769 node769Labels := by
  calc
    mixedMoment B raw37634 raw37634Labels = mixedMoment B raw37634step0 raw37634step0Labels := by
      have hz : ∀ j, raw37634 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37634step0 = (fun i j => raw37634 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37634step0 raw37634; decide +kernel
      have hl : raw37634step0Labels = raw37634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37634 raw37634Labels permutation346 hz
    mixedMoment B raw37634step0 raw37634step0Labels = mixedMoment B raw37634step1 raw37634step1Labels := by
      have ha : raw37634step1 = (fun i j => raw37634step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37634step1 raw37634step0; decide +kernel
      have hl : raw37634step1Labels = raw37634step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37634step0 raw37634step0Labels permutation35 permutation4
    mixedMoment B raw37634step1 raw37634step1Labels = mixedMoment B raw37634step2 raw37634step2Labels := by
      have ha : raw37634step2 = -raw37634step1 := by apply Matrix.ext; change ∀ i j, raw37634step2 i j = -(raw37634step1 i j); unfold raw37634step2 raw37634step1; decide +kernel
      have hl : raw37634step2Labels = raw37634step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node769 node769Labels := by rfl

def raw37635 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, -1, 3]]
def raw37635Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![-2, -1, 3]]
def raw37635step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw37635step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37635step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw37635step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37635 raw37635Labels = mixedMoment B node769 node769Labels := by
  calc
    mixedMoment B raw37635 raw37635Labels = mixedMoment B raw37635step0 raw37635step0Labels := by
      have hz : ∀ j, raw37635 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37635step0 = (fun i j => raw37635 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37635step0 raw37635; decide +kernel
      have hl : raw37635step0Labels = raw37635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37635 raw37635Labels permutation346 hz
    mixedMoment B raw37635step0 raw37635step0Labels = mixedMoment B raw37635step1 raw37635step1Labels := by
      have ha : raw37635step1 = (fun i j => raw37635step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37635step1 raw37635step0; decide +kernel
      have hl : raw37635step1Labels = raw37635step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37635step0 raw37635step0Labels permutation33 permutation4
    mixedMoment B raw37635step1 raw37635step1Labels = mixedMoment B raw37635step2 raw37635step2Labels := by
      have ha : raw37635step2 = -raw37635step1 := by apply Matrix.ext; change ∀ i j, raw37635step2 i j = -(raw37635step1 i j); unfold raw37635step2 raw37635step1; decide +kernel
      have hl : raw37635step2Labels = raw37635step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node769 node769Labels := by rfl

def raw37636 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37636Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37636step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37636step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37636step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37636step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw37636step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37636 raw37636Labels = mixedMoment B node767 node767Labels := by
  calc
    mixedMoment B raw37636 raw37636Labels = mixedMoment B raw37636step0 raw37636step0Labels := by
      have hz : ∀ j, raw37636 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37636step0 = (fun i j => raw37636 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37636step0 raw37636; decide +kernel
      have hl : raw37636step0Labels = raw37636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37636 raw37636Labels permutation346 hz
    mixedMoment B raw37636step0 raw37636step0Labels = mixedMoment B raw37636step1 raw37636step1Labels := by
      have ha : raw37636step1 = (fun i j => raw37636step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37636step1 raw37636step0; decide +kernel
      have hl : raw37636step1Labels = raw37636step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37636step0 raw37636step0Labels permutation32 permutation4
    mixedMoment B raw37636step1 raw37636step1Labels = mixedMoment B raw37636step2 raw37636step2Labels := by
      have ha : raw37636step2 = -raw37636step1 := by apply Matrix.ext; change ∀ i j, raw37636step2 i j = -(raw37636step1 i j); unfold raw37636step2 raw37636step1; decide +kernel
      have hl : raw37636step2Labels = raw37636step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node767 node767Labels := by rfl

def raw37637 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37637Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37637step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37637step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37637step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw37637step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37637 raw37637Labels = mixedMoment B node1571 node1571Labels := by
  calc
    mixedMoment B raw37637 raw37637Labels = mixedMoment B raw37637step0 raw37637step0Labels := by
      have hz : ∀ j, raw37637 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37637step0 = (fun i j => raw37637 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37637step0 raw37637; decide +kernel
      have hl : raw37637step0Labels = raw37637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37637 raw37637Labels permutation346 hz
    mixedMoment B raw37637step0 raw37637step0Labels = mixedMoment B raw37637step1 raw37637step1Labels := by
      have ha : raw37637step1 = (fun i j => raw37637step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37637step1 raw37637step0; decide +kernel
      have hl : raw37637step1Labels = raw37637step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37637step0 raw37637step0Labels permutation32 permutation4
    mixedMoment B raw37637step1 raw37637step1Labels = mixedMoment B raw37637step2 raw37637step2Labels := by
      have ha : raw37637step2 = -raw37637step1 := by apply Matrix.ext; change ∀ i j, raw37637step2 i j = -(raw37637step1 i j); unfold raw37637step2 raw37637step1; decide +kernel
      have hl : raw37637step2Labels = raw37637step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1571 node1571Labels := by rfl

def raw37638 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37638Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37638step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37638step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37638step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw37638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37638 raw37638Labels = mixedMoment B node1588 node1588Labels := by
  calc
    mixedMoment B raw37638 raw37638Labels = mixedMoment B raw37638step0 raw37638step0Labels := by
      have ha : raw37638step0 = (fun i j => raw37638 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37638step0 raw37638; decide +kernel
      have hl : raw37638step0Labels = raw37638Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37638 raw37638Labels permutation176 permutation4
    mixedMoment B raw37638step0 raw37638step0Labels = mixedMoment B raw37638step1 raw37638step1Labels := by
      have ha : raw37638step1 = -raw37638step0 := by apply Matrix.ext; change ∀ i j, raw37638step1 i j = -(raw37638step0 i j); unfold raw37638step1 raw37638step0; decide +kernel
      have hl : raw37638step1Labels = raw37638step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1588 node1588Labels := by rfl

def raw37639 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37639Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![-1, 0, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37639step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37639step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37639step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw37639step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37639 raw37639Labels = mixedMoment B node1674 node1674Labels := by
  calc
    mixedMoment B raw37639 raw37639Labels = mixedMoment B raw37639step0 raw37639step0Labels := by
      have hz : ∀ j, raw37639 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37639step0 = (fun i j => raw37639 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37639step0 raw37639; decide +kernel
      have hl : raw37639step0Labels = raw37639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37639 raw37639Labels permutation346 hz
    mixedMoment B raw37639step0 raw37639step0Labels = mixedMoment B raw37639step1 raw37639step1Labels := by
      have ha : raw37639step1 = (fun i j => raw37639step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37639step1 raw37639step0; decide +kernel
      have hl : raw37639step1Labels = raw37639step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37639step0 raw37639step0Labels permutation32 permutation4
    mixedMoment B raw37639step1 raw37639step1Labels = mixedMoment B raw37639step2 raw37639step2Labels := by
      have ha : raw37639step2 = -raw37639step1 := by apply Matrix.ext; change ∀ i j, raw37639step2 i j = -(raw37639step1 i j); unfold raw37639step2 raw37639step1; decide +kernel
      have hl : raw37639step2Labels = raw37639step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1674 node1674Labels := by rfl

def raw37640 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37640Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37640step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37640step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37640step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw37640step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37640 raw37640Labels = mixedMoment B node1674 node1674Labels := by
  calc
    mixedMoment B raw37640 raw37640Labels = mixedMoment B raw37640step0 raw37640step0Labels := by
      have hz : ∀ j, raw37640 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37640step0 = (fun i j => raw37640 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37640step0 raw37640; decide +kernel
      have hl : raw37640step0Labels = raw37640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37640 raw37640Labels permutation346 hz
    mixedMoment B raw37640step0 raw37640step0Labels = mixedMoment B raw37640step1 raw37640step1Labels := by
      have ha : raw37640step1 = (fun i j => raw37640step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37640step1 raw37640step0; decide +kernel
      have hl : raw37640step1Labels = raw37640step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37640step0 raw37640step0Labels permutation34 permutation4
    mixedMoment B raw37640step1 raw37640step1Labels = mixedMoment B raw37640step2 raw37640step2Labels := by
      have ha : raw37640step2 = -raw37640step1 := by apply Matrix.ext; change ∀ i j, raw37640step2 i j = -(raw37640step1 i j); unfold raw37640step2 raw37640step1; decide +kernel
      have hl : raw37640step2Labels = raw37640step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1674 node1674Labels := by rfl

def raw37641 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37641Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37641step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37641step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37641step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw37641step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37641 raw37641Labels = mixedMoment B node761 node761Labels := by
  calc
    mixedMoment B raw37641 raw37641Labels = mixedMoment B raw37641step0 raw37641step0Labels := by
      have ha : raw37641step0 = (fun i j => raw37641 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37641step0 raw37641; decide +kernel
      have hl : raw37641step0Labels = raw37641Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37641 raw37641Labels permutation152 permutation4
    mixedMoment B raw37641step0 raw37641step0Labels = mixedMoment B raw37641step1 raw37641step1Labels := by
      have ha : raw37641step1 = -raw37641step0 := by apply Matrix.ext; change ∀ i j, raw37641step1 i j = -(raw37641step0 i j); unfold raw37641step1 raw37641step0; decide +kernel
      have hl : raw37641step1Labels = raw37641step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node761 node761Labels := by rfl

def raw37642 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37642Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37642step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37642step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37642step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw37642step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37642 raw37642Labels = mixedMoment B node1567 node1567Labels := by
  calc
    mixedMoment B raw37642 raw37642Labels = mixedMoment B raw37642step0 raw37642step0Labels := by
      have ha : raw37642step0 = (fun i j => raw37642 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37642step0 raw37642; decide +kernel
      have hl : raw37642step0Labels = raw37642Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37642 raw37642Labels permutation152 permutation4
    mixedMoment B raw37642step0 raw37642step0Labels = mixedMoment B raw37642step1 raw37642step1Labels := by
      have ha : raw37642step1 = -raw37642step0 := by apply Matrix.ext; change ∀ i j, raw37642step1 i j = -(raw37642step0 i j); unfold raw37642step1 raw37642step0; decide +kernel
      have hl : raw37642step1Labels = raw37642step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1567 node1567Labels := by rfl

def raw37643 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37643Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37643step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37643step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37643step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37643step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw37643step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37643 raw37643Labels = mixedMoment B node1691 node1691Labels := by
  calc
    mixedMoment B raw37643 raw37643Labels = mixedMoment B raw37643step0 raw37643step0Labels := by
      have hz : ∀ j, raw37643 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37643step0 = (fun i j => raw37643 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37643step0 raw37643; decide +kernel
      have hl : raw37643step0Labels = raw37643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37643 raw37643Labels permutation346 hz
    mixedMoment B raw37643step0 raw37643step0Labels = mixedMoment B raw37643step1 raw37643step1Labels := by
      have ha : raw37643step1 = (fun i j => raw37643step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37643step1 raw37643step0; decide +kernel
      have hl : raw37643step1Labels = raw37643step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37643step0 raw37643step0Labels permutation32 permutation4
    mixedMoment B raw37643step1 raw37643step1Labels = mixedMoment B raw37643step2 raw37643step2Labels := by
      have ha : raw37643step2 = -raw37643step1 := by apply Matrix.ext; change ∀ i j, raw37643step2 i j = -(raw37643step1 i j); unfold raw37643step2 raw37643step1; decide +kernel
      have hl : raw37643step2Labels = raw37643step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1691 node1691Labels := by rfl

def raw37644 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37644Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw37644step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37644step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw37644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37644 raw37644Labels = mixedMoment B node1671 node1671Labels := by
  calc
    mixedMoment B raw37644 raw37644Labels = mixedMoment B raw37644step0 raw37644step0Labels := by
      have ha : raw37644step0 = (fun i j => raw37644 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37644step0 raw37644; decide +kernel
      have hl : raw37644step0Labels = raw37644Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37644 raw37644Labels permutation158 permutation4
    mixedMoment B raw37644step0 raw37644step0Labels = mixedMoment B raw37644step1 raw37644step1Labels := by
      have ha : raw37644step1 = -raw37644step0 := by apply Matrix.ext; change ∀ i j, raw37644step1 i j = -(raw37644step0 i j); unfold raw37644step1 raw37644step0; decide +kernel
      have hl : raw37644step1Labels = raw37644step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1671 node1671Labels := by rfl

def raw37645 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37645Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37645step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37645step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37645step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37645step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37645 raw37645Labels = mixedMoment B node1678 node1678Labels := by
  calc
    mixedMoment B raw37645 raw37645Labels = mixedMoment B raw37645step0 raw37645step0Labels := by
      have ha : raw37645step0 = (fun i j => raw37645 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37645step0 raw37645; decide +kernel
      have hl : raw37645step0Labels = raw37645Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37645 raw37645Labels permutation164 permutation4
    mixedMoment B raw37645step0 raw37645step0Labels = mixedMoment B raw37645step1 raw37645step1Labels := by
      have ha : raw37645step1 = -raw37645step0 := by apply Matrix.ext; change ∀ i j, raw37645step1 i j = -(raw37645step0 i j); unfold raw37645step1 raw37645step0; decide +kernel
      have hl : raw37645step1Labels = raw37645step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1678 node1678Labels := by rfl

def raw37646 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw37646Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37646step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37646step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37646step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37646 raw37646Labels = mixedMoment B node1678 node1678Labels := by
  calc
    mixedMoment B raw37646 raw37646Labels = mixedMoment B raw37646step0 raw37646step0Labels := by
      have ha : raw37646step0 = (fun i j => raw37646 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37646step0 raw37646; decide +kernel
      have hl : raw37646step0Labels = raw37646Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37646 raw37646Labels permutation170 permutation4
    mixedMoment B raw37646step0 raw37646step0Labels = mixedMoment B raw37646step1 raw37646step1Labels := by
      have ha : raw37646step1 = -raw37646step0 := by apply Matrix.ext; change ∀ i j, raw37646step1 i j = -(raw37646step0 i j); unfold raw37646step1 raw37646step0; decide +kernel
      have hl : raw37646step1Labels = raw37646step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1678 node1678Labels := by rfl

def raw37647 : Matrix (Fin 6) (Fin 2) ℤ := ![![4, -4], ![1, -1], ![0, 0], ![-1, 1], ![-2, 2], ![-2, 2]]
def raw37647Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37647step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![4, -4], ![1, -1], ![-1, 1], ![-2, 2], ![-2, 2]]
def raw37647step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37647step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw37647step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37647 raw37647Labels = mixedMoment B node4065 node4065Labels := by
  calc
    mixedMoment B raw37647 raw37647Labels = mixedMoment B raw37647step0 raw37647step0Labels := by
      have hz : ∀ j, raw37647 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37647step0 = (fun i j => raw37647 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37647step0 raw37647; decide +kernel
      have hl : raw37647step0Labels = raw37647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37647 raw37647Labels permutation346 hz
    mixedMoment B raw37647step0 raw37647step0Labels = mixedMoment B raw37647step1 raw37647step1Labels := by
      have ha : raw37647step1 = -raw37647step0 := by apply Matrix.ext; change ∀ i j, raw37647step1 i j = -(raw37647step0 i j); unfold raw37647step1 raw37647step0; decide +kernel
      have hl : raw37647step1Labels = raw37647step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4065 node4065Labels := by rfl

def raw37648 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37648Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37648step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37648step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw37648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37648step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw37648step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37648 raw37648Labels = mixedMoment B node1681 node1681Labels := by
  calc
    mixedMoment B raw37648 raw37648Labels = mixedMoment B raw37648step0 raw37648step0Labels := by
      have hz : ∀ j, raw37648 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37648step0 = (fun i j => raw37648 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37648step0 raw37648; decide +kernel
      have hl : raw37648step0Labels = raw37648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37648 raw37648Labels permutation346 hz
    mixedMoment B raw37648step0 raw37648step0Labels = mixedMoment B raw37648step1 raw37648step1Labels := by
      have ha : raw37648step1 = (fun i j => raw37648step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37648step1 raw37648step0; decide +kernel
      have hl : raw37648step1Labels = raw37648step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37648step0 raw37648step0Labels permutation36 permutation2
    mixedMoment B raw37648step1 raw37648step1Labels = mixedMoment B raw37648step2 raw37648step2Labels := by
      have ha : raw37648step2 = -raw37648step1 := by apply Matrix.ext; change ∀ i j, raw37648step2 i j = -(raw37648step1 i j); unfold raw37648step2 raw37648step1; decide +kernel
      have hl : raw37648step2Labels = raw37648step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1681 node1681Labels := by rfl

def raw37649 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37649Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37649step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw37649step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37649step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw37649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37649 raw37649Labels = mixedMoment B node3270 node3270Labels := by
  calc
    mixedMoment B raw37649 raw37649Labels = mixedMoment B raw37649step0 raw37649step0Labels := by
      have hz : ∀ j, raw37649 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37649step0 = (fun i j => raw37649 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37649step0 raw37649; decide +kernel
      have hl : raw37649step0Labels = raw37649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37649 raw37649Labels permutation346 hz
    mixedMoment B raw37649step0 raw37649step0Labels = mixedMoment B raw37649step1 raw37649step1Labels := by
      have ha : raw37649step1 = (fun i j => raw37649step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37649step1 raw37649step0; decide +kernel
      have hl : raw37649step1Labels = raw37649step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37649step0 raw37649step0Labels permutation36 permutation2
    mixedMoment B raw37649step1 raw37649step1Labels = mixedMoment B raw37649step2 raw37649step2Labels := by
      have ha : raw37649step2 = -raw37649step1 := by apply Matrix.ext; change ∀ i j, raw37649step2 i j = -(raw37649step1 i j); unfold raw37649step2 raw37649step1; decide +kernel
      have hl : raw37649step2Labels = raw37649step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3270 node3270Labels := by rfl

def raw37650 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37650Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw37650step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37650step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37650step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37650 raw37650Labels = mixedMoment B node3258 node3258Labels := by
  calc
    mixedMoment B raw37650 raw37650Labels = mixedMoment B raw37650step0 raw37650step0Labels := by
      have ha : raw37650step0 = (fun i j => raw37650 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37650step0 raw37650; decide +kernel
      have hl : raw37650step0Labels = raw37650Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37650 raw37650Labels permutation160 permutation4
    mixedMoment B raw37650step0 raw37650step0Labels = mixedMoment B raw37650step1 raw37650step1Labels := by
      have ha : raw37650step1 = -raw37650step0 := by apply Matrix.ext; change ∀ i j, raw37650step1 i j = -(raw37650step0 i j); unfold raw37650step1 raw37650step0; decide +kernel
      have hl : raw37650step1Labels = raw37650step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3258 node3258Labels := by rfl

def raw37651 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37651Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, -1, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37651step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw37651step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37651step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw37651step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37651 raw37651Labels = mixedMoment B node3270 node3270Labels := by
  calc
    mixedMoment B raw37651 raw37651Labels = mixedMoment B raw37651step0 raw37651step0Labels := by
      have hz : ∀ j, raw37651 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37651step0 = (fun i j => raw37651 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37651step0 raw37651; decide +kernel
      have hl : raw37651step0Labels = raw37651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37651 raw37651Labels permutation346 hz
    mixedMoment B raw37651step0 raw37651step0Labels = mixedMoment B raw37651step1 raw37651step1Labels := by
      have ha : raw37651step1 = (fun i j => raw37651step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37651step1 raw37651step0; decide +kernel
      have hl : raw37651step1Labels = raw37651step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37651step0 raw37651step0Labels permutation34 permutation4
    mixedMoment B raw37651step1 raw37651step1Labels = mixedMoment B raw37651step2 raw37651step2Labels := by
      have ha : raw37651step2 = -raw37651step1 := by apply Matrix.ext; change ∀ i j, raw37651step2 i j = -(raw37651step1 i j); unfold raw37651step2 raw37651step1; decide +kernel
      have hl : raw37651step2Labels = raw37651step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3270 node3270Labels := by rfl

def raw37652 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, -2, 2]]
def raw37652Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![0, -2, 2]]
def raw37652step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw37652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37652step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37652step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37652 raw37652Labels = mixedMoment B node3265 node3265Labels := by
  calc
    mixedMoment B raw37652 raw37652Labels = mixedMoment B raw37652step0 raw37652step0Labels := by
      have hz : ∀ j, raw37652 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37652step0 = (fun i j => raw37652 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37652step0 raw37652; decide +kernel
      have hl : raw37652step0Labels = raw37652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37652 raw37652Labels permutation346 hz
    mixedMoment B raw37652step0 raw37652step0Labels = mixedMoment B raw37652step1 raw37652step1Labels := by
      have ha : raw37652step1 = (fun i j => raw37652step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37652step1 raw37652step0; decide +kernel
      have hl : raw37652step1Labels = raw37652step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37652step0 raw37652step0Labels permutation32 permutation4
    mixedMoment B raw37652step1 raw37652step1Labels = mixedMoment B raw37652step2 raw37652step2Labels := by
      have ha : raw37652step2 = -raw37652step1 := by apply Matrix.ext; change ∀ i j, raw37652step2 i j = -(raw37652step1 i j); unfold raw37652step2 raw37652step1; decide +kernel
      have hl : raw37652step2Labels = raw37652step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3265 node3265Labels := by rfl

def raw37653 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2], ![1, -3, 2]]
def raw37653Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2], ![1, -3, 2]]
def raw37653step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37653step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw37653step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37653 raw37653Labels = mixedMoment B node2657 node2657Labels := by
  calc
    mixedMoment B raw37653 raw37653Labels = mixedMoment B raw37653step0 raw37653step0Labels := by
      have hz : ∀ j, raw37653 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37653step0 = (fun i j => raw37653 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37653step0 raw37653; decide +kernel
      have hl : raw37653step0Labels = raw37653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37653 raw37653Labels permutation346 hz
    mixedMoment B raw37653step0 raw37653step0Labels = mixedMoment B raw37653step1 raw37653step1Labels := by
      have ha : raw37653step1 = (fun i j => raw37653step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37653step1 raw37653step0; decide +kernel
      have hl : raw37653step1Labels = raw37653step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37653step0 raw37653step0Labels permutation151 permutation4
    _ = mixedMoment B node2657 node2657Labels := by rfl

def raw37654 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37654Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37654step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw37654step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37654 raw37654Labels = mixedMoment B node1691 node1691Labels := by
  calc
    mixedMoment B raw37654 raw37654Labels = mixedMoment B raw37654step0 raw37654step0Labels := by
      have hz : ∀ j, raw37654 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37654step0 = (fun i j => raw37654 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37654step0 raw37654; decide +kernel
      have hl : raw37654step0Labels = raw37654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37654 raw37654Labels permutation346 hz
    mixedMoment B raw37654step0 raw37654step0Labels = mixedMoment B raw37654step1 raw37654step1Labels := by
      have ha : raw37654step1 = -raw37654step0 := by apply Matrix.ext; change ∀ i j, raw37654step1 i j = -(raw37654step0 i j); unfold raw37654step1 raw37654step0; decide +kernel
      have hl : raw37654step1Labels = raw37654step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1691 node1691Labels := by rfl

def raw37655 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37655Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37655step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37655step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw37655step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37655 raw37655Labels = mixedMoment B node3274 node3274Labels := by
  calc
    mixedMoment B raw37655 raw37655Labels = mixedMoment B raw37655step0 raw37655step0Labels := by
      have hz : ∀ j, raw37655 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37655step0 = (fun i j => raw37655 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37655step0 raw37655; decide +kernel
      have hl : raw37655step0Labels = raw37655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37655 raw37655Labels permutation346 hz
    mixedMoment B raw37655step0 raw37655step0Labels = mixedMoment B raw37655step1 raw37655step1Labels := by
      have ha : raw37655step1 = -raw37655step0 := by apply Matrix.ext; change ∀ i j, raw37655step1 i j = -(raw37655step0 i j); unfold raw37655step1 raw37655step0; decide +kernel
      have hl : raw37655step1Labels = raw37655step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3274 node3274Labels := by rfl

def raw37656 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37656Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw37656step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37656step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw37656step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37656 raw37656Labels = mixedMoment B node3261 node3261Labels := by
  calc
    mixedMoment B raw37656 raw37656Labels = mixedMoment B raw37656step0 raw37656step0Labels := by
      have ha : raw37656step0 = (fun i j => raw37656 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37656step0 raw37656; decide +kernel
      have hl : raw37656step0Labels = raw37656Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37656 raw37656Labels permutation158 permutation4
    mixedMoment B raw37656step0 raw37656step0Labels = mixedMoment B raw37656step1 raw37656step1Labels := by
      have ha : raw37656step1 = -raw37656step0 := by apply Matrix.ext; change ∀ i j, raw37656step1 i j = -(raw37656step0 i j); unfold raw37656step1 raw37656step0; decide +kernel
      have hl : raw37656step1Labels = raw37656step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3261 node3261Labels := by rfl

def raw37657 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37657Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37657step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37657step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37657step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw37657step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37657 raw37657Labels = mixedMoment B node3274 node3274Labels := by
  calc
    mixedMoment B raw37657 raw37657Labels = mixedMoment B raw37657step0 raw37657step0Labels := by
      have hz : ∀ j, raw37657 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37657step0 = (fun i j => raw37657 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37657step0 raw37657; decide +kernel
      have hl : raw37657step0Labels = raw37657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37657 raw37657Labels permutation346 hz
    mixedMoment B raw37657step0 raw37657step0Labels = mixedMoment B raw37657step1 raw37657step1Labels := by
      have ha : raw37657step1 = (fun i j => raw37657step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37657step1 raw37657step0; decide +kernel
      have hl : raw37657step1Labels = raw37657step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37657step0 raw37657step0Labels permutation32 permutation4
    mixedMoment B raw37657step1 raw37657step1Labels = mixedMoment B raw37657step2 raw37657step2Labels := by
      have ha : raw37657step2 = -raw37657step1 := by apply Matrix.ext; change ∀ i j, raw37657step2 i j = -(raw37657step1 i j); unfold raw37657step2 raw37657step1; decide +kernel
      have hl : raw37657step2Labels = raw37657step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3274 node3274Labels := by rfl

def raw37658 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![-1, -1, 2]]
def raw37658Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 1, -1], ![-1, 0, 1], ![0, -2, 2], ![-1, -1, 2]]
def raw37658step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw37658step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37658step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37658step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37658 raw37658Labels = mixedMoment B node3265 node3265Labels := by
  calc
    mixedMoment B raw37658 raw37658Labels = mixedMoment B raw37658step0 raw37658step0Labels := by
      have hz : ∀ j, raw37658 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37658step0 = (fun i j => raw37658 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37658step0 raw37658; decide +kernel
      have hl : raw37658step0Labels = raw37658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37658 raw37658Labels permutation346 hz
    mixedMoment B raw37658step0 raw37658step0Labels = mixedMoment B raw37658step1 raw37658step1Labels := by
      have ha : raw37658step1 = (fun i j => raw37658step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37658step1 raw37658step0; decide +kernel
      have hl : raw37658step1Labels = raw37658step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37658step0 raw37658step0Labels permutation33 permutation4
    mixedMoment B raw37658step1 raw37658step1Labels = mixedMoment B raw37658step2 raw37658step2Labels := by
      have ha : raw37658step2 = -raw37658step1 := by apply Matrix.ext; change ∀ i j, raw37658step2 i j = -(raw37658step1 i j); unfold raw37658step2 raw37658step1; decide +kernel
      have hl : raw37658step2Labels = raw37658step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3265 node3265Labels := by rfl

def raw37659 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![-2, 0, 2]]
def raw37659Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 0, 2]]
def raw37659step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37659step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw37659step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37659step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw37659step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37659 raw37659Labels = mixedMoment B node1681 node1681Labels := by
  calc
    mixedMoment B raw37659 raw37659Labels = mixedMoment B raw37659step0 raw37659step0Labels := by
      have hz : ∀ j, raw37659 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37659step0 = (fun i j => raw37659 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37659step0 raw37659; decide +kernel
      have hl : raw37659step0Labels = raw37659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37659 raw37659Labels permutation346 hz
    mixedMoment B raw37659step0 raw37659step0Labels = mixedMoment B raw37659step1 raw37659step1Labels := by
      have ha : raw37659step1 = (fun i j => raw37659step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37659step1 raw37659step0; decide +kernel
      have hl : raw37659step1Labels = raw37659step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37659step0 raw37659step0Labels permutation36 permutation4
    mixedMoment B raw37659step1 raw37659step1Labels = mixedMoment B raw37659step2 raw37659step2Labels := by
      have ha : raw37659step2 = -raw37659step1 := by apply Matrix.ext; change ∀ i j, raw37659step2 i j = -(raw37659step1 i j); unfold raw37659step2 raw37659step1; decide +kernel
      have hl : raw37659step2Labels = raw37659step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1681 node1681Labels := by rfl

def raw37660 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![-2, 0, 2]]
def raw37660Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 0, 2]]
def raw37660step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw37660step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37660step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw37660step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37660 raw37660Labels = mixedMoment B node819 node819Labels := by
  calc
    mixedMoment B raw37660 raw37660Labels = mixedMoment B raw37660step0 raw37660step0Labels := by
      have hz : ∀ j, raw37660 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37660step0 = (fun i j => raw37660 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37660step0 raw37660; decide +kernel
      have hl : raw37660step0Labels = raw37660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37660 raw37660Labels permutation346 hz
    mixedMoment B raw37660step0 raw37660step0Labels = mixedMoment B raw37660step1 raw37660step1Labels := by
      have ha : raw37660step1 = (fun i j => raw37660step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37660step1 raw37660step0; decide +kernel
      have hl : raw37660step1Labels = raw37660step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37660step0 raw37660step0Labels permutation50 permutation4
    mixedMoment B raw37660step1 raw37660step1Labels = mixedMoment B raw37660step2 raw37660step2Labels := by
      have ha : raw37660step2 = -raw37660step1 := by apply Matrix.ext; change ∀ i j, raw37660step2 i j = -(raw37660step1 i j); unfold raw37660step2 raw37660step1; decide +kernel
      have hl : raw37660step2Labels = raw37660step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node819 node819Labels := by rfl

def raw37661 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![-2, 0, 2]]
def raw37661Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37661step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw37661step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37661step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37661step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37661 raw37661Labels = mixedMoment B node754 node754Labels := by
  calc
    mixedMoment B raw37661 raw37661Labels = mixedMoment B raw37661step0 raw37661step0Labels := by
      have ha : raw37661step0 = (fun i j => raw37661 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37661step0 raw37661; decide +kernel
      have hl : raw37661step0Labels = raw37661Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37661 raw37661Labels permutation170 permutation4
    mixedMoment B raw37661step0 raw37661step0Labels = mixedMoment B raw37661step1 raw37661step1Labels := by
      have ha : raw37661step1 = -raw37661step0 := by apply Matrix.ext; change ∀ i j, raw37661step1 i j = -(raw37661step0 i j); unfold raw37661step1 raw37661step0; decide +kernel
      have hl : raw37661step1Labels = raw37661step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node754 node754Labels := by rfl

def raw37662 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![0, -2, 2], ![-2, 0, 2]]
def raw37662Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![1, -2, 1], ![0, -2, 2], ![-2, 0, 2]]
def raw37662step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 0, 2]]
def raw37662step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37662step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw37662step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37662 raw37662Labels = mixedMoment B node758 node758Labels := by
  calc
    mixedMoment B raw37662 raw37662Labels = mixedMoment B raw37662step0 raw37662step0Labels := by
      have hz : ∀ j, raw37662 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37662step0 = (fun i j => raw37662 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37662step0 raw37662; decide +kernel
      have hl : raw37662step0Labels = raw37662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37662 raw37662Labels permutation346 hz
    mixedMoment B raw37662step0 raw37662step0Labels = mixedMoment B raw37662step1 raw37662step1Labels := by
      have ha : raw37662step1 = (fun i j => raw37662step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37662step1 raw37662step0; decide +kernel
      have hl : raw37662step1Labels = raw37662step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37662step0 raw37662step0Labels permutation36 permutation4
    mixedMoment B raw37662step1 raw37662step1Labels = mixedMoment B raw37662step2 raw37662step2Labels := by
      have ha : raw37662step2 = -raw37662step1 := by apply Matrix.ext; change ∀ i j, raw37662step2 i j = -(raw37662step1 i j); unfold raw37662step2 raw37662step1; decide +kernel
      have hl : raw37662step2Labels = raw37662step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node758 node758Labels := by rfl

def raw37663 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -3, 2], ![-2, 0, 2]]
def raw37663Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![0, -1, 1], ![1, -3, 2], ![-2, 0, 2]]
def raw37663step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37663step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 1, 2]]
def raw37663step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37663step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -1, -2]]
def raw37663step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37663 raw37663Labels = mixedMoment B node757 node757Labels := by
  calc
    mixedMoment B raw37663 raw37663Labels = mixedMoment B raw37663step0 raw37663step0Labels := by
      have hz : ∀ j, raw37663 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37663step0 = (fun i j => raw37663 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37663step0 raw37663; decide +kernel
      have hl : raw37663step0Labels = raw37663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37663 raw37663Labels permutation346 hz
    mixedMoment B raw37663step0 raw37663step0Labels = mixedMoment B raw37663step1 raw37663step1Labels := by
      have ha : raw37663step1 = (fun i j => raw37663step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37663step1 raw37663step0; decide +kernel
      have hl : raw37663step1Labels = raw37663step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37663step0 raw37663step0Labels permutation36 permutation4
    mixedMoment B raw37663step1 raw37663step1Labels = mixedMoment B raw37663step2 raw37663step2Labels := by
      have ha : raw37663step2 = -raw37663step1 := by apply Matrix.ext; change ∀ i j, raw37663step2 i j = -(raw37663step1 i j); unfold raw37663step2 raw37663step1; decide +kernel
      have hl : raw37663step2Labels = raw37663step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node757 node757Labels := by rfl

def raw37664 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![-1, -1, 2]]
def raw37664Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, -1, 2]]
def raw37664step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw37664step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37664step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37664step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37664 raw37664Labels = mixedMoment B node768 node768Labels := by
  calc
    mixedMoment B raw37664 raw37664Labels = mixedMoment B raw37664step0 raw37664step0Labels := by
      have hz : ∀ j, raw37664 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37664step0 = (fun i j => raw37664 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37664step0 raw37664; decide +kernel
      have hl : raw37664step0Labels = raw37664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37664 raw37664Labels permutation346 hz
    mixedMoment B raw37664step0 raw37664step0Labels = mixedMoment B raw37664step1 raw37664step1Labels := by
      have ha : raw37664step1 = (fun i j => raw37664step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37664step1 raw37664step0; decide +kernel
      have hl : raw37664step1Labels = raw37664step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37664step0 raw37664step0Labels permutation33 permutation4
    mixedMoment B raw37664step1 raw37664step1Labels = mixedMoment B raw37664step2 raw37664step2Labels := by
      have ha : raw37664step2 = -raw37664step1 := by apply Matrix.ext; change ∀ i j, raw37664step2 i j = -(raw37664step1 i j); unfold raw37664step2 raw37664step1; decide +kernel
      have hl : raw37664step2Labels = raw37664step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node768 node768Labels := by rfl

def raw37665 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37665Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37665step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37665step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, -2, 2], ![-3, 0, 3]]
def raw37665step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37665step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw37665step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37665 raw37665Labels = mixedMoment B node2169 node2169Labels := by
  calc
    mixedMoment B raw37665 raw37665Labels = mixedMoment B raw37665step0 raw37665step0Labels := by
      have hz : ∀ j, raw37665 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37665step0 = (fun i j => raw37665 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37665step0 raw37665; decide +kernel
      have hl : raw37665step0Labels = raw37665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37665 raw37665Labels permutation434 hz
    mixedMoment B raw37665step0 raw37665step0Labels = mixedMoment B raw37665step1 raw37665step1Labels := by
      have hz : ∀ j, raw37665step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37665step1 = (fun i j => raw37665step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37665step1 raw37665step0; decide +kernel
      have hl : raw37665step1Labels = raw37665step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37665step0 raw37665step0Labels permutation80 hz
    mixedMoment B raw37665step1 raw37665step1Labels = mixedMoment B raw37665step2 raw37665step2Labels := by
      have ha : raw37665step2 = (fun i j => raw37665step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37665step2 raw37665step1; decide +kernel
      have hl : raw37665step2Labels = raw37665step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37665step1 raw37665step1Labels permutation30 permutation2
    _ = mixedMoment B node2169 node2169Labels := by rfl

def raw37666 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37666Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37666step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37666step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![0, -2, 2], ![-3, 0, 3]]
def raw37666step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37666step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![3, -1, -2]]
def raw37666step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37666 raw37666Labels = mixedMoment B node2163 node2163Labels := by
  calc
    mixedMoment B raw37666 raw37666Labels = mixedMoment B raw37666step0 raw37666step0Labels := by
      have hz : ∀ j, raw37666 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37666step0 = (fun i j => raw37666 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37666step0 raw37666; decide +kernel
      have hl : raw37666step0Labels = raw37666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37666 raw37666Labels permutation434 hz
    mixedMoment B raw37666step0 raw37666step0Labels = mixedMoment B raw37666step1 raw37666step1Labels := by
      have hz : ∀ j, raw37666step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37666step1 = (fun i j => raw37666step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37666step1 raw37666step0; decide +kernel
      have hl : raw37666step1Labels = raw37666step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37666step0 raw37666step0Labels permutation80 hz
    mixedMoment B raw37666step1 raw37666step1Labels = mixedMoment B raw37666step2 raw37666step2Labels := by
      have ha : raw37666step2 = (fun i j => raw37666step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37666step2 raw37666step1; decide +kernel
      have hl : raw37666step2Labels = raw37666step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37666step1 raw37666step1Labels permutation30 permutation2
    _ = mixedMoment B node2163 node2163Labels := by rfl

def raw37667 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37667Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37667step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw37667step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37667 raw37667Labels = mixedMoment B node2161 node2161Labels := by
  calc
    mixedMoment B raw37667 raw37667Labels = mixedMoment B raw37667step0 raw37667step0Labels := by
      have hz : ∀ j, raw37667 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37667step0 = (fun i j => raw37667 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37667step0 raw37667; decide +kernel
      have hl : raw37667step0Labels = raw37667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37667 raw37667Labels permutation434 hz
    mixedMoment B raw37667step0 raw37667step0Labels = mixedMoment B raw37667step1 raw37667step1Labels := by
      have ha : raw37667step1 = (fun i j => raw37667step0 (permutation147 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37667step1 raw37667step0; decide +kernel
      have hl : raw37667step1Labels = raw37667step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37667step0 raw37667step0Labels permutation147 permutation2
    _ = mixedMoment B node2161 node2161Labels := by rfl

def raw37668 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37668Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37668step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw37668step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37668 raw37668Labels = mixedMoment B node2161 node2161Labels := by
  calc
    mixedMoment B raw37668 raw37668Labels = mixedMoment B raw37668step0 raw37668step0Labels := by
      have hz : ∀ j, raw37668 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37668step0 = (fun i j => raw37668 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37668step0 raw37668; decide +kernel
      have hl : raw37668step0Labels = raw37668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37668 raw37668Labels permutation346 hz
    mixedMoment B raw37668step0 raw37668step0Labels = mixedMoment B raw37668step1 raw37668step1Labels := by
      have ha : raw37668step1 = (fun i j => raw37668step0 (permutation147 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37668step1 raw37668step0; decide +kernel
      have hl : raw37668step1Labels = raw37668step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37668step0 raw37668step0Labels permutation147 permutation2
    _ = mixedMoment B node2161 node2161Labels := by rfl

def raw37669 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 0, 3]]
def raw37669Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![1, -3, 2], ![-3, 0, 3]]
def raw37669step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37669step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -3, 2], ![-3, 0, 3]]
def raw37669step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37669step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -3, 3], ![-3, 1, 2]]
def raw37669step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37669step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![3, -1, -2]]
def raw37669step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37669 raw37669Labels = mixedMoment B node2163 node2163Labels := by
  calc
    mixedMoment B raw37669 raw37669Labels = mixedMoment B raw37669step0 raw37669step0Labels := by
      have hz : ∀ j, raw37669 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37669step0 = (fun i j => raw37669 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37669step0 raw37669; decide +kernel
      have hl : raw37669step0Labels = raw37669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37669 raw37669Labels permutation434 hz
    mixedMoment B raw37669step0 raw37669step0Labels = mixedMoment B raw37669step1 raw37669step1Labels := by
      have hz : ∀ j, raw37669step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37669step1 = (fun i j => raw37669step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37669step1 raw37669step0; decide +kernel
      have hl : raw37669step1Labels = raw37669step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37669step0 raw37669step0Labels permutation80 hz
    mixedMoment B raw37669step1 raw37669step1Labels = mixedMoment B raw37669step2 raw37669step2Labels := by
      have ha : raw37669step2 = (fun i j => raw37669step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37669step2 raw37669step1; decide +kernel
      have hl : raw37669step2Labels = raw37669step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37669step1 raw37669step1Labels permutation9 permutation4
    mixedMoment B raw37669step2 raw37669step2Labels = mixedMoment B raw37669step3 raw37669step3Labels := by
      have ha : raw37669step3 = -raw37669step2 := by apply Matrix.ext; change ∀ i j, raw37669step3 i j = -(raw37669step2 i j); unfold raw37669step3 raw37669step2; decide +kernel
      have hl : raw37669step3Labels = raw37669step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2163 node2163Labels := by rfl

def raw37670 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37670Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37670step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37670step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, -2, 2], ![-2, -1, 3]]
def raw37670step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37670step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, -2, 3], ![-2, 0, 2]]
def raw37670step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37670step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw37670step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37670 raw37670Labels = mixedMoment B node2169 node2169Labels := by
  calc
    mixedMoment B raw37670 raw37670Labels = mixedMoment B raw37670step0 raw37670step0Labels := by
      have hz : ∀ j, raw37670 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37670step0 = (fun i j => raw37670 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37670step0 raw37670; decide +kernel
      have hl : raw37670step0Labels = raw37670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37670 raw37670Labels permutation434 hz
    mixedMoment B raw37670step0 raw37670step0Labels = mixedMoment B raw37670step1 raw37670step1Labels := by
      have hz : ∀ j, raw37670step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37670step1 = (fun i j => raw37670step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37670step1 raw37670step0; decide +kernel
      have hl : raw37670step1Labels = raw37670step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37670step0 raw37670step0Labels permutation80 hz
    mixedMoment B raw37670step1 raw37670step1Labels = mixedMoment B raw37670step2 raw37670step2Labels := by
      have ha : raw37670step2 = (fun i j => raw37670step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37670step2 raw37670step1; decide +kernel
      have hl : raw37670step2Labels = raw37670step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37670step1 raw37670step1Labels permutation9 permutation4
    mixedMoment B raw37670step2 raw37670step2Labels = mixedMoment B raw37670step3 raw37670step3Labels := by
      have ha : raw37670step3 = -raw37670step2 := by apply Matrix.ext; change ∀ i j, raw37670step3 i j = -(raw37670step2 i j); unfold raw37670step3 raw37670step2; decide +kernel
      have hl : raw37670step3Labels = raw37670step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2169 node2169Labels := by rfl

def raw37671 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![2, -2], ![0, 0], ![0, 0], ![-2, 2], ![-3, 3]]
def raw37671Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37671step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![2, -2], ![0, 0], ![-2, 2], ![-3, 3]]
def raw37671step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37671step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![2, -2], ![-2, 2], ![-3, 3]]
def raw37671step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37671step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![3, -3]]
def raw37671step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37671 raw37671Labels = mixedMoment B node4076 node4076Labels := by
  calc
    mixedMoment B raw37671 raw37671Labels = mixedMoment B raw37671step0 raw37671step0Labels := by
      have hz : ∀ j, raw37671 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37671step0 = (fun i j => raw37671 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37671step0 raw37671; decide +kernel
      have hl : raw37671step0Labels = raw37671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37671 raw37671Labels permutation434 hz
    mixedMoment B raw37671step0 raw37671step0Labels = mixedMoment B raw37671step1 raw37671step1Labels := by
      have hz : ∀ j, raw37671step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37671step1 = (fun i j => raw37671step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37671step1 raw37671step0; decide +kernel
      have hl : raw37671step1Labels = raw37671step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37671step0 raw37671step0Labels permutation80 hz
    mixedMoment B raw37671step1 raw37671step1Labels = mixedMoment B raw37671step2 raw37671step2Labels := by
      have ha : raw37671step2 = (fun i j => raw37671step1 (permutation31 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37671step2 raw37671step1; decide +kernel
      have hl : raw37671step2Labels = raw37671step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37671step1 raw37671step1Labels permutation31 permutation0
    _ = mixedMoment B node4076 node4076Labels := by rfl

def raw37672 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37672Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37672step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37672step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![-2, 0, 2], ![-1, -2, 3]]
def raw37672step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37672step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![2, 1, -3]]
def raw37672step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37672 raw37672Labels = mixedMoment B node3596 node3596Labels := by
  calc
    mixedMoment B raw37672 raw37672Labels = mixedMoment B raw37672step0 raw37672step0Labels := by
      have hz : ∀ j, raw37672 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37672step0 = (fun i j => raw37672 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37672step0 raw37672; decide +kernel
      have hl : raw37672step0Labels = raw37672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37672 raw37672Labels permutation434 hz
    mixedMoment B raw37672step0 raw37672step0Labels = mixedMoment B raw37672step1 raw37672step1Labels := by
      have hz : ∀ j, raw37672step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37672step1 = (fun i j => raw37672step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37672step1 raw37672step0; decide +kernel
      have hl : raw37672step1Labels = raw37672step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37672step0 raw37672step0Labels permutation80 hz
    mixedMoment B raw37672step1 raw37672step1Labels = mixedMoment B raw37672step2 raw37672step2Labels := by
      have ha : raw37672step2 = (fun i j => raw37672step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37672step2 raw37672step1; decide +kernel
      have hl : raw37672step2Labels = raw37672step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37672step1 raw37672step1Labels permutation31 permutation4
    _ = mixedMoment B node3596 node3596Labels := by rfl

def raw37673 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37673Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37673step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37673step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![-2, 0, 2], ![-1, -2, 3]]
def raw37673step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37673step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 3, -2], ![-2, -1, 3]]
def raw37673step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37673step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw37673step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37673 raw37673Labels = mixedMoment B node2273 node2273Labels := by
  calc
    mixedMoment B raw37673 raw37673Labels = mixedMoment B raw37673step0 raw37673step0Labels := by
      have hz : ∀ j, raw37673 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37673step0 = (fun i j => raw37673 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37673step0 raw37673; decide +kernel
      have hl : raw37673step0Labels = raw37673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37673 raw37673Labels permutation434 hz
    mixedMoment B raw37673step0 raw37673step0Labels = mixedMoment B raw37673step1 raw37673step1Labels := by
      have hz : ∀ j, raw37673step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37673step1 = (fun i j => raw37673step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37673step1 raw37673step0; decide +kernel
      have hl : raw37673step1Labels = raw37673step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37673step0 raw37673step0Labels permutation80 hz
    mixedMoment B raw37673step1 raw37673step1Labels = mixedMoment B raw37673step2 raw37673step2Labels := by
      have ha : raw37673step2 = (fun i j => raw37673step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37673step2 raw37673step1; decide +kernel
      have hl : raw37673step2Labels = raw37673step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37673step1 raw37673step1Labels permutation10 permutation4
    mixedMoment B raw37673step2 raw37673step2Labels = mixedMoment B raw37673step3 raw37673step3Labels := by
      have ha : raw37673step3 = -raw37673step2 := by apply Matrix.ext; change ∀ i j, raw37673step3 i j = -(raw37673step2 i j); unfold raw37673step3 raw37673step2; decide +kernel
      have hl : raw37673step3Labels = raw37673step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2273 node2273Labels := by rfl

def raw37674 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37674Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37674step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw37674step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37674step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw37674step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37674 raw37674Labels = mixedMoment B node2155 node2155Labels := by
  calc
    mixedMoment B raw37674 raw37674Labels = mixedMoment B raw37674step0 raw37674step0Labels := by
      have hz : ∀ j, raw37674 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37674step0 = (fun i j => raw37674 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37674step0 raw37674; decide +kernel
      have hl : raw37674step0Labels = raw37674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37674 raw37674Labels permutation434 hz
    mixedMoment B raw37674step0 raw37674step0Labels = mixedMoment B raw37674step1 raw37674step1Labels := by
      have ha : raw37674step1 = (fun i j => raw37674step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37674step1 raw37674step0; decide +kernel
      have hl : raw37674step1Labels = raw37674step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37674step0 raw37674step0Labels permutation34 permutation4
    mixedMoment B raw37674step1 raw37674step1Labels = mixedMoment B raw37674step2 raw37674step2Labels := by
      have ha : raw37674step2 = -raw37674step1 := by apply Matrix.ext; change ∀ i j, raw37674step2 i j = -(raw37674step1 i j); unfold raw37674step2 raw37674step1; decide +kernel
      have hl : raw37674step2Labels = raw37674step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2155 node2155Labels := by rfl

def raw37675 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37675Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37675step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw37675step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37675step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw37675step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37675 raw37675Labels = mixedMoment B node2155 node2155Labels := by
  calc
    mixedMoment B raw37675 raw37675Labels = mixedMoment B raw37675step0 raw37675step0Labels := by
      have hz : ∀ j, raw37675 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37675step0 = (fun i j => raw37675 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37675step0 raw37675; decide +kernel
      have hl : raw37675step0Labels = raw37675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37675 raw37675Labels permutation346 hz
    mixedMoment B raw37675step0 raw37675step0Labels = mixedMoment B raw37675step1 raw37675step1Labels := by
      have ha : raw37675step1 = (fun i j => raw37675step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37675step1 raw37675step0; decide +kernel
      have hl : raw37675step1Labels = raw37675step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37675step0 raw37675step0Labels permutation34 permutation4
    mixedMoment B raw37675step1 raw37675step1Labels = mixedMoment B raw37675step2 raw37675step2Labels := by
      have ha : raw37675step2 = -raw37675step1 := by apply Matrix.ext; change ∀ i j, raw37675step2 i j = -(raw37675step1 i j); unfold raw37675step2 raw37675step1; decide +kernel
      have hl : raw37675step2Labels = raw37675step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2155 node2155Labels := by rfl

def raw37676 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37676Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37676step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37676step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![-1, -1, 2], ![-1, -2, 3]]
def raw37676step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37676step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, -1, 2], ![-2, -1, 3]]
def raw37676step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37676step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]
def raw37676step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37676 raw37676Labels = mixedMoment B node2168 node2168Labels := by
  calc
    mixedMoment B raw37676 raw37676Labels = mixedMoment B raw37676step0 raw37676step0Labels := by
      have hz : ∀ j, raw37676 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37676step0 = (fun i j => raw37676 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37676step0 raw37676; decide +kernel
      have hl : raw37676step0Labels = raw37676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37676 raw37676Labels permutation434 hz
    mixedMoment B raw37676step0 raw37676step0Labels = mixedMoment B raw37676step1 raw37676step1Labels := by
      have hz : ∀ j, raw37676step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37676step1 = (fun i j => raw37676step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37676step1 raw37676step0; decide +kernel
      have hl : raw37676step1Labels = raw37676step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37676step0 raw37676step0Labels permutation80 hz
    mixedMoment B raw37676step1 raw37676step1Labels = mixedMoment B raw37676step2 raw37676step2Labels := by
      have ha : raw37676step2 = (fun i j => raw37676step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37676step2 raw37676step1; decide +kernel
      have hl : raw37676step2Labels = raw37676step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37676step1 raw37676step1Labels permutation8 permutation4
    mixedMoment B raw37676step2 raw37676step2Labels = mixedMoment B raw37676step3 raw37676step3Labels := by
      have ha : raw37676step3 = -raw37676step2 := by apply Matrix.ext; change ∀ i j, raw37676step3 i j = -(raw37676step2 i j); unfold raw37676step3 raw37676step2; decide +kernel
      have hl : raw37676step3Labels = raw37676step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2168 node2168Labels := by rfl

def raw37677 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37677Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37677step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37677step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![-2, 0, 2], ![0, -3, 3]]
def raw37677step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37677step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![3, 0, -3]]
def raw37677step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37677 raw37677Labels = mixedMoment B node2159 node2159Labels := by
  calc
    mixedMoment B raw37677 raw37677Labels = mixedMoment B raw37677step0 raw37677step0Labels := by
      have hz : ∀ j, raw37677 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37677step0 = (fun i j => raw37677 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37677step0 raw37677; decide +kernel
      have hl : raw37677step0Labels = raw37677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37677 raw37677Labels permutation434 hz
    mixedMoment B raw37677step0 raw37677step0Labels = mixedMoment B raw37677step1 raw37677step1Labels := by
      have hz : ∀ j, raw37677step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37677step1 = (fun i j => raw37677step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37677step1 raw37677step0; decide +kernel
      have hl : raw37677step1Labels = raw37677step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37677step0 raw37677step0Labels permutation80 hz
    mixedMoment B raw37677step1 raw37677step1Labels = mixedMoment B raw37677step2 raw37677step2Labels := by
      have ha : raw37677step2 = (fun i j => raw37677step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37677step2 raw37677step1; decide +kernel
      have hl : raw37677step2Labels = raw37677step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37677step1 raw37677step1Labels permutation31 permutation4
    _ = mixedMoment B node2159 node2159Labels := by rfl

def raw37678 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37678Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37678step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37678step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![-1, -1, 2], ![-2, -1, 3]]
def raw37678step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37678step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]
def raw37678step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37678 raw37678Labels = mixedMoment B node3423 node3423Labels := by
  calc
    mixedMoment B raw37678 raw37678Labels = mixedMoment B raw37678step0 raw37678step0Labels := by
      have hz : ∀ j, raw37678 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37678step0 = (fun i j => raw37678 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37678step0 raw37678; decide +kernel
      have hl : raw37678step0Labels = raw37678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37678 raw37678Labels permutation434 hz
    mixedMoment B raw37678step0 raw37678step0Labels = mixedMoment B raw37678step1 raw37678step1Labels := by
      have hz : ∀ j, raw37678step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37678step1 = (fun i j => raw37678step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37678step1 raw37678step0; decide +kernel
      have hl : raw37678step1Labels = raw37678step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37678step0 raw37678step0Labels permutation80 hz
    mixedMoment B raw37678step1 raw37678step1Labels = mixedMoment B raw37678step2 raw37678step2Labels := by
      have ha : raw37678step2 = (fun i j => raw37678step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37678step2 raw37678step1; decide +kernel
      have hl : raw37678step2Labels = raw37678step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37678step1 raw37678step1Labels permutation30 permutation2
    _ = mixedMoment B node3423 node3423Labels := by rfl

def raw37679 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37679Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37679step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37679step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![-1, -1, 2], ![-2, -1, 3]]
def raw37679step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37679step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 3, -2], ![-1, -1, 2], ![-1, -2, 3]]
def raw37679step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37679step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]
def raw37679step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37679 raw37679Labels = mixedMoment B node2286 node2286Labels := by
  calc
    mixedMoment B raw37679 raw37679Labels = mixedMoment B raw37679step0 raw37679step0Labels := by
      have hz : ∀ j, raw37679 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37679step0 = (fun i j => raw37679 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37679step0 raw37679; decide +kernel
      have hl : raw37679step0Labels = raw37679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37679 raw37679Labels permutation434 hz
    mixedMoment B raw37679step0 raw37679step0Labels = mixedMoment B raw37679step1 raw37679step1Labels := by
      have hz : ∀ j, raw37679step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37679step1 = (fun i j => raw37679step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37679step1 raw37679step0; decide +kernel
      have hl : raw37679step1Labels = raw37679step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37679step0 raw37679step0Labels permutation80 hz
    mixedMoment B raw37679step1 raw37679step1Labels = mixedMoment B raw37679step2 raw37679step2Labels := by
      have ha : raw37679step2 = (fun i j => raw37679step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37679step2 raw37679step1; decide +kernel
      have hl : raw37679step2Labels = raw37679step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37679step1 raw37679step1Labels permutation8 permutation4
    mixedMoment B raw37679step2 raw37679step2Labels = mixedMoment B raw37679step3 raw37679step3Labels := by
      have ha : raw37679step3 = -raw37679step2 := by apply Matrix.ext; change ∀ i j, raw37679step3 i j = -(raw37679step2 i j); unfold raw37679step3 raw37679step2; decide +kernel
      have hl : raw37679step3Labels = raw37679step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2286 node2286Labels := by rfl

def raw37680 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37680Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37680step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37680step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37680step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw37680step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37680 raw37680Labels = mixedMoment B node2164 node2164Labels := by
  calc
    mixedMoment B raw37680 raw37680Labels = mixedMoment B raw37680step0 raw37680step0Labels := by
      have hz : ∀ j, raw37680 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37680step0 = (fun i j => raw37680 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37680step0 raw37680; decide +kernel
      have hl : raw37680step0Labels = raw37680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37680 raw37680Labels permutation434 hz
    mixedMoment B raw37680step0 raw37680step0Labels = mixedMoment B raw37680step1 raw37680step1Labels := by
      have ha : raw37680step1 = (fun i j => raw37680step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37680step1 raw37680step0; decide +kernel
      have hl : raw37680step1Labels = raw37680step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37680step0 raw37680step0Labels permutation32 permutation4
    mixedMoment B raw37680step1 raw37680step1Labels = mixedMoment B raw37680step2 raw37680step2Labels := by
      have ha : raw37680step2 = -raw37680step1 := by apply Matrix.ext; change ∀ i j, raw37680step2 i j = -(raw37680step1 i j); unfold raw37680step2 raw37680step1; decide +kernel
      have hl : raw37680step2Labels = raw37680step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2164 node2164Labels := by rfl

def raw37681 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37681Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37681step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37681step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37681step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw37681step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37681 raw37681Labels = mixedMoment B node2164 node2164Labels := by
  calc
    mixedMoment B raw37681 raw37681Labels = mixedMoment B raw37681step0 raw37681step0Labels := by
      have hz : ∀ j, raw37681 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37681step0 = (fun i j => raw37681 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37681step0 raw37681; decide +kernel
      have hl : raw37681step0Labels = raw37681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37681 raw37681Labels permutation346 hz
    mixedMoment B raw37681step0 raw37681step0Labels = mixedMoment B raw37681step1 raw37681step1Labels := by
      have ha : raw37681step1 = (fun i j => raw37681step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37681step1 raw37681step0; decide +kernel
      have hl : raw37681step1Labels = raw37681step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37681step0 raw37681step0Labels permutation32 permutation4
    mixedMoment B raw37681step1 raw37681step1Labels = mixedMoment B raw37681step2 raw37681step2Labels := by
      have ha : raw37681step2 = -raw37681step1 := by apply Matrix.ext; change ∀ i j, raw37681step2 i j = -(raw37681step1 i j); unfold raw37681step2 raw37681step1; decide +kernel
      have hl : raw37681step2Labels = raw37681step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2164 node2164Labels := by rfl

def raw37682 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37682Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37682step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37682step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-2, 0, 2], ![-1, -2, 3]]
def raw37682step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37682step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, -2, 3], ![-2, 0, 2]]
def raw37682step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37682step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]
def raw37682step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37682 raw37682Labels = mixedMoment B node3423 node3423Labels := by
  calc
    mixedMoment B raw37682 raw37682Labels = mixedMoment B raw37682step0 raw37682step0Labels := by
      have hz : ∀ j, raw37682 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37682step0 = (fun i j => raw37682 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37682step0 raw37682; decide +kernel
      have hl : raw37682step0Labels = raw37682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37682 raw37682Labels permutation434 hz
    mixedMoment B raw37682step0 raw37682step0Labels = mixedMoment B raw37682step1 raw37682step1Labels := by
      have hz : ∀ j, raw37682step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37682step1 = (fun i j => raw37682step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37682step1 raw37682step0; decide +kernel
      have hl : raw37682step1Labels = raw37682step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37682step0 raw37682step0Labels permutation80 hz
    mixedMoment B raw37682step1 raw37682step1Labels = mixedMoment B raw37682step2 raw37682step2Labels := by
      have ha : raw37682step2 = (fun i j => raw37682step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37682step2 raw37682step1; decide +kernel
      have hl : raw37682step2Labels = raw37682step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37682step1 raw37682step1Labels permutation9 permutation2
    mixedMoment B raw37682step2 raw37682step2Labels = mixedMoment B raw37682step3 raw37682step3Labels := by
      have ha : raw37682step3 = -raw37682step2 := by apply Matrix.ext; change ∀ i j, raw37682step3 i j = -(raw37682step2 i j); unfold raw37682step3 raw37682step2; decide +kernel
      have hl : raw37682step3Labels = raw37682step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3423 node3423Labels := by rfl

def raw37683 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37683Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37683step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw37683step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37683step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw37683step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37683 raw37683Labels = mixedMoment B node3415 node3415Labels := by
  calc
    mixedMoment B raw37683 raw37683Labels = mixedMoment B raw37683step0 raw37683step0Labels := by
      have hz : ∀ j, raw37683 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37683step0 = (fun i j => raw37683 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37683step0 raw37683; decide +kernel
      have hl : raw37683step0Labels = raw37683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37683 raw37683Labels permutation434 hz
    mixedMoment B raw37683step0 raw37683step0Labels = mixedMoment B raw37683step1 raw37683step1Labels := by
      have ha : raw37683step1 = (fun i j => raw37683step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37683step1 raw37683step0; decide +kernel
      have hl : raw37683step1Labels = raw37683step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37683step0 raw37683step0Labels permutation34 permutation4
    mixedMoment B raw37683step1 raw37683step1Labels = mixedMoment B raw37683step2 raw37683step2Labels := by
      have ha : raw37683step2 = -raw37683step1 := by apply Matrix.ext; change ∀ i j, raw37683step2 i j = -(raw37683step1 i j); unfold raw37683step2 raw37683step1; decide +kernel
      have hl : raw37683step2Labels = raw37683step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3415 node3415Labels := by rfl

def raw37684 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37684Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37684step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw37684step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37684step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw37684step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37684 raw37684Labels = mixedMoment B node3415 node3415Labels := by
  calc
    mixedMoment B raw37684 raw37684Labels = mixedMoment B raw37684step0 raw37684step0Labels := by
      have hz : ∀ j, raw37684 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37684step0 = (fun i j => raw37684 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37684step0 raw37684; decide +kernel
      have hl : raw37684step0Labels = raw37684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37684 raw37684Labels permutation346 hz
    mixedMoment B raw37684step0 raw37684step0Labels = mixedMoment B raw37684step1 raw37684step1Labels := by
      have ha : raw37684step1 = (fun i j => raw37684step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37684step1 raw37684step0; decide +kernel
      have hl : raw37684step1Labels = raw37684step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37684step0 raw37684step0Labels permutation34 permutation4
    mixedMoment B raw37684step1 raw37684step1Labels = mixedMoment B raw37684step2 raw37684step2Labels := by
      have ha : raw37684step2 = -raw37684step1 := by apply Matrix.ext; change ∀ i j, raw37684step2 i j = -(raw37684step1 i j); unfold raw37684step2 raw37684step1; decide +kernel
      have hl : raw37684step2Labels = raw37684step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3415 node3415Labels := by rfl

def raw37685 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37685Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37685step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37685step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![-1, -1, 2], ![-1, -2, 3]]
def raw37685step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37685step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 1, -2], ![2, 1, -3]]
def raw37685step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37685 raw37685Labels = mixedMoment B node3422 node3422Labels := by
  calc
    mixedMoment B raw37685 raw37685Labels = mixedMoment B raw37685step0 raw37685step0Labels := by
      have hz : ∀ j, raw37685 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37685step0 = (fun i j => raw37685 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37685step0 raw37685; decide +kernel
      have hl : raw37685step0Labels = raw37685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37685 raw37685Labels permutation434 hz
    mixedMoment B raw37685step0 raw37685step0Labels = mixedMoment B raw37685step1 raw37685step1Labels := by
      have hz : ∀ j, raw37685step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37685step1 = (fun i j => raw37685step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37685step1 raw37685step0; decide +kernel
      have hl : raw37685step1Labels = raw37685step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37685step0 raw37685step0Labels permutation80 hz
    mixedMoment B raw37685step1 raw37685step1Labels = mixedMoment B raw37685step2 raw37685step2Labels := by
      have ha : raw37685step2 = (fun i j => raw37685step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37685step2 raw37685step1; decide +kernel
      have hl : raw37685step2Labels = raw37685step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37685step1 raw37685step1Labels permutation31 permutation4
    _ = mixedMoment B node3422 node3422Labels := by rfl

def raw37686 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37686Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37686step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37686step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![-2, 0, 2], ![0, -3, 3]]
def raw37686step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37686step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]
def raw37686step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37686 raw37686Labels = mixedMoment B node2168 node2168Labels := by
  calc
    mixedMoment B raw37686 raw37686Labels = mixedMoment B raw37686step0 raw37686step0Labels := by
      have hz : ∀ j, raw37686 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37686step0 = (fun i j => raw37686 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37686step0 raw37686; decide +kernel
      have hl : raw37686step0Labels = raw37686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37686 raw37686Labels permutation434 hz
    mixedMoment B raw37686step0 raw37686step0Labels = mixedMoment B raw37686step1 raw37686step1Labels := by
      have hz : ∀ j, raw37686step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37686step1 = (fun i j => raw37686step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37686step1 raw37686step0; decide +kernel
      have hl : raw37686step1Labels = raw37686step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37686step0 raw37686step0Labels permutation80 hz
    mixedMoment B raw37686step1 raw37686step1Labels = mixedMoment B raw37686step2 raw37686step2Labels := by
      have ha : raw37686step2 = (fun i j => raw37686step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37686step2 raw37686step1; decide +kernel
      have hl : raw37686step2Labels = raw37686step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37686step1 raw37686step1Labels permutation31 permutation4
    _ = mixedMoment B node2168 node2168Labels := by rfl

def raw37687 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37687Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37687step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37687step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, -1, 2], ![-2, -1, 3]]
def raw37687step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37687step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 1, -2], ![2, 1, -3]]
def raw37687step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37687 raw37687Labels = mixedMoment B node3422 node3422Labels := by
  calc
    mixedMoment B raw37687 raw37687Labels = mixedMoment B raw37687step0 raw37687step0Labels := by
      have hz : ∀ j, raw37687 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37687step0 = (fun i j => raw37687 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37687step0 raw37687; decide +kernel
      have hl : raw37687step0Labels = raw37687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37687 raw37687Labels permutation434 hz
    mixedMoment B raw37687step0 raw37687step0Labels = mixedMoment B raw37687step1 raw37687step1Labels := by
      have hz : ∀ j, raw37687step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37687step1 = (fun i j => raw37687step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37687step1 raw37687step0; decide +kernel
      have hl : raw37687step1Labels = raw37687step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37687step0 raw37687step0Labels permutation80 hz
    mixedMoment B raw37687step1 raw37687step1Labels = mixedMoment B raw37687step2 raw37687step2Labels := by
      have ha : raw37687step2 = (fun i j => raw37687step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37687step2 raw37687step1; decide +kernel
      have hl : raw37687step2Labels = raw37687step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37687step1 raw37687step1Labels permutation31 permutation2
    _ = mixedMoment B node3422 node3422Labels := by rfl

def raw37688 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37688Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37688step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw37688step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37688 raw37688Labels = mixedMoment B node3419 node3419Labels := by
  calc
    mixedMoment B raw37688 raw37688Labels = mixedMoment B raw37688step0 raw37688step0Labels := by
      have hz : ∀ j, raw37688 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37688step0 = (fun i j => raw37688 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37688step0 raw37688; decide +kernel
      have hl : raw37688step0Labels = raw37688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37688 raw37688Labels permutation434 hz
    mixedMoment B raw37688step0 raw37688step0Labels = mixedMoment B raw37688step1 raw37688step1Labels := by
      have ha : raw37688step1 = (fun i j => raw37688step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37688step1 raw37688step0; decide +kernel
      have hl : raw37688step1Labels = raw37688step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37688step0 raw37688step0Labels permutation151 permutation2
    _ = mixedMoment B node3419 node3419Labels := by rfl

def raw37689 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37689Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37689step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw37689step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37689 raw37689Labels = mixedMoment B node3419 node3419Labels := by
  calc
    mixedMoment B raw37689 raw37689Labels = mixedMoment B raw37689step0 raw37689step0Labels := by
      have hz : ∀ j, raw37689 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37689step0 = (fun i j => raw37689 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37689step0 raw37689; decide +kernel
      have hl : raw37689step0Labels = raw37689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37689 raw37689Labels permutation346 hz
    mixedMoment B raw37689step0 raw37689step0Labels = mixedMoment B raw37689step1 raw37689step1Labels := by
      have ha : raw37689step1 = (fun i j => raw37689step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37689step1 raw37689step0; decide +kernel
      have hl : raw37689step1Labels = raw37689step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37689step0 raw37689step0Labels permutation151 permutation2
    _ = mixedMoment B node3419 node3419Labels := by rfl

def raw37690 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37690Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37690step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37690step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, -2, 2], ![-2, -1, 3]]
def raw37690step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37690step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, -2, 3], ![-2, 0, 2]]
def raw37690step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37690step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]
def raw37690step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37690 raw37690Labels = mixedMoment B node3423 node3423Labels := by
  calc
    mixedMoment B raw37690 raw37690Labels = mixedMoment B raw37690step0 raw37690step0Labels := by
      have hz : ∀ j, raw37690 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37690step0 = (fun i j => raw37690 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37690step0 raw37690; decide +kernel
      have hl : raw37690step0Labels = raw37690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37690 raw37690Labels permutation434 hz
    mixedMoment B raw37690step0 raw37690step0Labels = mixedMoment B raw37690step1 raw37690step1Labels := by
      have hz : ∀ j, raw37690step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37690step1 = (fun i j => raw37690step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37690step1 raw37690step0; decide +kernel
      have hl : raw37690step1Labels = raw37690step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37690step0 raw37690step0Labels permutation80 hz
    mixedMoment B raw37690step1 raw37690step1Labels = mixedMoment B raw37690step2 raw37690step2Labels := by
      have ha : raw37690step2 = (fun i j => raw37690step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37690step2 raw37690step1; decide +kernel
      have hl : raw37690step2Labels = raw37690step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37690step1 raw37690step1Labels permutation9 permutation4
    mixedMoment B raw37690step2 raw37690step2Labels = mixedMoment B raw37690step3 raw37690step3Labels := by
      have ha : raw37690step3 = -raw37690step2 := by apply Matrix.ext; change ∀ i j, raw37690step3 i j = -(raw37690step2 i j); unfold raw37690step3 raw37690step2; decide +kernel
      have hl : raw37690step3Labels = raw37690step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3423 node3423Labels := by rfl

def raw37691 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37691Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![-1, 1, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37691step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw37691step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37691 raw37691Labels = mixedMoment B node3512 node3512Labels := by
  calc
    mixedMoment B raw37691 raw37691Labels = mixedMoment B raw37691step0 raw37691step0Labels := by
      have hz : ∀ j, raw37691 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37691step0 = (fun i j => raw37691 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37691step0 raw37691; decide +kernel
      have hl : raw37691step0Labels = raw37691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37691 raw37691Labels permutation434 hz
    mixedMoment B raw37691step0 raw37691step0Labels = mixedMoment B raw37691step1 raw37691step1Labels := by
      have ha : raw37691step1 = (fun i j => raw37691step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37691step1 raw37691step0; decide +kernel
      have hl : raw37691step1Labels = raw37691step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37691step0 raw37691step0Labels permutation144 permutation2
    _ = mixedMoment B node3512 node3512Labels := by rfl

def raw37692 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37692Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![-1, 1, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37692step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw37692step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37692 raw37692Labels = mixedMoment B node3512 node3512Labels := by
  calc
    mixedMoment B raw37692 raw37692Labels = mixedMoment B raw37692step0 raw37692step0Labels := by
      have hz : ∀ j, raw37692 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37692step0 = (fun i j => raw37692 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37692step0 raw37692; decide +kernel
      have hl : raw37692step0Labels = raw37692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37692 raw37692Labels permutation346 hz
    mixedMoment B raw37692step0 raw37692step0Labels = mixedMoment B raw37692step1 raw37692step1Labels := by
      have ha : raw37692step1 = (fun i j => raw37692step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37692step1 raw37692step0; decide +kernel
      have hl : raw37692step1Labels = raw37692step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37692step0 raw37692step0Labels permutation144 permutation2
    _ = mixedMoment B node3512 node3512Labels := by rfl

def raw37693 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37693Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37693step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw37693step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37693step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw37693step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37693 raw37693Labels = mixedMoment B node3326 node3326Labels := by
  calc
    mixedMoment B raw37693 raw37693Labels = mixedMoment B raw37693step0 raw37693step0Labels := by
      have hz : ∀ j, raw37693 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37693step0 = (fun i j => raw37693 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37693step0 raw37693; decide +kernel
      have hl : raw37693step0Labels = raw37693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37693 raw37693Labels permutation434 hz
    mixedMoment B raw37693step0 raw37693step0Labels = mixedMoment B raw37693step1 raw37693step1Labels := by
      have ha : raw37693step1 = (fun i j => raw37693step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37693step1 raw37693step0; decide +kernel
      have hl : raw37693step1Labels = raw37693step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37693step0 raw37693step0Labels permutation33 permutation2
    mixedMoment B raw37693step1 raw37693step1Labels = mixedMoment B raw37693step2 raw37693step2Labels := by
      have ha : raw37693step2 = -raw37693step1 := by apply Matrix.ext; change ∀ i j, raw37693step2 i j = -(raw37693step1 i j); unfold raw37693step2 raw37693step1; decide +kernel
      have hl : raw37693step2Labels = raw37693step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3326 node3326Labels := by rfl

def raw37694 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37694Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37694step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw37694step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37694step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw37694step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37694 raw37694Labels = mixedMoment B node3326 node3326Labels := by
  calc
    mixedMoment B raw37694 raw37694Labels = mixedMoment B raw37694step0 raw37694step0Labels := by
      have hz : ∀ j, raw37694 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37694step0 = (fun i j => raw37694 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37694step0 raw37694; decide +kernel
      have hl : raw37694step0Labels = raw37694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37694 raw37694Labels permutation346 hz
    mixedMoment B raw37694step0 raw37694step0Labels = mixedMoment B raw37694step1 raw37694step1Labels := by
      have ha : raw37694step1 = (fun i j => raw37694step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37694step1 raw37694step0; decide +kernel
      have hl : raw37694step1Labels = raw37694step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37694step0 raw37694step0Labels permutation33 permutation2
    mixedMoment B raw37694step1 raw37694step1Labels = mixedMoment B raw37694step2 raw37694step2Labels := by
      have ha : raw37694step2 = -raw37694step1 := by apply Matrix.ext; change ∀ i j, raw37694step2 i j = -(raw37694step1 i j); unfold raw37694step2 raw37694step1; decide +kernel
      have hl : raw37694step2Labels = raw37694step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3326 node3326Labels := by rfl

def raw37695 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![-1, -2, 3]]
def raw37695Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, 0, 0], ![-3, 1, 2], ![-1, -2, 3]]
def raw37695step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37695step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-3, 1, 2], ![-1, -2, 3]]
def raw37695step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37695step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![2, 0, -2], ![2, 1, -3]]
def raw37695step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37695 raw37695Labels = mixedMoment B node2369 node2369Labels := by
  calc
    mixedMoment B raw37695 raw37695Labels = mixedMoment B raw37695step0 raw37695step0Labels := by
      have hz : ∀ j, raw37695 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37695step0 = (fun i j => raw37695 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37695step0 raw37695; decide +kernel
      have hl : raw37695step0Labels = raw37695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37695 raw37695Labels permutation434 hz
    mixedMoment B raw37695step0 raw37695step0Labels = mixedMoment B raw37695step1 raw37695step1Labels := by
      have hz : ∀ j, raw37695step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37695step1 = (fun i j => raw37695step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37695step1 raw37695step0; decide +kernel
      have hl : raw37695step1Labels = raw37695step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37695step0 raw37695step0Labels permutation80 hz
    mixedMoment B raw37695step1 raw37695step1Labels = mixedMoment B raw37695step2 raw37695step2Labels := by
      have ha : raw37695step2 = (fun i j => raw37695step1 (permutation25 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37695step2 raw37695step1; decide +kernel
      have hl : raw37695step2Labels = raw37695step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37695step1 raw37695step1Labels permutation25 permutation2
    _ = mixedMoment B node2369 node2369Labels := by rfl

def raw37696 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-2, -1, 3]]
def raw37696Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, 0, 0], ![-2, 0, 2], ![-2, -1, 3]]
def raw37696step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37696step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-2, 0, 2], ![-2, -1, 3]]
def raw37696step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37696step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![2, 0, -2], ![2, 1, -3]]
def raw37696step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37696 raw37696Labels = mixedMoment B node3331 node3331Labels := by
  calc
    mixedMoment B raw37696 raw37696Labels = mixedMoment B raw37696step0 raw37696step0Labels := by
      have hz : ∀ j, raw37696 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37696step0 = (fun i j => raw37696 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37696step0 raw37696; decide +kernel
      have hl : raw37696step0Labels = raw37696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37696 raw37696Labels permutation434 hz
    mixedMoment B raw37696step0 raw37696step0Labels = mixedMoment B raw37696step1 raw37696step1Labels := by
      have hz : ∀ j, raw37696step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37696step1 = (fun i j => raw37696step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37696step1 raw37696step0; decide +kernel
      have hl : raw37696step1Labels = raw37696step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37696step0 raw37696step0Labels permutation80 hz
    mixedMoment B raw37696step1 raw37696step1Labels = mixedMoment B raw37696step2 raw37696step2Labels := by
      have ha : raw37696step2 = (fun i j => raw37696step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37696step2 raw37696step1; decide +kernel
      have hl : raw37696step2Labels = raw37696step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37696step1 raw37696step1Labels permutation31 permutation2
    _ = mixedMoment B node3331 node3331Labels := by rfl

def raw37697 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37697Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37697step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw37697step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37697 raw37697Labels = mixedMoment B node3325 node3325Labels := by
  calc
    mixedMoment B raw37697 raw37697Labels = mixedMoment B raw37697step0 raw37697step0Labels := by
      have hz : ∀ j, raw37697 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37697step0 = (fun i j => raw37697 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37697step0 raw37697; decide +kernel
      have hl : raw37697step0Labels = raw37697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37697 raw37697Labels permutation434 hz
    mixedMoment B raw37697step0 raw37697step0Labels = mixedMoment B raw37697step1 raw37697step1Labels := by
      have ha : raw37697step1 = -raw37697step0 := by apply Matrix.ext; change ∀ i j, raw37697step1 i j = -(raw37697step0 i j); unfold raw37697step1 raw37697step0; decide +kernel
      have hl : raw37697step1Labels = raw37697step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3325 node3325Labels := by rfl

def raw37698 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37698Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37698step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw37698step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37698 raw37698Labels = mixedMoment B node3325 node3325Labels := by
  calc
    mixedMoment B raw37698 raw37698Labels = mixedMoment B raw37698step0 raw37698step0Labels := by
      have hz : ∀ j, raw37698 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37698step0 = (fun i j => raw37698 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37698step0 raw37698; decide +kernel
      have hl : raw37698step0Labels = raw37698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37698 raw37698Labels permutation346 hz
    mixedMoment B raw37698step0 raw37698step0Labels = mixedMoment B raw37698step1 raw37698step1Labels := by
      have ha : raw37698step1 = -raw37698step0 := by apply Matrix.ext; change ∀ i j, raw37698step1 i j = -(raw37698step0 i j); unfold raw37698step1 raw37698step0; decide +kernel
      have hl : raw37698step1Labels = raw37698step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3325 node3325Labels := by rfl

def raw37699 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-3, 0, 3]]
def raw37699Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, 0, 0], ![-1, -1, 2], ![-3, 0, 3]]
def raw37699step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, -1, 2], ![-3, 0, 3]]
def raw37699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37699step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![2, 0, -2], ![2, 1, -3]]
def raw37699step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37699 raw37699Labels = mixedMoment B node1859 node1859Labels := by
  calc
    mixedMoment B raw37699 raw37699Labels = mixedMoment B raw37699step0 raw37699step0Labels := by
      have hz : ∀ j, raw37699 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37699step0 = (fun i j => raw37699 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37699step0 raw37699; decide +kernel
      have hl : raw37699step0Labels = raw37699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37699 raw37699Labels permutation434 hz
    mixedMoment B raw37699step0 raw37699step0Labels = mixedMoment B raw37699step1 raw37699step1Labels := by
      have hz : ∀ j, raw37699step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37699step1 = (fun i j => raw37699step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37699step1 raw37699step0; decide +kernel
      have hl : raw37699step1Labels = raw37699step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37699step0 raw37699step0Labels permutation80 hz
    mixedMoment B raw37699step1 raw37699step1Labels = mixedMoment B raw37699step2 raw37699step2Labels := by
      have ha : raw37699step2 = (fun i j => raw37699step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37699step2 raw37699step1; decide +kernel
      have hl : raw37699step2Labels = raw37699step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37699step1 raw37699step1Labels permutation31 permutation2
    _ = mixedMoment B node1859 node1859Labels := by rfl

def raw37700 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![3, -1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-3, 0, 3]]
def raw37700Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -1, -2], ![0, 0, 0], ![-1, -1, 2], ![-3, 0, 3]]
def raw37700step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37700step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![3, -1, -2], ![-1, -1, 2], ![-3, 0, 3]]
def raw37700step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37700step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 2, -3], ![3, -1, -2]]
def raw37700step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37700 raw37700Labels = mixedMoment B node1857 node1857Labels := by
  calc
    mixedMoment B raw37700 raw37700Labels = mixedMoment B raw37700step0 raw37700step0Labels := by
      have hz : ∀ j, raw37700 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37700step0 = (fun i j => raw37700 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37700step0 raw37700; decide +kernel
      have hl : raw37700step0Labels = raw37700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37700 raw37700Labels permutation434 hz
    mixedMoment B raw37700step0 raw37700step0Labels = mixedMoment B raw37700step1 raw37700step1Labels := by
      have hz : ∀ j, raw37700step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37700step1 = (fun i j => raw37700step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37700step1 raw37700step0; decide +kernel
      have hl : raw37700step1Labels = raw37700step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37700step0 raw37700step0Labels permutation80 hz
    mixedMoment B raw37700step1 raw37700step1Labels = mixedMoment B raw37700step2 raw37700step2Labels := by
      have ha : raw37700step2 = (fun i j => raw37700step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37700step2 raw37700step1; decide +kernel
      have hl : raw37700step2Labels = raw37700step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37700step1 raw37700step1Labels permutation30 permutation2
    _ = mixedMoment B node1857 node1857Labels := by rfl

def raw37701 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-3, 0, 3]]
def raw37701Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-3, 0, 3]]
def raw37701step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw37701step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37701 raw37701Labels = mixedMoment B node1851 node1851Labels := by
  calc
    mixedMoment B raw37701 raw37701Labels = mixedMoment B raw37701step0 raw37701step0Labels := by
      have hz : ∀ j, raw37701 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37701step0 = (fun i j => raw37701 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37701step0 raw37701; decide +kernel
      have hl : raw37701step0Labels = raw37701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37701 raw37701Labels permutation434 hz
    mixedMoment B raw37701step0 raw37701step0Labels = mixedMoment B raw37701step1 raw37701step1Labels := by
      have ha : raw37701step1 = (fun i j => raw37701step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37701step1 raw37701step0; decide +kernel
      have hl : raw37701step1Labels = raw37701step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37701step0 raw37701step0Labels permutation150 permutation2
    _ = mixedMoment B node1851 node1851Labels := by rfl

def raw37702 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-3, 0, 3]]
def raw37702Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-3, 0, 3]]
def raw37702step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37702step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw37702step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37702 raw37702Labels = mixedMoment B node1851 node1851Labels := by
  calc
    mixedMoment B raw37702 raw37702Labels = mixedMoment B raw37702step0 raw37702step0Labels := by
      have hz : ∀ j, raw37702 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37702step0 = (fun i j => raw37702 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37702step0 raw37702; decide +kernel
      have hl : raw37702step0Labels = raw37702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37702 raw37702Labels permutation346 hz
    mixedMoment B raw37702step0 raw37702step0Labels = mixedMoment B raw37702step1 raw37702step1Labels := by
      have ha : raw37702step1 = (fun i j => raw37702step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37702step1 raw37702step0; decide +kernel
      have hl : raw37702step1Labels = raw37702step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37702step0 raw37702step0Labels permutation150 permutation2
    _ = mixedMoment B node1851 node1851Labels := by rfl

def raw37703 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37703Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37703step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37703step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-3, 0, 3]]
def raw37703step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37703step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]
def raw37703step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37703 raw37703Labels = mixedMoment B node2168 node2168Labels := by
  calc
    mixedMoment B raw37703 raw37703Labels = mixedMoment B raw37703step0 raw37703step0Labels := by
      have hz : ∀ j, raw37703 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37703step0 = (fun i j => raw37703 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37703step0 raw37703; decide +kernel
      have hl : raw37703step0Labels = raw37703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37703 raw37703Labels permutation434 hz
    mixedMoment B raw37703step0 raw37703step0Labels = mixedMoment B raw37703step1 raw37703step1Labels := by
      have hz : ∀ j, raw37703step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37703step1 = (fun i j => raw37703step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37703step1 raw37703step0; decide +kernel
      have hl : raw37703step1Labels = raw37703step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37703step0 raw37703step0Labels permutation80 hz
    mixedMoment B raw37703step1 raw37703step1Labels = mixedMoment B raw37703step2 raw37703step2Labels := by
      have ha : raw37703step2 = (fun i j => raw37703step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37703step2 raw37703step1; decide +kernel
      have hl : raw37703step2Labels = raw37703step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37703step1 raw37703step1Labels permutation31 permutation2
    _ = mixedMoment B node2168 node2168Labels := by rfl

def raw37704 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37704Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 1, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37704step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 1, -3]]
def raw37704step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37704 raw37704Labels = mixedMoment B node1984 node1984Labels := by
  calc
    mixedMoment B raw37704 raw37704Labels = mixedMoment B raw37704step0 raw37704step0Labels := by
      have hz : ∀ j, raw37704 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37704step0 = (fun i j => raw37704 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37704step0 raw37704; decide +kernel
      have hl : raw37704step0Labels = raw37704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37704 raw37704Labels permutation434 hz
    mixedMoment B raw37704step0 raw37704step0Labels = mixedMoment B raw37704step1 raw37704step1Labels := by
      have ha : raw37704step1 = (fun i j => raw37704step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37704step1 raw37704step0; decide +kernel
      have hl : raw37704step1Labels = raw37704step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37704step0 raw37704step0Labels permutation145 permutation2
    _ = mixedMoment B node1984 node1984Labels := by rfl

def raw37705 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37705Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 1, 0], ![0, -2, 2], ![-3, 0, 3]]
def raw37705step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37705step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 1, -3]]
def raw37705step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37705 raw37705Labels = mixedMoment B node1984 node1984Labels := by
  calc
    mixedMoment B raw37705 raw37705Labels = mixedMoment B raw37705step0 raw37705step0Labels := by
      have hz : ∀ j, raw37705 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37705step0 = (fun i j => raw37705 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37705step0 raw37705; decide +kernel
      have hl : raw37705step0Labels = raw37705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37705 raw37705Labels permutation346 hz
    mixedMoment B raw37705step0 raw37705step0Labels = mixedMoment B raw37705step1 raw37705step1Labels := by
      have ha : raw37705step1 = (fun i j => raw37705step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37705step1 raw37705step0; decide +kernel
      have hl : raw37705step1Labels = raw37705step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37705step0 raw37705step0Labels permutation145 permutation2
    _ = mixedMoment B node1984 node1984Labels := by rfl

def raw37706 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-4, 1, 3]]
def raw37706Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, 0, 0], ![0, -2, 2], ![-4, 1, 3]]
def raw37706step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37706step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, -2, 2], ![-4, 1, 3]]
def raw37706step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37706step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![2, 0, -2], ![2, 1, -3]]
def raw37706step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37706 raw37706Labels = mixedMoment B node963 node963Labels := by
  calc
    mixedMoment B raw37706 raw37706Labels = mixedMoment B raw37706step0 raw37706step0Labels := by
      have hz : ∀ j, raw37706 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37706step0 = (fun i j => raw37706 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37706step0 raw37706; decide +kernel
      have hl : raw37706step0Labels = raw37706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37706 raw37706Labels permutation434 hz
    mixedMoment B raw37706step0 raw37706step0Labels = mixedMoment B raw37706step1 raw37706step1Labels := by
      have hz : ∀ j, raw37706step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37706step1 = (fun i j => raw37706step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37706step1 raw37706step0; decide +kernel
      have hl : raw37706step1Labels = raw37706step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37706step0 raw37706step0Labels permutation80 hz
    mixedMoment B raw37706step1 raw37706step1Labels = mixedMoment B raw37706step2 raw37706step2Labels := by
      have ha : raw37706step2 = (fun i j => raw37706step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37706step2 raw37706step1; decide +kernel
      have hl : raw37706step2Labels = raw37706step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37706step1 raw37706step1Labels permutation31 permutation2
    _ = mixedMoment B node963 node963Labels := by rfl

def raw37707 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37707Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 1, -2], ![1, -1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37707step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37707step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw37707step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37707 raw37707Labels = mixedMoment B node1850 node1850Labels := by
  calc
    mixedMoment B raw37707 raw37707Labels = mixedMoment B raw37707step0 raw37707step0Labels := by
      have hz : ∀ j, raw37707 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37707step0 = (fun i j => raw37707 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37707step0 raw37707; decide +kernel
      have hl : raw37707step0Labels = raw37707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37707 raw37707Labels permutation434 hz
    mixedMoment B raw37707step0 raw37707step0Labels = mixedMoment B raw37707step1 raw37707step1Labels := by
      have ha : raw37707step1 = (fun i j => raw37707step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37707step1 raw37707step0; decide +kernel
      have hl : raw37707step1Labels = raw37707step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37707step0 raw37707step0Labels permutation32 permutation4
    mixedMoment B raw37707step1 raw37707step1Labels = mixedMoment B raw37707step2 raw37707step2Labels := by
      have ha : raw37707step2 = -raw37707step1 := by apply Matrix.ext; change ∀ i j, raw37707step2 i j = -(raw37707step1 i j); unfold raw37707step2 raw37707step1; decide +kernel
      have hl : raw37707step2Labels = raw37707step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1850 node1850Labels := by rfl

def raw37708 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37708Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 1, -2], ![1, -1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37708step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37708step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37708step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw37708step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37708 raw37708Labels = mixedMoment B node1850 node1850Labels := by
  calc
    mixedMoment B raw37708 raw37708Labels = mixedMoment B raw37708step0 raw37708step0Labels := by
      have hz : ∀ j, raw37708 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37708step0 = (fun i j => raw37708 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37708step0 raw37708; decide +kernel
      have hl : raw37708step0Labels = raw37708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37708 raw37708Labels permutation346 hz
    mixedMoment B raw37708step0 raw37708step0Labels = mixedMoment B raw37708step1 raw37708step1Labels := by
      have ha : raw37708step1 = (fun i j => raw37708step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37708step1 raw37708step0; decide +kernel
      have hl : raw37708step1Labels = raw37708step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37708step0 raw37708step0Labels permutation32 permutation4
    mixedMoment B raw37708step1 raw37708step1Labels = mixedMoment B raw37708step2 raw37708step2Labels := by
      have ha : raw37708step2 = -raw37708step1 := by apply Matrix.ext; change ∀ i j, raw37708step2 i j = -(raw37708step1 i j); unfold raw37708step2 raw37708step1; decide +kernel
      have hl : raw37708step2Labels = raw37708step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1850 node1850Labels := by rfl

def raw37709 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37709Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 1, -2], ![0, 0, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37709step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37709step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 1, -2], ![0, -2, 2], ![-1, -2, 3]]
def raw37709step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37709step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![-2, 0, 2], ![-2, -1, 3]]
def raw37709step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37709step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![2, 0, -2], ![2, 1, -3]]
def raw37709step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37709 raw37709Labels = mixedMoment B node1859 node1859Labels := by
  calc
    mixedMoment B raw37709 raw37709Labels = mixedMoment B raw37709step0 raw37709step0Labels := by
      have hz : ∀ j, raw37709 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37709step0 = (fun i j => raw37709 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37709step0 raw37709; decide +kernel
      have hl : raw37709step0Labels = raw37709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37709 raw37709Labels permutation434 hz
    mixedMoment B raw37709step0 raw37709step0Labels = mixedMoment B raw37709step1 raw37709step1Labels := by
      have hz : ∀ j, raw37709step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37709step1 = (fun i j => raw37709step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37709step1 raw37709step0; decide +kernel
      have hl : raw37709step1Labels = raw37709step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37709step0 raw37709step0Labels permutation80 hz
    mixedMoment B raw37709step1 raw37709step1Labels = mixedMoment B raw37709step2 raw37709step2Labels := by
      have ha : raw37709step2 = (fun i j => raw37709step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37709step2 raw37709step1; decide +kernel
      have hl : raw37709step2Labels = raw37709step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37709step1 raw37709step1Labels permutation8 permutation4
    mixedMoment B raw37709step2 raw37709step2Labels = mixedMoment B raw37709step3 raw37709step3Labels := by
      have ha : raw37709step3 = -raw37709step2 := by apply Matrix.ext; change ∀ i j, raw37709step3 i j = -(raw37709step2 i j); unfold raw37709step3 raw37709step2; decide +kernel
      have hl : raw37709step3Labels = raw37709step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1859 node1859Labels := by rfl

def raw37710 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37710Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 1, -2], ![0, 0, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37710step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37710step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 1, -2], ![-1, -1, 2], ![0, -3, 3]]
def raw37710step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37710step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 1, -2], ![3, 0, -3]]
def raw37710step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37710 raw37710Labels = mixedMoment B node1856 node1856Labels := by
  calc
    mixedMoment B raw37710 raw37710Labels = mixedMoment B raw37710step0 raw37710step0Labels := by
      have hz : ∀ j, raw37710 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37710step0 = (fun i j => raw37710 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37710step0 raw37710; decide +kernel
      have hl : raw37710step0Labels = raw37710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37710 raw37710Labels permutation434 hz
    mixedMoment B raw37710step0 raw37710step0Labels = mixedMoment B raw37710step1 raw37710step1Labels := by
      have hz : ∀ j, raw37710step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37710step1 = (fun i j => raw37710step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37710step1 raw37710step0; decide +kernel
      have hl : raw37710step1Labels = raw37710step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37710step0 raw37710step0Labels permutation80 hz
    mixedMoment B raw37710step1 raw37710step1Labels = mixedMoment B raw37710step2 raw37710step2Labels := by
      have ha : raw37710step2 = (fun i j => raw37710step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37710step2 raw37710step1; decide +kernel
      have hl : raw37710step2Labels = raw37710step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37710step1 raw37710step1Labels permutation31 permutation4
    _ = mixedMoment B node1856 node1856Labels := by rfl

def raw37711 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37711Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 1, -2], ![1, -1, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37711step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37711step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-3, 0, 3]]
def raw37711step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37711step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw37711step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37711 raw37711Labels = mixedMoment B node1843 node1843Labels := by
  calc
    mixedMoment B raw37711 raw37711Labels = mixedMoment B raw37711step0 raw37711step0Labels := by
      have hz : ∀ j, raw37711 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37711step0 = (fun i j => raw37711 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37711step0 raw37711; decide +kernel
      have hl : raw37711step0Labels = raw37711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37711 raw37711Labels permutation434 hz
    mixedMoment B raw37711step0 raw37711step0Labels = mixedMoment B raw37711step1 raw37711step1Labels := by
      have ha : raw37711step1 = (fun i j => raw37711step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37711step1 raw37711step0; decide +kernel
      have hl : raw37711step1Labels = raw37711step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37711step0 raw37711step0Labels permutation34 permutation4
    mixedMoment B raw37711step1 raw37711step1Labels = mixedMoment B raw37711step2 raw37711step2Labels := by
      have ha : raw37711step2 = -raw37711step1 := by apply Matrix.ext; change ∀ i j, raw37711step2 i j = -(raw37711step1 i j); unfold raw37711step2 raw37711step1; decide +kernel
      have hl : raw37711step2Labels = raw37711step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1843 node1843Labels := by rfl

def raw37712 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37712Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 1, -2], ![1, -1, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37712step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-3, 0, 3]]
def raw37712step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37712step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw37712step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37712 raw37712Labels = mixedMoment B node1843 node1843Labels := by
  calc
    mixedMoment B raw37712 raw37712Labels = mixedMoment B raw37712step0 raw37712step0Labels := by
      have hz : ∀ j, raw37712 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37712step0 = (fun i j => raw37712 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37712step0 raw37712; decide +kernel
      have hl : raw37712step0Labels = raw37712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37712 raw37712Labels permutation346 hz
    mixedMoment B raw37712step0 raw37712step0Labels = mixedMoment B raw37712step1 raw37712step1Labels := by
      have ha : raw37712step1 = (fun i j => raw37712step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37712step1 raw37712step0; decide +kernel
      have hl : raw37712step1Labels = raw37712step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37712step0 raw37712step0Labels permutation34 permutation4
    mixedMoment B raw37712step1 raw37712step1Labels = mixedMoment B raw37712step2 raw37712step2Labels := by
      have ha : raw37712step2 = -raw37712step1 := by apply Matrix.ext; change ∀ i j, raw37712step2 i j = -(raw37712step1 i j); unfold raw37712step2 raw37712step1; decide +kernel
      have hl : raw37712step2Labels = raw37712step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1843 node1843Labels := by rfl

def raw37713 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -4, 3]]
def raw37713Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 1, -2], ![0, 0, 0], ![-2, 0, 2], ![1, -4, 3]]
def raw37713step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37713step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 1, -2], ![-2, 0, 2], ![1, -4, 3]]
def raw37713step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37713step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 1, -2], ![3, 0, -3]]
def raw37713step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37713 raw37713Labels = mixedMoment B node962 node962Labels := by
  calc
    mixedMoment B raw37713 raw37713Labels = mixedMoment B raw37713step0 raw37713step0Labels := by
      have hz : ∀ j, raw37713 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37713step0 = (fun i j => raw37713 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37713step0 raw37713; decide +kernel
      have hl : raw37713step0Labels = raw37713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37713 raw37713Labels permutation434 hz
    mixedMoment B raw37713step0 raw37713step0Labels = mixedMoment B raw37713step1 raw37713step1Labels := by
      have hz : ∀ j, raw37713step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37713step1 = (fun i j => raw37713step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37713step1 raw37713step0; decide +kernel
      have hl : raw37713step1Labels = raw37713step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37713step0 raw37713step0Labels permutation80 hz
    mixedMoment B raw37713step1 raw37713step1Labels = mixedMoment B raw37713step2 raw37713step2Labels := by
      have ha : raw37713step2 = (fun i j => raw37713step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37713step2 raw37713step1; decide +kernel
      have hl : raw37713step2Labels = raw37713step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37713step1 raw37713step1Labels permutation31 permutation4
    _ = mixedMoment B node962 node962Labels := by rfl

def raw37714 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37714Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37714step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw37714step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37714 raw37714Labels = mixedMoment B node3457 node3457Labels := by
  calc
    mixedMoment B raw37714 raw37714Labels = mixedMoment B raw37714step0 raw37714step0Labels := by
      have hz : ∀ j, raw37714 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37714step0 = (fun i j => raw37714 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37714step0 raw37714; decide +kernel
      have hl : raw37714step0Labels = raw37714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37714 raw37714Labels permutation346 hz
    mixedMoment B raw37714step0 raw37714step0Labels = mixedMoment B raw37714step1 raw37714step1Labels := by
      have ha : raw37714step1 = (fun i j => raw37714step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37714step1 raw37714step0; decide +kernel
      have hl : raw37714step1Labels = raw37714step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37714step0 raw37714step0Labels permutation144 permutation2
    _ = mixedMoment B node3457 node3457Labels := by rfl

def raw37715 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37715Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37715step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, -2, 3]]
def raw37715step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37715step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]
def raw37715step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37715 raw37715Labels = mixedMoment B node2256 node2256Labels := by
  calc
    mixedMoment B raw37715 raw37715Labels = mixedMoment B raw37715step0 raw37715step0Labels := by
      have hz : ∀ j, raw37715 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37715step0 = (fun i j => raw37715 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37715step0 raw37715; decide +kernel
      have hl : raw37715step0Labels = raw37715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37715 raw37715Labels permutation346 hz
    mixedMoment B raw37715step0 raw37715step0Labels = mixedMoment B raw37715step1 raw37715step1Labels := by
      have ha : raw37715step1 = (fun i j => raw37715step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37715step1 raw37715step0; decide +kernel
      have hl : raw37715step1Labels = raw37715step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37715step0 raw37715step0Labels permutation38 permutation4
    mixedMoment B raw37715step1 raw37715step1Labels = mixedMoment B raw37715step2 raw37715step2Labels := by
      have ha : raw37715step2 = -raw37715step1 := by apply Matrix.ext; change ∀ i j, raw37715step2 i j = -(raw37715step1 i j); unfold raw37715step2 raw37715step1; decide +kernel
      have hl : raw37715step2Labels = raw37715step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2256 node2256Labels := by rfl

def raw37716 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37716Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw37716step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37716step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw37716step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37716 raw37716Labels = mixedMoment B node2147 node2147Labels := by
  calc
    mixedMoment B raw37716 raw37716Labels = mixedMoment B raw37716step0 raw37716step0Labels := by
      have ha : raw37716step0 = (fun i j => raw37716 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37716step0 raw37716; decide +kernel
      have hl : raw37716step0Labels = raw37716Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37716 raw37716Labels permutation158 permutation4
    mixedMoment B raw37716step0 raw37716step0Labels = mixedMoment B raw37716step1 raw37716step1Labels := by
      have ha : raw37716step1 = -raw37716step0 := by apply Matrix.ext; change ∀ i j, raw37716step1 i j = -(raw37716step0 i j); unfold raw37716step1 raw37716step0; decide +kernel
      have hl : raw37716step1Labels = raw37716step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2147 node2147Labels := by rfl

def raw37717 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37717Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37717step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37717step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37717step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37717step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37717 raw37717Labels = mixedMoment B node2165 node2165Labels := by
  calc
    mixedMoment B raw37717 raw37717Labels = mixedMoment B raw37717step0 raw37717step0Labels := by
      have hz : ∀ j, raw37717 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37717step0 = (fun i j => raw37717 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37717step0 raw37717; decide +kernel
      have hl : raw37717step0Labels = raw37717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37717 raw37717Labels permutation346 hz
    mixedMoment B raw37717step0 raw37717step0Labels = mixedMoment B raw37717step1 raw37717step1Labels := by
      have ha : raw37717step1 = (fun i j => raw37717step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37717step1 raw37717step0; decide +kernel
      have hl : raw37717step1Labels = raw37717step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37717step0 raw37717step0Labels permutation32 permutation4
    mixedMoment B raw37717step1 raw37717step1Labels = mixedMoment B raw37717step2 raw37717step2Labels := by
      have ha : raw37717step2 = -raw37717step1 := by apply Matrix.ext; change ∀ i j, raw37717step2 i j = -(raw37717step1 i j); unfold raw37717step2 raw37717step1; decide +kernel
      have hl : raw37717step2Labels = raw37717step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2165 node2165Labels := by rfl

def raw37718 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, -1, 3]]
def raw37718Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![-1, 0, 1], ![1, -2, 1], ![-2, -1, 3]]
def raw37718step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw37718step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw37718step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37718 raw37718Labels = mixedMoment B node2153 node2153Labels := by
  calc
    mixedMoment B raw37718 raw37718Labels = mixedMoment B raw37718step0 raw37718step0Labels := by
      have hz : ∀ j, raw37718 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37718step0 = (fun i j => raw37718 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37718step0 raw37718; decide +kernel
      have hl : raw37718step0Labels = raw37718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37718 raw37718Labels permutation346 hz
    mixedMoment B raw37718step0 raw37718step0Labels = mixedMoment B raw37718step1 raw37718step1Labels := by
      have ha : raw37718step1 = (fun i j => raw37718step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37718step1 raw37718step0; decide +kernel
      have hl : raw37718step1Labels = raw37718step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37718step0 raw37718step0Labels permutation33 permutation4
    mixedMoment B raw37718step1 raw37718step1Labels = mixedMoment B raw37718step2 raw37718step2Labels := by
      have ha : raw37718step2 = -raw37718step1 := by apply Matrix.ext; change ∀ i j, raw37718step2 i j = -(raw37718step1 i j); unfold raw37718step2 raw37718step1; decide +kernel
      have hl : raw37718step2Labels = raw37718step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2153 node2153Labels := by rfl

def raw37719 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37719Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![-1, 0, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37719step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37719step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37719step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw37719step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37719 raw37719Labels = mixedMoment B node2151 node2151Labels := by
  calc
    mixedMoment B raw37719 raw37719Labels = mixedMoment B raw37719step0 raw37719step0Labels := by
      have hz : ∀ j, raw37719 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37719step0 = (fun i j => raw37719 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37719step0 raw37719; decide +kernel
      have hl : raw37719step0Labels = raw37719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37719 raw37719Labels permutation346 hz
    mixedMoment B raw37719step0 raw37719step0Labels = mixedMoment B raw37719step1 raw37719step1Labels := by
      have ha : raw37719step1 = (fun i j => raw37719step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37719step1 raw37719step0; decide +kernel
      have hl : raw37719step1Labels = raw37719step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37719step0 raw37719step0Labels permutation32 permutation4
    mixedMoment B raw37719step1 raw37719step1Labels = mixedMoment B raw37719step2 raw37719step2Labels := by
      have ha : raw37719step2 = -raw37719step1 := by apply Matrix.ext; change ∀ i j, raw37719step2 i j = -(raw37719step1 i j); unfold raw37719step2 raw37719step1; decide +kernel
      have hl : raw37719step2Labels = raw37719step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2151 node2151Labels := by rfl

def raw37720 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![2, -2], ![0, 0], ![-1, 1], ![-1, 1], ![-3, 3]]
def raw37720Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37720step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![2, -2], ![-1, 1], ![-1, 1], ![-3, 3]]
def raw37720step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37720step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]
def raw37720step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37720 raw37720Labels = mixedMoment B node4074 node4074Labels := by
  calc
    mixedMoment B raw37720 raw37720Labels = mixedMoment B raw37720step0 raw37720step0Labels := by
      have hz : ∀ j, raw37720 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37720step0 = (fun i j => raw37720 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37720step0 raw37720; decide +kernel
      have hl : raw37720step0Labels = raw37720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37720 raw37720Labels permutation346 hz
    mixedMoment B raw37720step0 raw37720step0Labels = mixedMoment B raw37720step1 raw37720step1Labels := by
      have ha : raw37720step1 = -raw37720step0 := by apply Matrix.ext; change ∀ i j, raw37720step1 i j = -(raw37720step0 i j); unfold raw37720step1 raw37720step0; decide +kernel
      have hl : raw37720step1Labels = raw37720step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4074 node4074Labels := by rfl

def raw37721 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37721Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37721step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw37721step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37721 raw37721Labels = mixedMoment B node2186 node2186Labels := by
  calc
    mixedMoment B raw37721 raw37721Labels = mixedMoment B raw37721step0 raw37721step0Labels := by
      have hz : ∀ j, raw37721 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37721step0 = (fun i j => raw37721 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37721step0 raw37721; decide +kernel
      have hl : raw37721step0Labels = raw37721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37721 raw37721Labels permutation346 hz
    mixedMoment B raw37721step0 raw37721step0Labels = mixedMoment B raw37721step1 raw37721step1Labels := by
      have ha : raw37721step1 = (fun i j => raw37721step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37721step1 raw37721step0; decide +kernel
      have hl : raw37721step1Labels = raw37721step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37721step0 raw37721step0Labels permutation144 permutation2
    _ = mixedMoment B node2186 node2186Labels := by rfl

def raw37722 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37722Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37722step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw37722step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37722 raw37722Labels = mixedMoment B node2180 node2180Labels := by
  calc
    mixedMoment B raw37722 raw37722Labels = mixedMoment B raw37722step0 raw37722step0Labels := by
      have hz : ∀ j, raw37722 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37722step0 = (fun i j => raw37722 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37722step0 raw37722; decide +kernel
      have hl : raw37722step0Labels = raw37722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37722 raw37722Labels permutation346 hz
    mixedMoment B raw37722step0 raw37722step0Labels = mixedMoment B raw37722step1 raw37722step1Labels := by
      have ha : raw37722step1 = (fun i j => raw37722step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37722step1 raw37722step0; decide +kernel
      have hl : raw37722step1Labels = raw37722step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37722step0 raw37722step0Labels permutation144 permutation2
    _ = mixedMoment B node2180 node2180Labels := by rfl

def raw37723 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37723Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37723step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37723step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37723step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37723step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37723 raw37723Labels = mixedMoment B node2160 node2160Labels := by
  calc
    mixedMoment B raw37723 raw37723Labels = mixedMoment B raw37723step0 raw37723step0Labels := by
      have ha : raw37723step0 = (fun i j => raw37723 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37723step0 raw37723; decide +kernel
      have hl : raw37723step0Labels = raw37723Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37723 raw37723Labels permutation170 permutation4
    mixedMoment B raw37723step0 raw37723step0Labels = mixedMoment B raw37723step1 raw37723step1Labels := by
      have ha : raw37723step1 = -raw37723step0 := by apply Matrix.ext; change ∀ i j, raw37723step1 i j = -(raw37723step0 i j); unfold raw37723step1 raw37723step0; decide +kernel
      have hl : raw37723step1Labels = raw37723step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2160 node2160Labels := by rfl

def raw37724 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37724Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37724step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw37724step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw37724step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37724 raw37724Labels = mixedMoment B node2162 node2162Labels := by
  calc
    mixedMoment B raw37724 raw37724Labels = mixedMoment B raw37724step0 raw37724step0Labels := by
      have hz : ∀ j, raw37724 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37724step0 = (fun i j => raw37724 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37724step0 raw37724; decide +kernel
      have hl : raw37724step0Labels = raw37724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37724 raw37724Labels permutation346 hz
    mixedMoment B raw37724step0 raw37724step0Labels = mixedMoment B raw37724step1 raw37724step1Labels := by
      have ha : raw37724step1 = (fun i j => raw37724step0 (permutation37 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37724step1 raw37724step0; decide +kernel
      have hl : raw37724step1Labels = raw37724step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37724step0 raw37724step0Labels permutation37 permutation4
    mixedMoment B raw37724step1 raw37724step1Labels = mixedMoment B raw37724step2 raw37724step2Labels := by
      have ha : raw37724step2 = -raw37724step1 := by apply Matrix.ext; change ∀ i j, raw37724step2 i j = -(raw37724step1 i j); unfold raw37724step2 raw37724step1; decide +kernel
      have hl : raw37724step2Labels = raw37724step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2162 node2162Labels := by rfl

def raw37725 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 0, 3]]
def raw37725Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, -1, 1], ![1, -2, 1], ![-3, 0, 3]]
def raw37725step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw37725step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37725step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw37725step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37725 raw37725Labels = mixedMoment B node2162 node2162Labels := by
  calc
    mixedMoment B raw37725 raw37725Labels = mixedMoment B raw37725step0 raw37725step0Labels := by
      have hz : ∀ j, raw37725 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37725step0 = (fun i j => raw37725 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37725step0 raw37725; decide +kernel
      have hl : raw37725step0Labels = raw37725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37725 raw37725Labels permutation346 hz
    mixedMoment B raw37725step0 raw37725step0Labels = mixedMoment B raw37725step1 raw37725step1Labels := by
      have ha : raw37725step1 = (fun i j => raw37725step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37725step1 raw37725step0; decide +kernel
      have hl : raw37725step1Labels = raw37725step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37725step0 raw37725step0Labels permutation36 permutation4
    mixedMoment B raw37725step1 raw37725step1Labels = mixedMoment B raw37725step2 raw37725step2Labels := by
      have ha : raw37725step2 = -raw37725step1 := by apply Matrix.ext; change ∀ i j, raw37725step2 i j = -(raw37725step1 i j); unfold raw37725step2 raw37725step1; decide +kernel
      have hl : raw37725step2Labels = raw37725step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2162 node2162Labels := by rfl

def raw37726 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37726Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37726step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37726step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37726step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]
def raw37726step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37726 raw37726Labels = mixedMoment B node3588 node3588Labels := by
  calc
    mixedMoment B raw37726 raw37726Labels = mixedMoment B raw37726step0 raw37726step0Labels := by
      have hz : ∀ j, raw37726 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37726step0 = (fun i j => raw37726 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37726step0 raw37726; decide +kernel
      have hl : raw37726step0Labels = raw37726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37726 raw37726Labels permutation346 hz
    mixedMoment B raw37726step0 raw37726step0Labels = mixedMoment B raw37726step1 raw37726step1Labels := by
      have ha : raw37726step1 = (fun i j => raw37726step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37726step1 raw37726step0; decide +kernel
      have hl : raw37726step1Labels = raw37726step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37726step0 raw37726step0Labels permutation32 permutation4
    mixedMoment B raw37726step1 raw37726step1Labels = mixedMoment B raw37726step2 raw37726step2Labels := by
      have ha : raw37726step2 = -raw37726step1 := by apply Matrix.ext; change ∀ i j, raw37726step2 i j = -(raw37726step1 i j); unfold raw37726step2 raw37726step1; decide +kernel
      have hl : raw37726step2Labels = raw37726step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3588 node3588Labels := by rfl

def raw37727 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37727Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37727step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37727step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-2, -1, 3]]
def raw37727step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37727step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw37727step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37727 raw37727Labels = mixedMoment B node2239 node2239Labels := by
  calc
    mixedMoment B raw37727 raw37727Labels = mixedMoment B raw37727step0 raw37727step0Labels := by
      have hz : ∀ j, raw37727 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37727step0 = (fun i j => raw37727 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37727step0 raw37727; decide +kernel
      have hl : raw37727step0Labels = raw37727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37727 raw37727Labels permutation346 hz
    mixedMoment B raw37727step0 raw37727step0Labels = mixedMoment B raw37727step1 raw37727step1Labels := by
      have ha : raw37727step1 = (fun i j => raw37727step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37727step1 raw37727step0; decide +kernel
      have hl : raw37727step1Labels = raw37727step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37727step0 raw37727step0Labels permutation40 permutation4
    mixedMoment B raw37727step1 raw37727step1Labels = mixedMoment B raw37727step2 raw37727step2Labels := by
      have ha : raw37727step2 = -raw37727step1 := by apply Matrix.ext; change ∀ i j, raw37727step2 i j = -(raw37727step1 i j); unfold raw37727step2 raw37727step1; decide +kernel
      have hl : raw37727step2Labels = raw37727step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2239 node2239Labels := by rfl

def raw37728 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37728Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37728step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw37728step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37728step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw37728step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37728 raw37728Labels = mixedMoment B node2140 node2140Labels := by
  calc
    mixedMoment B raw37728 raw37728Labels = mixedMoment B raw37728step0 raw37728step0Labels := by
      have ha : raw37728step0 = (fun i j => raw37728 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37728step0 raw37728; decide +kernel
      have hl : raw37728step0Labels = raw37728Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37728 raw37728Labels permutation160 permutation4
    mixedMoment B raw37728step0 raw37728step0Labels = mixedMoment B raw37728step1 raw37728step1Labels := by
      have ha : raw37728step1 = -raw37728step0 := by apply Matrix.ext; change ∀ i j, raw37728step1 i j = -(raw37728step0 i j); unfold raw37728step1 raw37728step0; decide +kernel
      have hl : raw37728step1Labels = raw37728step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2140 node2140Labels := by rfl

def raw37729 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37729Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37729step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37729step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw37729step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37729 raw37729Labels = mixedMoment B node2151 node2151Labels := by
  calc
    mixedMoment B raw37729 raw37729Labels = mixedMoment B raw37729step0 raw37729step0Labels := by
      have hz : ∀ j, raw37729 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37729step0 = (fun i j => raw37729 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37729step0 raw37729; decide +kernel
      have hl : raw37729step0Labels = raw37729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37729 raw37729Labels permutation346 hz
    mixedMoment B raw37729step0 raw37729step0Labels = mixedMoment B raw37729step1 raw37729step1Labels := by
      have ha : raw37729step1 = (fun i j => raw37729step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37729step1 raw37729step0; decide +kernel
      have hl : raw37729step1Labels = raw37729step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37729step0 raw37729step0Labels permutation34 permutation4
    mixedMoment B raw37729step1 raw37729step1Labels = mixedMoment B raw37729step2 raw37729step2Labels := by
      have ha : raw37729step2 = -raw37729step1 := by apply Matrix.ext; change ∀ i j, raw37729step2 i j = -(raw37729step1 i j); unfold raw37729step2 raw37729step1; decide +kernel
      have hl : raw37729step2Labels = raw37729step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2151 node2151Labels := by rfl

def raw37730 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37730Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, 0, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37730step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37730step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37730step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw37730step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37730 raw37730Labels = mixedMoment B node2143 node2143Labels := by
  calc
    mixedMoment B raw37730 raw37730Labels = mixedMoment B raw37730step0 raw37730step0Labels := by
      have hz : ∀ j, raw37730 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37730step0 = (fun i j => raw37730 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37730step0 raw37730; decide +kernel
      have hl : raw37730step0Labels = raw37730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37730 raw37730Labels permutation346 hz
    mixedMoment B raw37730step0 raw37730step0Labels = mixedMoment B raw37730step1 raw37730step1Labels := by
      have ha : raw37730step1 = (fun i j => raw37730step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37730step1 raw37730step0; decide +kernel
      have hl : raw37730step1Labels = raw37730step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37730step0 raw37730step0Labels permutation32 permutation4
    mixedMoment B raw37730step1 raw37730step1Labels = mixedMoment B raw37730step2 raw37730step2Labels := by
      have ha : raw37730step2 = -raw37730step1 := by apply Matrix.ext; change ∀ i j, raw37730step2 i j = -(raw37730step1 i j); unfold raw37730step2 raw37730step1; decide +kernel
      have hl : raw37730step2Labels = raw37730step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2143 node2143Labels := by rfl

def raw37731 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37731Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37731step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37731step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37731step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw37731step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37731 raw37731Labels = mixedMoment B node3411 node3411Labels := by
  calc
    mixedMoment B raw37731 raw37731Labels = mixedMoment B raw37731step0 raw37731step0Labels := by
      have hz : ∀ j, raw37731 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37731step0 = (fun i j => raw37731 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37731step0 raw37731; decide +kernel
      have hl : raw37731step0Labels = raw37731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37731 raw37731Labels permutation346 hz
    mixedMoment B raw37731step0 raw37731step0Labels = mixedMoment B raw37731step1 raw37731step1Labels := by
      have ha : raw37731step1 = (fun i j => raw37731step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37731step1 raw37731step0; decide +kernel
      have hl : raw37731step1Labels = raw37731step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37731step0 raw37731step0Labels permutation34 permutation2
    mixedMoment B raw37731step1 raw37731step1Labels = mixedMoment B raw37731step2 raw37731step2Labels := by
      have ha : raw37731step2 = -raw37731step1 := by apply Matrix.ext; change ∀ i j, raw37731step2 i j = -(raw37731step1 i j); unfold raw37731step2 raw37731step1; decide +kernel
      have hl : raw37731step2Labels = raw37731step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3411 node3411Labels := by rfl

def raw37732 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37732Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37732step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw37732step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37732step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw37732step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37732 raw37732Labels = mixedMoment B node3408 node3408Labels := by
  calc
    mixedMoment B raw37732 raw37732Labels = mixedMoment B raw37732step0 raw37732step0Labels := by
      have ha : raw37732step0 = (fun i j => raw37732 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37732step0 raw37732; decide +kernel
      have hl : raw37732step0Labels = raw37732Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37732 raw37732Labels permutation158 permutation4
    mixedMoment B raw37732step0 raw37732step0Labels = mixedMoment B raw37732step1 raw37732step1Labels := by
      have ha : raw37732step1 = -raw37732step0 := by apply Matrix.ext; change ∀ i j, raw37732step1 i j = -(raw37732step0 i j); unfold raw37732step1 raw37732step0; decide +kernel
      have hl : raw37732step1Labels = raw37732step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3408 node3408Labels := by rfl

def raw37733 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37733Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37733step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37733step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37733step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37733step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37733 raw37733Labels = mixedMoment B node3420 node3420Labels := by
  calc
    mixedMoment B raw37733 raw37733Labels = mixedMoment B raw37733step0 raw37733step0Labels := by
      have hz : ∀ j, raw37733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37733step0 = (fun i j => raw37733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37733step0 raw37733; decide +kernel
      have hl : raw37733step0Labels = raw37733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37733 raw37733Labels permutation346 hz
    mixedMoment B raw37733step0 raw37733step0Labels = mixedMoment B raw37733step1 raw37733step1Labels := by
      have ha : raw37733step1 = (fun i j => raw37733step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37733step1 raw37733step0; decide +kernel
      have hl : raw37733step1Labels = raw37733step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37733step0 raw37733step0Labels permutation32 permutation4
    mixedMoment B raw37733step1 raw37733step1Labels = mixedMoment B raw37733step2 raw37733step2Labels := by
      have ha : raw37733step2 = -raw37733step1 := by apply Matrix.ext; change ∀ i j, raw37733step2 i j = -(raw37733step1 i j); unfold raw37733step2 raw37733step1; decide +kernel
      have hl : raw37733step2Labels = raw37733step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3420 node3420Labels := by rfl

def raw37734 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, -1, 3]]
def raw37734Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![-1, 0, 1], ![1, -2, 1], ![-2, -1, 3]]
def raw37734step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw37734step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37734step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw37734step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37734 raw37734Labels = mixedMoment B node3413 node3413Labels := by
  calc
    mixedMoment B raw37734 raw37734Labels = mixedMoment B raw37734step0 raw37734step0Labels := by
      have hz : ∀ j, raw37734 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37734step0 = (fun i j => raw37734 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37734step0 raw37734; decide +kernel
      have hl : raw37734step0Labels = raw37734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37734 raw37734Labels permutation346 hz
    mixedMoment B raw37734step0 raw37734step0Labels = mixedMoment B raw37734step1 raw37734step1Labels := by
      have ha : raw37734step1 = (fun i j => raw37734step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37734step1 raw37734step0; decide +kernel
      have hl : raw37734step1Labels = raw37734step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37734step0 raw37734step0Labels permutation33 permutation4
    mixedMoment B raw37734step1 raw37734step1Labels = mixedMoment B raw37734step2 raw37734step2Labels := by
      have ha : raw37734step2 = -raw37734step1 := by apply Matrix.ext; change ∀ i j, raw37734step2 i j = -(raw37734step1 i j); unfold raw37734step2 raw37734step1; decide +kernel
      have hl : raw37734step2Labels = raw37734step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3413 node3413Labels := by rfl

def raw37735 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37735Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![-1, 0, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37735step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37735step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37735step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw37735step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37735 raw37735Labels = mixedMoment B node3411 node3411Labels := by
  calc
    mixedMoment B raw37735 raw37735Labels = mixedMoment B raw37735step0 raw37735step0Labels := by
      have hz : ∀ j, raw37735 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37735step0 = (fun i j => raw37735 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37735step0 raw37735; decide +kernel
      have hl : raw37735step0Labels = raw37735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37735 raw37735Labels permutation346 hz
    mixedMoment B raw37735step0 raw37735step0Labels = mixedMoment B raw37735step1 raw37735step1Labels := by
      have ha : raw37735step1 = (fun i j => raw37735step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37735step1 raw37735step0; decide +kernel
      have hl : raw37735step1Labels = raw37735step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37735step0 raw37735step0Labels permutation32 permutation4
    mixedMoment B raw37735step1 raw37735step1Labels = mixedMoment B raw37735step2 raw37735step2Labels := by
      have ha : raw37735step2 = -raw37735step1 := by apply Matrix.ext; change ∀ i j, raw37735step2 i j = -(raw37735step1 i j); unfold raw37735step2 raw37735step1; decide +kernel
      have hl : raw37735step2Labels = raw37735step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3411 node3411Labels := by rfl

def raw37736 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37736Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37736step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37736step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw37736step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37736 raw37736Labels = mixedMoment B node2185 node2185Labels := by
  calc
    mixedMoment B raw37736 raw37736Labels = mixedMoment B raw37736step0 raw37736step0Labels := by
      have hz : ∀ j, raw37736 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37736step0 = (fun i j => raw37736 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37736step0 raw37736; decide +kernel
      have hl : raw37736step0Labels = raw37736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37736 raw37736Labels permutation346 hz
    mixedMoment B raw37736step0 raw37736step0Labels = mixedMoment B raw37736step1 raw37736step1Labels := by
      have ha : raw37736step1 = (fun i j => raw37736step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37736step1 raw37736step0; decide +kernel
      have hl : raw37736step1Labels = raw37736step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37736step0 raw37736step0Labels permutation145 permutation2
    _ = mixedMoment B node2185 node2185Labels := by rfl

def raw37737 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37737Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37737step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw37737step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37737 raw37737Labels = mixedMoment B node2181 node2181Labels := by
  calc
    mixedMoment B raw37737 raw37737Labels = mixedMoment B raw37737step0 raw37737step0Labels := by
      have ha : raw37737step0 = (fun i j => raw37737 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37737step0 raw37737; decide +kernel
      have hl : raw37737step0Labels = raw37737Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37737 raw37737Labels permutation664 permutation2
    _ = mixedMoment B node2181 node2181Labels := by rfl

def raw37738 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37738Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![1, -2, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37738step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw37738step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37738 raw37738Labels = mixedMoment B node2223 node2223Labels := by
  calc
    mixedMoment B raw37738 raw37738Labels = mixedMoment B raw37738step0 raw37738step0Labels := by
      have hz : ∀ j, raw37738 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37738step0 = (fun i j => raw37738 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37738step0 raw37738; decide +kernel
      have hl : raw37738step0Labels = raw37738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37738 raw37738Labels permutation346 hz
    mixedMoment B raw37738step0 raw37738step0Labels = mixedMoment B raw37738step1 raw37738step1Labels := by
      have ha : raw37738step1 = (fun i j => raw37738step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37738step1 raw37738step0; decide +kernel
      have hl : raw37738step1Labels = raw37738step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37738step0 raw37738step0Labels permutation151 permutation2
    _ = mixedMoment B node2223 node2223Labels := by rfl

def raw37739 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 0, 3]]
def raw37739Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, -1, 1], ![1, -2, 1], ![-3, 0, 3]]
def raw37739step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw37739step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37739 raw37739Labels = mixedMoment B node2223 node2223Labels := by
  calc
    mixedMoment B raw37739 raw37739Labels = mixedMoment B raw37739step0 raw37739step0Labels := by
      have hz : ∀ j, raw37739 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37739step0 = (fun i j => raw37739 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37739step0 raw37739; decide +kernel
      have hl : raw37739step0Labels = raw37739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37739 raw37739Labels permutation346 hz
    mixedMoment B raw37739step0 raw37739step0Labels = mixedMoment B raw37739step1 raw37739step1Labels := by
      have ha : raw37739step1 = (fun i j => raw37739step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37739step1 raw37739step0; decide +kernel
      have hl : raw37739step1Labels = raw37739step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37739step0 raw37739step0Labels permutation145 permutation2
    _ = mixedMoment B node2223 node2223Labels := by rfl

def raw37740 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37740Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37740step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37740step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37740 raw37740Labels = mixedMoment B node3420 node3420Labels := by
  calc
    mixedMoment B raw37740 raw37740Labels = mixedMoment B raw37740step0 raw37740step0Labels := by
      have hz : ∀ j, raw37740 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37740step0 = (fun i j => raw37740 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37740step0 raw37740; decide +kernel
      have hl : raw37740step0Labels = raw37740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37740 raw37740Labels permutation346 hz
    mixedMoment B raw37740step0 raw37740step0Labels = mixedMoment B raw37740step1 raw37740step1Labels := by
      have ha : raw37740step1 = -raw37740step0 := by apply Matrix.ext; change ∀ i j, raw37740step1 i j = -(raw37740step0 i j); unfold raw37740step1 raw37740step0; decide +kernel
      have hl : raw37740step1Labels = raw37740step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3420 node3420Labels := by rfl

def raw37741 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37741Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw37741step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37741step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw37741step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37741 raw37741Labels = mixedMoment B node3403 node3403Labels := by
  calc
    mixedMoment B raw37741 raw37741Labels = mixedMoment B raw37741step0 raw37741step0Labels := by
      have ha : raw37741step0 = (fun i j => raw37741 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37741step0 raw37741; decide +kernel
      have hl : raw37741step0Labels = raw37741Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37741 raw37741Labels permutation160 permutation4
    mixedMoment B raw37741step0 raw37741step0Labels = mixedMoment B raw37741step1 raw37741step1Labels := by
      have ha : raw37741step1 = -raw37741step0 := by apply Matrix.ext; change ∀ i j, raw37741step1 i j = -(raw37741step0 i j); unfold raw37741step1 raw37741step0; decide +kernel
      have hl : raw37741step1Labels = raw37741step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3403 node3403Labels := by rfl

def raw37742 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37742Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37742step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37742step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37742step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw37742step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37742 raw37742Labels = mixedMoment B node3411 node3411Labels := by
  calc
    mixedMoment B raw37742 raw37742Labels = mixedMoment B raw37742step0 raw37742step0Labels := by
      have hz : ∀ j, raw37742 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37742step0 = (fun i j => raw37742 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37742step0 raw37742; decide +kernel
      have hl : raw37742step0Labels = raw37742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37742 raw37742Labels permutation346 hz
    mixedMoment B raw37742step0 raw37742step0Labels = mixedMoment B raw37742step1 raw37742step1Labels := by
      have ha : raw37742step1 = (fun i j => raw37742step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37742step1 raw37742step0; decide +kernel
      have hl : raw37742step1Labels = raw37742step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37742step0 raw37742step0Labels permutation34 permutation4
    mixedMoment B raw37742step1 raw37742step1Labels = mixedMoment B raw37742step2 raw37742step2Labels := by
      have ha : raw37742step2 = -raw37742step1 := by apply Matrix.ext; change ∀ i j, raw37742step2 i j = -(raw37742step1 i j); unfold raw37742step2 raw37742step1; decide +kernel
      have hl : raw37742step2Labels = raw37742step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3411 node3411Labels := by rfl

def raw37743 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37743Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37743step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw37743step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37743 raw37743Labels = mixedMoment B node2185 node2185Labels := by
  calc
    mixedMoment B raw37743 raw37743Labels = mixedMoment B raw37743step0 raw37743step0Labels := by
      have hz : ∀ j, raw37743 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37743step0 = (fun i j => raw37743 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37743step0 raw37743; decide +kernel
      have hl : raw37743step0Labels = raw37743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37743 raw37743Labels permutation346 hz
    mixedMoment B raw37743step0 raw37743step0Labels = mixedMoment B raw37743step1 raw37743step1Labels := by
      have ha : raw37743step1 = (fun i j => raw37743step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37743step1 raw37743step0; decide +kernel
      have hl : raw37743step1Labels = raw37743step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37743step0 raw37743step0Labels permutation145 permutation4
    _ = mixedMoment B node2185 node2185Labels := by rfl

def raw37744 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 1, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37744Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37744step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37744step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37744step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37744step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37744 raw37744Labels = mixedMoment B node1847 node1847Labels := by
  calc
    mixedMoment B raw37744 raw37744Labels = mixedMoment B raw37744step0 raw37744step0Labels := by
      have ha : raw37744step0 = (fun i j => raw37744 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37744step0 raw37744; decide +kernel
      have hl : raw37744step0Labels = raw37744Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37744 raw37744Labels permutation152 permutation4
    mixedMoment B raw37744step0 raw37744step0Labels = mixedMoment B raw37744step1 raw37744step1Labels := by
      have ha : raw37744step1 = -raw37744step0 := by apply Matrix.ext; change ∀ i j, raw37744step1 i j = -(raw37744step0 i j); unfold raw37744step1 raw37744step0; decide +kernel
      have hl : raw37744step1Labels = raw37744step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1847 node1847Labels := by rfl

def raw37745 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 2, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37745Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37745step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37745step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37745step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37745step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37745 raw37745Labels = mixedMoment B node3323 node3323Labels := by
  calc
    mixedMoment B raw37745 raw37745Labels = mixedMoment B raw37745step0 raw37745step0Labels := by
      have ha : raw37745step0 = (fun i j => raw37745 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37745step0 raw37745; decide +kernel
      have hl : raw37745step0Labels = raw37745Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37745 raw37745Labels permutation152 permutation4
    mixedMoment B raw37745step0 raw37745step0Labels = mixedMoment B raw37745step1 raw37745step1Labels := by
      have ha : raw37745step1 = -raw37745step0 := by apply Matrix.ext; change ∀ i j, raw37745step1 i j = -(raw37745step0 i j); unfold raw37745step1 raw37745step0; decide +kernel
      have hl : raw37745step1Labels = raw37745step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3323 node3323Labels := by rfl

def raw37746 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37746Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw37746step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37746step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw37746step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37746 raw37746Labels = mixedMoment B node3408 node3408Labels := by
  calc
    mixedMoment B raw37746 raw37746Labels = mixedMoment B raw37746step0 raw37746step0Labels := by
      have ha : raw37746step0 = (fun i j => raw37746 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37746step0 raw37746; decide +kernel
      have hl : raw37746step0Labels = raw37746Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37746 raw37746Labels permutation164 permutation4
    mixedMoment B raw37746step0 raw37746step0Labels = mixedMoment B raw37746step1 raw37746step1Labels := by
      have ha : raw37746step1 = -raw37746step0 := by apply Matrix.ext; change ∀ i j, raw37746step1 i j = -(raw37746step0 i j); unfold raw37746step1 raw37746step0; decide +kernel
      have hl : raw37746step1Labels = raw37746step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3408 node3408Labels := by rfl

def raw37747 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37747Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw37747step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37747 raw37747Labels = mixedMoment B node2176 node2176Labels := by
  calc
    mixedMoment B raw37747 raw37747Labels = mixedMoment B raw37747step0 raw37747step0Labels := by
      have ha : raw37747step0 = (fun i j => raw37747 (permutation662 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37747step0 raw37747; decide +kernel
      have hl : raw37747step0Labels = raw37747Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37747 raw37747Labels permutation662 permutation4
    _ = mixedMoment B node2176 node2176Labels := by rfl

def raw37748 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37748Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![-2, 1, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37748step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw37748step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37748 raw37748Labels = mixedMoment B node2212 node2212Labels := by
  calc
    mixedMoment B raw37748 raw37748Labels = mixedMoment B raw37748step0 raw37748step0Labels := by
      have hz : ∀ j, raw37748 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37748step0 = (fun i j => raw37748 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37748step0 raw37748; decide +kernel
      have hl : raw37748step0Labels = raw37748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37748 raw37748Labels permutation346 hz
    mixedMoment B raw37748step0 raw37748step0Labels = mixedMoment B raw37748step1 raw37748step1Labels := by
      have ha : raw37748step1 = (fun i j => raw37748step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37748step1 raw37748step0; decide +kernel
      have hl : raw37748step1Labels = raw37748step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37748step0 raw37748step0Labels permutation149 permutation4
    _ = mixedMoment B node2212 node2212Labels := by rfl

def raw37749 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -3, 3]]
def raw37749Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![-1, 0, 1], ![-2, 1, 1], ![0, -3, 3]]
def raw37749step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37749step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw37749step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37749 raw37749Labels = mixedMoment B node2212 node2212Labels := by
  calc
    mixedMoment B raw37749 raw37749Labels = mixedMoment B raw37749step0 raw37749step0Labels := by
      have hz : ∀ j, raw37749 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37749step0 = (fun i j => raw37749 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37749step0 raw37749; decide +kernel
      have hl : raw37749step0Labels = raw37749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37749 raw37749Labels permutation346 hz
    mixedMoment B raw37749step0 raw37749step0Labels = mixedMoment B raw37749step1 raw37749step1Labels := by
      have ha : raw37749step1 = (fun i j => raw37749step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37749step1 raw37749step0; decide +kernel
      have hl : raw37749step1Labels = raw37749step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37749step0 raw37749step0Labels permutation143 permutation4
    _ = mixedMoment B node2212 node2212Labels := by rfl

def raw37750 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37750Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37750step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37750step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37750step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37750 raw37750Labels = mixedMoment B node3510 node3510Labels := by
  calc
    mixedMoment B raw37750 raw37750Labels = mixedMoment B raw37750step0 raw37750step0Labels := by
      have ha : raw37750step0 = (fun i j => raw37750 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37750step0 raw37750; decide +kernel
      have hl : raw37750step0Labels = raw37750Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37750 raw37750Labels permutation176 permutation4
    mixedMoment B raw37750step0 raw37750step0Labels = mixedMoment B raw37750step1 raw37750step1Labels := by
      have ha : raw37750step1 = -raw37750step0 := by apply Matrix.ext; change ∀ i j, raw37750step1 i j = -(raw37750step0 i j); unfold raw37750step1 raw37750step0; decide +kernel
      have hl : raw37750step1Labels = raw37750step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3510 node3510Labels := by rfl

def raw37751 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37751Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37751step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw37751step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37751 raw37751Labels = mixedMoment B node3457 node3457Labels := by
  calc
    mixedMoment B raw37751 raw37751Labels = mixedMoment B raw37751step0 raw37751step0Labels := by
      have hz : ∀ j, raw37751 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37751step0 = (fun i j => raw37751 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37751step0 raw37751; decide +kernel
      have hl : raw37751step0Labels = raw37751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37751 raw37751Labels permutation346 hz
    mixedMoment B raw37751step0 raw37751step0Labels = mixedMoment B raw37751step1 raw37751step1Labels := by
      have ha : raw37751step1 = (fun i j => raw37751step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37751step1 raw37751step0; decide +kernel
      have hl : raw37751step1Labels = raw37751step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37751step0 raw37751step0Labels permutation150 permutation2
    _ = mixedMoment B node3457 node3457Labels := by rfl

def raw37752 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37752Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37752step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37752step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37752 raw37752Labels = mixedMoment B node3323 node3323Labels := by
  calc
    mixedMoment B raw37752 raw37752Labels = mixedMoment B raw37752step0 raw37752step0Labels := by
      have ha : raw37752step0 = -raw37752 := by apply Matrix.ext; change ∀ i j, raw37752step0 i j = -(raw37752 i j); unfold raw37752step0 raw37752; decide +kernel
      have hl : raw37752step0Labels = raw37752Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3323 node3323Labels := by rfl

def raw37753 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37753Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-2, 1, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37753step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37753step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 0, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw37753step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37753step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw37753step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37753 raw37753Labels = mixedMoment B node3329 node3329Labels := by
  calc
    mixedMoment B raw37753 raw37753Labels = mixedMoment B raw37753step0 raw37753step0Labels := by
      have hz : ∀ j, raw37753 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37753step0 = (fun i j => raw37753 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37753step0 raw37753; decide +kernel
      have hl : raw37753step0Labels = raw37753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37753 raw37753Labels permutation346 hz
    mixedMoment B raw37753step0 raw37753step0Labels = mixedMoment B raw37753step1 raw37753step1Labels := by
      have ha : raw37753step1 = (fun i j => raw37753step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37753step1 raw37753step0; decide +kernel
      have hl : raw37753step1Labels = raw37753step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37753step0 raw37753step0Labels permutation35 permutation2
    mixedMoment B raw37753step1 raw37753step1Labels = mixedMoment B raw37753step2 raw37753step2Labels := by
      have ha : raw37753step2 = -raw37753step1 := by apply Matrix.ext; change ∀ i j, raw37753step2 i j = -(raw37753step1 i j); unfold raw37753step2 raw37753step1; decide +kernel
      have hl : raw37753step2Labels = raw37753step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3329 node3329Labels := by rfl

def raw37754 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, -2, 3]]
def raw37754Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 0, 1], ![-2, 1, 1], ![-1, -2, 3]]
def raw37754step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 0, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw37754step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37754step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw37754step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37754 raw37754Labels = mixedMoment B node3329 node3329Labels := by
  calc
    mixedMoment B raw37754 raw37754Labels = mixedMoment B raw37754step0 raw37754step0Labels := by
      have hz : ∀ j, raw37754 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37754step0 = (fun i j => raw37754 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37754step0 raw37754; decide +kernel
      have hl : raw37754step0Labels = raw37754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37754 raw37754Labels permutation346 hz
    mixedMoment B raw37754step0 raw37754step0Labels = mixedMoment B raw37754step1 raw37754step1Labels := by
      have ha : raw37754step1 = (fun i j => raw37754step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37754step1 raw37754step0; decide +kernel
      have hl : raw37754step1Labels = raw37754step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37754step0 raw37754step0Labels permutation33 permutation2
    mixedMoment B raw37754step1 raw37754step1Labels = mixedMoment B raw37754step2 raw37754step2Labels := by
      have ha : raw37754step2 = -raw37754step1 := by apply Matrix.ext; change ∀ i j, raw37754step2 i j = -(raw37754step1 i j); unfold raw37754step2 raw37754step1; decide +kernel
      have hl : raw37754step2Labels = raw37754step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3329 node3329Labels := by rfl

def raw37755 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37755Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37755step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw37755step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37755 raw37755Labels = mixedMoment B node3327 node3327Labels := by
  calc
    mixedMoment B raw37755 raw37755Labels = mixedMoment B raw37755step0 raw37755step0Labels := by
      have hz : ∀ j, raw37755 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37755step0 = (fun i j => raw37755 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37755step0 raw37755; decide +kernel
      have hl : raw37755step0Labels = raw37755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37755 raw37755Labels permutation346 hz
    mixedMoment B raw37755step0 raw37755step0Labels = mixedMoment B raw37755step1 raw37755step1Labels := by
      have ha : raw37755step1 = -raw37755step0 := by apply Matrix.ext; change ∀ i j, raw37755step1 i j = -(raw37755step0 i j); unfold raw37755step1 raw37755step0; decide +kernel
      have hl : raw37755step1Labels = raw37755step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3327 node3327Labels := by rfl

def raw37756 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![3, -1, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37756Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37756step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 2, -3], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37756step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37756step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw37756step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37756 raw37756Labels = mixedMoment B node2367 node2367Labels := by
  calc
    mixedMoment B raw37756 raw37756Labels = mixedMoment B raw37756step0 raw37756step0Labels := by
      have hz : ∀ j, raw37756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37756step0 = (fun i j => raw37756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37756step0 raw37756; decide +kernel
      have hl : raw37756step0Labels = raw37756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37756 raw37756Labels permutation346 hz
    mixedMoment B raw37756step0 raw37756step0Labels = mixedMoment B raw37756step1 raw37756step1Labels := by
      have ha : raw37756step1 = (fun i j => raw37756step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37756step1 raw37756step0; decide +kernel
      have hl : raw37756step1Labels = raw37756step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37756step0 raw37756step0Labels permutation56 permutation2
    mixedMoment B raw37756step1 raw37756step1Labels = mixedMoment B raw37756step2 raw37756step2Labels := by
      have ha : raw37756step2 = -raw37756step1 := by apply Matrix.ext; change ∀ i j, raw37756step2 i j = -(raw37756step1 i j); unfold raw37756step2 raw37756step1; decide +kernel
      have hl : raw37756step2Labels = raw37756step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2367 node2367Labels := by rfl

def raw37757 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37757Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37757step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw37757step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37757 raw37757Labels = mixedMoment B node3426 node3426Labels := by
  calc
    mixedMoment B raw37757 raw37757Labels = mixedMoment B raw37757step0 raw37757step0Labels := by
      have ha : raw37757step0 = (fun i j => raw37757 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37757step0 raw37757; decide +kernel
      have hl : raw37757step0Labels = raw37757Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37757 raw37757Labels permutation663 permutation2
    _ = mixedMoment B node3426 node3426Labels := by rfl

def raw37758 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37758Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw37758step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37758step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw37758step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37758 raw37758Labels = mixedMoment B node3315 node3315Labels := by
  calc
    mixedMoment B raw37758 raw37758Labels = mixedMoment B raw37758step0 raw37758step0Labels := by
      have ha : raw37758step0 = (fun i j => raw37758 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37758step0 raw37758; decide +kernel
      have hl : raw37758step0Labels = raw37758Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37758 raw37758Labels permutation164 permutation2
    mixedMoment B raw37758step0 raw37758step0Labels = mixedMoment B raw37758step1 raw37758step1Labels := by
      have ha : raw37758step1 = -raw37758step0 := by apply Matrix.ext; change ∀ i j, raw37758step1 i j = -(raw37758step0 i j); unfold raw37758step1 raw37758step0; decide +kernel
      have hl : raw37758step1Labels = raw37758step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3315 node3315Labels := by rfl

def raw37759 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37759Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-2, 1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37759step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, -1, 3]]
def raw37759step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37759step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw37759step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37759 raw37759Labels = mixedMoment B node3318 node3318Labels := by
  calc
    mixedMoment B raw37759 raw37759Labels = mixedMoment B raw37759step0 raw37759step0Labels := by
      have hz : ∀ j, raw37759 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37759step0 = (fun i j => raw37759 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37759step0 raw37759; decide +kernel
      have hl : raw37759step0Labels = raw37759Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37759 raw37759Labels permutation346 hz
    mixedMoment B raw37759step0 raw37759step0Labels = mixedMoment B raw37759step1 raw37759step1Labels := by
      have ha : raw37759step1 = (fun i j => raw37759step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37759step1 raw37759step0; decide +kernel
      have hl : raw37759step1Labels = raw37759step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37759step0 raw37759step0Labels permutation34 permutation2
    mixedMoment B raw37759step1 raw37759step1Labels = mixedMoment B raw37759step2 raw37759step2Labels := by
      have ha : raw37759step2 = -raw37759step1 := by apply Matrix.ext; change ∀ i j, raw37759step2 i j = -(raw37759step1 i j); unfold raw37759step2 raw37759step1; decide +kernel
      have hl : raw37759step2Labels = raw37759step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3318 node3318Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
