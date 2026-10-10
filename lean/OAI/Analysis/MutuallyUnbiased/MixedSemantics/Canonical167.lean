import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw21376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21376Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21376step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21376step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21376 raw21376Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw21376 raw21376Labels = mixedMoment B raw21376step0 raw21376step0Labels := by
      have hz : ∀ j, raw21376 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21376step0 = (fun i j => raw21376 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21376step0 raw21376; decide +kernel
      have hl : raw21376step0Labels = raw21376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21376 raw21376Labels permutation346 hz
    mixedMoment B raw21376step0 raw21376step0Labels = mixedMoment B raw21376step1 raw21376step1Labels := by
      have ha : raw21376step1 = (fun i j => raw21376step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21376step1 raw21376step0; decide +kernel
      have hl : raw21376step1Labels = raw21376step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21376step0 raw21376step0Labels permutation40 permutation2
    _ = mixedMoment B node4346 node4346Labels := by rfl

def raw21377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21377Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21377step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21377step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw21377step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21377step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw21377step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21377 raw21377Labels = mixedMoment B node4505 node4505Labels := by
  calc
    mixedMoment B raw21377 raw21377Labels = mixedMoment B raw21377step0 raw21377step0Labels := by
      have hz : ∀ j, raw21377 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21377step0 = (fun i j => raw21377 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21377step0 raw21377; decide +kernel
      have hl : raw21377step0Labels = raw21377Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21377 raw21377Labels permutation520 hz
    mixedMoment B raw21377step0 raw21377step0Labels = mixedMoment B raw21377step1 raw21377step1Labels := by
      have hz : ∀ j, raw21377step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21377step1 = (fun i j => raw21377step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21377step1 raw21377step0; decide +kernel
      have hl : raw21377step1Labels = raw21377step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21377step0 raw21377step0Labels permutation104 hz
    mixedMoment B raw21377step1 raw21377step1Labels = mixedMoment B raw21377step2 raw21377step2Labels := by
      have hz : ∀ j, raw21377step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw21377step2 = (fun i j => raw21377step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw21377step2 raw21377step1; decide +kernel
      have hl : raw21377step2Labels = raw21377step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21377step1 raw21377step1Labels permutation20 hz
    _ = mixedMoment B node4505 node4505Labels := by rfl

def raw21378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21378Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21378step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21378 raw21378Labels = mixedMoment B node4151 node4151Labels := by
  calc
    mixedMoment B raw21378 raw21378Labels = mixedMoment B raw21378step0 raw21378step0Labels := by
      have hz : ∀ j, raw21378 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21378step0 = (fun i j => raw21378 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21378step0 raw21378; decide +kernel
      have hl : raw21378step0Labels = raw21378Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21378 raw21378Labels permutation434 hz
    _ = mixedMoment B node4151 node4151Labels := by rfl

def raw21379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21379Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21379step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21379 raw21379Labels = mixedMoment B node4365 node4365Labels := by
  calc
    mixedMoment B raw21379 raw21379Labels = mixedMoment B raw21379step0 raw21379step0Labels := by
      have hz : ∀ j, raw21379 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21379step0 = (fun i j => raw21379 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21379step0 raw21379; decide +kernel
      have hl : raw21379step0Labels = raw21379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21379 raw21379Labels permutation434 hz
    _ = mixedMoment B node4365 node4365Labels := by rfl

def raw21380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21380step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21380 raw21380Labels = mixedMoment B node4326 node4326Labels := by
  calc
    mixedMoment B raw21380 raw21380Labels = mixedMoment B raw21380step0 raw21380step0Labels := by
      have ha : raw21380step0 = (fun i j => raw21380 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21380step0 raw21380; decide +kernel
      have hl : raw21380step0Labels = raw21380Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21380 raw21380Labels permutation200 permutation2
    _ = mixedMoment B node4326 node4326Labels := by rfl

def raw21381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21381step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21381step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21381step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21381 raw21381Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw21381 raw21381Labels = mixedMoment B raw21381step0 raw21381step0Labels := by
      have hz : ∀ j, raw21381 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21381step0 = (fun i j => raw21381 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21381step0 raw21381; decide +kernel
      have hl : raw21381step0Labels = raw21381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21381 raw21381Labels permutation520 hz
    mixedMoment B raw21381step0 raw21381step0Labels = mixedMoment B raw21381step1 raw21381step1Labels := by
      have hz : ∀ j, raw21381step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21381step1 = (fun i j => raw21381step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21381step1 raw21381step0; decide +kernel
      have hl : raw21381step1Labels = raw21381step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21381step0 raw21381step0Labels permutation104 hz
    _ = mixedMoment B node4460 node4460Labels := by rfl

def raw21382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21382step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21382 raw21382Labels = mixedMoment B node4151 node4151Labels := by
  calc
    mixedMoment B raw21382 raw21382Labels = mixedMoment B raw21382step0 raw21382step0Labels := by
      have hz : ∀ j, raw21382 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21382step0 = (fun i j => raw21382 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21382step0 raw21382; decide +kernel
      have hl : raw21382step0Labels = raw21382Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21382 raw21382Labels permutation346 hz
    _ = mixedMoment B node4151 node4151Labels := by rfl

def raw21383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21383step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21383 raw21383Labels = mixedMoment B node4365 node4365Labels := by
  calc
    mixedMoment B raw21383 raw21383Labels = mixedMoment B raw21383step0 raw21383step0Labels := by
      have hz : ∀ j, raw21383 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21383step0 = (fun i j => raw21383 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21383step0 raw21383; decide +kernel
      have hl : raw21383step0Labels = raw21383Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21383 raw21383Labels permutation346 hz
    _ = mixedMoment B node4365 node4365Labels := by rfl

def raw21384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21384step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21384 raw21384Labels = mixedMoment B node4326 node4326Labels := by
  calc
    mixedMoment B raw21384 raw21384Labels = mixedMoment B raw21384step0 raw21384step0Labels := by
      have ha : raw21384step0 = (fun i j => raw21384 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21384step0 raw21384; decide +kernel
      have hl : raw21384step0Labels = raw21384Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21384 raw21384Labels permutation176 permutation2
    _ = mixedMoment B node4326 node4326Labels := by rfl

def raw21385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21385step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21385step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21385step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21385 raw21385Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw21385 raw21385Labels = mixedMoment B raw21385step0 raw21385step0Labels := by
      have hz : ∀ j, raw21385 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21385step0 = (fun i j => raw21385 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21385step0 raw21385; decide +kernel
      have hl : raw21385step0Labels = raw21385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21385 raw21385Labels permutation520 hz
    mixedMoment B raw21385step0 raw21385step0Labels = mixedMoment B raw21385step1 raw21385step1Labels := by
      have hz : ∀ j, raw21385step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21385step1 = (fun i j => raw21385step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21385step1 raw21385step0; decide +kernel
      have hl : raw21385step1Labels = raw21385step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21385step0 raw21385step0Labels permutation80 hz
    _ = mixedMoment B node4460 node4460Labels := by rfl

def raw21386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21386step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21386step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw21386step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21386 raw21386Labels = mixedMoment B node4160 node4160Labels := by
  calc
    mixedMoment B raw21386 raw21386Labels = mixedMoment B raw21386step0 raw21386step0Labels := by
      have hz : ∀ j, raw21386 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21386step0 = (fun i j => raw21386 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21386step0 raw21386; decide +kernel
      have hl : raw21386step0Labels = raw21386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21386 raw21386Labels permutation434 hz
    mixedMoment B raw21386step0 raw21386step0Labels = mixedMoment B raw21386step1 raw21386step1Labels := by
      have hz : ∀ j, raw21386step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21386step1 = (fun i j => raw21386step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21386step1 raw21386step0; decide +kernel
      have hl : raw21386step1Labels = raw21386step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21386step0 raw21386step0Labels permutation80 hz
    _ = mixedMoment B node4160 node4160Labels := by rfl

def raw21387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21387step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21387step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw21387step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21387 raw21387Labels = mixedMoment B node4373 node4373Labels := by
  calc
    mixedMoment B raw21387 raw21387Labels = mixedMoment B raw21387step0 raw21387step0Labels := by
      have hz : ∀ j, raw21387 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21387step0 = (fun i j => raw21387 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21387step0 raw21387; decide +kernel
      have hl : raw21387step0Labels = raw21387Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21387 raw21387Labels permutation434 hz
    mixedMoment B raw21387step0 raw21387step0Labels = mixedMoment B raw21387step1 raw21387step1Labels := by
      have hz : ∀ j, raw21387step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21387step1 = (fun i j => raw21387step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21387step1 raw21387step0; decide +kernel
      have hl : raw21387step1Labels = raw21387step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21387step0 raw21387step0Labels permutation80 hz
    _ = mixedMoment B node4373 node4373Labels := by rfl

def raw21388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21388step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw21388step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21388 raw21388Labels = mixedMoment B node4334 node4334Labels := by
  calc
    mixedMoment B raw21388 raw21388Labels = mixedMoment B raw21388step0 raw21388step0Labels := by
      have hz : ∀ j, raw21388 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21388step0 = (fun i j => raw21388 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21388step0 raw21388; decide +kernel
      have hl : raw21388step0Labels = raw21388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21388 raw21388Labels permutation434 hz
    mixedMoment B raw21388step0 raw21388step0Labels = mixedMoment B raw21388step1 raw21388step1Labels := by
      have ha : raw21388step1 = (fun i j => raw21388step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21388step1 raw21388step0; decide +kernel
      have hl : raw21388step1Labels = raw21388step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21388step0 raw21388step0Labels permutation38 permutation2
    _ = mixedMoment B node4334 node4334Labels := by rfl

def raw21389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21389step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21389step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw21389step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21389 raw21389Labels = mixedMoment B node4334 node4334Labels := by
  calc
    mixedMoment B raw21389 raw21389Labels = mixedMoment B raw21389step0 raw21389step0Labels := by
      have hz : ∀ j, raw21389 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21389step0 = (fun i j => raw21389 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21389step0 raw21389; decide +kernel
      have hl : raw21389step0Labels = raw21389Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21389 raw21389Labels permutation346 hz
    mixedMoment B raw21389step0 raw21389step0Labels = mixedMoment B raw21389step1 raw21389step1Labels := by
      have ha : raw21389step1 = (fun i j => raw21389step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21389step1 raw21389step0; decide +kernel
      have hl : raw21389step1Labels = raw21389step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21389step0 raw21389step0Labels permutation38 permutation2
    _ = mixedMoment B node4334 node4334Labels := by rfl

def raw21390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21390step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21390step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw21390step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21390 raw21390Labels = mixedMoment B node4156 node4156Labels := by
  calc
    mixedMoment B raw21390 raw21390Labels = mixedMoment B raw21390step0 raw21390step0Labels := by
      have hz : ∀ j, raw21390 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21390step0 = (fun i j => raw21390 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21390step0 raw21390; decide +kernel
      have hl : raw21390step0Labels = raw21390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21390 raw21390Labels permutation434 hz
    mixedMoment B raw21390step0 raw21390step0Labels = mixedMoment B raw21390step1 raw21390step1Labels := by
      have hz : ∀ j, raw21390step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21390step1 = (fun i j => raw21390step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21390step1 raw21390step0; decide +kernel
      have hl : raw21390step1Labels = raw21390step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21390step0 raw21390step0Labels permutation80 hz
    _ = mixedMoment B node4156 node4156Labels := by rfl

def raw21391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21391step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21391step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![4, -2, -2]]
def raw21391step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21391 raw21391Labels = mixedMoment B node4370 node4370Labels := by
  calc
    mixedMoment B raw21391 raw21391Labels = mixedMoment B raw21391step0 raw21391step0Labels := by
      have hz : ∀ j, raw21391 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21391step0 = (fun i j => raw21391 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21391step0 raw21391; decide +kernel
      have hl : raw21391step0Labels = raw21391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21391 raw21391Labels permutation434 hz
    mixedMoment B raw21391step0 raw21391step0Labels = mixedMoment B raw21391step1 raw21391step1Labels := by
      have hz : ∀ j, raw21391step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21391step1 = (fun i j => raw21391step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21391step1 raw21391step0; decide +kernel
      have hl : raw21391step1Labels = raw21391step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21391step0 raw21391step0Labels permutation80 hz
    _ = mixedMoment B node4370 node4370Labels := by rfl

def raw21392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21392step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21392step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw21392step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21392 raw21392Labels = mixedMoment B node4330 node4330Labels := by
  calc
    mixedMoment B raw21392 raw21392Labels = mixedMoment B raw21392step0 raw21392step0Labels := by
      have hz : ∀ j, raw21392 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21392step0 = (fun i j => raw21392 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21392step0 raw21392; decide +kernel
      have hl : raw21392step0Labels = raw21392Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21392 raw21392Labels permutation434 hz
    mixedMoment B raw21392step0 raw21392step0Labels = mixedMoment B raw21392step1 raw21392step1Labels := by
      have ha : raw21392step1 = (fun i j => raw21392step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21392step1 raw21392step0; decide +kernel
      have hl : raw21392step1Labels = raw21392step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21392step0 raw21392step0Labels permutation38 permutation2
    _ = mixedMoment B node4330 node4330Labels := by rfl

def raw21393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21393Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21393step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21393step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw21393step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21393 raw21393Labels = mixedMoment B node4330 node4330Labels := by
  calc
    mixedMoment B raw21393 raw21393Labels = mixedMoment B raw21393step0 raw21393step0Labels := by
      have hz : ∀ j, raw21393 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21393step0 = (fun i j => raw21393 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21393step0 raw21393; decide +kernel
      have hl : raw21393step0Labels = raw21393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21393 raw21393Labels permutation346 hz
    mixedMoment B raw21393step0 raw21393step0Labels = mixedMoment B raw21393step1 raw21393step1Labels := by
      have ha : raw21393step1 = (fun i j => raw21393step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21393step1 raw21393step0; decide +kernel
      have hl : raw21393step1Labels = raw21393step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21393step0 raw21393step0Labels permutation38 permutation2
    _ = mixedMoment B node4330 node4330Labels := by rfl

def raw21394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw21394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw21394step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21394step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![4, -2, -2]]
def raw21394step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21394step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw21394step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21394 raw21394Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw21394 raw21394Labels = mixedMoment B raw21394step0 raw21394step0Labels := by
      have hz : ∀ j, raw21394 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21394step0 = (fun i j => raw21394 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21394step0 raw21394; decide +kernel
      have hl : raw21394step0Labels = raw21394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21394 raw21394Labels permutation520 hz
    mixedMoment B raw21394step0 raw21394step0Labels = mixedMoment B raw21394step1 raw21394step1Labels := by
      have hz : ∀ j, raw21394step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21394step1 = (fun i j => raw21394step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21394step1 raw21394step0; decide +kernel
      have hl : raw21394step1Labels = raw21394step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21394step0 raw21394step0Labels permutation104 hz
    mixedMoment B raw21394step1 raw21394step1Labels = mixedMoment B raw21394step2 raw21394step2Labels := by
      have hz : ∀ j, raw21394step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw21394step2 = (fun i j => raw21394step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw21394step2 raw21394step1; decide +kernel
      have hl : raw21394step2Labels = raw21394step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21394step1 raw21394step1Labels permutation20 hz
    _ = mixedMoment B node4468 node4468Labels := by rfl

def raw21395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21395Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21395step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21395step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21395step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21395step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![-1, -1, 2], ![-3, 3, 0]]
def raw21395step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21395step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw21395step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21395 raw21395Labels = mixedMoment B node2966 node2966Labels := by
  calc
    mixedMoment B raw21395 raw21395Labels = mixedMoment B raw21395step0 raw21395step0Labels := by
      have hz : ∀ j, raw21395 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21395step0 = (fun i j => raw21395 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21395step0 raw21395; decide +kernel
      have hl : raw21395step0Labels = raw21395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21395 raw21395Labels permutation434 hz
    mixedMoment B raw21395step0 raw21395step0Labels = mixedMoment B raw21395step1 raw21395step1Labels := by
      have hz : ∀ j, raw21395step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21395step1 = (fun i j => raw21395step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21395step1 raw21395step0; decide +kernel
      have hl : raw21395step1Labels = raw21395step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21395step0 raw21395step0Labels permutation80 hz
    mixedMoment B raw21395step1 raw21395step1Labels = mixedMoment B raw21395step2 raw21395step2Labels := by
      have ha : raw21395step2 = (fun i j => raw21395step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21395step2 raw21395step1; decide +kernel
      have hl : raw21395step2Labels = raw21395step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21395step1 raw21395step1Labels permutation31 permutation3
    mixedMoment B raw21395step2 raw21395step2Labels = mixedMoment B raw21395step3 raw21395step3Labels := by
      have ha : raw21395step3 = -raw21395step2 := by apply Matrix.ext; change ∀ i j, raw21395step3 i j = -(raw21395step2 i j); unfold raw21395step3 raw21395step2; decide +kernel
      have hl : raw21395step3Labels = raw21395step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2966 node2966Labels := by rfl

def raw21396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21396Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21396step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21396step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw21396step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21396step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw21396step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21396 raw21396Labels = mixedMoment B node2941 node2941Labels := by
  calc
    mixedMoment B raw21396 raw21396Labels = mixedMoment B raw21396step0 raw21396step0Labels := by
      have hz : ∀ j, raw21396 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21396step0 = (fun i j => raw21396 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21396step0 raw21396; decide +kernel
      have hl : raw21396step0Labels = raw21396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21396 raw21396Labels permutation434 hz
    mixedMoment B raw21396step0 raw21396step0Labels = mixedMoment B raw21396step1 raw21396step1Labels := by
      have ha : raw21396step1 = (fun i j => raw21396step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21396step1 raw21396step0; decide +kernel
      have hl : raw21396step1Labels = raw21396step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21396step0 raw21396step0Labels permutation149 permutation3
    mixedMoment B raw21396step1 raw21396step1Labels = mixedMoment B raw21396step2 raw21396step2Labels := by
      have ha : raw21396step2 = -raw21396step1 := by apply Matrix.ext; change ∀ i j, raw21396step2 i j = -(raw21396step1 i j); unfold raw21396step2 raw21396step1; decide +kernel
      have hl : raw21396step2Labels = raw21396step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2941 node2941Labels := by rfl

def raw21397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21397Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21397step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw21397step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21397step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw21397step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21397 raw21397Labels = mixedMoment B node2941 node2941Labels := by
  calc
    mixedMoment B raw21397 raw21397Labels = mixedMoment B raw21397step0 raw21397step0Labels := by
      have hz : ∀ j, raw21397 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21397step0 = (fun i j => raw21397 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21397step0 raw21397; decide +kernel
      have hl : raw21397step0Labels = raw21397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21397 raw21397Labels permutation346 hz
    mixedMoment B raw21397step0 raw21397step0Labels = mixedMoment B raw21397step1 raw21397step1Labels := by
      have ha : raw21397step1 = (fun i j => raw21397step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21397step1 raw21397step0; decide +kernel
      have hl : raw21397step1Labels = raw21397step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21397step0 raw21397step0Labels permutation149 permutation3
    mixedMoment B raw21397step1 raw21397step1Labels = mixedMoment B raw21397step2 raw21397step2Labels := by
      have ha : raw21397step2 = -raw21397step1 := by apply Matrix.ext; change ∀ i j, raw21397step2 i j = -(raw21397step1 i j); unfold raw21397step2 raw21397step1; decide +kernel
      have hl : raw21397step2Labels = raw21397step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2941 node2941Labels := by rfl

def raw21398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21398Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21398step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21398step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw21398step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21398step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw21398step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21398step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-3, 3, 0]]
def raw21398step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21398step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw21398step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21398 raw21398Labels = mixedMoment B node3114 node3114Labels := by
  calc
    mixedMoment B raw21398 raw21398Labels = mixedMoment B raw21398step0 raw21398step0Labels := by
      have hz : ∀ j, raw21398 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21398step0 = (fun i j => raw21398 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21398step0 raw21398; decide +kernel
      have hl : raw21398step0Labels = raw21398Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21398 raw21398Labels permutation520 hz
    mixedMoment B raw21398step0 raw21398step0Labels = mixedMoment B raw21398step1 raw21398step1Labels := by
      have hz : ∀ j, raw21398step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21398step1 = (fun i j => raw21398step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21398step1 raw21398step0; decide +kernel
      have hl : raw21398step1Labels = raw21398step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21398step0 raw21398step0Labels permutation104 hz
    mixedMoment B raw21398step1 raw21398step1Labels = mixedMoment B raw21398step2 raw21398step2Labels := by
      have hz : ∀ j, raw21398step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw21398step2 = (fun i j => raw21398step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw21398step2 raw21398step1; decide +kernel
      have hl : raw21398step2Labels = raw21398step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21398step1 raw21398step1Labels permutation20 hz
    mixedMoment B raw21398step2 raw21398step2Labels = mixedMoment B raw21398step3 raw21398step3Labels := by
      have ha : raw21398step3 = (fun i j => raw21398step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21398step3 raw21398step2; decide +kernel
      have hl : raw21398step3Labels = raw21398step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21398step2 raw21398step2Labels permutation7 permutation3
    mixedMoment B raw21398step3 raw21398step3Labels = mixedMoment B raw21398step4 raw21398step4Labels := by
      have ha : raw21398step4 = -raw21398step3 := by apply Matrix.ext; change ∀ i j, raw21398step4 i j = -(raw21398step3 i j); unfold raw21398step4 raw21398step3; decide +kernel
      have hl : raw21398step4Labels = raw21398step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3114 node3114Labels := by rfl

def raw21399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21399Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21399step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21399step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw21399step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21399step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw21399step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21399 raw21399Labels = mixedMoment B node3230 node3230Labels := by
  calc
    mixedMoment B raw21399 raw21399Labels = mixedMoment B raw21399step0 raw21399step0Labels := by
      have hz : ∀ j, raw21399 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21399step0 = (fun i j => raw21399 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21399step0 raw21399; decide +kernel
      have hl : raw21399step0Labels = raw21399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21399 raw21399Labels permutation434 hz
    mixedMoment B raw21399step0 raw21399step0Labels = mixedMoment B raw21399step1 raw21399step1Labels := by
      have hz : ∀ j, raw21399step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21399step1 = (fun i j => raw21399step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21399step1 raw21399step0; decide +kernel
      have hl : raw21399step1Labels = raw21399step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21399step0 raw21399step0Labels permutation80 hz
    mixedMoment B raw21399step1 raw21399step1Labels = mixedMoment B raw21399step2 raw21399step2Labels := by
      have ha : raw21399step2 = (fun i j => raw21399step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21399step2 raw21399step1; decide +kernel
      have hl : raw21399step2Labels = raw21399step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21399step1 raw21399step1Labels permutation8 permutation3
    _ = mixedMoment B node3230 node3230Labels := by rfl

def raw21400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21400Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21400step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21400step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21400step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21400step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21400step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21400 raw21400Labels = mixedMoment B node647 node647Labels := by
  calc
    mixedMoment B raw21400 raw21400Labels = mixedMoment B raw21400step0 raw21400step0Labels := by
      have hz : ∀ j, raw21400 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21400step0 = (fun i j => raw21400 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21400step0 raw21400; decide +kernel
      have hl : raw21400step0Labels = raw21400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21400 raw21400Labels permutation434 hz
    mixedMoment B raw21400step0 raw21400step0Labels = mixedMoment B raw21400step1 raw21400step1Labels := by
      have hz : ∀ j, raw21400step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21400step1 = (fun i j => raw21400step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21400step1 raw21400step0; decide +kernel
      have hl : raw21400step1Labels = raw21400step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21400step0 raw21400step0Labels permutation80 hz
    mixedMoment B raw21400step1 raw21400step1Labels = mixedMoment B raw21400step2 raw21400step2Labels := by
      have ha : raw21400step2 = (fun i j => raw21400step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21400step2 raw21400step1; decide +kernel
      have hl : raw21400step2Labels = raw21400step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21400step1 raw21400step1Labels permutation8 permutation3
    _ = mixedMoment B node647 node647Labels := by rfl

def raw21401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21401Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21401step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21401step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21401step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21401 raw21401Labels = mixedMoment B node1342 node1342Labels := by
  calc
    mixedMoment B raw21401 raw21401Labels = mixedMoment B raw21401step0 raw21401step0Labels := by
      have hz : ∀ j, raw21401 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21401step0 = (fun i j => raw21401 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21401step0 raw21401; decide +kernel
      have hl : raw21401step0Labels = raw21401Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21401 raw21401Labels permutation434 hz
    mixedMoment B raw21401step0 raw21401step0Labels = mixedMoment B raw21401step1 raw21401step1Labels := by
      have ha : raw21401step1 = (fun i j => raw21401step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21401step1 raw21401step0; decide +kernel
      have hl : raw21401step1Labels = raw21401step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21401step0 raw21401step0Labels permutation38 permutation3
    _ = mixedMoment B node1342 node1342Labels := by rfl

def raw21402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21402Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21402step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21402step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21402 raw21402Labels = mixedMoment B node1342 node1342Labels := by
  calc
    mixedMoment B raw21402 raw21402Labels = mixedMoment B raw21402step0 raw21402step0Labels := by
      have hz : ∀ j, raw21402 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21402step0 = (fun i j => raw21402 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21402step0 raw21402; decide +kernel
      have hl : raw21402step0Labels = raw21402Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21402 raw21402Labels permutation346 hz
    mixedMoment B raw21402step0 raw21402step0Labels = mixedMoment B raw21402step1 raw21402step1Labels := by
      have ha : raw21402step1 = (fun i j => raw21402step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21402step1 raw21402step0; decide +kernel
      have hl : raw21402step1Labels = raw21402step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21402step0 raw21402step0Labels permutation38 permutation3
    _ = mixedMoment B node1342 node1342Labels := by rfl

def raw21403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21403Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21403step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21403step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw21403step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21403step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw21403step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21403step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![3, -2, -1]]
def raw21403step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21403 raw21403Labels = mixedMoment B node1450 node1450Labels := by
  calc
    mixedMoment B raw21403 raw21403Labels = mixedMoment B raw21403step0 raw21403step0Labels := by
      have hz : ∀ j, raw21403 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21403step0 = (fun i j => raw21403 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21403step0 raw21403; decide +kernel
      have hl : raw21403step0Labels = raw21403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21403 raw21403Labels permutation520 hz
    mixedMoment B raw21403step0 raw21403step0Labels = mixedMoment B raw21403step1 raw21403step1Labels := by
      have hz : ∀ j, raw21403step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21403step1 = (fun i j => raw21403step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21403step1 raw21403step0; decide +kernel
      have hl : raw21403step1Labels = raw21403step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21403step0 raw21403step0Labels permutation104 hz
    mixedMoment B raw21403step1 raw21403step1Labels = mixedMoment B raw21403step2 raw21403step2Labels := by
      have hz : ∀ j, raw21403step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw21403step2 = (fun i j => raw21403step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw21403step2 raw21403step1; decide +kernel
      have hl : raw21403step2Labels = raw21403step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21403step1 raw21403step1Labels permutation20 hz
    mixedMoment B raw21403step2 raw21403step2Labels = mixedMoment B raw21403step3 raw21403step3Labels := by
      have ha : raw21403step3 = (fun i j => raw21403step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21403step3 raw21403step2; decide +kernel
      have hl : raw21403step3Labels = raw21403step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21403step2 raw21403step2Labels permutation2 permutation3
    _ = mixedMoment B node1450 node1450Labels := by rfl

def raw21404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21404Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21404step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21404step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw21404step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21404step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw21404step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21404 raw21404Labels = mixedMoment B node1448 node1448Labels := by
  calc
    mixedMoment B raw21404 raw21404Labels = mixedMoment B raw21404step0 raw21404step0Labels := by
      have hz : ∀ j, raw21404 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21404step0 = (fun i j => raw21404 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21404step0 raw21404; decide +kernel
      have hl : raw21404step0Labels = raw21404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21404 raw21404Labels permutation434 hz
    mixedMoment B raw21404step0 raw21404step0Labels = mixedMoment B raw21404step1 raw21404step1Labels := by
      have hz : ∀ j, raw21404step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21404step1 = (fun i j => raw21404step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21404step1 raw21404step0; decide +kernel
      have hl : raw21404step1Labels = raw21404step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21404step0 raw21404step0Labels permutation80 hz
    mixedMoment B raw21404step1 raw21404step1Labels = mixedMoment B raw21404step2 raw21404step2Labels := by
      have ha : raw21404step2 = (fun i j => raw21404step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21404step2 raw21404step1; decide +kernel
      have hl : raw21404step2Labels = raw21404step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21404step1 raw21404step1Labels permutation8 permutation3
    _ = mixedMoment B node1448 node1448Labels := by rfl

def raw21405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21405Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21405step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21405step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21405step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21405 raw21405Labels = mixedMoment B node630 node630Labels := by
  calc
    mixedMoment B raw21405 raw21405Labels = mixedMoment B raw21405step0 raw21405step0Labels := by
      have hz : ∀ j, raw21405 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21405step0 = (fun i j => raw21405 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21405step0 raw21405; decide +kernel
      have hl : raw21405step0Labels = raw21405Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21405 raw21405Labels permutation434 hz
    mixedMoment B raw21405step0 raw21405step0Labels = mixedMoment B raw21405step1 raw21405step1Labels := by
      have ha : raw21405step1 = (fun i j => raw21405step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21405step1 raw21405step0; decide +kernel
      have hl : raw21405step1Labels = raw21405step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21405step0 raw21405step0Labels permutation32 permutation3
    _ = mixedMoment B node630 node630Labels := by rfl

def raw21406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21406Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21406step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21406step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21406step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21406 raw21406Labels = mixedMoment B node1320 node1320Labels := by
  calc
    mixedMoment B raw21406 raw21406Labels = mixedMoment B raw21406step0 raw21406step0Labels := by
      have hz : ∀ j, raw21406 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21406step0 = (fun i j => raw21406 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21406step0 raw21406; decide +kernel
      have hl : raw21406step0Labels = raw21406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21406 raw21406Labels permutation434 hz
    mixedMoment B raw21406step0 raw21406step0Labels = mixedMoment B raw21406step1 raw21406step1Labels := by
      have ha : raw21406step1 = (fun i j => raw21406step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21406step1 raw21406step0; decide +kernel
      have hl : raw21406step1Labels = raw21406step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21406step0 raw21406step0Labels permutation32 permutation3
    _ = mixedMoment B node1320 node1320Labels := by rfl

def raw21407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21407Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21407step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21407 raw21407Labels = mixedMoment B node1329 node1329Labels := by
  calc
    mixedMoment B raw21407 raw21407Labels = mixedMoment B raw21407step0 raw21407step0Labels := by
      have ha : raw21407step0 = (fun i j => raw21407 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21407step0 raw21407; decide +kernel
      have hl : raw21407step0Labels = raw21407Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21407 raw21407Labels permutation200 permutation3
    _ = mixedMoment B node1329 node1329Labels := by rfl

def raw21408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21408Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21408step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21408step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21408step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21408step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21408 raw21408Labels = mixedMoment B node1416 node1416Labels := by
  calc
    mixedMoment B raw21408 raw21408Labels = mixedMoment B raw21408step0 raw21408step0Labels := by
      have hz : ∀ j, raw21408 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21408step0 = (fun i j => raw21408 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21408step0 raw21408; decide +kernel
      have hl : raw21408step0Labels = raw21408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21408 raw21408Labels permutation520 hz
    mixedMoment B raw21408step0 raw21408step0Labels = mixedMoment B raw21408step1 raw21408step1Labels := by
      have hz : ∀ j, raw21408step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21408step1 = (fun i j => raw21408step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21408step1 raw21408step0; decide +kernel
      have hl : raw21408step1Labels = raw21408step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21408step0 raw21408step0Labels permutation104 hz
    mixedMoment B raw21408step1 raw21408step1Labels = mixedMoment B raw21408step2 raw21408step2Labels := by
      have ha : raw21408step2 = (fun i j => raw21408step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21408step2 raw21408step1; decide +kernel
      have hl : raw21408step2Labels = raw21408step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21408step1 raw21408step1Labels permutation8 permutation3
    _ = mixedMoment B node1416 node1416Labels := by rfl

def raw21409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21409Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21409step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21409step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw21409step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21409 raw21409Labels = mixedMoment B node1414 node1414Labels := by
  calc
    mixedMoment B raw21409 raw21409Labels = mixedMoment B raw21409step0 raw21409step0Labels := by
      have hz : ∀ j, raw21409 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21409step0 = (fun i j => raw21409 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21409step0 raw21409; decide +kernel
      have hl : raw21409step0Labels = raw21409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21409 raw21409Labels permutation434 hz
    mixedMoment B raw21409step0 raw21409step0Labels = mixedMoment B raw21409step1 raw21409step1Labels := by
      have ha : raw21409step1 = (fun i j => raw21409step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21409step1 raw21409step0; decide +kernel
      have hl : raw21409step1Labels = raw21409step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21409step0 raw21409step0Labels permutation32 permutation3
    _ = mixedMoment B node1414 node1414Labels := by rfl

def raw21410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21410Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21410step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21410step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21410step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21410 raw21410Labels = mixedMoment B node630 node630Labels := by
  calc
    mixedMoment B raw21410 raw21410Labels = mixedMoment B raw21410step0 raw21410step0Labels := by
      have hz : ∀ j, raw21410 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21410step0 = (fun i j => raw21410 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21410step0 raw21410; decide +kernel
      have hl : raw21410step0Labels = raw21410Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21410 raw21410Labels permutation346 hz
    mixedMoment B raw21410step0 raw21410step0Labels = mixedMoment B raw21410step1 raw21410step1Labels := by
      have ha : raw21410step1 = (fun i j => raw21410step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21410step1 raw21410step0; decide +kernel
      have hl : raw21410step1Labels = raw21410step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21410step0 raw21410step0Labels permutation32 permutation3
    _ = mixedMoment B node630 node630Labels := by rfl

def raw21411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21411Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21411step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21411step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21411step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21411 raw21411Labels = mixedMoment B node1320 node1320Labels := by
  calc
    mixedMoment B raw21411 raw21411Labels = mixedMoment B raw21411step0 raw21411step0Labels := by
      have hz : ∀ j, raw21411 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21411step0 = (fun i j => raw21411 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21411step0 raw21411; decide +kernel
      have hl : raw21411step0Labels = raw21411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21411 raw21411Labels permutation346 hz
    mixedMoment B raw21411step0 raw21411step0Labels = mixedMoment B raw21411step1 raw21411step1Labels := by
      have ha : raw21411step1 = (fun i j => raw21411step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21411step1 raw21411step0; decide +kernel
      have hl : raw21411step1Labels = raw21411step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21411step0 raw21411step0Labels permutation32 permutation3
    _ = mixedMoment B node1320 node1320Labels := by rfl

def raw21412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21412Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21412step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21412 raw21412Labels = mixedMoment B node1329 node1329Labels := by
  calc
    mixedMoment B raw21412 raw21412Labels = mixedMoment B raw21412step0 raw21412step0Labels := by
      have ha : raw21412step0 = (fun i j => raw21412 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21412step0 raw21412; decide +kernel
      have hl : raw21412step0Labels = raw21412Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21412 raw21412Labels permutation176 permutation3
    _ = mixedMoment B node1329 node1329Labels := by rfl

def raw21413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21413Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21413step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21413step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21413step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21413step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21413step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21413 raw21413Labels = mixedMoment B node1416 node1416Labels := by
  calc
    mixedMoment B raw21413 raw21413Labels = mixedMoment B raw21413step0 raw21413step0Labels := by
      have hz : ∀ j, raw21413 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21413step0 = (fun i j => raw21413 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21413step0 raw21413; decide +kernel
      have hl : raw21413step0Labels = raw21413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21413 raw21413Labels permutation520 hz
    mixedMoment B raw21413step0 raw21413step0Labels = mixedMoment B raw21413step1 raw21413step1Labels := by
      have hz : ∀ j, raw21413step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21413step1 = (fun i j => raw21413step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21413step1 raw21413step0; decide +kernel
      have hl : raw21413step1Labels = raw21413step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21413step0 raw21413step0Labels permutation80 hz
    mixedMoment B raw21413step1 raw21413step1Labels = mixedMoment B raw21413step2 raw21413step2Labels := by
      have ha : raw21413step2 = (fun i j => raw21413step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21413step2 raw21413step1; decide +kernel
      have hl : raw21413step2Labels = raw21413step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21413step1 raw21413step1Labels permutation8 permutation3
    _ = mixedMoment B node1416 node1416Labels := by rfl

def raw21414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21414Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21414step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21414step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw21414step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21414 raw21414Labels = mixedMoment B node1414 node1414Labels := by
  calc
    mixedMoment B raw21414 raw21414Labels = mixedMoment B raw21414step0 raw21414step0Labels := by
      have hz : ∀ j, raw21414 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21414step0 = (fun i j => raw21414 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21414step0 raw21414; decide +kernel
      have hl : raw21414step0Labels = raw21414Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21414 raw21414Labels permutation346 hz
    mixedMoment B raw21414step0 raw21414step0Labels = mixedMoment B raw21414step1 raw21414step1Labels := by
      have ha : raw21414step1 = (fun i j => raw21414step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21414step1 raw21414step0; decide +kernel
      have hl : raw21414step1Labels = raw21414step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21414step0 raw21414step0Labels permutation32 permutation3
    _ = mixedMoment B node1414 node1414Labels := by rfl

def raw21415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21415Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21415step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21415step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw21415step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21415step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw21415step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21415 raw21415Labels = mixedMoment B node636 node636Labels := by
  calc
    mixedMoment B raw21415 raw21415Labels = mixedMoment B raw21415step0 raw21415step0Labels := by
      have hz : ∀ j, raw21415 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21415step0 = (fun i j => raw21415 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21415step0 raw21415; decide +kernel
      have hl : raw21415step0Labels = raw21415Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21415 raw21415Labels permutation434 hz
    mixedMoment B raw21415step0 raw21415step0Labels = mixedMoment B raw21415step1 raw21415step1Labels := by
      have hz : ∀ j, raw21415step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21415step1 = (fun i j => raw21415step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21415step1 raw21415step0; decide +kernel
      have hl : raw21415step1Labels = raw21415step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21415step0 raw21415step0Labels permutation80 hz
    mixedMoment B raw21415step1 raw21415step1Labels = mixedMoment B raw21415step2 raw21415step2Labels := by
      have ha : raw21415step2 = (fun i j => raw21415step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21415step2 raw21415step1; decide +kernel
      have hl : raw21415step2Labels = raw21415step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21415step1 raw21415step1Labels permutation8 permutation3
    _ = mixedMoment B node636 node636Labels := by rfl

def raw21416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21416Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21416step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21416step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw21416step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21416step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw21416step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21416 raw21416Labels = mixedMoment B node1325 node1325Labels := by
  calc
    mixedMoment B raw21416 raw21416Labels = mixedMoment B raw21416step0 raw21416step0Labels := by
      have hz : ∀ j, raw21416 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21416step0 = (fun i j => raw21416 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21416step0 raw21416; decide +kernel
      have hl : raw21416step0Labels = raw21416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21416 raw21416Labels permutation434 hz
    mixedMoment B raw21416step0 raw21416step0Labels = mixedMoment B raw21416step1 raw21416step1Labels := by
      have hz : ∀ j, raw21416step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21416step1 = (fun i j => raw21416step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21416step1 raw21416step0; decide +kernel
      have hl : raw21416step1Labels = raw21416step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21416step0 raw21416step0Labels permutation80 hz
    mixedMoment B raw21416step1 raw21416step1Labels = mixedMoment B raw21416step2 raw21416step2Labels := by
      have ha : raw21416step2 = (fun i j => raw21416step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21416step2 raw21416step1; decide +kernel
      have hl : raw21416step2Labels = raw21416step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21416step1 raw21416step1Labels permutation8 permutation3
    _ = mixedMoment B node1325 node1325Labels := by rfl

def raw21417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21417Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21417step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21417step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw21417step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21417 raw21417Labels = mixedMoment B node1334 node1334Labels := by
  calc
    mixedMoment B raw21417 raw21417Labels = mixedMoment B raw21417step0 raw21417step0Labels := by
      have hz : ∀ j, raw21417 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21417step0 = (fun i j => raw21417 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21417step0 raw21417; decide +kernel
      have hl : raw21417step0Labels = raw21417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21417 raw21417Labels permutation434 hz
    mixedMoment B raw21417step0 raw21417step0Labels = mixedMoment B raw21417step1 raw21417step1Labels := by
      have ha : raw21417step1 = (fun i j => raw21417step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21417step1 raw21417step0; decide +kernel
      have hl : raw21417step1Labels = raw21417step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21417step0 raw21417step0Labels permutation38 permutation3
    _ = mixedMoment B node1334 node1334Labels := by rfl

def raw21418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21418Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21418step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw21418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21418 raw21418Labels = mixedMoment B node1334 node1334Labels := by
  calc
    mixedMoment B raw21418 raw21418Labels = mixedMoment B raw21418step0 raw21418step0Labels := by
      have hz : ∀ j, raw21418 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21418step0 = (fun i j => raw21418 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21418step0 raw21418; decide +kernel
      have hl : raw21418step0Labels = raw21418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21418 raw21418Labels permutation346 hz
    mixedMoment B raw21418step0 raw21418step0Labels = mixedMoment B raw21418step1 raw21418step1Labels := by
      have ha : raw21418step1 = (fun i j => raw21418step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21418step1 raw21418step0; decide +kernel
      have hl : raw21418step1Labels = raw21418step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21418step0 raw21418step0Labels permutation38 permutation3
    _ = mixedMoment B node1334 node1334Labels := by rfl

def raw21419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw21419Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw21419step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21419step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw21419step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21419step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw21419step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21419 raw21419Labels = mixedMoment B node1419 node1419Labels := by
  calc
    mixedMoment B raw21419 raw21419Labels = mixedMoment B raw21419step0 raw21419step0Labels := by
      have hz : ∀ j, raw21419 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21419step0 = (fun i j => raw21419 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21419step0 raw21419; decide +kernel
      have hl : raw21419step0Labels = raw21419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21419 raw21419Labels permutation434 hz
    mixedMoment B raw21419step0 raw21419step0Labels = mixedMoment B raw21419step1 raw21419step1Labels := by
      have hz : ∀ j, raw21419step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21419step1 = (fun i j => raw21419step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21419step1 raw21419step0; decide +kernel
      have hl : raw21419step1Labels = raw21419step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21419step0 raw21419step0Labels permutation80 hz
    mixedMoment B raw21419step1 raw21419step1Labels = mixedMoment B raw21419step2 raw21419step2Labels := by
      have ha : raw21419step2 = (fun i j => raw21419step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21419step2 raw21419step1; decide +kernel
      have hl : raw21419step2Labels = raw21419step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21419step1 raw21419step1Labels permutation9 permutation3
    _ = mixedMoment B node1419 node1419Labels := by rfl

def raw21420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21420Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21420step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21420step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw21420step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21420step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw21420step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21420 raw21420Labels = mixedMoment B node633 node633Labels := by
  calc
    mixedMoment B raw21420 raw21420Labels = mixedMoment B raw21420step0 raw21420step0Labels := by
      have hz : ∀ j, raw21420 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21420step0 = (fun i j => raw21420 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21420step0 raw21420; decide +kernel
      have hl : raw21420step0Labels = raw21420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21420 raw21420Labels permutation434 hz
    mixedMoment B raw21420step0 raw21420step0Labels = mixedMoment B raw21420step1 raw21420step1Labels := by
      have hz : ∀ j, raw21420step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21420step1 = (fun i j => raw21420step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21420step1 raw21420step0; decide +kernel
      have hl : raw21420step1Labels = raw21420step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21420step0 raw21420step0Labels permutation80 hz
    mixedMoment B raw21420step1 raw21420step1Labels = mixedMoment B raw21420step2 raw21420step2Labels := by
      have ha : raw21420step2 = (fun i j => raw21420step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21420step2 raw21420step1; decide +kernel
      have hl : raw21420step2Labels = raw21420step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21420step1 raw21420step1Labels permutation8 permutation3
    _ = mixedMoment B node633 node633Labels := by rfl

def raw21421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21421Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21421step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21421step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![4, -2, -2]]
def raw21421step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21421step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, -1, 2], ![-4, 3, 1]]
def raw21421step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21421step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![4, -3, -1]]
def raw21421step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21421 raw21421Labels = mixedMoment B node1142 node1142Labels := by
  calc
    mixedMoment B raw21421 raw21421Labels = mixedMoment B raw21421step0 raw21421step0Labels := by
      have hz : ∀ j, raw21421 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21421step0 = (fun i j => raw21421 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21421step0 raw21421; decide +kernel
      have hl : raw21421step0Labels = raw21421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21421 raw21421Labels permutation434 hz
    mixedMoment B raw21421step0 raw21421step0Labels = mixedMoment B raw21421step1 raw21421step1Labels := by
      have hz : ∀ j, raw21421step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21421step1 = (fun i j => raw21421step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21421step1 raw21421step0; decide +kernel
      have hl : raw21421step1Labels = raw21421step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21421step0 raw21421step0Labels permutation80 hz
    mixedMoment B raw21421step1 raw21421step1Labels = mixedMoment B raw21421step2 raw21421step2Labels := by
      have ha : raw21421step2 = (fun i j => raw21421step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21421step2 raw21421step1; decide +kernel
      have hl : raw21421step2Labels = raw21421step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21421step1 raw21421step1Labels permutation31 permutation3
    mixedMoment B raw21421step2 raw21421step2Labels = mixedMoment B raw21421step3 raw21421step3Labels := by
      have ha : raw21421step3 = -raw21421step2 := by apply Matrix.ext; change ∀ i j, raw21421step3 i j = -(raw21421step2 i j); unfold raw21421step3 raw21421step2; decide +kernel
      have hl : raw21421step3Labels = raw21421step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1142 node1142Labels := by rfl

def raw21422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21422Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21422step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21422step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 3, 1]]
def raw21422step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21422step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw21422step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21422 raw21422Labels = mixedMoment B node1118 node1118Labels := by
  calc
    mixedMoment B raw21422 raw21422Labels = mixedMoment B raw21422step0 raw21422step0Labels := by
      have hz : ∀ j, raw21422 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21422step0 = (fun i j => raw21422 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21422step0 raw21422; decide +kernel
      have hl : raw21422step0Labels = raw21422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21422 raw21422Labels permutation434 hz
    mixedMoment B raw21422step0 raw21422step0Labels = mixedMoment B raw21422step1 raw21422step1Labels := by
      have ha : raw21422step1 = (fun i j => raw21422step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21422step1 raw21422step0; decide +kernel
      have hl : raw21422step1Labels = raw21422step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21422step0 raw21422step0Labels permutation149 permutation3
    mixedMoment B raw21422step1 raw21422step1Labels = mixedMoment B raw21422step2 raw21422step2Labels := by
      have ha : raw21422step2 = -raw21422step1 := by apply Matrix.ext; change ∀ i j, raw21422step2 i j = -(raw21422step1 i j); unfold raw21422step2 raw21422step1; decide +kernel
      have hl : raw21422step2Labels = raw21422step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1118 node1118Labels := by rfl

def raw21423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21423Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21423step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21423step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 3, 1]]
def raw21423step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21423step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw21423step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21423 raw21423Labels = mixedMoment B node1118 node1118Labels := by
  calc
    mixedMoment B raw21423 raw21423Labels = mixedMoment B raw21423step0 raw21423step0Labels := by
      have hz : ∀ j, raw21423 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21423step0 = (fun i j => raw21423 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21423step0 raw21423; decide +kernel
      have hl : raw21423step0Labels = raw21423Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21423 raw21423Labels permutation346 hz
    mixedMoment B raw21423step0 raw21423step0Labels = mixedMoment B raw21423step1 raw21423step1Labels := by
      have ha : raw21423step1 = (fun i j => raw21423step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21423step1 raw21423step0; decide +kernel
      have hl : raw21423step1Labels = raw21423step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21423step0 raw21423step0Labels permutation149 permutation3
    mixedMoment B raw21423step1 raw21423step1Labels = mixedMoment B raw21423step2 raw21423step2Labels := by
      have ha : raw21423step2 = -raw21423step1 := by apply Matrix.ext; change ∀ i j, raw21423step2 i j = -(raw21423step1 i j); unfold raw21423step2 raw21423step1; decide +kernel
      have hl : raw21423step2Labels = raw21423step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1118 node1118Labels := by rfl

def raw21424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw21424Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw21424step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21424step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![4, -2, -2]]
def raw21424step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21424step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw21424step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21424step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![0, -1, 1], ![-4, 3, 1]]
def raw21424step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21424step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw21424step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21424 raw21424Labels = mixedMoment B node1275 node1275Labels := by
  calc
    mixedMoment B raw21424 raw21424Labels = mixedMoment B raw21424step0 raw21424step0Labels := by
      have hz : ∀ j, raw21424 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21424step0 = (fun i j => raw21424 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21424step0 raw21424; decide +kernel
      have hl : raw21424step0Labels = raw21424Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21424 raw21424Labels permutation520 hz
    mixedMoment B raw21424step0 raw21424step0Labels = mixedMoment B raw21424step1 raw21424step1Labels := by
      have hz : ∀ j, raw21424step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21424step1 = (fun i j => raw21424step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21424step1 raw21424step0; decide +kernel
      have hl : raw21424step1Labels = raw21424step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21424step0 raw21424step0Labels permutation104 hz
    mixedMoment B raw21424step1 raw21424step1Labels = mixedMoment B raw21424step2 raw21424step2Labels := by
      have hz : ∀ j, raw21424step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw21424step2 = (fun i j => raw21424step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw21424step2 raw21424step1; decide +kernel
      have hl : raw21424step2Labels = raw21424step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21424step1 raw21424step1Labels permutation20 hz
    mixedMoment B raw21424step2 raw21424step2Labels = mixedMoment B raw21424step3 raw21424step3Labels := by
      have ha : raw21424step3 = (fun i j => raw21424step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21424step3 raw21424step2; decide +kernel
      have hl : raw21424step3Labels = raw21424step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21424step2 raw21424step2Labels permutation7 permutation3
    mixedMoment B raw21424step3 raw21424step3Labels = mixedMoment B raw21424step4 raw21424step4Labels := by
      have ha : raw21424step4 = -raw21424step3 := by apply Matrix.ext; change ∀ i j, raw21424step4 i j = -(raw21424step3 i j); unfold raw21424step4 raw21424step3; decide +kernel
      have hl : raw21424step4Labels = raw21424step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1275 node1275Labels := by rfl

def raw21425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21425Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21425step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21425step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21425step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21425step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw21425step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21425step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw21425step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21425step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw21425step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21425 raw21425Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw21425 raw21425Labels = mixedMoment B raw21425step0 raw21425step0Labels := by
      have hz : ∀ j, raw21425 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21425step0 = (fun i j => raw21425 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21425step0 raw21425; decide +kernel
      have hl : raw21425step0Labels = raw21425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21425 raw21425Labels permutation434 hz
    mixedMoment B raw21425step0 raw21425step0Labels = mixedMoment B raw21425step1 raw21425step1Labels := by
      have hz : ∀ j, raw21425step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21425step1 = (fun i j => raw21425step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21425step1 raw21425step0; decide +kernel
      have hl : raw21425step1Labels = raw21425step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21425step0 raw21425step0Labels permutation80 hz
    mixedMoment B raw21425step1 raw21425step1Labels = mixedMoment B raw21425step2 raw21425step2Labels := by
      have ha : raw21425step2 = (fun i j => raw21425step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21425step2 raw21425step1; decide +kernel
      have hl : raw21425step2Labels = raw21425step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21425step1 raw21425step1Labels permutation10 permutation7
    mixedMoment B raw21425step2 raw21425step2Labels = mixedMoment B raw21425step3 raw21425step3Labels := by
      have ha : raw21425step3 = -raw21425step2 := by apply Matrix.ext; change ∀ i j, raw21425step3 i j = -(raw21425step2 i j); unfold raw21425step3 raw21425step2; decide +kernel
      have hl : raw21425step3Labels = raw21425step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21425step3 raw21425step3Labels = mixedMoment B raw21425step4 raw21425step4Labels := by
      have ha : raw21425step4 = raw21425step3 := by apply Matrix.ext; unfold raw21425step4 raw21425step3; decide +kernel
      have hl : raw21425step3Labels = labelEmbedding1 ∘ raw21425step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21425step3 raw21425step3Labels raw21425step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2261 node2261Labels := by rfl

def raw21426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21426Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21426step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21426step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw21426step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21426step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21426step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21426step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21426step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21426 raw21426Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw21426 raw21426Labels = mixedMoment B raw21426step0 raw21426step0Labels := by
      have hz : ∀ j, raw21426 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21426step0 = (fun i j => raw21426 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21426step0 raw21426; decide +kernel
      have hl : raw21426step0Labels = raw21426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21426 raw21426Labels permutation434 hz
    mixedMoment B raw21426step0 raw21426step0Labels = mixedMoment B raw21426step1 raw21426step1Labels := by
      have ha : raw21426step1 = (fun i j => raw21426step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21426step1 raw21426step0; decide +kernel
      have hl : raw21426step1Labels = raw21426step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21426step0 raw21426step0Labels permutation40 permutation7
    mixedMoment B raw21426step1 raw21426step1Labels = mixedMoment B raw21426step2 raw21426step2Labels := by
      have ha : raw21426step2 = -raw21426step1 := by apply Matrix.ext; change ∀ i j, raw21426step2 i j = -(raw21426step1 i j); unfold raw21426step2 raw21426step1; decide +kernel
      have hl : raw21426step2Labels = raw21426step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21426step2 raw21426step2Labels = mixedMoment B raw21426step3 raw21426step3Labels := by
      have ha : raw21426step3 = raw21426step2 := by apply Matrix.ext; unfold raw21426step3 raw21426step2; decide +kernel
      have hl : raw21426step2Labels = labelEmbedding1 ∘ raw21426step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21426step2 raw21426step2Labels raw21426step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

def raw21427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21427Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21427step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21427step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw21427step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21427step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21427step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21427step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21427step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21427 raw21427Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw21427 raw21427Labels = mixedMoment B raw21427step0 raw21427step0Labels := by
      have hz : ∀ j, raw21427 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21427step0 = (fun i j => raw21427 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21427step0 raw21427; decide +kernel
      have hl : raw21427step0Labels = raw21427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21427 raw21427Labels permutation346 hz
    mixedMoment B raw21427step0 raw21427step0Labels = mixedMoment B raw21427step1 raw21427step1Labels := by
      have ha : raw21427step1 = (fun i j => raw21427step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21427step1 raw21427step0; decide +kernel
      have hl : raw21427step1Labels = raw21427step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21427step0 raw21427step0Labels permutation40 permutation7
    mixedMoment B raw21427step1 raw21427step1Labels = mixedMoment B raw21427step2 raw21427step2Labels := by
      have ha : raw21427step2 = -raw21427step1 := by apply Matrix.ext; change ∀ i j, raw21427step2 i j = -(raw21427step1 i j); unfold raw21427step2 raw21427step1; decide +kernel
      have hl : raw21427step2Labels = raw21427step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21427step2 raw21427step2Labels = mixedMoment B raw21427step3 raw21427step3Labels := by
      have ha : raw21427step3 = raw21427step2 := by apply Matrix.ext; unfold raw21427step3 raw21427step2; decide +kernel
      have hl : raw21427step2Labels = labelEmbedding1 ∘ raw21427step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21427step2 raw21427step2Labels raw21427step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

def raw21428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21428Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21428step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21428step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw21428step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21428step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw21428step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21428step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-2, -1, 3]]
def raw21428step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21428step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw21428step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21428step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw21428step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21428 raw21428Labels = mixedMoment B node2292 node2292Labels := by
  calc
    mixedMoment B raw21428 raw21428Labels = mixedMoment B raw21428step0 raw21428step0Labels := by
      have hz : ∀ j, raw21428 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21428step0 = (fun i j => raw21428 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21428step0 raw21428; decide +kernel
      have hl : raw21428step0Labels = raw21428Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21428 raw21428Labels permutation520 hz
    mixedMoment B raw21428step0 raw21428step0Labels = mixedMoment B raw21428step1 raw21428step1Labels := by
      have hz : ∀ j, raw21428step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21428step1 = (fun i j => raw21428step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21428step1 raw21428step0; decide +kernel
      have hl : raw21428step1Labels = raw21428step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21428step0 raw21428step0Labels permutation104 hz
    mixedMoment B raw21428step1 raw21428step1Labels = mixedMoment B raw21428step2 raw21428step2Labels := by
      have hz : ∀ j, raw21428step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw21428step2 = (fun i j => raw21428step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw21428step2 raw21428step1; decide +kernel
      have hl : raw21428step2Labels = raw21428step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21428step1 raw21428step1Labels permutation20 hz
    mixedMoment B raw21428step2 raw21428step2Labels = mixedMoment B raw21428step3 raw21428step3Labels := by
      have ha : raw21428step3 = (fun i j => raw21428step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21428step3 raw21428step2; decide +kernel
      have hl : raw21428step3Labels = raw21428step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21428step2 raw21428step2Labels permutation2 permutation7
    mixedMoment B raw21428step3 raw21428step3Labels = mixedMoment B raw21428step4 raw21428step4Labels := by
      have ha : raw21428step4 = -raw21428step3 := by apply Matrix.ext; change ∀ i j, raw21428step4 i j = -(raw21428step3 i j); unfold raw21428step4 raw21428step3; decide +kernel
      have hl : raw21428step4Labels = raw21428step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21428step4 raw21428step4Labels = mixedMoment B raw21428step5 raw21428step5Labels := by
      have ha : raw21428step5 = raw21428step4 := by apply Matrix.ext; unfold raw21428step5 raw21428step4; decide +kernel
      have hl : raw21428step4Labels = labelEmbedding1 ∘ raw21428step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21428step4 raw21428step4Labels raw21428step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2292 node2292Labels := by rfl

def raw21429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21429Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21429step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21429step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw21429step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21429step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw21429step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21429step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw21429step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21429step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw21429step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21429 raw21429Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw21429 raw21429Labels = mixedMoment B raw21429step0 raw21429step0Labels := by
      have hz : ∀ j, raw21429 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21429step0 = (fun i j => raw21429 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21429step0 raw21429; decide +kernel
      have hl : raw21429step0Labels = raw21429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21429 raw21429Labels permutation434 hz
    mixedMoment B raw21429step0 raw21429step0Labels = mixedMoment B raw21429step1 raw21429step1Labels := by
      have hz : ∀ j, raw21429step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21429step1 = (fun i j => raw21429step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21429step1 raw21429step0; decide +kernel
      have hl : raw21429step1Labels = raw21429step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21429step0 raw21429step0Labels permutation80 hz
    mixedMoment B raw21429step1 raw21429step1Labels = mixedMoment B raw21429step2 raw21429step2Labels := by
      have ha : raw21429step2 = (fun i j => raw21429step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21429step2 raw21429step1; decide +kernel
      have hl : raw21429step2Labels = raw21429step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21429step1 raw21429step1Labels permutation10 permutation7
    mixedMoment B raw21429step2 raw21429step2Labels = mixedMoment B raw21429step3 raw21429step3Labels := by
      have ha : raw21429step3 = -raw21429step2 := by apply Matrix.ext; change ∀ i j, raw21429step3 i j = -(raw21429step2 i j); unfold raw21429step3 raw21429step2; decide +kernel
      have hl : raw21429step3Labels = raw21429step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21429step3 raw21429step3Labels = mixedMoment B raw21429step4 raw21429step4Labels := by
      have ha : raw21429step4 = raw21429step3 := by apply Matrix.ext; unfold raw21429step4 raw21429step3; decide +kernel
      have hl : raw21429step3Labels = labelEmbedding1 ∘ raw21429step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21429step3 raw21429step3Labels raw21429step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2264 node2264Labels := by rfl

def raw21430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21430Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21430step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21430step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21430step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21430step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21430step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21430step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21430step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21430step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21430step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21430 raw21430Labels = mixedMoment B node1518 node1518Labels := by
  calc
    mixedMoment B raw21430 raw21430Labels = mixedMoment B raw21430step0 raw21430step0Labels := by
      have hz : ∀ j, raw21430 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21430step0 = (fun i j => raw21430 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21430step0 raw21430; decide +kernel
      have hl : raw21430step0Labels = raw21430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21430 raw21430Labels permutation434 hz
    mixedMoment B raw21430step0 raw21430step0Labels = mixedMoment B raw21430step1 raw21430step1Labels := by
      have hz : ∀ j, raw21430step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21430step1 = (fun i j => raw21430step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21430step1 raw21430step0; decide +kernel
      have hl : raw21430step1Labels = raw21430step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21430step0 raw21430step0Labels permutation80 hz
    mixedMoment B raw21430step1 raw21430step1Labels = mixedMoment B raw21430step2 raw21430step2Labels := by
      have ha : raw21430step2 = (fun i j => raw21430step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21430step2 raw21430step1; decide +kernel
      have hl : raw21430step2Labels = raw21430step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21430step1 raw21430step1Labels permutation10 permutation7
    mixedMoment B raw21430step2 raw21430step2Labels = mixedMoment B raw21430step3 raw21430step3Labels := by
      have ha : raw21430step3 = -raw21430step2 := by apply Matrix.ext; change ∀ i j, raw21430step3 i j = -(raw21430step2 i j); unfold raw21430step3 raw21430step2; decide +kernel
      have hl : raw21430step3Labels = raw21430step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21430step3 raw21430step3Labels = mixedMoment B raw21430step4 raw21430step4Labels := by
      have ha : raw21430step4 = raw21430step3 := by apply Matrix.ext; unfold raw21430step4 raw21430step3; decide +kernel
      have hl : raw21430step3Labels = labelEmbedding1 ∘ raw21430step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21430step3 raw21430step3Labels raw21430step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1518 node1518Labels := by rfl

def raw21431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21431Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21431step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21431step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21431step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21431step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21431step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21431step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21431 raw21431Labels = mixedMoment B node1674 node1674Labels := by
  calc
    mixedMoment B raw21431 raw21431Labels = mixedMoment B raw21431step0 raw21431step0Labels := by
      have hz : ∀ j, raw21431 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21431step0 = (fun i j => raw21431 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21431step0 raw21431; decide +kernel
      have hl : raw21431step0Labels = raw21431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21431 raw21431Labels permutation434 hz
    mixedMoment B raw21431step0 raw21431step0Labels = mixedMoment B raw21431step1 raw21431step1Labels := by
      have ha : raw21431step1 = (fun i j => raw21431step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21431step1 raw21431step0; decide +kernel
      have hl : raw21431step1Labels = raw21431step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21431step0 raw21431step0Labels permutation40 permutation7
    mixedMoment B raw21431step1 raw21431step1Labels = mixedMoment B raw21431step2 raw21431step2Labels := by
      have ha : raw21431step2 = -raw21431step1 := by apply Matrix.ext; change ∀ i j, raw21431step2 i j = -(raw21431step1 i j); unfold raw21431step2 raw21431step1; decide +kernel
      have hl : raw21431step2Labels = raw21431step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21431step2 raw21431step2Labels = mixedMoment B raw21431step3 raw21431step3Labels := by
      have ha : raw21431step3 = raw21431step2 := by apply Matrix.ext; unfold raw21431step3 raw21431step2; decide +kernel
      have hl : raw21431step2Labels = labelEmbedding1 ∘ raw21431step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21431step2 raw21431step2Labels raw21431step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1674 node1674Labels := by rfl

def raw21432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21432Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21432step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21432step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw21432step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21432step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21432step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21432step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw21432step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21432 raw21432Labels = mixedMoment B node1674 node1674Labels := by
  calc
    mixedMoment B raw21432 raw21432Labels = mixedMoment B raw21432step0 raw21432step0Labels := by
      have hz : ∀ j, raw21432 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21432step0 = (fun i j => raw21432 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21432step0 raw21432; decide +kernel
      have hl : raw21432step0Labels = raw21432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21432 raw21432Labels permutation346 hz
    mixedMoment B raw21432step0 raw21432step0Labels = mixedMoment B raw21432step1 raw21432step1Labels := by
      have ha : raw21432step1 = (fun i j => raw21432step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21432step1 raw21432step0; decide +kernel
      have hl : raw21432step1Labels = raw21432step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21432step0 raw21432step0Labels permutation40 permutation7
    mixedMoment B raw21432step1 raw21432step1Labels = mixedMoment B raw21432step2 raw21432step2Labels := by
      have ha : raw21432step2 = -raw21432step1 := by apply Matrix.ext; change ∀ i j, raw21432step2 i j = -(raw21432step1 i j); unfold raw21432step2 raw21432step1; decide +kernel
      have hl : raw21432step2Labels = raw21432step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21432step2 raw21432step2Labels = mixedMoment B raw21432step3 raw21432step3Labels := by
      have ha : raw21432step3 = raw21432step2 := by apply Matrix.ext; unfold raw21432step3 raw21432step2; decide +kernel
      have hl : raw21432step2Labels = labelEmbedding1 ∘ raw21432step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21432step2 raw21432step2Labels raw21432step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1674 node1674Labels := by rfl

def raw21433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21433Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21433step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21433step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw21433step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21433step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw21433step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21433step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-2, -1, 3]]
def raw21433step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21433step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![2, 1, -3]]
def raw21433step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21433step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![2, 1, -3]]
def raw21433step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21433 raw21433Labels = mixedMoment B node1754 node1754Labels := by
  calc
    mixedMoment B raw21433 raw21433Labels = mixedMoment B raw21433step0 raw21433step0Labels := by
      have hz : ∀ j, raw21433 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21433step0 = (fun i j => raw21433 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21433step0 raw21433; decide +kernel
      have hl : raw21433step0Labels = raw21433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21433 raw21433Labels permutation520 hz
    mixedMoment B raw21433step0 raw21433step0Labels = mixedMoment B raw21433step1 raw21433step1Labels := by
      have hz : ∀ j, raw21433step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21433step1 = (fun i j => raw21433step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21433step1 raw21433step0; decide +kernel
      have hl : raw21433step1Labels = raw21433step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21433step0 raw21433step0Labels permutation104 hz
    mixedMoment B raw21433step1 raw21433step1Labels = mixedMoment B raw21433step2 raw21433step2Labels := by
      have hz : ∀ j, raw21433step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw21433step2 = (fun i j => raw21433step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw21433step2 raw21433step1; decide +kernel
      have hl : raw21433step2Labels = raw21433step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21433step1 raw21433step1Labels permutation20 hz
    mixedMoment B raw21433step2 raw21433step2Labels = mixedMoment B raw21433step3 raw21433step3Labels := by
      have ha : raw21433step3 = (fun i j => raw21433step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21433step3 raw21433step2; decide +kernel
      have hl : raw21433step3Labels = raw21433step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21433step2 raw21433step2Labels permutation2 permutation7
    mixedMoment B raw21433step3 raw21433step3Labels = mixedMoment B raw21433step4 raw21433step4Labels := by
      have ha : raw21433step4 = -raw21433step3 := by apply Matrix.ext; change ∀ i j, raw21433step4 i j = -(raw21433step3 i j); unfold raw21433step4 raw21433step3; decide +kernel
      have hl : raw21433step4Labels = raw21433step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21433step4 raw21433step4Labels = mixedMoment B raw21433step5 raw21433step5Labels := by
      have ha : raw21433step5 = raw21433step4 := by apply Matrix.ext; unfold raw21433step5 raw21433step4; decide +kernel
      have hl : raw21433step4Labels = labelEmbedding1 ∘ raw21433step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21433step4 raw21433step4Labels raw21433step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1754 node1754Labels := by rfl

def raw21434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21434Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21434step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21434step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw21434step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21434step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw21434step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21434step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw21434step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21434step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw21434step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21434 raw21434Labels = mixedMoment B node1727 node1727Labels := by
  calc
    mixedMoment B raw21434 raw21434Labels = mixedMoment B raw21434step0 raw21434step0Labels := by
      have hz : ∀ j, raw21434 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21434step0 = (fun i j => raw21434 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21434step0 raw21434; decide +kernel
      have hl : raw21434step0Labels = raw21434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21434 raw21434Labels permutation434 hz
    mixedMoment B raw21434step0 raw21434step0Labels = mixedMoment B raw21434step1 raw21434step1Labels := by
      have hz : ∀ j, raw21434step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21434step1 = (fun i j => raw21434step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21434step1 raw21434step0; decide +kernel
      have hl : raw21434step1Labels = raw21434step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21434step0 raw21434step0Labels permutation80 hz
    mixedMoment B raw21434step1 raw21434step1Labels = mixedMoment B raw21434step2 raw21434step2Labels := by
      have ha : raw21434step2 = (fun i j => raw21434step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21434step2 raw21434step1; decide +kernel
      have hl : raw21434step2Labels = raw21434step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21434step1 raw21434step1Labels permutation10 permutation7
    mixedMoment B raw21434step2 raw21434step2Labels = mixedMoment B raw21434step3 raw21434step3Labels := by
      have ha : raw21434step3 = -raw21434step2 := by apply Matrix.ext; change ∀ i j, raw21434step3 i j = -(raw21434step2 i j); unfold raw21434step3 raw21434step2; decide +kernel
      have hl : raw21434step3Labels = raw21434step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21434step3 raw21434step3Labels = mixedMoment B raw21434step4 raw21434step4Labels := by
      have ha : raw21434step4 = raw21434step3 := by apply Matrix.ext; unfold raw21434step4 raw21434step3; decide +kernel
      have hl : raw21434step3Labels = labelEmbedding1 ∘ raw21434step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21434step3 raw21434step3Labels raw21434step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1727 node1727Labels := by rfl

def raw21435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21435Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21435step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw21435step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21435step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21435step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21435step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21435step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21435 raw21435Labels = mixedMoment B node1505 node1505Labels := by
  calc
    mixedMoment B raw21435 raw21435Labels = mixedMoment B raw21435step0 raw21435step0Labels := by
      have hz : ∀ j, raw21435 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21435step0 = (fun i j => raw21435 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21435step0 raw21435; decide +kernel
      have hl : raw21435step0Labels = raw21435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21435 raw21435Labels permutation434 hz
    mixedMoment B raw21435step0 raw21435step0Labels = mixedMoment B raw21435step1 raw21435step1Labels := by
      have ha : raw21435step1 = (fun i j => raw21435step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21435step1 raw21435step0; decide +kernel
      have hl : raw21435step1Labels = raw21435step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21435step0 raw21435step0Labels permutation40 permutation7
    mixedMoment B raw21435step1 raw21435step1Labels = mixedMoment B raw21435step2 raw21435step2Labels := by
      have ha : raw21435step2 = -raw21435step1 := by apply Matrix.ext; change ∀ i j, raw21435step2 i j = -(raw21435step1 i j); unfold raw21435step2 raw21435step1; decide +kernel
      have hl : raw21435step2Labels = raw21435step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21435step2 raw21435step2Labels = mixedMoment B raw21435step3 raw21435step3Labels := by
      have ha : raw21435step3 = raw21435step2 := by apply Matrix.ext; unfold raw21435step3 raw21435step2; decide +kernel
      have hl : raw21435step2Labels = labelEmbedding1 ∘ raw21435step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21435step2 raw21435step2Labels raw21435step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1505 node1505Labels := by rfl

def raw21436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21436Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21436step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21436step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw21436step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21436step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw21436step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21436step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw21436step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21436 raw21436Labels = mixedMoment B node1704 node1704Labels := by
  calc
    mixedMoment B raw21436 raw21436Labels = mixedMoment B raw21436step0 raw21436step0Labels := by
      have hz : ∀ j, raw21436 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21436step0 = (fun i j => raw21436 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21436step0 raw21436; decide +kernel
      have hl : raw21436step0Labels = raw21436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21436 raw21436Labels permutation434 hz
    mixedMoment B raw21436step0 raw21436step0Labels = mixedMoment B raw21436step1 raw21436step1Labels := by
      have ha : raw21436step1 = (fun i j => raw21436step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21436step1 raw21436step0; decide +kernel
      have hl : raw21436step1Labels = raw21436step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21436step0 raw21436step0Labels permutation40 permutation7
    mixedMoment B raw21436step1 raw21436step1Labels = mixedMoment B raw21436step2 raw21436step2Labels := by
      have ha : raw21436step2 = -raw21436step1 := by apply Matrix.ext; change ∀ i j, raw21436step2 i j = -(raw21436step1 i j); unfold raw21436step2 raw21436step1; decide +kernel
      have hl : raw21436step2Labels = raw21436step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21436step2 raw21436step2Labels = mixedMoment B raw21436step3 raw21436step3Labels := by
      have ha : raw21436step3 = raw21436step2 := by apply Matrix.ext; unfold raw21436step3 raw21436step2; decide +kernel
      have hl : raw21436step2Labels = labelEmbedding1 ∘ raw21436step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21436step2 raw21436step2Labels raw21436step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1704 node1704Labels := by rfl

def raw21437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21437Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw21437step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21437step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21437step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21437step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21437step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21437 raw21437Labels = mixedMoment B node1663 node1663Labels := by
  calc
    mixedMoment B raw21437 raw21437Labels = mixedMoment B raw21437step0 raw21437step0Labels := by
      have ha : raw21437step0 = (fun i j => raw21437 (permutation208 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21437step0 raw21437; decide +kernel
      have hl : raw21437step0Labels = raw21437Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21437 raw21437Labels permutation208 permutation7
    mixedMoment B raw21437step0 raw21437step0Labels = mixedMoment B raw21437step1 raw21437step1Labels := by
      have ha : raw21437step1 = -raw21437step0 := by apply Matrix.ext; change ∀ i j, raw21437step1 i j = -(raw21437step0 i j); unfold raw21437step1 raw21437step0; decide +kernel
      have hl : raw21437step1Labels = raw21437step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21437step1 raw21437step1Labels = mixedMoment B raw21437step2 raw21437step2Labels := by
      have ha : raw21437step2 = raw21437step1 := by apply Matrix.ext; unfold raw21437step2 raw21437step1; decide +kernel
      have hl : raw21437step1Labels = labelEmbedding1 ∘ raw21437step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21437step1 raw21437step1Labels raw21437step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1663 node1663Labels := by rfl

def raw21438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21438Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21438step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21438step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21438step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21438step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw21438step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21438step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21438step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21438step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21438step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21438 raw21438Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw21438 raw21438Labels = mixedMoment B raw21438step0 raw21438step0Labels := by
      have hz : ∀ j, raw21438 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21438step0 = (fun i j => raw21438 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21438step0 raw21438; decide +kernel
      have hl : raw21438step0Labels = raw21438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21438 raw21438Labels permutation520 hz
    mixedMoment B raw21438step0 raw21438step0Labels = mixedMoment B raw21438step1 raw21438step1Labels := by
      have hz : ∀ j, raw21438step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21438step1 = (fun i j => raw21438step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21438step1 raw21438step0; decide +kernel
      have hl : raw21438step1Labels = raw21438step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21438step0 raw21438step0Labels permutation104 hz
    mixedMoment B raw21438step1 raw21438step1Labels = mixedMoment B raw21438step2 raw21438step2Labels := by
      have ha : raw21438step2 = (fun i j => raw21438step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21438step2 raw21438step1; decide +kernel
      have hl : raw21438step2Labels = raw21438step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21438step1 raw21438step1Labels permutation10 permutation7
    mixedMoment B raw21438step2 raw21438step2Labels = mixedMoment B raw21438step3 raw21438step3Labels := by
      have ha : raw21438step3 = -raw21438step2 := by apply Matrix.ext; change ∀ i j, raw21438step3 i j = -(raw21438step2 i j); unfold raw21438step3 raw21438step2; decide +kernel
      have hl : raw21438step3Labels = raw21438step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21438step3 raw21438step3Labels = mixedMoment B raw21438step4 raw21438step4Labels := by
      have ha : raw21438step4 = raw21438step3 := by apply Matrix.ext; unfold raw21438step4 raw21438step3; decide +kernel
      have hl : raw21438step3Labels = labelEmbedding1 ∘ raw21438step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21438step3 raw21438step3Labels raw21438step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

def raw21439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21439Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21439step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21439step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw21439step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21439step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw21439step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21439step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw21439step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21439 raw21439Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw21439 raw21439Labels = mixedMoment B raw21439step0 raw21439step0Labels := by
      have hz : ∀ j, raw21439 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21439step0 = (fun i j => raw21439 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21439step0 raw21439; decide +kernel
      have hl : raw21439step0Labels = raw21439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21439 raw21439Labels permutation434 hz
    mixedMoment B raw21439step0 raw21439step0Labels = mixedMoment B raw21439step1 raw21439step1Labels := by
      have ha : raw21439step1 = (fun i j => raw21439step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21439step1 raw21439step0; decide +kernel
      have hl : raw21439step1Labels = raw21439step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21439step0 raw21439step0Labels permutation40 permutation7
    mixedMoment B raw21439step1 raw21439step1Labels = mixedMoment B raw21439step2 raw21439step2Labels := by
      have ha : raw21439step2 = -raw21439step1 := by apply Matrix.ext; change ∀ i j, raw21439step2 i j = -(raw21439step1 i j); unfold raw21439step2 raw21439step1; decide +kernel
      have hl : raw21439step2Labels = raw21439step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21439step2 raw21439step2Labels = mixedMoment B raw21439step3 raw21439step3Labels := by
      have ha : raw21439step3 = raw21439step2 := by apply Matrix.ext; unfold raw21439step3 raw21439step2; decide +kernel
      have hl : raw21439step2Labels = labelEmbedding1 ∘ raw21439step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21439step2 raw21439step2Labels raw21439step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1707 node1707Labels := by rfl

def raw21440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21440Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21440step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw21440step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21440step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21440step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21440step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21440step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21440 raw21440Labels = mixedMoment B node1505 node1505Labels := by
  calc
    mixedMoment B raw21440 raw21440Labels = mixedMoment B raw21440step0 raw21440step0Labels := by
      have hz : ∀ j, raw21440 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21440step0 = (fun i j => raw21440 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21440step0 raw21440; decide +kernel
      have hl : raw21440step0Labels = raw21440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21440 raw21440Labels permutation346 hz
    mixedMoment B raw21440step0 raw21440step0Labels = mixedMoment B raw21440step1 raw21440step1Labels := by
      have ha : raw21440step1 = (fun i j => raw21440step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21440step1 raw21440step0; decide +kernel
      have hl : raw21440step1Labels = raw21440step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21440step0 raw21440step0Labels permutation40 permutation7
    mixedMoment B raw21440step1 raw21440step1Labels = mixedMoment B raw21440step2 raw21440step2Labels := by
      have ha : raw21440step2 = -raw21440step1 := by apply Matrix.ext; change ∀ i j, raw21440step2 i j = -(raw21440step1 i j); unfold raw21440step2 raw21440step1; decide +kernel
      have hl : raw21440step2Labels = raw21440step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21440step2 raw21440step2Labels = mixedMoment B raw21440step3 raw21440step3Labels := by
      have ha : raw21440step3 = raw21440step2 := by apply Matrix.ext; unfold raw21440step3 raw21440step2; decide +kernel
      have hl : raw21440step2Labels = labelEmbedding1 ∘ raw21440step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21440step2 raw21440step2Labels raw21440step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1505 node1505Labels := by rfl

def raw21441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21441Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21441step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw21441step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21441step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw21441step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21441step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw21441step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21441 raw21441Labels = mixedMoment B node1704 node1704Labels := by
  calc
    mixedMoment B raw21441 raw21441Labels = mixedMoment B raw21441step0 raw21441step0Labels := by
      have hz : ∀ j, raw21441 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21441step0 = (fun i j => raw21441 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21441step0 raw21441; decide +kernel
      have hl : raw21441step0Labels = raw21441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21441 raw21441Labels permutation346 hz
    mixedMoment B raw21441step0 raw21441step0Labels = mixedMoment B raw21441step1 raw21441step1Labels := by
      have ha : raw21441step1 = (fun i j => raw21441step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21441step1 raw21441step0; decide +kernel
      have hl : raw21441step1Labels = raw21441step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21441step0 raw21441step0Labels permutation40 permutation7
    mixedMoment B raw21441step1 raw21441step1Labels = mixedMoment B raw21441step2 raw21441step2Labels := by
      have ha : raw21441step2 = -raw21441step1 := by apply Matrix.ext; change ∀ i j, raw21441step2 i j = -(raw21441step1 i j); unfold raw21441step2 raw21441step1; decide +kernel
      have hl : raw21441step2Labels = raw21441step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21441step2 raw21441step2Labels = mixedMoment B raw21441step3 raw21441step3Labels := by
      have ha : raw21441step3 = raw21441step2 := by apply Matrix.ext; unfold raw21441step3 raw21441step2; decide +kernel
      have hl : raw21441step2Labels = labelEmbedding1 ∘ raw21441step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21441step2 raw21441step2Labels raw21441step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1704 node1704Labels := by rfl

def raw21442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21442Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21442step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw21442step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21442step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21442step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21442step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21442step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21442 raw21442Labels = mixedMoment B node1663 node1663Labels := by
  calc
    mixedMoment B raw21442 raw21442Labels = mixedMoment B raw21442step0 raw21442step0Labels := by
      have ha : raw21442step0 = (fun i j => raw21442 (permutation184 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21442step0 raw21442; decide +kernel
      have hl : raw21442step0Labels = raw21442Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21442 raw21442Labels permutation184 permutation7
    mixedMoment B raw21442step0 raw21442step0Labels = mixedMoment B raw21442step1 raw21442step1Labels := by
      have ha : raw21442step1 = -raw21442step0 := by apply Matrix.ext; change ∀ i j, raw21442step1 i j = -(raw21442step0 i j); unfold raw21442step1 raw21442step0; decide +kernel
      have hl : raw21442step1Labels = raw21442step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21442step1 raw21442step1Labels = mixedMoment B raw21442step2 raw21442step2Labels := by
      have ha : raw21442step2 = raw21442step1 := by apply Matrix.ext; unfold raw21442step2 raw21442step1; decide +kernel
      have hl : raw21442step1Labels = labelEmbedding1 ∘ raw21442step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21442step1 raw21442step1Labels raw21442step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1663 node1663Labels := by rfl

def raw21443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21443Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21443step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21443step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21443step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21443step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw21443step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21443step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21443step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21443step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw21443step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21443 raw21443Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw21443 raw21443Labels = mixedMoment B raw21443step0 raw21443step0Labels := by
      have hz : ∀ j, raw21443 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21443step0 = (fun i j => raw21443 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21443step0 raw21443; decide +kernel
      have hl : raw21443step0Labels = raw21443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21443 raw21443Labels permutation520 hz
    mixedMoment B raw21443step0 raw21443step0Labels = mixedMoment B raw21443step1 raw21443step1Labels := by
      have hz : ∀ j, raw21443step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21443step1 = (fun i j => raw21443step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21443step1 raw21443step0; decide +kernel
      have hl : raw21443step1Labels = raw21443step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21443step0 raw21443step0Labels permutation80 hz
    mixedMoment B raw21443step1 raw21443step1Labels = mixedMoment B raw21443step2 raw21443step2Labels := by
      have ha : raw21443step2 = (fun i j => raw21443step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21443step2 raw21443step1; decide +kernel
      have hl : raw21443step2Labels = raw21443step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21443step1 raw21443step1Labels permutation10 permutation7
    mixedMoment B raw21443step2 raw21443step2Labels = mixedMoment B raw21443step3 raw21443step3Labels := by
      have ha : raw21443step3 = -raw21443step2 := by apply Matrix.ext; change ∀ i j, raw21443step3 i j = -(raw21443step2 i j); unfold raw21443step3 raw21443step2; decide +kernel
      have hl : raw21443step3Labels = raw21443step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21443step3 raw21443step3Labels = mixedMoment B raw21443step4 raw21443step4Labels := by
      have ha : raw21443step4 = raw21443step3 := by apply Matrix.ext; unfold raw21443step4 raw21443step3; decide +kernel
      have hl : raw21443step3Labels = labelEmbedding1 ∘ raw21443step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21443step3 raw21443step3Labels raw21443step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

def raw21444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21444Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21444step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw21444step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21444step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw21444step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21444step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw21444step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21444 raw21444Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw21444 raw21444Labels = mixedMoment B raw21444step0 raw21444step0Labels := by
      have hz : ∀ j, raw21444 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21444step0 = (fun i j => raw21444 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21444step0 raw21444; decide +kernel
      have hl : raw21444step0Labels = raw21444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21444 raw21444Labels permutation346 hz
    mixedMoment B raw21444step0 raw21444step0Labels = mixedMoment B raw21444step1 raw21444step1Labels := by
      have ha : raw21444step1 = (fun i j => raw21444step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21444step1 raw21444step0; decide +kernel
      have hl : raw21444step1Labels = raw21444step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21444step0 raw21444step0Labels permutation40 permutation7
    mixedMoment B raw21444step1 raw21444step1Labels = mixedMoment B raw21444step2 raw21444step2Labels := by
      have ha : raw21444step2 = -raw21444step1 := by apply Matrix.ext; change ∀ i j, raw21444step2 i j = -(raw21444step1 i j); unfold raw21444step2 raw21444step1; decide +kernel
      have hl : raw21444step2Labels = raw21444step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21444step2 raw21444step2Labels = mixedMoment B raw21444step3 raw21444step3Labels := by
      have ha : raw21444step3 = raw21444step2 := by apply Matrix.ext; unfold raw21444step3 raw21444step2; decide +kernel
      have hl : raw21444step2Labels = labelEmbedding1 ∘ raw21444step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21444step2 raw21444step2Labels raw21444step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1707 node1707Labels := by rfl

def raw21445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21445Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21445step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21445step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw21445step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21445step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw21445step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21445step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw21445step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21445step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw21445step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21445 raw21445Labels = mixedMoment B node1523 node1523Labels := by
  calc
    mixedMoment B raw21445 raw21445Labels = mixedMoment B raw21445step0 raw21445step0Labels := by
      have hz : ∀ j, raw21445 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21445step0 = (fun i j => raw21445 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21445step0 raw21445; decide +kernel
      have hl : raw21445step0Labels = raw21445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21445 raw21445Labels permutation434 hz
    mixedMoment B raw21445step0 raw21445step0Labels = mixedMoment B raw21445step1 raw21445step1Labels := by
      have hz : ∀ j, raw21445step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21445step1 = (fun i j => raw21445step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21445step1 raw21445step0; decide +kernel
      have hl : raw21445step1Labels = raw21445step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21445step0 raw21445step0Labels permutation80 hz
    mixedMoment B raw21445step1 raw21445step1Labels = mixedMoment B raw21445step2 raw21445step2Labels := by
      have ha : raw21445step2 = (fun i j => raw21445step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21445step2 raw21445step1; decide +kernel
      have hl : raw21445step2Labels = raw21445step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21445step1 raw21445step1Labels permutation10 permutation7
    mixedMoment B raw21445step2 raw21445step2Labels = mixedMoment B raw21445step3 raw21445step3Labels := by
      have ha : raw21445step3 = -raw21445step2 := by apply Matrix.ext; change ∀ i j, raw21445step3 i j = -(raw21445step2 i j); unfold raw21445step3 raw21445step2; decide +kernel
      have hl : raw21445step3Labels = raw21445step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21445step3 raw21445step3Labels = mixedMoment B raw21445step4 raw21445step4Labels := by
      have ha : raw21445step4 = raw21445step3 := by apply Matrix.ext; unfold raw21445step4 raw21445step3; decide +kernel
      have hl : raw21445step3Labels = labelEmbedding1 ∘ raw21445step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21445step3 raw21445step3Labels raw21445step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1523 node1523Labels := by rfl

def raw21446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21446Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21446step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21446step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw21446step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21446step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 2, -1], ![-2, -1, 3]]
def raw21446step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21446step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw21446step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21446step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw21446step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21446 raw21446Labels = mixedMoment B node1735 node1735Labels := by
  calc
    mixedMoment B raw21446 raw21446Labels = mixedMoment B raw21446step0 raw21446step0Labels := by
      have hz : ∀ j, raw21446 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21446step0 = (fun i j => raw21446 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21446step0 raw21446; decide +kernel
      have hl : raw21446step0Labels = raw21446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21446 raw21446Labels permutation434 hz
    mixedMoment B raw21446step0 raw21446step0Labels = mixedMoment B raw21446step1 raw21446step1Labels := by
      have hz : ∀ j, raw21446step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21446step1 = (fun i j => raw21446step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21446step1 raw21446step0; decide +kernel
      have hl : raw21446step1Labels = raw21446step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21446step0 raw21446step0Labels permutation80 hz
    mixedMoment B raw21446step1 raw21446step1Labels = mixedMoment B raw21446step2 raw21446step2Labels := by
      have ha : raw21446step2 = (fun i j => raw21446step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21446step2 raw21446step1; decide +kernel
      have hl : raw21446step2Labels = raw21446step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21446step1 raw21446step1Labels permutation10 permutation7
    mixedMoment B raw21446step2 raw21446step2Labels = mixedMoment B raw21446step3 raw21446step3Labels := by
      have ha : raw21446step3 = -raw21446step2 := by apply Matrix.ext; change ∀ i j, raw21446step3 i j = -(raw21446step2 i j); unfold raw21446step3 raw21446step2; decide +kernel
      have hl : raw21446step3Labels = raw21446step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21446step3 raw21446step3Labels = mixedMoment B raw21446step4 raw21446step4Labels := by
      have ha : raw21446step4 = raw21446step3 := by apply Matrix.ext; unfold raw21446step4 raw21446step3; decide +kernel
      have hl : raw21446step3Labels = labelEmbedding1 ∘ raw21446step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21446step3 raw21446step3Labels raw21446step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1735 node1735Labels := by rfl

def raw21447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21447Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21447step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21447step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw21447step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21447step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw21447step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21447step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw21447step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21447 raw21447Labels = mixedMoment B node1679 node1679Labels := by
  calc
    mixedMoment B raw21447 raw21447Labels = mixedMoment B raw21447step0 raw21447step0Labels := by
      have hz : ∀ j, raw21447 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21447step0 = (fun i j => raw21447 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21447step0 raw21447; decide +kernel
      have hl : raw21447step0Labels = raw21447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21447 raw21447Labels permutation434 hz
    mixedMoment B raw21447step0 raw21447step0Labels = mixedMoment B raw21447step1 raw21447step1Labels := by
      have ha : raw21447step1 = (fun i j => raw21447step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21447step1 raw21447step0; decide +kernel
      have hl : raw21447step1Labels = raw21447step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21447step0 raw21447step0Labels permutation40 permutation7
    mixedMoment B raw21447step1 raw21447step1Labels = mixedMoment B raw21447step2 raw21447step2Labels := by
      have ha : raw21447step2 = -raw21447step1 := by apply Matrix.ext; change ∀ i j, raw21447step2 i j = -(raw21447step1 i j); unfold raw21447step2 raw21447step1; decide +kernel
      have hl : raw21447step2Labels = raw21447step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21447step2 raw21447step2Labels = mixedMoment B raw21447step3 raw21447step3Labels := by
      have ha : raw21447step3 = raw21447step2 := by apply Matrix.ext; unfold raw21447step3 raw21447step2; decide +kernel
      have hl : raw21447step2Labels = labelEmbedding1 ∘ raw21447step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21447step2 raw21447step2Labels raw21447step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1679 node1679Labels := by rfl

def raw21448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21448Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21448step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21448step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw21448step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21448step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw21448step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21448step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw21448step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21448 raw21448Labels = mixedMoment B node1679 node1679Labels := by
  calc
    mixedMoment B raw21448 raw21448Labels = mixedMoment B raw21448step0 raw21448step0Labels := by
      have hz : ∀ j, raw21448 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21448step0 = (fun i j => raw21448 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21448step0 raw21448; decide +kernel
      have hl : raw21448step0Labels = raw21448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21448 raw21448Labels permutation346 hz
    mixedMoment B raw21448step0 raw21448step0Labels = mixedMoment B raw21448step1 raw21448step1Labels := by
      have ha : raw21448step1 = (fun i j => raw21448step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21448step1 raw21448step0; decide +kernel
      have hl : raw21448step1Labels = raw21448step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21448step0 raw21448step0Labels permutation40 permutation7
    mixedMoment B raw21448step1 raw21448step1Labels = mixedMoment B raw21448step2 raw21448step2Labels := by
      have ha : raw21448step2 = -raw21448step1 := by apply Matrix.ext; change ∀ i j, raw21448step2 i j = -(raw21448step1 i j); unfold raw21448step2 raw21448step1; decide +kernel
      have hl : raw21448step2Labels = raw21448step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21448step2 raw21448step2Labels = mixedMoment B raw21448step3 raw21448step3Labels := by
      have ha : raw21448step3 = raw21448step2 := by apply Matrix.ext; unfold raw21448step3 raw21448step2; decide +kernel
      have hl : raw21448step2Labels = labelEmbedding1 ∘ raw21448step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21448step2 raw21448step2Labels raw21448step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1679 node1679Labels := by rfl

def raw21449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw21449Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw21449step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21449step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw21449step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21449step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw21449step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21449step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw21449step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21449step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw21449step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21449 raw21449Labels = mixedMoment B node1738 node1738Labels := by
  calc
    mixedMoment B raw21449 raw21449Labels = mixedMoment B raw21449step0 raw21449step0Labels := by
      have hz : ∀ j, raw21449 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21449step0 = (fun i j => raw21449 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21449step0 raw21449; decide +kernel
      have hl : raw21449step0Labels = raw21449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21449 raw21449Labels permutation434 hz
    mixedMoment B raw21449step0 raw21449step0Labels = mixedMoment B raw21449step1 raw21449step1Labels := by
      have hz : ∀ j, raw21449step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21449step1 = (fun i j => raw21449step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21449step1 raw21449step0; decide +kernel
      have hl : raw21449step1Labels = raw21449step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21449step0 raw21449step0Labels permutation80 hz
    mixedMoment B raw21449step1 raw21449step1Labels = mixedMoment B raw21449step2 raw21449step2Labels := by
      have ha : raw21449step2 = (fun i j => raw21449step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21449step2 raw21449step1; decide +kernel
      have hl : raw21449step2Labels = raw21449step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21449step1 raw21449step1Labels permutation10 permutation7
    mixedMoment B raw21449step2 raw21449step2Labels = mixedMoment B raw21449step3 raw21449step3Labels := by
      have ha : raw21449step3 = -raw21449step2 := by apply Matrix.ext; change ∀ i j, raw21449step3 i j = -(raw21449step2 i j); unfold raw21449step3 raw21449step2; decide +kernel
      have hl : raw21449step3Labels = raw21449step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21449step3 raw21449step3Labels = mixedMoment B raw21449step4 raw21449step4Labels := by
      have ha : raw21449step4 = raw21449step3 := by apply Matrix.ext; unfold raw21449step4 raw21449step3; decide +kernel
      have hl : raw21449step3Labels = labelEmbedding1 ∘ raw21449step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21449step3 raw21449step3Labels raw21449step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1738 node1738Labels := by rfl

def raw21450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21450Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21450step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21450step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw21450step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21450step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-2, -2, 4]]
def raw21450step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21450step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw21450step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21450step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw21450step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21450 raw21450Labels = mixedMoment B node1516 node1516Labels := by
  calc
    mixedMoment B raw21450 raw21450Labels = mixedMoment B raw21450step0 raw21450step0Labels := by
      have hz : ∀ j, raw21450 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21450step0 = (fun i j => raw21450 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21450step0 raw21450; decide +kernel
      have hl : raw21450step0Labels = raw21450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21450 raw21450Labels permutation434 hz
    mixedMoment B raw21450step0 raw21450step0Labels = mixedMoment B raw21450step1 raw21450step1Labels := by
      have hz : ∀ j, raw21450step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21450step1 = (fun i j => raw21450step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21450step1 raw21450step0; decide +kernel
      have hl : raw21450step1Labels = raw21450step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21450step0 raw21450step0Labels permutation80 hz
    mixedMoment B raw21450step1 raw21450step1Labels = mixedMoment B raw21450step2 raw21450step2Labels := by
      have ha : raw21450step2 = (fun i j => raw21450step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21450step2 raw21450step1; decide +kernel
      have hl : raw21450step2Labels = raw21450step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21450step1 raw21450step1Labels permutation10 permutation7
    mixedMoment B raw21450step2 raw21450step2Labels = mixedMoment B raw21450step3 raw21450step3Labels := by
      have ha : raw21450step3 = -raw21450step2 := by apply Matrix.ext; change ∀ i j, raw21450step3 i j = -(raw21450step2 i j); unfold raw21450step3 raw21450step2; decide +kernel
      have hl : raw21450step3Labels = raw21450step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21450step3 raw21450step3Labels = mixedMoment B raw21450step4 raw21450step4Labels := by
      have ha : raw21450step4 = raw21450step3 := by apply Matrix.ext; unfold raw21450step4 raw21450step3; decide +kernel
      have hl : raw21450step3Labels = labelEmbedding1 ∘ raw21450step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21450step3 raw21450step3Labels raw21450step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1516 node1516Labels := by rfl

def raw21451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21451Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21451step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21451step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![4, -2, -2]]
def raw21451step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21451step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 2, -1], ![-2, -2, 4]]
def raw21451step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21451step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw21451step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21451step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw21451step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21451 raw21451Labels = mixedMoment B node1722 node1722Labels := by
  calc
    mixedMoment B raw21451 raw21451Labels = mixedMoment B raw21451step0 raw21451step0Labels := by
      have hz : ∀ j, raw21451 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21451step0 = (fun i j => raw21451 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21451step0 raw21451; decide +kernel
      have hl : raw21451step0Labels = raw21451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21451 raw21451Labels permutation434 hz
    mixedMoment B raw21451step0 raw21451step0Labels = mixedMoment B raw21451step1 raw21451step1Labels := by
      have hz : ∀ j, raw21451step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21451step1 = (fun i j => raw21451step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21451step1 raw21451step0; decide +kernel
      have hl : raw21451step1Labels = raw21451step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21451step0 raw21451step0Labels permutation80 hz
    mixedMoment B raw21451step1 raw21451step1Labels = mixedMoment B raw21451step2 raw21451step2Labels := by
      have ha : raw21451step2 = (fun i j => raw21451step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21451step2 raw21451step1; decide +kernel
      have hl : raw21451step2Labels = raw21451step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21451step1 raw21451step1Labels permutation10 permutation7
    mixedMoment B raw21451step2 raw21451step2Labels = mixedMoment B raw21451step3 raw21451step3Labels := by
      have ha : raw21451step3 = -raw21451step2 := by apply Matrix.ext; change ∀ i j, raw21451step3 i j = -(raw21451step2 i j); unfold raw21451step3 raw21451step2; decide +kernel
      have hl : raw21451step3Labels = raw21451step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21451step3 raw21451step3Labels = mixedMoment B raw21451step4 raw21451step4Labels := by
      have ha : raw21451step4 = raw21451step3 := by apply Matrix.ext; unfold raw21451step4 raw21451step3; decide +kernel
      have hl : raw21451step3Labels = labelEmbedding1 ∘ raw21451step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21451step3 raw21451step3Labels raw21451step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1722 node1722Labels := by rfl

def raw21452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21452Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21452step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21452step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -2, 4]]
def raw21452step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21452step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw21452step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21452step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw21452step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21452 raw21452Labels = mixedMoment B node1672 node1672Labels := by
  calc
    mixedMoment B raw21452 raw21452Labels = mixedMoment B raw21452step0 raw21452step0Labels := by
      have hz : ∀ j, raw21452 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21452step0 = (fun i j => raw21452 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21452step0 raw21452; decide +kernel
      have hl : raw21452step0Labels = raw21452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21452 raw21452Labels permutation434 hz
    mixedMoment B raw21452step0 raw21452step0Labels = mixedMoment B raw21452step1 raw21452step1Labels := by
      have ha : raw21452step1 = (fun i j => raw21452step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21452step1 raw21452step0; decide +kernel
      have hl : raw21452step1Labels = raw21452step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21452step0 raw21452step0Labels permutation40 permutation7
    mixedMoment B raw21452step1 raw21452step1Labels = mixedMoment B raw21452step2 raw21452step2Labels := by
      have ha : raw21452step2 = -raw21452step1 := by apply Matrix.ext; change ∀ i j, raw21452step2 i j = -(raw21452step1 i j); unfold raw21452step2 raw21452step1; decide +kernel
      have hl : raw21452step2Labels = raw21452step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21452step2 raw21452step2Labels = mixedMoment B raw21452step3 raw21452step3Labels := by
      have ha : raw21452step3 = raw21452step2 := by apply Matrix.ext; unfold raw21452step3 raw21452step2; decide +kernel
      have hl : raw21452step2Labels = labelEmbedding1 ∘ raw21452step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21452step2 raw21452step2Labels raw21452step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1672 node1672Labels := by rfl

def raw21453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21453Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21453step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -2, 4]]
def raw21453step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21453step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw21453step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21453step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw21453step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21453 raw21453Labels = mixedMoment B node1672 node1672Labels := by
  calc
    mixedMoment B raw21453 raw21453Labels = mixedMoment B raw21453step0 raw21453step0Labels := by
      have hz : ∀ j, raw21453 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21453step0 = (fun i j => raw21453 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21453step0 raw21453; decide +kernel
      have hl : raw21453step0Labels = raw21453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21453 raw21453Labels permutation346 hz
    mixedMoment B raw21453step0 raw21453step0Labels = mixedMoment B raw21453step1 raw21453step1Labels := by
      have ha : raw21453step1 = (fun i j => raw21453step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21453step1 raw21453step0; decide +kernel
      have hl : raw21453step1Labels = raw21453step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21453step0 raw21453step0Labels permutation40 permutation7
    mixedMoment B raw21453step1 raw21453step1Labels = mixedMoment B raw21453step2 raw21453step2Labels := by
      have ha : raw21453step2 = -raw21453step1 := by apply Matrix.ext; change ∀ i j, raw21453step2 i j = -(raw21453step1 i j); unfold raw21453step2 raw21453step1; decide +kernel
      have hl : raw21453step2Labels = raw21453step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21453step2 raw21453step2Labels = mixedMoment B raw21453step3 raw21453step3Labels := by
      have ha : raw21453step3 = raw21453step2 := by apply Matrix.ext; unfold raw21453step3 raw21453step2; decide +kernel
      have hl : raw21453step2Labels = labelEmbedding1 ∘ raw21453step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21453step2 raw21453step2Labels raw21453step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1672 node1672Labels := by rfl

def raw21454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw21454Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw21454step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21454step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![4, -2, -2]]
def raw21454step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21454step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw21454step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21454step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw21454step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21454step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw21454step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21454step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw21454step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21454 raw21454Labels = mixedMoment B node1752 node1752Labels := by
  calc
    mixedMoment B raw21454 raw21454Labels = mixedMoment B raw21454step0 raw21454step0Labels := by
      have hz : ∀ j, raw21454 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21454step0 = (fun i j => raw21454 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21454step0 raw21454; decide +kernel
      have hl : raw21454step0Labels = raw21454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21454 raw21454Labels permutation520 hz
    mixedMoment B raw21454step0 raw21454step0Labels = mixedMoment B raw21454step1 raw21454step1Labels := by
      have hz : ∀ j, raw21454step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21454step1 = (fun i j => raw21454step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21454step1 raw21454step0; decide +kernel
      have hl : raw21454step1Labels = raw21454step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21454step0 raw21454step0Labels permutation104 hz
    mixedMoment B raw21454step1 raw21454step1Labels = mixedMoment B raw21454step2 raw21454step2Labels := by
      have hz : ∀ j, raw21454step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw21454step2 = (fun i j => raw21454step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw21454step2 raw21454step1; decide +kernel
      have hl : raw21454step2Labels = raw21454step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21454step1 raw21454step1Labels permutation20 hz
    mixedMoment B raw21454step2 raw21454step2Labels = mixedMoment B raw21454step3 raw21454step3Labels := by
      have ha : raw21454step3 = (fun i j => raw21454step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21454step3 raw21454step2; decide +kernel
      have hl : raw21454step3Labels = raw21454step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21454step2 raw21454step2Labels permutation2 permutation7
    mixedMoment B raw21454step3 raw21454step3Labels = mixedMoment B raw21454step4 raw21454step4Labels := by
      have ha : raw21454step4 = -raw21454step3 := by apply Matrix.ext; change ∀ i j, raw21454step4 i j = -(raw21454step3 i j); unfold raw21454step4 raw21454step3; decide +kernel
      have hl : raw21454step4Labels = raw21454step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21454step4 raw21454step4Labels = mixedMoment B raw21454step5 raw21454step5Labels := by
      have ha : raw21454step5 = raw21454step4 := by apply Matrix.ext; unfold raw21454step5 raw21454step4; decide +kernel
      have hl : raw21454step4Labels = labelEmbedding1 ∘ raw21454step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21454step4 raw21454step4Labels raw21454step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1752 node1752Labels := by rfl

def raw21455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21455Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21455step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21455step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21455step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21455 raw21455Labels = mixedMoment B node1043 node1043Labels := by
  calc
    mixedMoment B raw21455 raw21455Labels = mixedMoment B raw21455step0 raw21455step0Labels := by
      have hz : ∀ j, raw21455 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21455step0 = (fun i j => raw21455 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21455step0 raw21455; decide +kernel
      have hl : raw21455step0Labels = raw21455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21455 raw21455Labels permutation434 hz
    mixedMoment B raw21455step0 raw21455step0Labels = mixedMoment B raw21455step1 raw21455step1Labels := by
      have hz : ∀ j, raw21455step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21455step1 = (fun i j => raw21455step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21455step1 raw21455step0; decide +kernel
      have hl : raw21455step1Labels = raw21455step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21455step0 raw21455step0Labels permutation80 hz
    _ = mixedMoment B node1043 node1043Labels := by rfl

def raw21456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21456step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21456step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21456step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21456step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21456 raw21456Labels = mixedMoment B node605 node605Labels := by
  calc
    mixedMoment B raw21456 raw21456Labels = mixedMoment B raw21456step0 raw21456step0Labels := by
      have hz : ∀ j, raw21456 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21456step0 = (fun i j => raw21456 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21456step0 raw21456; decide +kernel
      have hl : raw21456step0Labels = raw21456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21456 raw21456Labels permutation434 hz
    mixedMoment B raw21456step0 raw21456step0Labels = mixedMoment B raw21456step1 raw21456step1Labels := by
      have hz : ∀ j, raw21456step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21456step1 = (fun i j => raw21456step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21456step1 raw21456step0; decide +kernel
      have hl : raw21456step1Labels = raw21456step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21456step0 raw21456step0Labels permutation80 hz
    mixedMoment B raw21456step1 raw21456step1Labels = mixedMoment B raw21456step2 raw21456step2Labels := by
      have ha : raw21456step2 = (fun i j => raw21456step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21456step2 raw21456step1; decide +kernel
      have hl : raw21456step2Labels = raw21456step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21456step1 raw21456step1Labels permutation10 permutation2
    _ = mixedMoment B node605 node605Labels := by rfl

def raw21457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21457Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21457step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21457 raw21457Labels = mixedMoment B node579 node579Labels := by
  calc
    mixedMoment B raw21457 raw21457Labels = mixedMoment B raw21457step0 raw21457step0Labels := by
      have hz : ∀ j, raw21457 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21457step0 = (fun i j => raw21457 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21457step0 raw21457; decide +kernel
      have hl : raw21457step0Labels = raw21457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21457 raw21457Labels permutation434 hz
    _ = mixedMoment B node579 node579Labels := by rfl

def raw21458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21458Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21458 raw21458Labels = mixedMoment B node579 node579Labels := by
  calc
    mixedMoment B raw21458 raw21458Labels = mixedMoment B raw21458step0 raw21458step0Labels := by
      have hz : ∀ j, raw21458 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21458step0 = (fun i j => raw21458 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21458step0 raw21458; decide +kernel
      have hl : raw21458step0Labels = raw21458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21458 raw21458Labels permutation346 hz
    _ = mixedMoment B node579 node579Labels := by rfl

def raw21459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21459Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21459step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw21459step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21459 raw21459Labels = mixedMoment B node588 node588Labels := by
  calc
    mixedMoment B raw21459 raw21459Labels = mixedMoment B raw21459step0 raw21459step0Labels := by
      have hz : ∀ j, raw21459 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21459step0 = (fun i j => raw21459 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21459step0 raw21459; decide +kernel
      have hl : raw21459step0Labels = raw21459Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21459 raw21459Labels permutation434 hz
    mixedMoment B raw21459step0 raw21459step0Labels = mixedMoment B raw21459step1 raw21459step1Labels := by
      have hz : ∀ j, raw21459step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21459step1 = (fun i j => raw21459step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21459step1 raw21459step0; decide +kernel
      have hl : raw21459step1Labels = raw21459step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21459step0 raw21459step0Labels permutation80 hz
    _ = mixedMoment B node588 node588Labels := by rfl

def raw21460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21460Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21460step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21460step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw21460step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21460 raw21460Labels = mixedMoment B node584 node584Labels := by
  calc
    mixedMoment B raw21460 raw21460Labels = mixedMoment B raw21460step0 raw21460step0Labels := by
      have hz : ∀ j, raw21460 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21460step0 = (fun i j => raw21460 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21460step0 raw21460; decide +kernel
      have hl : raw21460step0Labels = raw21460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21460 raw21460Labels permutation434 hz
    mixedMoment B raw21460step0 raw21460step0Labels = mixedMoment B raw21460step1 raw21460step1Labels := by
      have hz : ∀ j, raw21460step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21460step1 = (fun i j => raw21460step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21460step1 raw21460step0; decide +kernel
      have hl : raw21460step1Labels = raw21460step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21460step0 raw21460step0Labels permutation80 hz
    _ = mixedMoment B node584 node584Labels := by rfl

def raw21461 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![0, 0], ![0, 0], ![2, -2]]
def raw21461Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21461step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![0, 0], ![2, -2]]
def raw21461step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21461step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![2, -2]]
def raw21461step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21461step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw21461step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical21461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21461 raw21461Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw21461 raw21461Labels = mixedMoment B raw21461step0 raw21461step0Labels := by
      have hz : ∀ j, raw21461 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21461step0 = (fun i j => raw21461 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21461step0 raw21461; decide +kernel
      have hl : raw21461step0Labels = raw21461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21461 raw21461Labels permutation520 hz
    mixedMoment B raw21461step0 raw21461step0Labels = mixedMoment B raw21461step1 raw21461step1Labels := by
      have hz : ∀ j, raw21461step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21461step1 = (fun i j => raw21461step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21461step1 raw21461step0; decide +kernel
      have hl : raw21461step1Labels = raw21461step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21461step0 raw21461step0Labels permutation104 hz
    mixedMoment B raw21461step1 raw21461step1Labels = mixedMoment B raw21461step2 raw21461step2Labels := by
      have hz : ∀ j, raw21461step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw21461step2 = (fun i j => raw21461step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw21461step2 raw21461step1; decide +kernel
      have hl : raw21461step2Labels = raw21461step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21461step1 raw21461step1Labels permutation20 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw21462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21462Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21462step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21462step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21462 raw21462Labels = mixedMoment B node924 node924Labels := by
  calc
    mixedMoment B raw21462 raw21462Labels = mixedMoment B raw21462step0 raw21462step0Labels := by
      have hz : ∀ j, raw21462 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21462step0 = (fun i j => raw21462 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21462step0 raw21462; decide +kernel
      have hl : raw21462step0Labels = raw21462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21462 raw21462Labels permutation434 hz
    mixedMoment B raw21462step0 raw21462step0Labels = mixedMoment B raw21462step1 raw21462step1Labels := by
      have ha : raw21462step1 = (fun i j => raw21462step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21462step1 raw21462step0; decide +kernel
      have hl : raw21462step1Labels = raw21462step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21462step0 raw21462step0Labels permutation40 permutation2
    _ = mixedMoment B node924 node924Labels := by rfl

def raw21463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21463Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21463step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21463step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21463step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21463 raw21463Labels = mixedMoment B node924 node924Labels := by
  calc
    mixedMoment B raw21463 raw21463Labels = mixedMoment B raw21463step0 raw21463step0Labels := by
      have hz : ∀ j, raw21463 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21463step0 = (fun i j => raw21463 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21463step0 raw21463; decide +kernel
      have hl : raw21463step0Labels = raw21463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21463 raw21463Labels permutation346 hz
    mixedMoment B raw21463step0 raw21463step0Labels = mixedMoment B raw21463step1 raw21463step1Labels := by
      have ha : raw21463step1 = (fun i j => raw21463step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21463step1 raw21463step0; decide +kernel
      have hl : raw21463step1Labels = raw21463step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21463step0 raw21463step0Labels permutation40 permutation2
    _ = mixedMoment B node924 node924Labels := by rfl

def raw21464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21464Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21464step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21464step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw21464step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21464step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw21464step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21464 raw21464Labels = mixedMoment B node1089 node1089Labels := by
  calc
    mixedMoment B raw21464 raw21464Labels = mixedMoment B raw21464step0 raw21464step0Labels := by
      have hz : ∀ j, raw21464 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21464step0 = (fun i j => raw21464 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21464step0 raw21464; decide +kernel
      have hl : raw21464step0Labels = raw21464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21464 raw21464Labels permutation520 hz
    mixedMoment B raw21464step0 raw21464step0Labels = mixedMoment B raw21464step1 raw21464step1Labels := by
      have hz : ∀ j, raw21464step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21464step1 = (fun i j => raw21464step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21464step1 raw21464step0; decide +kernel
      have hl : raw21464step1Labels = raw21464step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21464step0 raw21464step0Labels permutation104 hz
    mixedMoment B raw21464step1 raw21464step1Labels = mixedMoment B raw21464step2 raw21464step2Labels := by
      have hz : ∀ j, raw21464step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw21464step2 = (fun i j => raw21464step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw21464step2 raw21464step1; decide +kernel
      have hl : raw21464step2Labels = raw21464step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21464step1 raw21464step1Labels permutation20 hz
    _ = mixedMoment B node1089 node1089Labels := by rfl

def raw21465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21465Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21465step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21465step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw21465step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21465step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw21465step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21465 raw21465Labels = mixedMoment B node1082 node1082Labels := by
  calc
    mixedMoment B raw21465 raw21465Labels = mixedMoment B raw21465step0 raw21465step0Labels := by
      have hz : ∀ j, raw21465 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21465step0 = (fun i j => raw21465 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21465step0 raw21465; decide +kernel
      have hl : raw21465step0Labels = raw21465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21465 raw21465Labels permutation434 hz
    mixedMoment B raw21465step0 raw21465step0Labels = mixedMoment B raw21465step1 raw21465step1Labels := by
      have hz : ∀ j, raw21465step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21465step1 = (fun i j => raw21465step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21465step1 raw21465step0; decide +kernel
      have hl : raw21465step1Labels = raw21465step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21465step0 raw21465step0Labels permutation80 hz
    mixedMoment B raw21465step1 raw21465step1Labels = mixedMoment B raw21465step2 raw21465step2Labels := by
      have ha : raw21465step2 = (fun i j => raw21465step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21465step2 raw21465step1; decide +kernel
      have hl : raw21465step2Labels = raw21465step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21465step1 raw21465step1Labels permutation10 permutation2
    _ = mixedMoment B node1082 node1082Labels := by rfl

def raw21466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21466Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21466step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21466step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21466step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21466 raw21466Labels = mixedMoment B node2109 node2109Labels := by
  calc
    mixedMoment B raw21466 raw21466Labels = mixedMoment B raw21466step0 raw21466step0Labels := by
      have hz : ∀ j, raw21466 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21466step0 = (fun i j => raw21466 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21466step0 raw21466; decide +kernel
      have hl : raw21466step0Labels = raw21466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21466 raw21466Labels permutation434 hz
    mixedMoment B raw21466step0 raw21466step0Labels = mixedMoment B raw21466step1 raw21466step1Labels := by
      have hz : ∀ j, raw21466step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21466step1 = (fun i j => raw21466step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21466step1 raw21466step0; decide +kernel
      have hl : raw21466step1Labels = raw21466step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21466step0 raw21466step0Labels permutation80 hz
    _ = mixedMoment B node2109 node2109Labels := by rfl

def raw21467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21467Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21467step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21467 raw21467Labels = mixedMoment B node943 node943Labels := by
  calc
    mixedMoment B raw21467 raw21467Labels = mixedMoment B raw21467step0 raw21467step0Labels := by
      have hz : ∀ j, raw21467 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21467step0 = (fun i j => raw21467 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21467step0 raw21467; decide +kernel
      have hl : raw21467step0Labels = raw21467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21467 raw21467Labels permutation434 hz
    _ = mixedMoment B node943 node943Labels := by rfl

def raw21468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21468Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21468step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21468 raw21468Labels = mixedMoment B node943 node943Labels := by
  calc
    mixedMoment B raw21468 raw21468Labels = mixedMoment B raw21468step0 raw21468step0Labels := by
      have hz : ∀ j, raw21468 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21468step0 = (fun i j => raw21468 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21468step0 raw21468; decide +kernel
      have hl : raw21468step0Labels = raw21468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21468 raw21468Labels permutation346 hz
    _ = mixedMoment B node943 node943Labels := by rfl

def raw21469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21469Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21469step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21469step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw21469step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21469 raw21469Labels = mixedMoment B node952 node952Labels := by
  calc
    mixedMoment B raw21469 raw21469Labels = mixedMoment B raw21469step0 raw21469step0Labels := by
      have hz : ∀ j, raw21469 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21469step0 = (fun i j => raw21469 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21469step0 raw21469; decide +kernel
      have hl : raw21469step0Labels = raw21469Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21469 raw21469Labels permutation434 hz
    mixedMoment B raw21469step0 raw21469step0Labels = mixedMoment B raw21469step1 raw21469step1Labels := by
      have hz : ∀ j, raw21469step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21469step1 = (fun i j => raw21469step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21469step1 raw21469step0; decide +kernel
      have hl : raw21469step1Labels = raw21469step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21469step0 raw21469step0Labels permutation80 hz
    _ = mixedMoment B node952 node952Labels := by rfl

def raw21470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21470Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21470step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21470step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![4, -2, -2]]
def raw21470step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21470 raw21470Labels = mixedMoment B node948 node948Labels := by
  calc
    mixedMoment B raw21470 raw21470Labels = mixedMoment B raw21470step0 raw21470step0Labels := by
      have hz : ∀ j, raw21470 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21470step0 = (fun i j => raw21470 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21470step0 raw21470; decide +kernel
      have hl : raw21470step0Labels = raw21470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21470 raw21470Labels permutation434 hz
    mixedMoment B raw21470step0 raw21470step0Labels = mixedMoment B raw21470step1 raw21470step1Labels := by
      have hz : ∀ j, raw21470step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21470step1 = (fun i j => raw21470step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21470step1 raw21470step0; decide +kernel
      have hl : raw21470step1Labels = raw21470step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21470step0 raw21470step0Labels permutation80 hz
    _ = mixedMoment B node948 node948Labels := by rfl

def raw21471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21471Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21471step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21471 raw21471Labels = mixedMoment B node904 node904Labels := by
  calc
    mixedMoment B raw21471 raw21471Labels = mixedMoment B raw21471step0 raw21471step0Labels := by
      have ha : raw21471step0 = (fun i j => raw21471 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21471step0 raw21471; decide +kernel
      have hl : raw21471step0Labels = raw21471Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21471 raw21471Labels permutation200 permutation2
    _ = mixedMoment B node904 node904Labels := by rfl

def raw21472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21472Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21472step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21472step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21472step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21472 raw21472Labels = mixedMoment B node1043 node1043Labels := by
  calc
    mixedMoment B raw21472 raw21472Labels = mixedMoment B raw21472step0 raw21472step0Labels := by
      have hz : ∀ j, raw21472 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21472step0 = (fun i j => raw21472 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21472step0 raw21472; decide +kernel
      have hl : raw21472step0Labels = raw21472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21472 raw21472Labels permutation520 hz
    mixedMoment B raw21472step0 raw21472step0Labels = mixedMoment B raw21472step1 raw21472step1Labels := by
      have hz : ∀ j, raw21472step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21472step1 = (fun i j => raw21472step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21472step1 raw21472step0; decide +kernel
      have hl : raw21472step1Labels = raw21472step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21472step0 raw21472step0Labels permutation104 hz
    _ = mixedMoment B node1043 node1043Labels := by rfl

def raw21473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21473Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21473step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21473 raw21473Labels = mixedMoment B node1040 node1040Labels := by
  calc
    mixedMoment B raw21473 raw21473Labels = mixedMoment B raw21473step0 raw21473step0Labels := by
      have hz : ∀ j, raw21473 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21473step0 = (fun i j => raw21473 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21473step0 raw21473; decide +kernel
      have hl : raw21473step0Labels = raw21473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21473 raw21473Labels permutation434 hz
    _ = mixedMoment B node1040 node1040Labels := by rfl

def raw21474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21474Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21474step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21474step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21474step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21474 raw21474Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw21474 raw21474Labels = mixedMoment B raw21474step0 raw21474step0Labels := by
      have hz : ∀ j, raw21474 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21474step0 = (fun i j => raw21474 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21474step0 raw21474; decide +kernel
      have hl : raw21474step0Labels = raw21474Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21474 raw21474Labels permutation434 hz
    mixedMoment B raw21474step0 raw21474step0Labels = mixedMoment B raw21474step1 raw21474step1Labels := by
      have ha : raw21474step1 = (fun i j => raw21474step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21474step1 raw21474step0; decide +kernel
      have hl : raw21474step1Labels = raw21474step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21474step0 raw21474step0Labels permutation38 permutation2
    _ = mixedMoment B node2022 node2022Labels := by rfl

def raw21475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21475Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21475step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21475step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21475 raw21475Labels = mixedMoment B node904 node904Labels := by
  calc
    mixedMoment B raw21475 raw21475Labels = mixedMoment B raw21475step0 raw21475step0Labels := by
      have ha : raw21475step0 = (fun i j => raw21475 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21475step0 raw21475; decide +kernel
      have hl : raw21475step0Labels = raw21475Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21475 raw21475Labels permutation176 permutation2
    _ = mixedMoment B node904 node904Labels := by rfl

def raw21476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21476Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21476step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21476step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw21476step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21476 raw21476Labels = mixedMoment B node912 node912Labels := by
  calc
    mixedMoment B raw21476 raw21476Labels = mixedMoment B raw21476step0 raw21476step0Labels := by
      have hz : ∀ j, raw21476 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21476step0 = (fun i j => raw21476 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21476step0 raw21476; decide +kernel
      have hl : raw21476step0Labels = raw21476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21476 raw21476Labels permutation434 hz
    mixedMoment B raw21476step0 raw21476step0Labels = mixedMoment B raw21476step1 raw21476step1Labels := by
      have ha : raw21476step1 = (fun i j => raw21476step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21476step1 raw21476step0; decide +kernel
      have hl : raw21476step1Labels = raw21476step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21476step0 raw21476step0Labels permutation38 permutation2
    _ = mixedMoment B node912 node912Labels := by rfl

def raw21477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21477Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21477step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21477step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw21477step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21477 raw21477Labels = mixedMoment B node908 node908Labels := by
  calc
    mixedMoment B raw21477 raw21477Labels = mixedMoment B raw21477step0 raw21477step0Labels := by
      have hz : ∀ j, raw21477 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21477step0 = (fun i j => raw21477 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21477step0 raw21477; decide +kernel
      have hl : raw21477step0Labels = raw21477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21477 raw21477Labels permutation434 hz
    mixedMoment B raw21477step0 raw21477step0Labels = mixedMoment B raw21477step1 raw21477step1Labels := by
      have ha : raw21477step1 = (fun i j => raw21477step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21477step1 raw21477step0; decide +kernel
      have hl : raw21477step1Labels = raw21477step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21477step0 raw21477step0Labels permutation38 permutation2
    _ = mixedMoment B node908 node908Labels := by rfl

def raw21478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21478step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21478step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21478step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw21478step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21478step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw21478step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21478 raw21478Labels = mixedMoment B node4121 node4121Labels := by
  calc
    mixedMoment B raw21478 raw21478Labels = mixedMoment B raw21478step0 raw21478step0Labels := by
      have hz : ∀ j, raw21478 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21478step0 = (fun i j => raw21478 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21478step0 raw21478; decide +kernel
      have hl : raw21478step0Labels = raw21478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21478 raw21478Labels permutation434 hz
    mixedMoment B raw21478step0 raw21478step0Labels = mixedMoment B raw21478step1 raw21478step1Labels := by
      have hz : ∀ j, raw21478step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21478step1 = (fun i j => raw21478step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21478step1 raw21478step0; decide +kernel
      have hl : raw21478step1Labels = raw21478step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21478step0 raw21478step0Labels permutation80 hz
    mixedMoment B raw21478step1 raw21478step1Labels = mixedMoment B raw21478step2 raw21478step2Labels := by
      have ha : raw21478step2 = (fun i j => raw21478step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21478step2 raw21478step1; decide +kernel
      have hl : raw21478step2Labels = raw21478step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21478step1 raw21478step1Labels permutation10 permutation3
    mixedMoment B raw21478step2 raw21478step2Labels = mixedMoment B raw21478step3 raw21478step3Labels := by
      have ha : raw21478step3 = raw21478step2 := by apply Matrix.ext; unfold raw21478step3 raw21478step2; decide +kernel
      have hl : raw21478step2Labels = labelEmbedding6 ∘ raw21478step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21478step2 raw21478step2Labels raw21478step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4121 node4121Labels := by rfl

def raw21479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21479step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21479step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw21479step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21479step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw21479step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21479 raw21479Labels = mixedMoment B node4303 node4303Labels := by
  calc
    mixedMoment B raw21479 raw21479Labels = mixedMoment B raw21479step0 raw21479step0Labels := by
      have hz : ∀ j, raw21479 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21479step0 = (fun i j => raw21479 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21479step0 raw21479; decide +kernel
      have hl : raw21479step0Labels = raw21479Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21479 raw21479Labels permutation434 hz
    mixedMoment B raw21479step0 raw21479step0Labels = mixedMoment B raw21479step1 raw21479step1Labels := by
      have ha : raw21479step1 = (fun i j => raw21479step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21479step1 raw21479step0; decide +kernel
      have hl : raw21479step1Labels = raw21479step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21479step0 raw21479step0Labels permutation40 permutation3
    mixedMoment B raw21479step1 raw21479step1Labels = mixedMoment B raw21479step2 raw21479step2Labels := by
      have ha : raw21479step2 = raw21479step1 := by apply Matrix.ext; unfold raw21479step2 raw21479step1; decide +kernel
      have hl : raw21479step1Labels = labelEmbedding6 ∘ raw21479step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21479step1 raw21479step1Labels raw21479step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4303 node4303Labels := by rfl

def raw21480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21480step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21480step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw21480step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21480step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw21480step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21480 raw21480Labels = mixedMoment B node4303 node4303Labels := by
  calc
    mixedMoment B raw21480 raw21480Labels = mixedMoment B raw21480step0 raw21480step0Labels := by
      have hz : ∀ j, raw21480 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21480step0 = (fun i j => raw21480 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21480step0 raw21480; decide +kernel
      have hl : raw21480step0Labels = raw21480Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21480 raw21480Labels permutation346 hz
    mixedMoment B raw21480step0 raw21480step0Labels = mixedMoment B raw21480step1 raw21480step1Labels := by
      have ha : raw21480step1 = (fun i j => raw21480step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21480step1 raw21480step0; decide +kernel
      have hl : raw21480step1Labels = raw21480step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21480step0 raw21480step0Labels permutation40 permutation3
    mixedMoment B raw21480step1 raw21480step1Labels = mixedMoment B raw21480step2 raw21480step2Labels := by
      have ha : raw21480step2 = raw21480step1 := by apply Matrix.ext; unfold raw21480step2 raw21480step1; decide +kernel
      have hl : raw21480step1Labels = labelEmbedding6 ∘ raw21480step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21480step1 raw21480step1Labels raw21480step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4303 node4303Labels := by rfl

def raw21481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21481step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21481step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw21481step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21481step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21481step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21481step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21481step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21481 raw21481Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw21481 raw21481Labels = mixedMoment B raw21481step0 raw21481step0Labels := by
      have hz : ∀ j, raw21481 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21481step0 = (fun i j => raw21481 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21481step0 raw21481; decide +kernel
      have hl : raw21481step0Labels = raw21481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21481 raw21481Labels permutation434 hz
    mixedMoment B raw21481step0 raw21481step0Labels = mixedMoment B raw21481step1 raw21481step1Labels := by
      have hz : ∀ j, raw21481step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21481step1 = (fun i j => raw21481step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21481step1 raw21481step0; decide +kernel
      have hl : raw21481step1Labels = raw21481step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21481step0 raw21481step0Labels permutation80 hz
    mixedMoment B raw21481step1 raw21481step1Labels = mixedMoment B raw21481step2 raw21481step2Labels := by
      have ha : raw21481step2 = (fun i j => raw21481step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21481step2 raw21481step1; decide +kernel
      have hl : raw21481step2Labels = raw21481step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21481step1 raw21481step1Labels permutation10 permutation3
    mixedMoment B raw21481step2 raw21481step2Labels = mixedMoment B raw21481step3 raw21481step3Labels := by
      have ha : raw21481step3 = raw21481step2 := by apply Matrix.ext; unfold raw21481step3 raw21481step2; decide +kernel
      have hl : raw21481step2Labels = labelEmbedding6 ∘ raw21481step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21481step2 raw21481step2Labels raw21481step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4499 node4499Labels := by rfl

def raw21482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21482step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21482step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21482step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21482step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21482step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21482 raw21482Labels = mixedMoment B node4101 node4101Labels := by
  calc
    mixedMoment B raw21482 raw21482Labels = mixedMoment B raw21482step0 raw21482step0Labels := by
      have hz : ∀ j, raw21482 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21482step0 = (fun i j => raw21482 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21482step0 raw21482; decide +kernel
      have hl : raw21482step0Labels = raw21482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21482 raw21482Labels permutation434 hz
    mixedMoment B raw21482step0 raw21482step0Labels = mixedMoment B raw21482step1 raw21482step1Labels := by
      have ha : raw21482step1 = (fun i j => raw21482step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21482step1 raw21482step0; decide +kernel
      have hl : raw21482step1Labels = raw21482step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21482step0 raw21482step0Labels permutation34 permutation3
    mixedMoment B raw21482step1 raw21482step1Labels = mixedMoment B raw21482step2 raw21482step2Labels := by
      have ha : raw21482step2 = raw21482step1 := by apply Matrix.ext; unfold raw21482step2 raw21482step1; decide +kernel
      have hl : raw21482step1Labels = labelEmbedding6 ∘ raw21482step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21482step1 raw21482step1Labels raw21482step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4101 node4101Labels := by rfl

def raw21483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21483step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21483step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21483step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21483step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21483step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21483 raw21483Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw21483 raw21483Labels = mixedMoment B raw21483step0 raw21483step0Labels := by
      have hz : ∀ j, raw21483 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21483step0 = (fun i j => raw21483 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21483step0 raw21483; decide +kernel
      have hl : raw21483step0Labels = raw21483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21483 raw21483Labels permutation434 hz
    mixedMoment B raw21483step0 raw21483step0Labels = mixedMoment B raw21483step1 raw21483step1Labels := by
      have ha : raw21483step1 = (fun i j => raw21483step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21483step1 raw21483step0; decide +kernel
      have hl : raw21483step1Labels = raw21483step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21483step0 raw21483step0Labels permutation34 permutation3
    mixedMoment B raw21483step1 raw21483step1Labels = mixedMoment B raw21483step2 raw21483step2Labels := by
      have ha : raw21483step2 = raw21483step1 := by apply Matrix.ext; unfold raw21483step2 raw21483step1; decide +kernel
      have hl : raw21483step1Labels = labelEmbedding6 ∘ raw21483step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21483step1 raw21483step1Labels raw21483step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4346 node4346Labels := by rfl

def raw21484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21484step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21484step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21484step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21484 raw21484Labels = mixedMoment B node4287 node4287Labels := by
  calc
    mixedMoment B raw21484 raw21484Labels = mixedMoment B raw21484step0 raw21484step0Labels := by
      have ha : raw21484step0 = (fun i j => raw21484 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21484step0 raw21484; decide +kernel
      have hl : raw21484step0Labels = raw21484Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21484 raw21484Labels permutation202 permutation3
    mixedMoment B raw21484step0 raw21484step0Labels = mixedMoment B raw21484step1 raw21484step1Labels := by
      have ha : raw21484step1 = raw21484step0 := by apply Matrix.ext; unfold raw21484step1 raw21484step0; decide +kernel
      have hl : raw21484step0Labels = labelEmbedding6 ∘ raw21484step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21484step0 raw21484step0Labels raw21484step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4287 node4287Labels := by rfl

def raw21485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21485step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21485step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21485step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21485step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21485step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21485 raw21485Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw21485 raw21485Labels = mixedMoment B raw21485step0 raw21485step0Labels := by
      have hz : ∀ j, raw21485 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21485step0 = (fun i j => raw21485 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21485step0 raw21485; decide +kernel
      have hl : raw21485step0Labels = raw21485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21485 raw21485Labels permutation434 hz
    mixedMoment B raw21485step0 raw21485step0Labels = mixedMoment B raw21485step1 raw21485step1Labels := by
      have ha : raw21485step1 = (fun i j => raw21485step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21485step1 raw21485step0; decide +kernel
      have hl : raw21485step1Labels = raw21485step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21485step0 raw21485step0Labels permutation34 permutation3
    mixedMoment B raw21485step1 raw21485step1Labels = mixedMoment B raw21485step2 raw21485step2Labels := by
      have ha : raw21485step2 = raw21485step1 := by apply Matrix.ext; unfold raw21485step2 raw21485step1; decide +kernel
      have hl : raw21485step1Labels = labelEmbedding6 ∘ raw21485step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21485step1 raw21485step1Labels raw21485step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw21486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21486step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21486step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21486step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21486step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21486step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21486 raw21486Labels = mixedMoment B node4101 node4101Labels := by
  calc
    mixedMoment B raw21486 raw21486Labels = mixedMoment B raw21486step0 raw21486step0Labels := by
      have hz : ∀ j, raw21486 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21486step0 = (fun i j => raw21486 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21486step0 raw21486; decide +kernel
      have hl : raw21486step0Labels = raw21486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21486 raw21486Labels permutation346 hz
    mixedMoment B raw21486step0 raw21486step0Labels = mixedMoment B raw21486step1 raw21486step1Labels := by
      have ha : raw21486step1 = (fun i j => raw21486step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21486step1 raw21486step0; decide +kernel
      have hl : raw21486step1Labels = raw21486step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21486step0 raw21486step0Labels permutation34 permutation3
    mixedMoment B raw21486step1 raw21486step1Labels = mixedMoment B raw21486step2 raw21486step2Labels := by
      have ha : raw21486step2 = raw21486step1 := by apply Matrix.ext; unfold raw21486step2 raw21486step1; decide +kernel
      have hl : raw21486step1Labels = labelEmbedding6 ∘ raw21486step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21486step1 raw21486step1Labels raw21486step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4101 node4101Labels := by rfl

def raw21487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21487Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21487step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21487step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21487step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21487step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21487 raw21487Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw21487 raw21487Labels = mixedMoment B raw21487step0 raw21487step0Labels := by
      have hz : ∀ j, raw21487 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21487step0 = (fun i j => raw21487 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21487step0 raw21487; decide +kernel
      have hl : raw21487step0Labels = raw21487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21487 raw21487Labels permutation346 hz
    mixedMoment B raw21487step0 raw21487step0Labels = mixedMoment B raw21487step1 raw21487step1Labels := by
      have ha : raw21487step1 = (fun i j => raw21487step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21487step1 raw21487step0; decide +kernel
      have hl : raw21487step1Labels = raw21487step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21487step0 raw21487step0Labels permutation34 permutation3
    mixedMoment B raw21487step1 raw21487step1Labels = mixedMoment B raw21487step2 raw21487step2Labels := by
      have ha : raw21487step2 = raw21487step1 := by apply Matrix.ext; unfold raw21487step2 raw21487step1; decide +kernel
      have hl : raw21487step1Labels = labelEmbedding6 ∘ raw21487step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21487step1 raw21487step1Labels raw21487step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4346 node4346Labels := by rfl

def raw21488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21488Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21488step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21488step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21488step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21488step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21488 raw21488Labels = mixedMoment B node4287 node4287Labels := by
  calc
    mixedMoment B raw21488 raw21488Labels = mixedMoment B raw21488step0 raw21488step0Labels := by
      have ha : raw21488step0 = (fun i j => raw21488 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21488step0 raw21488; decide +kernel
      have hl : raw21488step0Labels = raw21488Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21488 raw21488Labels permutation178 permutation3
    mixedMoment B raw21488step0 raw21488step0Labels = mixedMoment B raw21488step1 raw21488step1Labels := by
      have ha : raw21488step1 = raw21488step0 := by apply Matrix.ext; unfold raw21488step1 raw21488step0; decide +kernel
      have hl : raw21488step0Labels = labelEmbedding6 ∘ raw21488step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21488step0 raw21488step0Labels raw21488step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4287 node4287Labels := by rfl

def raw21489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21489Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21489step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21489step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21489step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21489step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21489step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21489 raw21489Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw21489 raw21489Labels = mixedMoment B raw21489step0 raw21489step0Labels := by
      have hz : ∀ j, raw21489 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21489step0 = (fun i j => raw21489 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21489step0 raw21489; decide +kernel
      have hl : raw21489step0Labels = raw21489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21489 raw21489Labels permutation346 hz
    mixedMoment B raw21489step0 raw21489step0Labels = mixedMoment B raw21489step1 raw21489step1Labels := by
      have ha : raw21489step1 = (fun i j => raw21489step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21489step1 raw21489step0; decide +kernel
      have hl : raw21489step1Labels = raw21489step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21489step0 raw21489step0Labels permutation34 permutation3
    mixedMoment B raw21489step1 raw21489step1Labels = mixedMoment B raw21489step2 raw21489step2Labels := by
      have ha : raw21489step2 = raw21489step1 := by apply Matrix.ext; unfold raw21489step2 raw21489step1; decide +kernel
      have hl : raw21489step1Labels = labelEmbedding6 ∘ raw21489step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21489step1 raw21489step1Labels raw21489step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw21490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21490Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21490step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21490step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![2, -1, -1], ![3, -2, -1]]
def raw21490step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21490step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw21490step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21490step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw21490step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21490 raw21490Labels = mixedMoment B node4110 node4110Labels := by
  calc
    mixedMoment B raw21490 raw21490Labels = mixedMoment B raw21490step0 raw21490step0Labels := by
      have hz : ∀ j, raw21490 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21490step0 = (fun i j => raw21490 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21490step0 raw21490; decide +kernel
      have hl : raw21490step0Labels = raw21490Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21490 raw21490Labels permutation434 hz
    mixedMoment B raw21490step0 raw21490step0Labels = mixedMoment B raw21490step1 raw21490step1Labels := by
      have hz : ∀ j, raw21490step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21490step1 = (fun i j => raw21490step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21490step1 raw21490step0; decide +kernel
      have hl : raw21490step1Labels = raw21490step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21490step0 raw21490step0Labels permutation80 hz
    mixedMoment B raw21490step1 raw21490step1Labels = mixedMoment B raw21490step2 raw21490step2Labels := by
      have ha : raw21490step2 = (fun i j => raw21490step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21490step2 raw21490step1; decide +kernel
      have hl : raw21490step2Labels = raw21490step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21490step1 raw21490step1Labels permutation8 permutation3
    mixedMoment B raw21490step2 raw21490step2Labels = mixedMoment B raw21490step3 raw21490step3Labels := by
      have ha : raw21490step3 = raw21490step2 := by apply Matrix.ext; unfold raw21490step3 raw21490step2; decide +kernel
      have hl : raw21490step2Labels = labelEmbedding6 ∘ raw21490step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21490step2 raw21490step2Labels raw21490step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4110 node4110Labels := by rfl

def raw21491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21491Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21491step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21491step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -1, -1], ![3, -2, -1]]
def raw21491step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21491step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21491step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21491step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw21491step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21491 raw21491Labels = mixedMoment B node4360 node4360Labels := by
  calc
    mixedMoment B raw21491 raw21491Labels = mixedMoment B raw21491step0 raw21491step0Labels := by
      have hz : ∀ j, raw21491 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21491step0 = (fun i j => raw21491 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21491step0 raw21491; decide +kernel
      have hl : raw21491step0Labels = raw21491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21491 raw21491Labels permutation434 hz
    mixedMoment B raw21491step0 raw21491step0Labels = mixedMoment B raw21491step1 raw21491step1Labels := by
      have hz : ∀ j, raw21491step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21491step1 = (fun i j => raw21491step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21491step1 raw21491step0; decide +kernel
      have hl : raw21491step1Labels = raw21491step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21491step0 raw21491step0Labels permutation80 hz
    mixedMoment B raw21491step1 raw21491step1Labels = mixedMoment B raw21491step2 raw21491step2Labels := by
      have ha : raw21491step2 = (fun i j => raw21491step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21491step2 raw21491step1; decide +kernel
      have hl : raw21491step2Labels = raw21491step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21491step1 raw21491step1Labels permutation8 permutation3
    mixedMoment B raw21491step2 raw21491step2Labels = mixedMoment B raw21491step3 raw21491step3Labels := by
      have ha : raw21491step3 = raw21491step2 := by apply Matrix.ext; unfold raw21491step3 raw21491step2; decide +kernel
      have hl : raw21491step2Labels = labelEmbedding6 ∘ raw21491step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21491step2 raw21491step2Labels raw21491step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4360 node4360Labels := by rfl

def raw21492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21492Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21492step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw21492step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21492step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw21492step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21492 raw21492Labels = mixedMoment B node4295 node4295Labels := by
  calc
    mixedMoment B raw21492 raw21492Labels = mixedMoment B raw21492step0 raw21492step0Labels := by
      have hz : ∀ j, raw21492 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21492step0 = (fun i j => raw21492 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21492step0 raw21492; decide +kernel
      have hl : raw21492step0Labels = raw21492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21492 raw21492Labels permutation434 hz
    mixedMoment B raw21492step0 raw21492step0Labels = mixedMoment B raw21492step1 raw21492step1Labels := by
      have ha : raw21492step1 = (fun i j => raw21492step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21492step1 raw21492step0; decide +kernel
      have hl : raw21492step1Labels = raw21492step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21492step0 raw21492step0Labels permutation38 permutation3
    mixedMoment B raw21492step1 raw21492step1Labels = mixedMoment B raw21492step2 raw21492step2Labels := by
      have ha : raw21492step2 = raw21492step1 := by apply Matrix.ext; unfold raw21492step2 raw21492step1; decide +kernel
      have hl : raw21492step1Labels = labelEmbedding6 ∘ raw21492step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21492step1 raw21492step1Labels raw21492step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4295 node4295Labels := by rfl

def raw21493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21493Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw21493step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw21493step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21493step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw21493step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21493 raw21493Labels = mixedMoment B node4295 node4295Labels := by
  calc
    mixedMoment B raw21493 raw21493Labels = mixedMoment B raw21493step0 raw21493step0Labels := by
      have hz : ∀ j, raw21493 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21493step0 = (fun i j => raw21493 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21493step0 raw21493; decide +kernel
      have hl : raw21493step0Labels = raw21493Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21493 raw21493Labels permutation346 hz
    mixedMoment B raw21493step0 raw21493step0Labels = mixedMoment B raw21493step1 raw21493step1Labels := by
      have ha : raw21493step1 = (fun i j => raw21493step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21493step1 raw21493step0; decide +kernel
      have hl : raw21493step1Labels = raw21493step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21493step0 raw21493step0Labels permutation38 permutation3
    mixedMoment B raw21493step1 raw21493step1Labels = mixedMoment B raw21493step2 raw21493step2Labels := by
      have ha : raw21493step2 = raw21493step1 := by apply Matrix.ext; unfold raw21493step2 raw21493step1; decide +kernel
      have hl : raw21493step1Labels = labelEmbedding6 ∘ raw21493step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21493step1 raw21493step1Labels raw21493step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4295 node4295Labels := by rfl

def raw21494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw21494Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw21494step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21494step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw21494step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21494step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw21494step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21494step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw21494step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21494 raw21494Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw21494 raw21494Labels = mixedMoment B raw21494step0 raw21494step0Labels := by
      have hz : ∀ j, raw21494 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21494step0 = (fun i j => raw21494 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21494step0 raw21494; decide +kernel
      have hl : raw21494step0Labels = raw21494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21494 raw21494Labels permutation434 hz
    mixedMoment B raw21494step0 raw21494step0Labels = mixedMoment B raw21494step1 raw21494step1Labels := by
      have hz : ∀ j, raw21494step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21494step1 = (fun i j => raw21494step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21494step1 raw21494step0; decide +kernel
      have hl : raw21494step1Labels = raw21494step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21494step0 raw21494step0Labels permutation80 hz
    mixedMoment B raw21494step1 raw21494step1Labels = mixedMoment B raw21494step2 raw21494step2Labels := by
      have ha : raw21494step2 = (fun i j => raw21494step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21494step2 raw21494step1; decide +kernel
      have hl : raw21494step2Labels = raw21494step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21494step1 raw21494step1Labels permutation8 permutation3
    mixedMoment B raw21494step2 raw21494step2Labels = mixedMoment B raw21494step3 raw21494step3Labels := by
      have ha : raw21494step3 = raw21494step2 := by apply Matrix.ext; unfold raw21494step3 raw21494step2; decide +kernel
      have hl : raw21494step2Labels = labelEmbedding6 ∘ raw21494step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21494step2 raw21494step2Labels raw21494step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4467 node4467Labels := by rfl

def raw21495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21495Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21495step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21495step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, 0, -1], ![4, -3, -1]]
def raw21495step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21495step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw21495step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21495step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw21495step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21495 raw21495Labels = mixedMoment B node4103 node4103Labels := by
  calc
    mixedMoment B raw21495 raw21495Labels = mixedMoment B raw21495step0 raw21495step0Labels := by
      have hz : ∀ j, raw21495 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21495step0 = (fun i j => raw21495 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21495step0 raw21495; decide +kernel
      have hl : raw21495step0Labels = raw21495Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21495 raw21495Labels permutation434 hz
    mixedMoment B raw21495step0 raw21495step0Labels = mixedMoment B raw21495step1 raw21495step1Labels := by
      have hz : ∀ j, raw21495step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21495step1 = (fun i j => raw21495step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21495step1 raw21495step0; decide +kernel
      have hl : raw21495step1Labels = raw21495step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21495step0 raw21495step0Labels permutation80 hz
    mixedMoment B raw21495step1 raw21495step1Labels = mixedMoment B raw21495step2 raw21495step2Labels := by
      have ha : raw21495step2 = (fun i j => raw21495step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21495step2 raw21495step1; decide +kernel
      have hl : raw21495step2Labels = raw21495step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21495step1 raw21495step1Labels permutation8 permutation3
    mixedMoment B raw21495step2 raw21495step2Labels = mixedMoment B raw21495step3 raw21495step3Labels := by
      have ha : raw21495step3 = raw21495step2 := by apply Matrix.ext; unfold raw21495step3 raw21495step2; decide +kernel
      have hl : raw21495step2Labels = labelEmbedding6 ∘ raw21495step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21495step2 raw21495step2Labels raw21495step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4103 node4103Labels := by rfl

def raw21496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21496Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21496step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21496step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![4, -3, -1]]
def raw21496step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21496step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw21496step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21496step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw21496step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21496 raw21496Labels = mixedMoment B node4350 node4350Labels := by
  calc
    mixedMoment B raw21496 raw21496Labels = mixedMoment B raw21496step0 raw21496step0Labels := by
      have hz : ∀ j, raw21496 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21496step0 = (fun i j => raw21496 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21496step0 raw21496; decide +kernel
      have hl : raw21496step0Labels = raw21496Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21496 raw21496Labels permutation434 hz
    mixedMoment B raw21496step0 raw21496step0Labels = mixedMoment B raw21496step1 raw21496step1Labels := by
      have hz : ∀ j, raw21496step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21496step1 = (fun i j => raw21496step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21496step1 raw21496step0; decide +kernel
      have hl : raw21496step1Labels = raw21496step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21496step0 raw21496step0Labels permutation80 hz
    mixedMoment B raw21496step1 raw21496step1Labels = mixedMoment B raw21496step2 raw21496step2Labels := by
      have ha : raw21496step2 = (fun i j => raw21496step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21496step2 raw21496step1; decide +kernel
      have hl : raw21496step2Labels = raw21496step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21496step1 raw21496step1Labels permutation8 permutation3
    mixedMoment B raw21496step2 raw21496step2Labels = mixedMoment B raw21496step3 raw21496step3Labels := by
      have ha : raw21496step3 = raw21496step2 := by apply Matrix.ext; unfold raw21496step3 raw21496step2; decide +kernel
      have hl : raw21496step2Labels = labelEmbedding6 ∘ raw21496step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21496step2 raw21496step2Labels raw21496step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4350 node4350Labels := by rfl

def raw21497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21497Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21497step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw21497step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21497step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw21497step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21497 raw21497Labels = mixedMoment B node4289 node4289Labels := by
  calc
    mixedMoment B raw21497 raw21497Labels = mixedMoment B raw21497step0 raw21497step0Labels := by
      have hz : ∀ j, raw21497 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21497step0 = (fun i j => raw21497 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21497step0 raw21497; decide +kernel
      have hl : raw21497step0Labels = raw21497Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21497 raw21497Labels permutation434 hz
    mixedMoment B raw21497step0 raw21497step0Labels = mixedMoment B raw21497step1 raw21497step1Labels := by
      have ha : raw21497step1 = (fun i j => raw21497step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21497step1 raw21497step0; decide +kernel
      have hl : raw21497step1Labels = raw21497step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21497step0 raw21497step0Labels permutation38 permutation3
    mixedMoment B raw21497step1 raw21497step1Labels = mixedMoment B raw21497step2 raw21497step2Labels := by
      have ha : raw21497step2 = raw21497step1 := by apply Matrix.ext; unfold raw21497step2 raw21497step1; decide +kernel
      have hl : raw21497step1Labels = labelEmbedding6 ∘ raw21497step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21497step1 raw21497step1Labels raw21497step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4289 node4289Labels := by rfl

def raw21498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21498Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw21498step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw21498step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21498step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw21498step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21498 raw21498Labels = mixedMoment B node4289 node4289Labels := by
  calc
    mixedMoment B raw21498 raw21498Labels = mixedMoment B raw21498step0 raw21498step0Labels := by
      have hz : ∀ j, raw21498 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21498step0 = (fun i j => raw21498 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21498step0 raw21498; decide +kernel
      have hl : raw21498step0Labels = raw21498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21498 raw21498Labels permutation346 hz
    mixedMoment B raw21498step0 raw21498step0Labels = mixedMoment B raw21498step1 raw21498step1Labels := by
      have ha : raw21498step1 = (fun i j => raw21498step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21498step1 raw21498step0; decide +kernel
      have hl : raw21498step1Labels = raw21498step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21498step0 raw21498step0Labels permutation38 permutation3
    mixedMoment B raw21498step1 raw21498step1Labels = mixedMoment B raw21498step2 raw21498step2Labels := by
      have ha : raw21498step2 = raw21498step1 := by apply Matrix.ext; unfold raw21498step2 raw21498step1; decide +kernel
      have hl : raw21498step1Labels = labelEmbedding6 ∘ raw21498step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21498step1 raw21498step1Labels raw21498step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4289 node4289Labels := by rfl

def raw21499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21499Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21499step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21499step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21499step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21499step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw21499step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21499 raw21499Labels = mixedMoment B node555 node555Labels := by
  calc
    mixedMoment B raw21499 raw21499Labels = mixedMoment B raw21499step0 raw21499step0Labels := by
      have hz : ∀ j, raw21499 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21499step0 = (fun i j => raw21499 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21499step0 raw21499; decide +kernel
      have hl : raw21499step0Labels = raw21499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21499 raw21499Labels permutation434 hz
    mixedMoment B raw21499step0 raw21499step0Labels = mixedMoment B raw21499step1 raw21499step1Labels := by
      have hz : ∀ j, raw21499step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21499step1 = (fun i j => raw21499step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21499step1 raw21499step0; decide +kernel
      have hl : raw21499step1Labels = raw21499step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21499step0 raw21499step0Labels permutation80 hz
    mixedMoment B raw21499step1 raw21499step1Labels = mixedMoment B raw21499step2 raw21499step2Labels := by
      have ha : raw21499step2 = (fun i j => raw21499step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21499step2 raw21499step1; decide +kernel
      have hl : raw21499step2Labels = raw21499step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21499step1 raw21499step1Labels permutation10 permutation3
    _ = mixedMoment B node555 node555Labels := by rfl

def raw21500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21500Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21500step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21500step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw21500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21500 raw21500Labels = mixedMoment B node881 node881Labels := by
  calc
    mixedMoment B raw21500 raw21500Labels = mixedMoment B raw21500step0 raw21500step0Labels := by
      have hz : ∀ j, raw21500 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21500step0 = (fun i j => raw21500 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21500step0 raw21500; decide +kernel
      have hl : raw21500step0Labels = raw21500Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21500 raw21500Labels permutation434 hz
    mixedMoment B raw21500step0 raw21500step0Labels = mixedMoment B raw21500step1 raw21500step1Labels := by
      have ha : raw21500step1 = (fun i j => raw21500step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21500step1 raw21500step0; decide +kernel
      have hl : raw21500step1Labels = raw21500step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21500step0 raw21500step0Labels permutation40 permutation3
    _ = mixedMoment B node881 node881Labels := by rfl

def raw21501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21501Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21501step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21501step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw21501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21501 raw21501Labels = mixedMoment B node881 node881Labels := by
  calc
    mixedMoment B raw21501 raw21501Labels = mixedMoment B raw21501step0 raw21501step0Labels := by
      have hz : ∀ j, raw21501 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21501step0 = (fun i j => raw21501 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21501step0 raw21501; decide +kernel
      have hl : raw21501step0Labels = raw21501Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21501 raw21501Labels permutation346 hz
    mixedMoment B raw21501step0 raw21501step0Labels = mixedMoment B raw21501step1 raw21501step1Labels := by
      have ha : raw21501step1 = (fun i j => raw21501step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21501step1 raw21501step0; decide +kernel
      have hl : raw21501step1Labels = raw21501step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21501step0 raw21501step0Labels permutation40 permutation3
    _ = mixedMoment B node881 node881Labels := by rfl

def raw21502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21502Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21502step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21502step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw21502step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21502step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw21502step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21502 raw21502Labels = mixedMoment B node1083 node1083Labels := by
  calc
    mixedMoment B raw21502 raw21502Labels = mixedMoment B raw21502step0 raw21502step0Labels := by
      have hz : ∀ j, raw21502 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21502step0 = (fun i j => raw21502 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21502step0 raw21502; decide +kernel
      have hl : raw21502step0Labels = raw21502Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21502 raw21502Labels permutation434 hz
    mixedMoment B raw21502step0 raw21502step0Labels = mixedMoment B raw21502step1 raw21502step1Labels := by
      have hz : ∀ j, raw21502step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21502step1 = (fun i j => raw21502step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21502step1 raw21502step0; decide +kernel
      have hl : raw21502step1Labels = raw21502step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21502step0 raw21502step0Labels permutation80 hz
    mixedMoment B raw21502step1 raw21502step1Labels = mixedMoment B raw21502step2 raw21502step2Labels := by
      have ha : raw21502step2 = (fun i j => raw21502step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21502step2 raw21502step1; decide +kernel
      have hl : raw21502step2Labels = raw21502step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21502step1 raw21502step1Labels permutation10 permutation3
    _ = mixedMoment B node1083 node1083Labels := by rfl

def raw21503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21503Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21503step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21503step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21503 raw21503Labels = mixedMoment B node538 node538Labels := by
  calc
    mixedMoment B raw21503 raw21503Labels = mixedMoment B raw21503step0 raw21503step0Labels := by
      have hz : ∀ j, raw21503 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21503step0 = (fun i j => raw21503 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21503step0 raw21503; decide +kernel
      have hl : raw21503step0Labels = raw21503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21503 raw21503Labels permutation434 hz
    mixedMoment B raw21503step0 raw21503step0Labels = mixedMoment B raw21503step1 raw21503step1Labels := by
      have ha : raw21503step1 = (fun i j => raw21503step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21503step1 raw21503step0; decide +kernel
      have hl : raw21503step1Labels = raw21503step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21503step0 raw21503step0Labels permutation34 permutation3
    _ = mixedMoment B node538 node538Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
