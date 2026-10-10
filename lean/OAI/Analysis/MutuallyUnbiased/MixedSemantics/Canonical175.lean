import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw22400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22400Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22400step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22400step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw22400step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22400step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw22400step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22400 raw22400Labels = mixedMoment B node1273 node1273Labels := by
  calc
    mixedMoment B raw22400 raw22400Labels = mixedMoment B raw22400step0 raw22400step0Labels := by
      have hz : ∀ j, raw22400 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22400step0 = (fun i j => raw22400 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22400step0 raw22400; decide +kernel
      have hl : raw22400step0Labels = raw22400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22400 raw22400Labels permutation434 hz
    mixedMoment B raw22400step0 raw22400step0Labels = mixedMoment B raw22400step1 raw22400step1Labels := by
      have hz : ∀ j, raw22400step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22400step1 = (fun i j => raw22400step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22400step1 raw22400step0; decide +kernel
      have hl : raw22400step1Labels = raw22400step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22400step0 raw22400step0Labels permutation80 hz
    mixedMoment B raw22400step1 raw22400step1Labels = mixedMoment B raw22400step2 raw22400step2Labels := by
      have ha : raw22400step2 = (fun i j => raw22400step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22400step2 raw22400step1; decide +kernel
      have hl : raw22400step2Labels = raw22400step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22400step1 raw22400step1Labels permutation9 permutation2
    _ = mixedMoment B node1273 node1273Labels := by rfl

def raw22401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22401Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22401step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22401step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw22401step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22401 raw22401Labels = mixedMoment B node1171 node1171Labels := by
  calc
    mixedMoment B raw22401 raw22401Labels = mixedMoment B raw22401step0 raw22401step0Labels := by
      have hz : ∀ j, raw22401 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22401step0 = (fun i j => raw22401 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22401step0 raw22401; decide +kernel
      have hl : raw22401step0Labels = raw22401Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22401 raw22401Labels permutation434 hz
    mixedMoment B raw22401step0 raw22401step0Labels = mixedMoment B raw22401step1 raw22401step1Labels := by
      have ha : raw22401step1 = (fun i j => raw22401step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22401step1 raw22401step0; decide +kernel
      have hl : raw22401step1Labels = raw22401step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22401step0 raw22401step0Labels permutation39 permutation2
    _ = mixedMoment B node1171 node1171Labels := by rfl

def raw22402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22402Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22402step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw22402step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22402 raw22402Labels = mixedMoment B node1171 node1171Labels := by
  calc
    mixedMoment B raw22402 raw22402Labels = mixedMoment B raw22402step0 raw22402step0Labels := by
      have hz : ∀ j, raw22402 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22402step0 = (fun i j => raw22402 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22402step0 raw22402; decide +kernel
      have hl : raw22402step0Labels = raw22402Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22402 raw22402Labels permutation346 hz
    mixedMoment B raw22402step0 raw22402step0Labels = mixedMoment B raw22402step1 raw22402step1Labels := by
      have ha : raw22402step1 = (fun i j => raw22402step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22402step1 raw22402step0; decide +kernel
      have hl : raw22402step1Labels = raw22402step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22402step0 raw22402step0Labels permutation39 permutation2
    _ = mixedMoment B node1171 node1171Labels := by rfl

def raw22403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw22403Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw22403step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22403step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw22403step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22403 raw22403Labels = mixedMoment B node1306 node1306Labels := by
  calc
    mixedMoment B raw22403 raw22403Labels = mixedMoment B raw22403step0 raw22403step0Labels := by
      have hz : ∀ j, raw22403 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22403step0 = (fun i j => raw22403 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22403step0 raw22403; decide +kernel
      have hl : raw22403step0Labels = raw22403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22403 raw22403Labels permutation434 hz
    mixedMoment B raw22403step0 raw22403step0Labels = mixedMoment B raw22403step1 raw22403step1Labels := by
      have hz : ∀ j, raw22403step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22403step1 = (fun i j => raw22403step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22403step1 raw22403step0; decide +kernel
      have hl : raw22403step1Labels = raw22403step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22403step0 raw22403step0Labels permutation80 hz
    _ = mixedMoment B node1306 node1306Labels := by rfl

def raw22404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -2, 1]]
def raw22404Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -2, 1]]
def raw22404step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22404step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![2, 0, -2], ![1, -2, 1]]
def raw22404step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22404step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw22404step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22404 raw22404Labels = mixedMoment B node1294 node1294Labels := by
  calc
    mixedMoment B raw22404 raw22404Labels = mixedMoment B raw22404step0 raw22404step0Labels := by
      have hz : ∀ j, raw22404 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22404step0 = (fun i j => raw22404 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22404step0 raw22404; decide +kernel
      have hl : raw22404step0Labels = raw22404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22404 raw22404Labels permutation434 hz
    mixedMoment B raw22404step0 raw22404step0Labels = mixedMoment B raw22404step1 raw22404step1Labels := by
      have hz : ∀ j, raw22404step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22404step1 = (fun i j => raw22404step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22404step1 raw22404step0; decide +kernel
      have hl : raw22404step1Labels = raw22404step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22404step0 raw22404step0Labels permutation80 hz
    mixedMoment B raw22404step1 raw22404step1Labels = mixedMoment B raw22404step2 raw22404step2Labels := by
      have ha : raw22404step2 = (fun i j => raw22404step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22404step2 raw22404step1; decide +kernel
      have hl : raw22404step2Labels = raw22404step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22404step1 raw22404step1Labels permutation12 permutation2
    _ = mixedMoment B node1294 node1294Labels := by rfl

def raw22405 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![0, 0], ![2, -2], ![-1, 1]]
def raw22405Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22405step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![2, -2], ![-1, 1]]
def raw22405step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22405step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![2, -2], ![-1, 1]]
def raw22405step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22405step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw22405step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22405 raw22405Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw22405 raw22405Labels = mixedMoment B raw22405step0 raw22405step0Labels := by
      have hz : ∀ j, raw22405 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22405step0 = (fun i j => raw22405 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22405step0 raw22405; decide +kernel
      have hl : raw22405step0Labels = raw22405Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22405 raw22405Labels permutation434 hz
    mixedMoment B raw22405step0 raw22405step0Labels = mixedMoment B raw22405step1 raw22405step1Labels := by
      have hz : ∀ j, raw22405step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22405step1 = (fun i j => raw22405step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22405step1 raw22405step0; decide +kernel
      have hl : raw22405step1Labels = raw22405step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22405step0 raw22405step0Labels permutation80 hz
    mixedMoment B raw22405step1 raw22405step1Labels = mixedMoment B raw22405step2 raw22405step2Labels := by
      have ha : raw22405step2 = (fun i j => raw22405step1 (permutation12 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22405step2 raw22405step1; decide +kernel
      have hl : raw22405step2Labels = raw22405step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22405step1 raw22405step1Labels permutation12 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw22406 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22406Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22406step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22406step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22406step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22406step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw22406step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22406 raw22406Labels = mixedMoment B node2683 node2683Labels := by
  calc
    mixedMoment B raw22406 raw22406Labels = mixedMoment B raw22406step0 raw22406step0Labels := by
      have hz : ∀ j, raw22406 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22406step0 = (fun i j => raw22406 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22406step0 raw22406; decide +kernel
      have hl : raw22406step0Labels = raw22406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22406 raw22406Labels permutation434 hz
    mixedMoment B raw22406step0 raw22406step0Labels = mixedMoment B raw22406step1 raw22406step1Labels := by
      have hz : ∀ j, raw22406step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22406step1 = (fun i j => raw22406step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22406step1 raw22406step0; decide +kernel
      have hl : raw22406step1Labels = raw22406step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22406step0 raw22406step0Labels permutation80 hz
    mixedMoment B raw22406step1 raw22406step1Labels = mixedMoment B raw22406step2 raw22406step2Labels := by
      have ha : raw22406step2 = (fun i j => raw22406step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22406step2 raw22406step1; decide +kernel
      have hl : raw22406step2Labels = raw22406step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22406step1 raw22406step1Labels permutation31 permutation4
    _ = mixedMoment B node2683 node2683Labels := by rfl

def raw22407 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22407Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22407step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22407step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22407step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22407step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw22407step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22407step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![2, -2, 0], ![2, 0, -2]]
def raw22407step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22407 raw22407Labels = mixedMoment B node1660 node1660Labels := by
  calc
    mixedMoment B raw22407 raw22407Labels = mixedMoment B raw22407step0 raw22407step0Labels := by
      have hz : ∀ j, raw22407 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22407step0 = (fun i j => raw22407 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22407step0 raw22407; decide +kernel
      have hl : raw22407step0Labels = raw22407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22407 raw22407Labels permutation434 hz
    mixedMoment B raw22407step0 raw22407step0Labels = mixedMoment B raw22407step1 raw22407step1Labels := by
      have hz : ∀ j, raw22407step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22407step1 = (fun i j => raw22407step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22407step1 raw22407step0; decide +kernel
      have hl : raw22407step1Labels = raw22407step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22407step0 raw22407step0Labels permutation80 hz
    mixedMoment B raw22407step1 raw22407step1Labels = mixedMoment B raw22407step2 raw22407step2Labels := by
      have ha : raw22407step2 = (fun i j => raw22407step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22407step2 raw22407step1; decide +kernel
      have hl : raw22407step2Labels = raw22407step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22407step1 raw22407step1Labels permutation12 permutation2
    mixedMoment B raw22407step2 raw22407step2Labels = mixedMoment B raw22407step3 raw22407step3Labels := by
      have ha : raw22407step3 = -raw22407step2 := by apply Matrix.ext; change ∀ i j, raw22407step3 i j = -(raw22407step2 i j); unfold raw22407step3 raw22407step2; decide +kernel
      have hl : raw22407step3Labels = raw22407step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1660 node1660Labels := by rfl

def raw22408 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22408Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22408step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22408step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw22408step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22408step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22408 raw22408Labels = mixedMoment B node1655 node1655Labels := by
  calc
    mixedMoment B raw22408 raw22408Labels = mixedMoment B raw22408step0 raw22408step0Labels := by
      have hz : ∀ j, raw22408 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22408step0 = (fun i j => raw22408 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22408step0 raw22408; decide +kernel
      have hl : raw22408step0Labels = raw22408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22408 raw22408Labels permutation434 hz
    mixedMoment B raw22408step0 raw22408step0Labels = mixedMoment B raw22408step1 raw22408step1Labels := by
      have ha : raw22408step1 = (fun i j => raw22408step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22408step1 raw22408step0; decide +kernel
      have hl : raw22408step1Labels = raw22408step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22408step0 raw22408step0Labels permutation50 permutation2
    mixedMoment B raw22408step1 raw22408step1Labels = mixedMoment B raw22408step2 raw22408step2Labels := by
      have ha : raw22408step2 = -raw22408step1 := by apply Matrix.ext; change ∀ i j, raw22408step2 i j = -(raw22408step1 i j); unfold raw22408step2 raw22408step1; decide +kernel
      have hl : raw22408step2Labels = raw22408step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1655 node1655Labels := by rfl

def raw22409 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22409Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22409step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22409step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw22409step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22409step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22409step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22409 raw22409Labels = mixedMoment B node1655 node1655Labels := by
  calc
    mixedMoment B raw22409 raw22409Labels = mixedMoment B raw22409step0 raw22409step0Labels := by
      have hz : ∀ j, raw22409 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22409step0 = (fun i j => raw22409 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22409step0 raw22409; decide +kernel
      have hl : raw22409step0Labels = raw22409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22409 raw22409Labels permutation346 hz
    mixedMoment B raw22409step0 raw22409step0Labels = mixedMoment B raw22409step1 raw22409step1Labels := by
      have ha : raw22409step1 = (fun i j => raw22409step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22409step1 raw22409step0; decide +kernel
      have hl : raw22409step1Labels = raw22409step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22409step0 raw22409step0Labels permutation50 permutation2
    mixedMoment B raw22409step1 raw22409step1Labels = mixedMoment B raw22409step2 raw22409step2Labels := by
      have ha : raw22409step2 = -raw22409step1 := by apply Matrix.ext; change ∀ i j, raw22409step2 i j = -(raw22409step1 i j); unfold raw22409step2 raw22409step1; decide +kernel
      have hl : raw22409step2Labels = raw22409step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1655 node1655Labels := by rfl

def raw22410 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw22410Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw22410step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22410step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw22410step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22410step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw22410step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22410step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![3, -1, -2]]
def raw22410step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22410 raw22410Labels = mixedMoment B node1657 node1657Labels := by
  calc
    mixedMoment B raw22410 raw22410Labels = mixedMoment B raw22410step0 raw22410step0Labels := by
      have hz : ∀ j, raw22410 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22410step0 = (fun i j => raw22410 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22410step0 raw22410; decide +kernel
      have hl : raw22410step0Labels = raw22410Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22410 raw22410Labels permutation434 hz
    mixedMoment B raw22410step0 raw22410step0Labels = mixedMoment B raw22410step1 raw22410step1Labels := by
      have hz : ∀ j, raw22410step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22410step1 = (fun i j => raw22410step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22410step1 raw22410step0; decide +kernel
      have hl : raw22410step1Labels = raw22410step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22410step0 raw22410step0Labels permutation80 hz
    mixedMoment B raw22410step1 raw22410step1Labels = mixedMoment B raw22410step2 raw22410step2Labels := by
      have ha : raw22410step2 = (fun i j => raw22410step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22410step2 raw22410step1; decide +kernel
      have hl : raw22410step2Labels = raw22410step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22410step1 raw22410step1Labels permutation12 permutation2
    mixedMoment B raw22410step2 raw22410step2Labels = mixedMoment B raw22410step3 raw22410step3Labels := by
      have ha : raw22410step3 = -raw22410step2 := by apply Matrix.ext; change ∀ i j, raw22410step3 i j = -(raw22410step2 i j); unfold raw22410step3 raw22410step2; decide +kernel
      have hl : raw22410step3Labels = raw22410step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1657 node1657Labels := by rfl

def raw22411 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22411Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22411step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22411step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22411step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22411step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw22411step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22411step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22411step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22411 raw22411Labels = mixedMoment B node1738 node1738Labels := by
  calc
    mixedMoment B raw22411 raw22411Labels = mixedMoment B raw22411step0 raw22411step0Labels := by
      have hz : ∀ j, raw22411 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22411step0 = (fun i j => raw22411 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22411step0 raw22411; decide +kernel
      have hl : raw22411step0Labels = raw22411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22411 raw22411Labels permutation434 hz
    mixedMoment B raw22411step0 raw22411step0Labels = mixedMoment B raw22411step1 raw22411step1Labels := by
      have hz : ∀ j, raw22411step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22411step1 = (fun i j => raw22411step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22411step1 raw22411step0; decide +kernel
      have hl : raw22411step1Labels = raw22411step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22411step0 raw22411step0Labels permutation80 hz
    mixedMoment B raw22411step1 raw22411step1Labels = mixedMoment B raw22411step2 raw22411step2Labels := by
      have ha : raw22411step2 = (fun i j => raw22411step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22411step2 raw22411step1; decide +kernel
      have hl : raw22411step2Labels = raw22411step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22411step1 raw22411step1Labels permutation12 permutation2
    mixedMoment B raw22411step2 raw22411step2Labels = mixedMoment B raw22411step3 raw22411step3Labels := by
      have ha : raw22411step3 = -raw22411step2 := by apply Matrix.ext; change ∀ i j, raw22411step3 i j = -(raw22411step2 i j); unfold raw22411step3 raw22411step2; decide +kernel
      have hl : raw22411step3Labels = raw22411step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1738 node1738Labels := by rfl

def raw22412 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22412Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22412step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22412step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22412step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22412step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 0, 2], ![1, -3, 2]]
def raw22412step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22412step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-3, 1, 2]]
def raw22412step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22412step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw22412step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22412 raw22412Labels = mixedMoment B node1741 node1741Labels := by
  calc
    mixedMoment B raw22412 raw22412Labels = mixedMoment B raw22412step0 raw22412step0Labels := by
      have hz : ∀ j, raw22412 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22412step0 = (fun i j => raw22412 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22412step0 raw22412; decide +kernel
      have hl : raw22412step0Labels = raw22412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22412 raw22412Labels permutation434 hz
    mixedMoment B raw22412step0 raw22412step0Labels = mixedMoment B raw22412step1 raw22412step1Labels := by
      have hz : ∀ j, raw22412step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22412step1 = (fun i j => raw22412step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22412step1 raw22412step0; decide +kernel
      have hl : raw22412step1Labels = raw22412step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22412step0 raw22412step0Labels permutation80 hz
    mixedMoment B raw22412step1 raw22412step1Labels = mixedMoment B raw22412step2 raw22412step2Labels := by
      have hz : ∀ j, raw22412step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22412step2 = (fun i j => raw22412step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22412step2 raw22412step1; decide +kernel
      have hl : raw22412step2Labels = raw22412step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22412step1 raw22412step1Labels permutation14 hz
    mixedMoment B raw22412step2 raw22412step2Labels = mixedMoment B raw22412step3 raw22412step3Labels := by
      have ha : raw22412step3 = (fun i j => raw22412step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22412step3 raw22412step2; decide +kernel
      have hl : raw22412step3Labels = raw22412step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22412step2 raw22412step2Labels permutation2 permutation4
    mixedMoment B raw22412step3 raw22412step3Labels = mixedMoment B raw22412step4 raw22412step4Labels := by
      have ha : raw22412step4 = -raw22412step3 := by apply Matrix.ext; change ∀ i j, raw22412step4 i j = -(raw22412step3 i j); unfold raw22412step4 raw22412step3; decide +kernel
      have hl : raw22412step4Labels = raw22412step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1741 node1741Labels := by rfl

def raw22413 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22413Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22413step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22413step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22413step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22413step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw22413step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22413 raw22413Labels = mixedMoment B node2683 node2683Labels := by
  calc
    mixedMoment B raw22413 raw22413Labels = mixedMoment B raw22413step0 raw22413step0Labels := by
      have hz : ∀ j, raw22413 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22413step0 = (fun i j => raw22413 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22413step0 raw22413; decide +kernel
      have hl : raw22413step0Labels = raw22413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22413 raw22413Labels permutation434 hz
    mixedMoment B raw22413step0 raw22413step0Labels = mixedMoment B raw22413step1 raw22413step1Labels := by
      have hz : ∀ j, raw22413step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22413step1 = (fun i j => raw22413step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22413step1 raw22413step0; decide +kernel
      have hl : raw22413step1Labels = raw22413step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22413step0 raw22413step0Labels permutation56 hz
    mixedMoment B raw22413step1 raw22413step1Labels = mixedMoment B raw22413step2 raw22413step2Labels := by
      have ha : raw22413step2 = (fun i j => raw22413step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22413step2 raw22413step1; decide +kernel
      have hl : raw22413step2Labels = raw22413step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22413step1 raw22413step1Labels permutation31 permutation4
    _ = mixedMoment B node2683 node2683Labels := by rfl

def raw22414 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22414Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22414step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22414step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw22414step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22414step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw22414step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22414 raw22414Labels = mixedMoment B node2683 node2683Labels := by
  calc
    mixedMoment B raw22414 raw22414Labels = mixedMoment B raw22414step0 raw22414step0Labels := by
      have hz : ∀ j, raw22414 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22414step0 = (fun i j => raw22414 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22414step0 raw22414; decide +kernel
      have hl : raw22414step0Labels = raw22414Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22414 raw22414Labels permutation346 hz
    mixedMoment B raw22414step0 raw22414step0Labels = mixedMoment B raw22414step1 raw22414step1Labels := by
      have hz : ∀ j, raw22414step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22414step1 = (fun i j => raw22414step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22414step1 raw22414step0; decide +kernel
      have hl : raw22414step1Labels = raw22414step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22414step0 raw22414step0Labels permutation56 hz
    mixedMoment B raw22414step1 raw22414step1Labels = mixedMoment B raw22414step2 raw22414step2Labels := by
      have ha : raw22414step2 = (fun i j => raw22414step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22414step2 raw22414step1; decide +kernel
      have hl : raw22414step2Labels = raw22414step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22414step1 raw22414step1Labels permutation31 permutation4
    _ = mixedMoment B node2683 node2683Labels := by rfl

def raw22415 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw22415Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw22415step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22415step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw22415step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22415step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-3, 1, 2], ![1, -3, 2]]
def raw22415step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22415step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![2, 2, -4]]
def raw22415step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22415 raw22415Labels = mixedMoment B node2780 node2780Labels := by
  calc
    mixedMoment B raw22415 raw22415Labels = mixedMoment B raw22415step0 raw22415step0Labels := by
      have hz : ∀ j, raw22415 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22415step0 = (fun i j => raw22415 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22415step0 raw22415; decide +kernel
      have hl : raw22415step0Labels = raw22415Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22415 raw22415Labels permutation434 hz
    mixedMoment B raw22415step0 raw22415step0Labels = mixedMoment B raw22415step1 raw22415step1Labels := by
      have hz : ∀ j, raw22415step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22415step1 = (fun i j => raw22415step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22415step1 raw22415step0; decide +kernel
      have hl : raw22415step1Labels = raw22415step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22415step0 raw22415step0Labels permutation80 hz
    mixedMoment B raw22415step1 raw22415step1Labels = mixedMoment B raw22415step2 raw22415step2Labels := by
      have hz : ∀ j, raw22415step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22415step2 = (fun i j => raw22415step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22415step2 raw22415step1; decide +kernel
      have hl : raw22415step2Labels = raw22415step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22415step1 raw22415step1Labels permutation14 hz
    mixedMoment B raw22415step2 raw22415step2Labels = mixedMoment B raw22415step3 raw22415step3Labels := by
      have ha : raw22415step3 = (fun i j => raw22415step2 (permutation5 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22415step3 raw22415step2; decide +kernel
      have hl : raw22415step3Labels = raw22415step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22415step2 raw22415step2Labels permutation5 permutation2
    _ = mixedMoment B node2780 node2780Labels := by rfl

def raw22416 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22416Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22416step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22416step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22416step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 0, 2], ![0, -2, 2]]
def raw22416step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22416step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![0, -2, 2], ![-2, 0, 2]]
def raw22416step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22416step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]
def raw22416step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22416 raw22416Labels = mixedMoment B node3311 node3311Labels := by
  calc
    mixedMoment B raw22416 raw22416Labels = mixedMoment B raw22416step0 raw22416step0Labels := by
      have hz : ∀ j, raw22416 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22416step0 = (fun i j => raw22416 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22416step0 raw22416; decide +kernel
      have hl : raw22416step0Labels = raw22416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22416 raw22416Labels permutation434 hz
    mixedMoment B raw22416step0 raw22416step0Labels = mixedMoment B raw22416step1 raw22416step1Labels := by
      have hz : ∀ j, raw22416step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22416step1 = (fun i j => raw22416step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22416step1 raw22416step0; decide +kernel
      have hl : raw22416step1Labels = raw22416step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22416step0 raw22416step0Labels permutation80 hz
    mixedMoment B raw22416step1 raw22416step1Labels = mixedMoment B raw22416step2 raw22416step2Labels := by
      have hz : ∀ j, raw22416step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22416step2 = (fun i j => raw22416step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22416step2 raw22416step1; decide +kernel
      have hl : raw22416step2Labels = raw22416step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22416step1 raw22416step1Labels permutation14 hz
    mixedMoment B raw22416step2 raw22416step2Labels = mixedMoment B raw22416step3 raw22416step3Labels := by
      have ha : raw22416step3 = (fun i j => raw22416step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22416step3 raw22416step2; decide +kernel
      have hl : raw22416step3Labels = raw22416step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22416step2 raw22416step2Labels permutation3 permutation2
    mixedMoment B raw22416step3 raw22416step3Labels = mixedMoment B raw22416step4 raw22416step4Labels := by
      have ha : raw22416step4 = -raw22416step3 := by apply Matrix.ext; change ∀ i j, raw22416step4 i j = -(raw22416step3 i j); unfold raw22416step4 raw22416step3; decide +kernel
      have hl : raw22416step4Labels = raw22416step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3311 node3311Labels := by rfl

def raw22417 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw22417Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw22417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22417step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw22417step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22417step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw22417step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22417step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22417step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22417 raw22417Labels = mixedMoment B node1627 node1627Labels := by
  calc
    mixedMoment B raw22417 raw22417Labels = mixedMoment B raw22417step0 raw22417step0Labels := by
      have hz : ∀ j, raw22417 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22417step0 = (fun i j => raw22417 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22417step0 raw22417; decide +kernel
      have hl : raw22417step0Labels = raw22417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22417 raw22417Labels permutation434 hz
    mixedMoment B raw22417step0 raw22417step0Labels = mixedMoment B raw22417step1 raw22417step1Labels := by
      have hz : ∀ j, raw22417step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22417step1 = (fun i j => raw22417step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22417step1 raw22417step0; decide +kernel
      have hl : raw22417step1Labels = raw22417step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22417step0 raw22417step0Labels permutation80 hz
    mixedMoment B raw22417step1 raw22417step1Labels = mixedMoment B raw22417step2 raw22417step2Labels := by
      have ha : raw22417step2 = (fun i j => raw22417step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22417step2 raw22417step1; decide +kernel
      have hl : raw22417step2Labels = raw22417step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22417step1 raw22417step1Labels permutation8 permutation4
    mixedMoment B raw22417step2 raw22417step2Labels = mixedMoment B raw22417step3 raw22417step3Labels := by
      have ha : raw22417step3 = -raw22417step2 := by apply Matrix.ext; change ∀ i j, raw22417step3 i j = -(raw22417step2 i j); unfold raw22417step3 raw22417step2; decide +kernel
      have hl : raw22417step3Labels = raw22417step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1627 node1627Labels := by rfl

def raw22418 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw22418Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, 0, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw22418step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22418step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw22418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22418step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -2, 0], ![2, 2, -4]]
def raw22418step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22418 raw22418Labels = mixedMoment B node2409 node2409Labels := by
  calc
    mixedMoment B raw22418 raw22418Labels = mixedMoment B raw22418step0 raw22418step0Labels := by
      have hz : ∀ j, raw22418 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22418step0 = (fun i j => raw22418 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22418step0 raw22418; decide +kernel
      have hl : raw22418step0Labels = raw22418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22418 raw22418Labels permutation434 hz
    mixedMoment B raw22418step0 raw22418step0Labels = mixedMoment B raw22418step1 raw22418step1Labels := by
      have hz : ∀ j, raw22418step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22418step1 = (fun i j => raw22418step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22418step1 raw22418step0; decide +kernel
      have hl : raw22418step1Labels = raw22418step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22418step0 raw22418step0Labels permutation80 hz
    mixedMoment B raw22418step1 raw22418step1Labels = mixedMoment B raw22418step2 raw22418step2Labels := by
      have ha : raw22418step2 = (fun i j => raw22418step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22418step2 raw22418step1; decide +kernel
      have hl : raw22418step2Labels = raw22418step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22418step1 raw22418step1Labels permutation31 permutation4
    _ = mixedMoment B node2409 node2409Labels := by rfl

def raw22419 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw22419Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw22419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22419step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw22419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22419 raw22419Labels = mixedMoment B node2397 node2397Labels := by
  calc
    mixedMoment B raw22419 raw22419Labels = mixedMoment B raw22419step0 raw22419step0Labels := by
      have hz : ∀ j, raw22419 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22419step0 = (fun i j => raw22419 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22419step0 raw22419; decide +kernel
      have hl : raw22419step0Labels = raw22419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22419 raw22419Labels permutation434 hz
    mixedMoment B raw22419step0 raw22419step0Labels = mixedMoment B raw22419step1 raw22419step1Labels := by
      have ha : raw22419step1 = (fun i j => raw22419step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22419step1 raw22419step0; decide +kernel
      have hl : raw22419step1Labels = raw22419step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22419step0 raw22419step0Labels permutation149 permutation4
    _ = mixedMoment B node2397 node2397Labels := by rfl

def raw22420 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw22420Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw22420step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw22420step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22420 raw22420Labels = mixedMoment B node2397 node2397Labels := by
  calc
    mixedMoment B raw22420 raw22420Labels = mixedMoment B raw22420step0 raw22420step0Labels := by
      have hz : ∀ j, raw22420 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22420step0 = (fun i j => raw22420 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22420step0 raw22420; decide +kernel
      have hl : raw22420step0Labels = raw22420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22420 raw22420Labels permutation346 hz
    mixedMoment B raw22420step0 raw22420step0Labels = mixedMoment B raw22420step1 raw22420step1Labels := by
      have ha : raw22420step1 = (fun i j => raw22420step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22420step1 raw22420step0; decide +kernel
      have hl : raw22420step1Labels = raw22420step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22420step0 raw22420step0Labels permutation149 permutation4
    _ = mixedMoment B node2397 node2397Labels := by rfl

def raw22421 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22421Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22421step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22421step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22421step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22421step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22421step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22421step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22421step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22421 raw22421Labels = mixedMoment B node3301 node3301Labels := by
  calc
    mixedMoment B raw22421 raw22421Labels = mixedMoment B raw22421step0 raw22421step0Labels := by
      have hz : ∀ j, raw22421 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22421step0 = (fun i j => raw22421 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22421step0 raw22421; decide +kernel
      have hl : raw22421step0Labels = raw22421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22421 raw22421Labels permutation434 hz
    mixedMoment B raw22421step0 raw22421step0Labels = mixedMoment B raw22421step1 raw22421step1Labels := by
      have hz : ∀ j, raw22421step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22421step1 = (fun i j => raw22421step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22421step1 raw22421step0; decide +kernel
      have hl : raw22421step1Labels = raw22421step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22421step0 raw22421step0Labels permutation80 hz
    mixedMoment B raw22421step1 raw22421step1Labels = mixedMoment B raw22421step2 raw22421step2Labels := by
      have ha : raw22421step2 = (fun i j => raw22421step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22421step2 raw22421step1; decide +kernel
      have hl : raw22421step2Labels = raw22421step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22421step1 raw22421step1Labels permutation8 permutation4
    mixedMoment B raw22421step2 raw22421step2Labels = mixedMoment B raw22421step3 raw22421step3Labels := by
      have ha : raw22421step3 = -raw22421step2 := by apply Matrix.ext; change ∀ i j, raw22421step3 i j = -(raw22421step2 i j); unfold raw22421step3 raw22421step2; decide +kernel
      have hl : raw22421step3Labels = raw22421step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3301 node3301Labels := by rfl

def raw22422 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22422Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22422step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22422step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw22422step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22422step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22422step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22422 raw22422Labels = mixedMoment B node3295 node3295Labels := by
  calc
    mixedMoment B raw22422 raw22422Labels = mixedMoment B raw22422step0 raw22422step0Labels := by
      have hz : ∀ j, raw22422 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22422step0 = (fun i j => raw22422 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22422step0 raw22422; decide +kernel
      have hl : raw22422step0Labels = raw22422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22422 raw22422Labels permutation434 hz
    mixedMoment B raw22422step0 raw22422step0Labels = mixedMoment B raw22422step1 raw22422step1Labels := by
      have ha : raw22422step1 = (fun i j => raw22422step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22422step1 raw22422step0; decide +kernel
      have hl : raw22422step1Labels = raw22422step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22422step0 raw22422step0Labels permutation42 permutation2
    mixedMoment B raw22422step1 raw22422step1Labels = mixedMoment B raw22422step2 raw22422step2Labels := by
      have ha : raw22422step2 = -raw22422step1 := by apply Matrix.ext; change ∀ i j, raw22422step2 i j = -(raw22422step1 i j); unfold raw22422step2 raw22422step1; decide +kernel
      have hl : raw22422step2Labels = raw22422step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3295 node3295Labels := by rfl

def raw22423 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22423Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22423step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22423step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw22423step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22423step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22423step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22423 raw22423Labels = mixedMoment B node3295 node3295Labels := by
  calc
    mixedMoment B raw22423 raw22423Labels = mixedMoment B raw22423step0 raw22423step0Labels := by
      have hz : ∀ j, raw22423 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22423step0 = (fun i j => raw22423 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22423step0 raw22423; decide +kernel
      have hl : raw22423step0Labels = raw22423Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22423 raw22423Labels permutation346 hz
    mixedMoment B raw22423step0 raw22423step0Labels = mixedMoment B raw22423step1 raw22423step1Labels := by
      have ha : raw22423step1 = (fun i j => raw22423step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22423step1 raw22423step0; decide +kernel
      have hl : raw22423step1Labels = raw22423step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22423step0 raw22423step0Labels permutation42 permutation2
    mixedMoment B raw22423step1 raw22423step1Labels = mixedMoment B raw22423step2 raw22423step2Labels := by
      have ha : raw22423step2 = -raw22423step1 := by apply Matrix.ext; change ∀ i j, raw22423step2 i j = -(raw22423step1 i j); unfold raw22423step2 raw22423step1; decide +kernel
      have hl : raw22423step2Labels = raw22423step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3295 node3295Labels := by rfl

def raw22424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22424Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22424step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22424 raw22424Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw22424 raw22424Labels = mixedMoment B raw22424step0 raw22424step0Labels := by
      have hz : ∀ j, raw22424 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22424step0 = (fun i j => raw22424 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22424step0 raw22424; decide +kernel
      have hl : raw22424step0Labels = raw22424Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22424 raw22424Labels permutation346 hz
    _ = mixedMoment B node2488 node2488Labels := by rfl

def raw22425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22425Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22425step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22425 raw22425Labels = mixedMoment B node1219 node1219Labels := by
  calc
    mixedMoment B raw22425 raw22425Labels = mixedMoment B raw22425step0 raw22425step0Labels := by
      have hz : ∀ j, raw22425 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22425step0 = (fun i j => raw22425 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22425step0 raw22425; decide +kernel
      have hl : raw22425step0Labels = raw22425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22425 raw22425Labels permutation346 hz
    _ = mixedMoment B node1219 node1219Labels := by rfl

def raw22426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22426Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22426step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22426 raw22426Labels = mixedMoment B node1113 node1113Labels := by
  calc
    mixedMoment B raw22426 raw22426Labels = mixedMoment B raw22426step0 raw22426step0Labels := by
      have ha : raw22426step0 = (fun i j => raw22426 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22426step0 raw22426; decide +kernel
      have hl : raw22426step0Labels = raw22426Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22426 raw22426Labels permutation158 permutation2
    _ = mixedMoment B node1113 node1113Labels := by rfl

def raw22427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22427Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22427step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22427 raw22427Labels = mixedMoment B node1138 node1138Labels := by
  calc
    mixedMoment B raw22427 raw22427Labels = mixedMoment B raw22427step0 raw22427step0Labels := by
      have hz : ∀ j, raw22427 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22427step0 = (fun i j => raw22427 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22427step0 raw22427; decide +kernel
      have hl : raw22427step0Labels = raw22427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22427 raw22427Labels permutation346 hz
    _ = mixedMoment B node1138 node1138Labels := by rfl

def raw22428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, 0, -2]]
def raw22428Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0], ![2, 0, -2]]
def raw22428step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22428step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw22428step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22428 raw22428Labels = mixedMoment B node1121 node1121Labels := by
  calc
    mixedMoment B raw22428 raw22428Labels = mixedMoment B raw22428step0 raw22428step0Labels := by
      have hz : ∀ j, raw22428 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22428step0 = (fun i j => raw22428 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22428step0 raw22428; decide +kernel
      have hl : raw22428step0Labels = raw22428Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22428 raw22428Labels permutation346 hz
    mixedMoment B raw22428step0 raw22428step0Labels = mixedMoment B raw22428step1 raw22428step1Labels := by
      have ha : raw22428step1 = (fun i j => raw22428step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22428step1 raw22428step0; decide +kernel
      have hl : raw22428step1Labels = raw22428step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22428step0 raw22428step0Labels permutation33 permutation2
    _ = mixedMoment B node1121 node1121Labels := by rfl

def raw22429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22429Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22429step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22429 raw22429Labels = mixedMoment B node631 node631Labels := by
  calc
    mixedMoment B raw22429 raw22429Labels = mixedMoment B raw22429step0 raw22429step0Labels := by
      have hz : ∀ j, raw22429 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22429step0 = (fun i j => raw22429 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22429step0 raw22429; decide +kernel
      have hl : raw22429step0Labels = raw22429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22429 raw22429Labels permutation346 hz
    _ = mixedMoment B node631 node631Labels := by rfl

def raw22430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22430Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22430step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22430step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22430 raw22430Labels = mixedMoment B node1151 node1151Labels := by
  calc
    mixedMoment B raw22430 raw22430Labels = mixedMoment B raw22430step0 raw22430step0Labels := by
      have ha : raw22430step0 = (fun i j => raw22430 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22430step0 raw22430; decide +kernel
      have hl : raw22430step0Labels = raw22430Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22430 raw22430Labels permutation176 permutation2
    _ = mixedMoment B node1151 node1151Labels := by rfl

def raw22431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw22431Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw22431step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22431step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22431 raw22431Labels = mixedMoment B node1241 node1241Labels := by
  calc
    mixedMoment B raw22431 raw22431Labels = mixedMoment B raw22431step0 raw22431step0Labels := by
      have hz : ∀ j, raw22431 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22431step0 = (fun i j => raw22431 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22431step0 raw22431; decide +kernel
      have hl : raw22431step0Labels = raw22431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22431 raw22431Labels permutation346 hz
    mixedMoment B raw22431step0 raw22431step0Labels = mixedMoment B raw22431step1 raw22431step1Labels := by
      have ha : raw22431step1 = (fun i j => raw22431step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22431step1 raw22431step0; decide +kernel
      have hl : raw22431step1Labels = raw22431step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22431step0 raw22431step0Labels permutation33 permutation2
    _ = mixedMoment B node1241 node1241Labels := by rfl

def raw22432 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22432Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22432step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22432step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw22432step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22432step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw22432step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22432 raw22432Labels = mixedMoment B node1611 node1611Labels := by
  calc
    mixedMoment B raw22432 raw22432Labels = mixedMoment B raw22432step0 raw22432step0Labels := by
      have hz : ∀ j, raw22432 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22432step0 = (fun i j => raw22432 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22432step0 raw22432; decide +kernel
      have hl : raw22432step0Labels = raw22432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22432 raw22432Labels permutation346 hz
    mixedMoment B raw22432step0 raw22432step0Labels = mixedMoment B raw22432step1 raw22432step1Labels := by
      have ha : raw22432step1 = (fun i j => raw22432step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22432step1 raw22432step0; decide +kernel
      have hl : raw22432step1Labels = raw22432step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22432step0 raw22432step0Labels permutation42 permutation2
    mixedMoment B raw22432step1 raw22432step1Labels = mixedMoment B raw22432step2 raw22432step2Labels := by
      have ha : raw22432step2 = -raw22432step1 := by apply Matrix.ext; change ∀ i j, raw22432step2 i j = -(raw22432step1 i j); unfold raw22432step2 raw22432step1; decide +kernel
      have hl : raw22432step2Labels = raw22432step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1611 node1611Labels := by rfl

def raw22433 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22433Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw22433step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22433step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22433step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22433 raw22433Labels = mixedMoment B node1606 node1606Labels := by
  calc
    mixedMoment B raw22433 raw22433Labels = mixedMoment B raw22433step0 raw22433step0Labels := by
      have ha : raw22433step0 = (fun i j => raw22433 (permutation218 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22433step0 raw22433; decide +kernel
      have hl : raw22433step0Labels = raw22433Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22433 raw22433Labels permutation218 permutation2
    mixedMoment B raw22433step0 raw22433step0Labels = mixedMoment B raw22433step1 raw22433step1Labels := by
      have ha : raw22433step1 = -raw22433step0 := by apply Matrix.ext; change ∀ i j, raw22433step1 i j = -(raw22433step0 i j); unfold raw22433step1 raw22433step0; decide +kernel
      have hl : raw22433step1Labels = raw22433step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1606 node1606Labels := by rfl

def raw22434 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22434Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22434step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22434step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw22434step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22434step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw22434step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22434 raw22434Labels = mixedMoment B node1608 node1608Labels := by
  calc
    mixedMoment B raw22434 raw22434Labels = mixedMoment B raw22434step0 raw22434step0Labels := by
      have hz : ∀ j, raw22434 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22434step0 = (fun i j => raw22434 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22434step0 raw22434; decide +kernel
      have hl : raw22434step0Labels = raw22434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22434 raw22434Labels permutation346 hz
    mixedMoment B raw22434step0 raw22434step0Labels = mixedMoment B raw22434step1 raw22434step1Labels := by
      have ha : raw22434step1 = (fun i j => raw22434step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22434step1 raw22434step0; decide +kernel
      have hl : raw22434step1Labels = raw22434step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22434step0 raw22434step0Labels permutation42 permutation2
    mixedMoment B raw22434step1 raw22434step1Labels = mixedMoment B raw22434step2 raw22434step2Labels := by
      have ha : raw22434step2 = -raw22434step1 := by apply Matrix.ext; change ∀ i j, raw22434step2 i j = -(raw22434step1 i j); unfold raw22434step2 raw22434step1; decide +kernel
      have hl : raw22434step2Labels = raw22434step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1608 node1608Labels := by rfl

def raw22435 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22435Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22435step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22435step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22435step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22435step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22435 raw22435Labels = mixedMoment B node1618 node1618Labels := by
  calc
    mixedMoment B raw22435 raw22435Labels = mixedMoment B raw22435step0 raw22435step0Labels := by
      have hz : ∀ j, raw22435 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22435step0 = (fun i j => raw22435 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22435step0 raw22435; decide +kernel
      have hl : raw22435step0Labels = raw22435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22435 raw22435Labels permutation346 hz
    mixedMoment B raw22435step0 raw22435step0Labels = mixedMoment B raw22435step1 raw22435step1Labels := by
      have ha : raw22435step1 = (fun i j => raw22435step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22435step1 raw22435step0; decide +kernel
      have hl : raw22435step1Labels = raw22435step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22435step0 raw22435step0Labels permutation39 permutation2
    mixedMoment B raw22435step1 raw22435step1Labels = mixedMoment B raw22435step2 raw22435step2Labels := by
      have ha : raw22435step2 = -raw22435step1 := by apply Matrix.ext; change ∀ i j, raw22435step2 i j = -(raw22435step1 i j); unfold raw22435step2 raw22435step1; decide +kernel
      have hl : raw22435step2Labels = raw22435step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1618 node1618Labels := by rfl

def raw22436 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22436Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22436step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22436step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22436step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22436step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22436step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22436 raw22436Labels = mixedMoment B node1618 node1618Labels := by
  calc
    mixedMoment B raw22436 raw22436Labels = mixedMoment B raw22436step0 raw22436step0Labels := by
      have hz : ∀ j, raw22436 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22436step0 = (fun i j => raw22436 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22436step0 raw22436; decide +kernel
      have hl : raw22436step0Labels = raw22436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22436 raw22436Labels permutation346 hz
    mixedMoment B raw22436step0 raw22436step0Labels = mixedMoment B raw22436step1 raw22436step1Labels := by
      have ha : raw22436step1 = (fun i j => raw22436step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22436step1 raw22436step0; decide +kernel
      have hl : raw22436step1Labels = raw22436step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22436step0 raw22436step0Labels permutation32 permutation4
    mixedMoment B raw22436step1 raw22436step1Labels = mixedMoment B raw22436step2 raw22436step2Labels := by
      have ha : raw22436step2 = -raw22436step1 := by apply Matrix.ext; change ∀ i j, raw22436step2 i j = -(raw22436step1 i j); unfold raw22436step2 raw22436step1; decide +kernel
      have hl : raw22436step2Labels = raw22436step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1618 node1618Labels := by rfl

def raw22437 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22437Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![1, -1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22437step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22437step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22437step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22437step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22437step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22437 raw22437Labels = mixedMoment B node3243 node3243Labels := by
  calc
    mixedMoment B raw22437 raw22437Labels = mixedMoment B raw22437step0 raw22437step0Labels := by
      have hz : ∀ j, raw22437 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22437step0 = (fun i j => raw22437 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22437step0 raw22437; decide +kernel
      have hl : raw22437step0Labels = raw22437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22437 raw22437Labels permutation346 hz
    mixedMoment B raw22437step0 raw22437step0Labels = mixedMoment B raw22437step1 raw22437step1Labels := by
      have ha : raw22437step1 = (fun i j => raw22437step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22437step1 raw22437step0; decide +kernel
      have hl : raw22437step1Labels = raw22437step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22437step0 raw22437step0Labels permutation32 permutation4
    mixedMoment B raw22437step1 raw22437step1Labels = mixedMoment B raw22437step2 raw22437step2Labels := by
      have ha : raw22437step2 = -raw22437step1 := by apply Matrix.ext; change ∀ i j, raw22437step2 i j = -(raw22437step1 i j); unfold raw22437step2 raw22437step1; decide +kernel
      have hl : raw22437step2Labels = raw22437step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3243 node3243Labels := by rfl

def raw22438 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22438Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22438step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22438step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22438step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22438step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22438 raw22438Labels = mixedMoment B node3280 node3280Labels := by
  calc
    mixedMoment B raw22438 raw22438Labels = mixedMoment B raw22438step0 raw22438step0Labels := by
      have ha : raw22438step0 = (fun i j => raw22438 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22438step0 raw22438; decide +kernel
      have hl : raw22438step0Labels = raw22438Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22438 raw22438Labels permutation152 permutation4
    mixedMoment B raw22438step0 raw22438step0Labels = mixedMoment B raw22438step1 raw22438step1Labels := by
      have ha : raw22438step1 = -raw22438step0 := by apply Matrix.ext; change ∀ i j, raw22438step1 i j = -(raw22438step0 i j); unfold raw22438step1 raw22438step0; decide +kernel
      have hl : raw22438step1Labels = raw22438step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3280 node3280Labels := by rfl

def raw22439 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22439Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22439step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22439step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22439step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22439step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw22439step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22439 raw22439Labels = mixedMoment B node3297 node3297Labels := by
  calc
    mixedMoment B raw22439 raw22439Labels = mixedMoment B raw22439step0 raw22439step0Labels := by
      have hz : ∀ j, raw22439 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22439step0 = (fun i j => raw22439 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22439step0 raw22439; decide +kernel
      have hl : raw22439step0Labels = raw22439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22439 raw22439Labels permutation346 hz
    mixedMoment B raw22439step0 raw22439step0Labels = mixedMoment B raw22439step1 raw22439step1Labels := by
      have ha : raw22439step1 = (fun i j => raw22439step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22439step1 raw22439step0; decide +kernel
      have hl : raw22439step1Labels = raw22439step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22439step0 raw22439step0Labels permutation38 permutation2
    mixedMoment B raw22439step1 raw22439step1Labels = mixedMoment B raw22439step2 raw22439step2Labels := by
      have ha : raw22439step2 = -raw22439step1 := by apply Matrix.ext; change ∀ i j, raw22439step2 i j = -(raw22439step1 i j); unfold raw22439step2 raw22439step1; decide +kernel
      have hl : raw22439step2Labels = raw22439step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3297 node3297Labels := by rfl

def raw22440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22440Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22440 raw22440Labels = mixedMoment B node2489 node2489Labels := by
  calc
    mixedMoment B raw22440 raw22440Labels = mixedMoment B raw22440step0 raw22440step0Labels := by
      have hz : ∀ j, raw22440 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22440step0 = (fun i j => raw22440 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22440step0 raw22440; decide +kernel
      have hl : raw22440step0Labels = raw22440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22440 raw22440Labels permutation346 hz
    _ = mixedMoment B node2489 node2489Labels := by rfl

def raw22441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22441Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22441 raw22441Labels = mixedMoment B node1220 node1220Labels := by
  calc
    mixedMoment B raw22441 raw22441Labels = mixedMoment B raw22441step0 raw22441step0Labels := by
      have hz : ∀ j, raw22441 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22441step0 = (fun i j => raw22441 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22441step0 raw22441; decide +kernel
      have hl : raw22441step0Labels = raw22441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22441 raw22441Labels permutation346 hz
    _ = mixedMoment B node1220 node1220Labels := by rfl

def raw22442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22442Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22442step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw22442step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22442 raw22442Labels = mixedMoment B node1114 node1114Labels := by
  calc
    mixedMoment B raw22442 raw22442Labels = mixedMoment B raw22442step0 raw22442step0Labels := by
      have ha : raw22442step0 = (fun i j => raw22442 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22442step0 raw22442; decide +kernel
      have hl : raw22442step0Labels = raw22442Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22442 raw22442Labels permutation158 permutation2
    _ = mixedMoment B node1114 node1114Labels := by rfl

def raw22443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22443Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22443step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22443 raw22443Labels = mixedMoment B node1139 node1139Labels := by
  calc
    mixedMoment B raw22443 raw22443Labels = mixedMoment B raw22443step0 raw22443step0Labels := by
      have hz : ∀ j, raw22443 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22443step0 = (fun i j => raw22443 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22443step0 raw22443; decide +kernel
      have hl : raw22443step0Labels = raw22443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22443 raw22443Labels permutation346 hz
    _ = mixedMoment B node1139 node1139Labels := by rfl

def raw22444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw22444Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw22444step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw22444step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22444 raw22444Labels = mixedMoment B node1120 node1120Labels := by
  calc
    mixedMoment B raw22444 raw22444Labels = mixedMoment B raw22444step0 raw22444step0Labels := by
      have hz : ∀ j, raw22444 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22444step0 = (fun i j => raw22444 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22444step0 raw22444; decide +kernel
      have hl : raw22444step0Labels = raw22444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22444 raw22444Labels permutation346 hz
    mixedMoment B raw22444step0 raw22444step0Labels = mixedMoment B raw22444step1 raw22444step1Labels := by
      have ha : raw22444step1 = (fun i j => raw22444step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22444step1 raw22444step0; decide +kernel
      have hl : raw22444step1Labels = raw22444step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22444step0 raw22444step0Labels permutation33 permutation2
    _ = mixedMoment B node1120 node1120Labels := by rfl

def raw22445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw22445Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw22445step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22445 raw22445Labels = mixedMoment B node1120 node1120Labels := by
  calc
    mixedMoment B raw22445 raw22445Labels = mixedMoment B raw22445step0 raw22445step0Labels := by
      have hz : ∀ j, raw22445 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22445step0 = (fun i j => raw22445 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22445step0 raw22445; decide +kernel
      have hl : raw22445step0Labels = raw22445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22445 raw22445Labels permutation346 hz
    _ = mixedMoment B node1120 node1120Labels := by rfl

def raw22446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22446Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22446step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22446 raw22446Labels = mixedMoment B node632 node632Labels := by
  calc
    mixedMoment B raw22446 raw22446Labels = mixedMoment B raw22446step0 raw22446step0Labels := by
      have hz : ∀ j, raw22446 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22446step0 = (fun i j => raw22446 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22446step0 raw22446; decide +kernel
      have hl : raw22446step0Labels = raw22446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22446 raw22446Labels permutation346 hz
    _ = mixedMoment B node632 node632Labels := by rfl

def raw22447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22447Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw22447step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22447 raw22447Labels = mixedMoment B node1152 node1152Labels := by
  calc
    mixedMoment B raw22447 raw22447Labels = mixedMoment B raw22447step0 raw22447step0Labels := by
      have ha : raw22447step0 = (fun i j => raw22447 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22447step0 raw22447; decide +kernel
      have hl : raw22447step0Labels = raw22447Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22447 raw22447Labels permutation176 permutation2
    _ = mixedMoment B node1152 node1152Labels := by rfl

def raw22448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw22448Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw22448step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22448 raw22448Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw22448 raw22448Labels = mixedMoment B raw22448step0 raw22448step0Labels := by
      have hz : ∀ j, raw22448 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22448step0 = (fun i j => raw22448 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22448step0 raw22448; decide +kernel
      have hl : raw22448step0Labels = raw22448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22448 raw22448Labels permutation346 hz
    _ = mixedMoment B node1240 node1240Labels := by rfl

def raw22449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw22449Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw22449step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw22449step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22449 raw22449Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw22449 raw22449Labels = mixedMoment B raw22449step0 raw22449step0Labels := by
      have hz : ∀ j, raw22449 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22449step0 = (fun i j => raw22449 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22449step0 raw22449; decide +kernel
      have hl : raw22449step0Labels = raw22449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22449 raw22449Labels permutation346 hz
    mixedMoment B raw22449step0 raw22449step0Labels = mixedMoment B raw22449step1 raw22449step1Labels := by
      have ha : raw22449step1 = (fun i j => raw22449step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22449step1 raw22449step0; decide +kernel
      have hl : raw22449step1Labels = raw22449step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22449step0 raw22449step0Labels permutation33 permutation2
    _ = mixedMoment B node1240 node1240Labels := by rfl

def raw22450 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22450Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22450step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw22450step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22450step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw22450step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22450 raw22450Labels = mixedMoment B node1626 node1626Labels := by
  calc
    mixedMoment B raw22450 raw22450Labels = mixedMoment B raw22450step0 raw22450step0Labels := by
      have hz : ∀ j, raw22450 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22450step0 = (fun i j => raw22450 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22450step0 raw22450; decide +kernel
      have hl : raw22450step0Labels = raw22450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22450 raw22450Labels permutation346 hz
    mixedMoment B raw22450step0 raw22450step0Labels = mixedMoment B raw22450step1 raw22450step1Labels := by
      have ha : raw22450step1 = (fun i j => raw22450step0 (permutation41 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22450step1 raw22450step0; decide +kernel
      have hl : raw22450step1Labels = raw22450step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22450step0 raw22450step0Labels permutation41 permutation2
    mixedMoment B raw22450step1 raw22450step1Labels = mixedMoment B raw22450step2 raw22450step2Labels := by
      have ha : raw22450step2 = -raw22450step1 := by apply Matrix.ext; change ∀ i j, raw22450step2 i j = -(raw22450step1 i j); unfold raw22450step2 raw22450step1; decide +kernel
      have hl : raw22450step2Labels = raw22450step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1626 node1626Labels := by rfl

def raw22451 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22451Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22451step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22451step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw22451step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22451 raw22451Labels = mixedMoment B node1614 node1614Labels := by
  calc
    mixedMoment B raw22451 raw22451Labels = mixedMoment B raw22451step0 raw22451step0Labels := by
      have ha : raw22451step0 = (fun i j => raw22451 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22451step0 raw22451; decide +kernel
      have hl : raw22451step0Labels = raw22451Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22451 raw22451Labels permutation200 permutation2
    mixedMoment B raw22451step0 raw22451step0Labels = mixedMoment B raw22451step1 raw22451step1Labels := by
      have ha : raw22451step1 = -raw22451step0 := by apply Matrix.ext; change ∀ i j, raw22451step1 i j = -(raw22451step0 i j); unfold raw22451step1 raw22451step0; decide +kernel
      have hl : raw22451step1Labels = raw22451step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1614 node1614Labels := by rfl

def raw22452 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22452Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22452step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22452step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22452step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw22452step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22452 raw22452Labels = mixedMoment B node1751 node1751Labels := by
  calc
    mixedMoment B raw22452 raw22452Labels = mixedMoment B raw22452step0 raw22452step0Labels := by
      have hz : ∀ j, raw22452 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22452step0 = (fun i j => raw22452 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22452step0 raw22452; decide +kernel
      have hl : raw22452step0Labels = raw22452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22452 raw22452Labels permutation434 hz
    mixedMoment B raw22452step0 raw22452step0Labels = mixedMoment B raw22452step1 raw22452step1Labels := by
      have hz : ∀ j, raw22452step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22452step1 = (fun i j => raw22452step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22452step1 raw22452step0; decide +kernel
      have hl : raw22452step1Labels = raw22452step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22452step0 raw22452step0Labels permutation80 hz
    mixedMoment B raw22452step1 raw22452step1Labels = mixedMoment B raw22452step2 raw22452step2Labels := by
      have ha : raw22452step2 = -raw22452step1 := by apply Matrix.ext; change ∀ i j, raw22452step2 i j = -(raw22452step1 i j); unfold raw22452step2 raw22452step1; decide +kernel
      have hl : raw22452step2Labels = raw22452step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1751 node1751Labels := by rfl

def raw22453 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22453Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22453step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22453step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22453step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22453 raw22453Labels = mixedMoment B node1618 node1618Labels := by
  calc
    mixedMoment B raw22453 raw22453Labels = mixedMoment B raw22453step0 raw22453step0Labels := by
      have hz : ∀ j, raw22453 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22453step0 = (fun i j => raw22453 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22453step0 raw22453; decide +kernel
      have hl : raw22453step0Labels = raw22453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22453 raw22453Labels permutation346 hz
    mixedMoment B raw22453step0 raw22453step0Labels = mixedMoment B raw22453step1 raw22453step1Labels := by
      have ha : raw22453step1 = (fun i j => raw22453step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22453step1 raw22453step0; decide +kernel
      have hl : raw22453step1Labels = raw22453step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22453step0 raw22453step0Labels permutation38 permutation2
    mixedMoment B raw22453step1 raw22453step1Labels = mixedMoment B raw22453step2 raw22453step2Labels := by
      have ha : raw22453step2 = -raw22453step1 := by apply Matrix.ext; change ∀ i j, raw22453step2 i j = -(raw22453step1 i j); unfold raw22453step2 raw22453step1; decide +kernel
      have hl : raw22453step2Labels = raw22453step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1618 node1618Labels := by rfl

def raw22454 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22454Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22454step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22454step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22454step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22454step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw22454step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22454 raw22454Labels = mixedMoment B node3297 node3297Labels := by
  calc
    mixedMoment B raw22454 raw22454Labels = mixedMoment B raw22454step0 raw22454step0Labels := by
      have hz : ∀ j, raw22454 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22454step0 = (fun i j => raw22454 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22454step0 raw22454; decide +kernel
      have hl : raw22454step0Labels = raw22454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22454 raw22454Labels permutation265 hz
    mixedMoment B raw22454step0 raw22454step0Labels = mixedMoment B raw22454step1 raw22454step1Labels := by
      have ha : raw22454step1 = (fun i j => raw22454step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22454step1 raw22454step0; decide +kernel
      have hl : raw22454step1Labels = raw22454step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22454step0 raw22454step0Labels permutation38 permutation2
    mixedMoment B raw22454step1 raw22454step1Labels = mixedMoment B raw22454step2 raw22454step2Labels := by
      have ha : raw22454step2 = -raw22454step1 := by apply Matrix.ext; change ∀ i j, raw22454step2 i j = -(raw22454step1 i j); unfold raw22454step2 raw22454step1; decide +kernel
      have hl : raw22454step2Labels = raw22454step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3297 node3297Labels := by rfl

def raw22455 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22455Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22455step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22455step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22455step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22455step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, -1, 2], ![-1, -1, 2]]
def raw22455step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22455step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 1, -2], ![1, 1, -2]]
def raw22455step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22455 raw22455Labels = mixedMoment B node3312 node3312Labels := by
  calc
    mixedMoment B raw22455 raw22455Labels = mixedMoment B raw22455step0 raw22455step0Labels := by
      have hz : ∀ j, raw22455 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22455step0 = (fun i j => raw22455 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22455step0 raw22455; decide +kernel
      have hl : raw22455step0Labels = raw22455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22455 raw22455Labels permutation434 hz
    mixedMoment B raw22455step0 raw22455step0Labels = mixedMoment B raw22455step1 raw22455step1Labels := by
      have hz : ∀ j, raw22455step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22455step1 = (fun i j => raw22455step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22455step1 raw22455step0; decide +kernel
      have hl : raw22455step1Labels = raw22455step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22455step0 raw22455step0Labels permutation80 hz
    mixedMoment B raw22455step1 raw22455step1Labels = mixedMoment B raw22455step2 raw22455step2Labels := by
      have hz : ∀ j, raw22455step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22455step2 = (fun i j => raw22455step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22455step2 raw22455step1; decide +kernel
      have hl : raw22455step2Labels = raw22455step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22455step1 raw22455step1Labels permutation14 hz
    mixedMoment B raw22455step2 raw22455step2Labels = mixedMoment B raw22455step3 raw22455step3Labels := by
      have ha : raw22455step3 = -raw22455step2 := by apply Matrix.ext; change ∀ i j, raw22455step3 i j = -(raw22455step2 i j); unfold raw22455step3 raw22455step2; decide +kernel
      have hl : raw22455step3Labels = raw22455step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3312 node3312Labels := by rfl

def raw22456 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22456step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22456step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22456step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22456step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22456 raw22456Labels = mixedMoment B node3301 node3301Labels := by
  calc
    mixedMoment B raw22456 raw22456Labels = mixedMoment B raw22456step0 raw22456step0Labels := by
      have hz : ∀ j, raw22456 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22456step0 = (fun i j => raw22456 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22456step0 raw22456; decide +kernel
      have hl : raw22456step0Labels = raw22456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22456 raw22456Labels permutation346 hz
    mixedMoment B raw22456step0 raw22456step0Labels = mixedMoment B raw22456step1 raw22456step1Labels := by
      have hz : ∀ j, raw22456step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22456step1 = (fun i j => raw22456step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22456step1 raw22456step0; decide +kernel
      have hl : raw22456step1Labels = raw22456step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22456step0 raw22456step0Labels permutation56 hz
    mixedMoment B raw22456step1 raw22456step1Labels = mixedMoment B raw22456step2 raw22456step2Labels := by
      have ha : raw22456step2 = -raw22456step1 := by apply Matrix.ext; change ∀ i j, raw22456step2 i j = -(raw22456step1 i j); unfold raw22456step2 raw22456step1; decide +kernel
      have hl : raw22456step2Labels = raw22456step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3301 node3301Labels := by rfl

def raw22457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw22457Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw22457step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22457step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22457step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22457 raw22457Labels = mixedMoment B node1182 node1182Labels := by
  calc
    mixedMoment B raw22457 raw22457Labels = mixedMoment B raw22457step0 raw22457step0Labels := by
      have hz : ∀ j, raw22457 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22457step0 = (fun i j => raw22457 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22457step0 raw22457; decide +kernel
      have hl : raw22457step0Labels = raw22457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22457 raw22457Labels permutation346 hz
    mixedMoment B raw22457step0 raw22457step0Labels = mixedMoment B raw22457step1 raw22457step1Labels := by
      have ha : raw22457step1 = (fun i j => raw22457step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22457step1 raw22457step0; decide +kernel
      have hl : raw22457step1Labels = raw22457step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22457step0 raw22457step0Labels permutation39 permutation2
    _ = mixedMoment B node1182 node1182Labels := by rfl

def raw22458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw22458Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw22458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22458step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw22458step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22458 raw22458Labels = mixedMoment B node2608 node2608Labels := by
  calc
    mixedMoment B raw22458 raw22458Labels = mixedMoment B raw22458step0 raw22458step0Labels := by
      have hz : ∀ j, raw22458 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22458step0 = (fun i j => raw22458 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22458step0 raw22458; decide +kernel
      have hl : raw22458step0Labels = raw22458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22458 raw22458Labels permutation346 hz
    mixedMoment B raw22458step0 raw22458step0Labels = mixedMoment B raw22458step1 raw22458step1Labels := by
      have ha : raw22458step1 = (fun i j => raw22458step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22458step1 raw22458step0; decide +kernel
      have hl : raw22458step1Labels = raw22458step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22458step0 raw22458step0Labels permutation33 permutation2
    _ = mixedMoment B node2608 node2608Labels := by rfl

def raw22459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, -1, -1]]
def raw22459Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22459 raw22459Labels = mixedMoment B node2533 node2533Labels := by
  calc
    mixedMoment B raw22459 raw22459Labels = mixedMoment B raw22459step0 raw22459step0Labels := by
      have ha : raw22459step0 = (fun i j => raw22459 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22459step0 raw22459; decide +kernel
      have hl : raw22459step0Labels = raw22459Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22459 raw22459Labels permutation183 permutation2
    _ = mixedMoment B node2533 node2533Labels := by rfl

def raw22460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw22460Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw22460step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22460step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22460step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22460 raw22460Labels = mixedMoment B node2388 node2388Labels := by
  calc
    mixedMoment B raw22460 raw22460Labels = mixedMoment B raw22460step0 raw22460step0Labels := by
      have hz : ∀ j, raw22460 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22460step0 = (fun i j => raw22460 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22460step0 raw22460; decide +kernel
      have hl : raw22460step0Labels = raw22460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22460 raw22460Labels permutation346 hz
    mixedMoment B raw22460step0 raw22460step0Labels = mixedMoment B raw22460step1 raw22460step1Labels := by
      have ha : raw22460step1 = (fun i j => raw22460step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22460step1 raw22460step0; decide +kernel
      have hl : raw22460step1Labels = raw22460step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22460step0 raw22460step0Labels permutation39 permutation2
    _ = mixedMoment B node2388 node2388Labels := by rfl

def raw22461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw22461Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw22461step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22461step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw22461step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22461 raw22461Labels = mixedMoment B node2673 node2673Labels := by
  calc
    mixedMoment B raw22461 raw22461Labels = mixedMoment B raw22461step0 raw22461step0Labels := by
      have hz : ∀ j, raw22461 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22461step0 = (fun i j => raw22461 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22461step0 raw22461; decide +kernel
      have hl : raw22461step0Labels = raw22461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22461 raw22461Labels permutation346 hz
    mixedMoment B raw22461step0 raw22461step0Labels = mixedMoment B raw22461step1 raw22461step1Labels := by
      have ha : raw22461step1 = (fun i j => raw22461step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22461step1 raw22461step0; decide +kernel
      have hl : raw22461step1Labels = raw22461step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22461step0 raw22461step0Labels permutation38 permutation2
    _ = mixedMoment B node2673 node2673Labels := by rfl

def raw22462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw22462Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw22462step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22462step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22462 raw22462Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw22462 raw22462Labels = mixedMoment B raw22462step0 raw22462step0Labels := by
      have hz : ∀ j, raw22462 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22462step0 = (fun i j => raw22462 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22462step0 raw22462; decide +kernel
      have hl : raw22462step0Labels = raw22462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22462 raw22462Labels permutation346 hz
    mixedMoment B raw22462step0 raw22462step0Labels = mixedMoment B raw22462step1 raw22462step1Labels := by
      have ha : raw22462step1 = (fun i j => raw22462step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22462step1 raw22462step0; decide +kernel
      have hl : raw22462step1Labels = raw22462step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22462step0 raw22462step0Labels permutation39 permutation2
    _ = mixedMoment B node2672 node2672Labels := by rfl

def raw22463 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![-2, 2], ![2, -2], ![1, -1]]
def raw22463Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22463step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-2, 2], ![2, -2], ![1, -1]]
def raw22463step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22463step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw22463step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22463 raw22463Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw22463 raw22463Labels = mixedMoment B raw22463step0 raw22463step0Labels := by
      have hz : ∀ j, raw22463 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22463step0 = (fun i j => raw22463 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22463step0 raw22463; decide +kernel
      have hl : raw22463step0Labels = raw22463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22463 raw22463Labels permutation346 hz
    mixedMoment B raw22463step0 raw22463step0Labels = mixedMoment B raw22463step1 raw22463step1Labels := by
      have ha : raw22463step1 = (fun i j => raw22463step0 (permutation39 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22463step1 raw22463step0; decide +kernel
      have hl : raw22463step1Labels = raw22463step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22463step0 raw22463step0Labels permutation39 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw22464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22464Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22464step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22464 raw22464Labels = mixedMoment B node1196 node1196Labels := by
  calc
    mixedMoment B raw22464 raw22464Labels = mixedMoment B raw22464step0 raw22464step0Labels := by
      have ha : raw22464step0 = (fun i j => raw22464 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22464step0 raw22464; decide +kernel
      have hl : raw22464step0Labels = raw22464Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22464 raw22464Labels permutation183 permutation2
    _ = mixedMoment B node1196 node1196Labels := by rfl

def raw22465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22465Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22465step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22465step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22465 raw22465Labels = mixedMoment B node2609 node2609Labels := by
  calc
    mixedMoment B raw22465 raw22465Labels = mixedMoment B raw22465step0 raw22465step0Labels := by
      have ha : raw22465step0 = (fun i j => raw22465 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22465step0 raw22465; decide +kernel
      have hl : raw22465step0Labels = raw22465Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22465 raw22465Labels permutation153 permutation2
    _ = mixedMoment B node2609 node2609Labels := by rfl

def raw22466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22466Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22466step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22466step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22466 raw22466Labels = mixedMoment B node2452 node2452Labels := by
  calc
    mixedMoment B raw22466 raw22466Labels = mixedMoment B raw22466step0 raw22466step0Labels := by
      have ha : raw22466step0 = (fun i j => raw22466 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22466step0 raw22466; decide +kernel
      have hl : raw22466step0Labels = raw22466Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22466 raw22466Labels permutation183 permutation2
    _ = mixedMoment B node2452 node2452Labels := by rfl

def raw22467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22467Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22467step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22467 raw22467Labels = mixedMoment B node2452 node2452Labels := by
  calc
    mixedMoment B raw22467 raw22467Labels = mixedMoment B raw22467step0 raw22467step0Labels := by
      have ha : raw22467step0 = (fun i j => raw22467 (permutation207 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22467step0 raw22467; decide +kernel
      have hl : raw22467step0Labels = raw22467Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22467 raw22467Labels permutation207 permutation2
    _ = mixedMoment B node2452 node2452Labels := by rfl

def raw22468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw22468Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22468step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw22468step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22468 raw22468Labels = mixedMoment B node2695 node2695Labels := by
  calc
    mixedMoment B raw22468 raw22468Labels = mixedMoment B raw22468step0 raw22468step0Labels := by
      have ha : raw22468step0 = (fun i j => raw22468 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22468step0 raw22468; decide +kernel
      have hl : raw22468step0Labels = raw22468Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22468 raw22468Labels permutation182 permutation2
    _ = mixedMoment B node2695 node2695Labels := by rfl

def raw22469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw22469Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw22469step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22469 raw22469Labels = mixedMoment B node2694 node2694Labels := by
  calc
    mixedMoment B raw22469 raw22469Labels = mixedMoment B raw22469step0 raw22469step0Labels := by
      have ha : raw22469step0 = (fun i j => raw22469 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22469step0 raw22469; decide +kernel
      have hl : raw22469step0Labels = raw22469Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22469 raw22469Labels permutation183 permutation2
    _ = mixedMoment B node2694 node2694Labels := by rfl

def raw22470 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]
def raw22470Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22470step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw22470step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22470 raw22470Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw22470 raw22470Labels = mixedMoment B raw22470step0 raw22470step0Labels := by
      have ha : raw22470step0 = (fun i j => raw22470 (permutation183 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22470step0 raw22470; decide +kernel
      have hl : raw22470step0Labels = raw22470Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22470 raw22470Labels permutation183 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

def raw22471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22471step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22471step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22471step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22471step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22471step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22471step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22471step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22471 raw22471Labels = mixedMoment B node4185 node4185Labels := by
  calc
    mixedMoment B raw22471 raw22471Labels = mixedMoment B raw22471step0 raw22471step0Labels := by
      have hz : ∀ j, raw22471 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22471step0 = (fun i j => raw22471 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22471step0 raw22471; decide +kernel
      have hl : raw22471step0Labels = raw22471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22471 raw22471Labels permutation434 hz
    mixedMoment B raw22471step0 raw22471step0Labels = mixedMoment B raw22471step1 raw22471step1Labels := by
      have hz : ∀ j, raw22471step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22471step1 = (fun i j => raw22471step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22471step1 raw22471step0; decide +kernel
      have hl : raw22471step1Labels = raw22471step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22471step0 raw22471step0Labels permutation80 hz
    mixedMoment B raw22471step1 raw22471step1Labels = mixedMoment B raw22471step2 raw22471step2Labels := by
      have ha : raw22471step2 = (fun i j => raw22471step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22471step2 raw22471step1; decide +kernel
      have hl : raw22471step2Labels = raw22471step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22471step1 raw22471step1Labels permutation9 permutation3
    mixedMoment B raw22471step2 raw22471step2Labels = mixedMoment B raw22471step3 raw22471step3Labels := by
      have ha : raw22471step3 = raw22471step2 := by apply Matrix.ext; unfold raw22471step3 raw22471step2; decide +kernel
      have hl : raw22471step2Labels = labelEmbedding6 ∘ raw22471step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22471step2 raw22471step2Labels raw22471step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4185 node4185Labels := by rfl

def raw22472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22472step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22472step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22472step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22472step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22472step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22472 raw22472Labels = mixedMoment B node4553 node4553Labels := by
  calc
    mixedMoment B raw22472 raw22472Labels = mixedMoment B raw22472step0 raw22472step0Labels := by
      have hz : ∀ j, raw22472 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22472step0 = (fun i j => raw22472 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22472step0 raw22472; decide +kernel
      have hl : raw22472step0Labels = raw22472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22472 raw22472Labels permutation434 hz
    mixedMoment B raw22472step0 raw22472step0Labels = mixedMoment B raw22472step1 raw22472step1Labels := by
      have ha : raw22472step1 = (fun i j => raw22472step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22472step1 raw22472step0; decide +kernel
      have hl : raw22472step1Labels = raw22472step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22472step0 raw22472step0Labels permutation39 permutation3
    mixedMoment B raw22472step1 raw22472step1Labels = mixedMoment B raw22472step2 raw22472step2Labels := by
      have ha : raw22472step2 = raw22472step1 := by apply Matrix.ext; unfold raw22472step2 raw22472step1; decide +kernel
      have hl : raw22472step1Labels = labelEmbedding6 ∘ raw22472step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22472step1 raw22472step1Labels raw22472step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4553 node4553Labels := by rfl

def raw22473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22473step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22473step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22473step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22473step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22473step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22473 raw22473Labels = mixedMoment B node4553 node4553Labels := by
  calc
    mixedMoment B raw22473 raw22473Labels = mixedMoment B raw22473step0 raw22473step0Labels := by
      have hz : ∀ j, raw22473 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22473step0 = (fun i j => raw22473 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22473step0 raw22473; decide +kernel
      have hl : raw22473step0Labels = raw22473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22473 raw22473Labels permutation346 hz
    mixedMoment B raw22473step0 raw22473step0Labels = mixedMoment B raw22473step1 raw22473step1Labels := by
      have ha : raw22473step1 = (fun i j => raw22473step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22473step1 raw22473step0; decide +kernel
      have hl : raw22473step1Labels = raw22473step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22473step0 raw22473step0Labels permutation39 permutation3
    mixedMoment B raw22473step1 raw22473step1Labels = mixedMoment B raw22473step2 raw22473step2Labels := by
      have ha : raw22473step2 = raw22473step1 := by apply Matrix.ext; unfold raw22473step2 raw22473step1; decide +kernel
      have hl : raw22473step1Labels = labelEmbedding6 ∘ raw22473step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22473step1 raw22473step1Labels raw22473step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4553 node4553Labels := by rfl

def raw22474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw22474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw22474step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22474step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw22474step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22474step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw22474step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22474step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw22474step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22474 raw22474Labels = mixedMoment B node4619 node4619Labels := by
  calc
    mixedMoment B raw22474 raw22474Labels = mixedMoment B raw22474step0 raw22474step0Labels := by
      have hz : ∀ j, raw22474 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22474step0 = (fun i j => raw22474 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22474step0 raw22474; decide +kernel
      have hl : raw22474step0Labels = raw22474Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22474 raw22474Labels permutation434 hz
    mixedMoment B raw22474step0 raw22474step0Labels = mixedMoment B raw22474step1 raw22474step1Labels := by
      have hz : ∀ j, raw22474step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22474step1 = (fun i j => raw22474step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22474step1 raw22474step0; decide +kernel
      have hl : raw22474step1Labels = raw22474step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22474step0 raw22474step0Labels permutation80 hz
    mixedMoment B raw22474step1 raw22474step1Labels = mixedMoment B raw22474step2 raw22474step2Labels := by
      have ha : raw22474step2 = (fun i j => raw22474step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22474step2 raw22474step1; decide +kernel
      have hl : raw22474step2Labels = raw22474step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22474step1 raw22474step1Labels permutation12 permutation3
    mixedMoment B raw22474step2 raw22474step2Labels = mixedMoment B raw22474step3 raw22474step3Labels := by
      have ha : raw22474step3 = raw22474step2 := by apply Matrix.ext; unfold raw22474step3 raw22474step2; decide +kernel
      have hl : raw22474step2Labels = labelEmbedding6 ∘ raw22474step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22474step2 raw22474step2Labels raw22474step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4619 node4619Labels := by rfl

def raw22475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22475step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22475step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22475step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22475step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22475step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22475step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22475step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22475 raw22475Labels = mixedMoment B node4185 node4185Labels := by
  calc
    mixedMoment B raw22475 raw22475Labels = mixedMoment B raw22475step0 raw22475step0Labels := by
      have hz : ∀ j, raw22475 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22475step0 = (fun i j => raw22475 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22475step0 raw22475; decide +kernel
      have hl : raw22475step0Labels = raw22475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22475 raw22475Labels permutation434 hz
    mixedMoment B raw22475step0 raw22475step0Labels = mixedMoment B raw22475step1 raw22475step1Labels := by
      have hz : ∀ j, raw22475step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22475step1 = (fun i j => raw22475step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22475step1 raw22475step0; decide +kernel
      have hl : raw22475step1Labels = raw22475step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22475step0 raw22475step0Labels permutation56 hz
    mixedMoment B raw22475step1 raw22475step1Labels = mixedMoment B raw22475step2 raw22475step2Labels := by
      have ha : raw22475step2 = (fun i j => raw22475step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22475step2 raw22475step1; decide +kernel
      have hl : raw22475step2Labels = raw22475step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22475step1 raw22475step1Labels permutation9 permutation3
    mixedMoment B raw22475step2 raw22475step2Labels = mixedMoment B raw22475step3 raw22475step3Labels := by
      have ha : raw22475step3 = raw22475step2 := by apply Matrix.ext; unfold raw22475step3 raw22475step2; decide +kernel
      have hl : raw22475step2Labels = labelEmbedding6 ∘ raw22475step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22475step2 raw22475step2Labels raw22475step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4185 node4185Labels := by rfl

def raw22476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22476step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22476step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22476step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22476step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22476step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22476 raw22476Labels = mixedMoment B node4553 node4553Labels := by
  calc
    mixedMoment B raw22476 raw22476Labels = mixedMoment B raw22476step0 raw22476step0Labels := by
      have hz : ∀ j, raw22476 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22476step0 = (fun i j => raw22476 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22476step0 raw22476; decide +kernel
      have hl : raw22476step0Labels = raw22476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22476 raw22476Labels permutation434 hz
    mixedMoment B raw22476step0 raw22476step0Labels = mixedMoment B raw22476step1 raw22476step1Labels := by
      have ha : raw22476step1 = (fun i j => raw22476step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22476step1 raw22476step0; decide +kernel
      have hl : raw22476step1Labels = raw22476step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22476step0 raw22476step0Labels permutation33 permutation3
    mixedMoment B raw22476step1 raw22476step1Labels = mixedMoment B raw22476step2 raw22476step2Labels := by
      have ha : raw22476step2 = raw22476step1 := by apply Matrix.ext; unfold raw22476step2 raw22476step1; decide +kernel
      have hl : raw22476step1Labels = labelEmbedding6 ∘ raw22476step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22476step1 raw22476step1Labels raw22476step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4553 node4553Labels := by rfl

def raw22477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22477step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22477step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22477step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22477step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22477step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22477 raw22477Labels = mixedMoment B node4553 node4553Labels := by
  calc
    mixedMoment B raw22477 raw22477Labels = mixedMoment B raw22477step0 raw22477step0Labels := by
      have hz : ∀ j, raw22477 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22477step0 = (fun i j => raw22477 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22477step0 raw22477; decide +kernel
      have hl : raw22477step0Labels = raw22477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22477 raw22477Labels permutation265 hz
    mixedMoment B raw22477step0 raw22477step0Labels = mixedMoment B raw22477step1 raw22477step1Labels := by
      have ha : raw22477step1 = (fun i j => raw22477step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22477step1 raw22477step0; decide +kernel
      have hl : raw22477step1Labels = raw22477step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22477step0 raw22477step0Labels permutation39 permutation3
    mixedMoment B raw22477step1 raw22477step1Labels = mixedMoment B raw22477step2 raw22477step2Labels := by
      have ha : raw22477step2 = raw22477step1 := by apply Matrix.ext; unfold raw22477step2 raw22477step1; decide +kernel
      have hl : raw22477step1Labels = labelEmbedding6 ∘ raw22477step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22477step1 raw22477step1Labels raw22477step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4553 node4553Labels := by rfl

def raw22478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw22478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw22478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22478step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw22478step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22478step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw22478step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22478step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw22478step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22478 raw22478Labels = mixedMoment B node4619 node4619Labels := by
  calc
    mixedMoment B raw22478 raw22478Labels = mixedMoment B raw22478step0 raw22478step0Labels := by
      have hz : ∀ j, raw22478 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22478step0 = (fun i j => raw22478 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22478step0 raw22478; decide +kernel
      have hl : raw22478step0Labels = raw22478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22478 raw22478Labels permutation434 hz
    mixedMoment B raw22478step0 raw22478step0Labels = mixedMoment B raw22478step1 raw22478step1Labels := by
      have hz : ∀ j, raw22478step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22478step1 = (fun i j => raw22478step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22478step1 raw22478step0; decide +kernel
      have hl : raw22478step1Labels = raw22478step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22478step0 raw22478step0Labels permutation56 hz
    mixedMoment B raw22478step1 raw22478step1Labels = mixedMoment B raw22478step2 raw22478step2Labels := by
      have ha : raw22478step2 = (fun i j => raw22478step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22478step2 raw22478step1; decide +kernel
      have hl : raw22478step2Labels = raw22478step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22478step1 raw22478step1Labels permutation12 permutation3
    mixedMoment B raw22478step2 raw22478step2Labels = mixedMoment B raw22478step3 raw22478step3Labels := by
      have ha : raw22478step3 = raw22478step2 := by apply Matrix.ext; unfold raw22478step3 raw22478step2; decide +kernel
      have hl : raw22478step2Labels = labelEmbedding6 ∘ raw22478step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22478step2 raw22478step2Labels raw22478step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4619 node4619Labels := by rfl

def raw22479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22479step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22479step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22479step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22479step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22479step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22479step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22479step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22479 raw22479Labels = mixedMoment B node4185 node4185Labels := by
  calc
    mixedMoment B raw22479 raw22479Labels = mixedMoment B raw22479step0 raw22479step0Labels := by
      have hz : ∀ j, raw22479 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22479step0 = (fun i j => raw22479 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22479step0 raw22479; decide +kernel
      have hl : raw22479step0Labels = raw22479Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22479 raw22479Labels permutation346 hz
    mixedMoment B raw22479step0 raw22479step0Labels = mixedMoment B raw22479step1 raw22479step1Labels := by
      have hz : ∀ j, raw22479step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22479step1 = (fun i j => raw22479step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22479step1 raw22479step0; decide +kernel
      have hl : raw22479step1Labels = raw22479step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22479step0 raw22479step0Labels permutation56 hz
    mixedMoment B raw22479step1 raw22479step1Labels = mixedMoment B raw22479step2 raw22479step2Labels := by
      have ha : raw22479step2 = (fun i j => raw22479step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22479step2 raw22479step1; decide +kernel
      have hl : raw22479step2Labels = raw22479step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22479step1 raw22479step1Labels permutation9 permutation3
    mixedMoment B raw22479step2 raw22479step2Labels = mixedMoment B raw22479step3 raw22479step3Labels := by
      have ha : raw22479step3 = raw22479step2 := by apply Matrix.ext; unfold raw22479step3 raw22479step2; decide +kernel
      have hl : raw22479step2Labels = labelEmbedding6 ∘ raw22479step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22479step2 raw22479step2Labels raw22479step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4185 node4185Labels := by rfl

def raw22480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22480step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22480step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22480step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22480step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22480step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22480 raw22480Labels = mixedMoment B node4553 node4553Labels := by
  calc
    mixedMoment B raw22480 raw22480Labels = mixedMoment B raw22480step0 raw22480step0Labels := by
      have hz : ∀ j, raw22480 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22480step0 = (fun i j => raw22480 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22480step0 raw22480; decide +kernel
      have hl : raw22480step0Labels = raw22480Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22480 raw22480Labels permutation346 hz
    mixedMoment B raw22480step0 raw22480step0Labels = mixedMoment B raw22480step1 raw22480step1Labels := by
      have ha : raw22480step1 = (fun i j => raw22480step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22480step1 raw22480step0; decide +kernel
      have hl : raw22480step1Labels = raw22480step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22480step0 raw22480step0Labels permutation33 permutation3
    mixedMoment B raw22480step1 raw22480step1Labels = mixedMoment B raw22480step2 raw22480step2Labels := by
      have ha : raw22480step2 = raw22480step1 := by apply Matrix.ext; unfold raw22480step2 raw22480step1; decide +kernel
      have hl : raw22480step1Labels = labelEmbedding6 ∘ raw22480step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22480step1 raw22480step1Labels raw22480step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4553 node4553Labels := by rfl

def raw22481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22481step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22481step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22481step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22481step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22481step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22481 raw22481Labels = mixedMoment B node4553 node4553Labels := by
  calc
    mixedMoment B raw22481 raw22481Labels = mixedMoment B raw22481step0 raw22481step0Labels := by
      have hz : ∀ j, raw22481 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22481step0 = (fun i j => raw22481 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22481step0 raw22481; decide +kernel
      have hl : raw22481step0Labels = raw22481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22481 raw22481Labels permutation265 hz
    mixedMoment B raw22481step0 raw22481step0Labels = mixedMoment B raw22481step1 raw22481step1Labels := by
      have ha : raw22481step1 = (fun i j => raw22481step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22481step1 raw22481step0; decide +kernel
      have hl : raw22481step1Labels = raw22481step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22481step0 raw22481step0Labels permutation33 permutation3
    mixedMoment B raw22481step1 raw22481step1Labels = mixedMoment B raw22481step2 raw22481step2Labels := by
      have ha : raw22481step2 = raw22481step1 := by apply Matrix.ext; unfold raw22481step2 raw22481step1; decide +kernel
      have hl : raw22481step1Labels = labelEmbedding6 ∘ raw22481step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22481step1 raw22481step1Labels raw22481step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4553 node4553Labels := by rfl

def raw22482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22482step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22482step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22482step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22482step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![3, -3, 0], ![2, 0, -2]]
def raw22482step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22482step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw22482step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22482step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw22482step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22482 raw22482Labels = mixedMoment B node4190 node4190Labels := by
  calc
    mixedMoment B raw22482 raw22482Labels = mixedMoment B raw22482step0 raw22482step0Labels := by
      have hz : ∀ j, raw22482 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22482step0 = (fun i j => raw22482 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22482step0 raw22482; decide +kernel
      have hl : raw22482step0Labels = raw22482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22482 raw22482Labels permutation434 hz
    mixedMoment B raw22482step0 raw22482step0Labels = mixedMoment B raw22482step1 raw22482step1Labels := by
      have hz : ∀ j, raw22482step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22482step1 = (fun i j => raw22482step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22482step1 raw22482step0; decide +kernel
      have hl : raw22482step1Labels = raw22482step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22482step0 raw22482step0Labels permutation80 hz
    mixedMoment B raw22482step1 raw22482step1Labels = mixedMoment B raw22482step2 raw22482step2Labels := by
      have hz : ∀ j, raw22482step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22482step2 = (fun i j => raw22482step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22482step2 raw22482step1; decide +kernel
      have hl : raw22482step2Labels = raw22482step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22482step1 raw22482step1Labels permutation14 hz
    mixedMoment B raw22482step2 raw22482step2Labels = mixedMoment B raw22482step3 raw22482step3Labels := by
      have ha : raw22482step3 = (fun i j => raw22482step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22482step3 raw22482step2; decide +kernel
      have hl : raw22482step3Labels = raw22482step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22482step2 raw22482step2Labels permutation3 permutation3
    mixedMoment B raw22482step3 raw22482step3Labels = mixedMoment B raw22482step4 raw22482step4Labels := by
      have ha : raw22482step4 = raw22482step3 := by apply Matrix.ext; unfold raw22482step4 raw22482step3; decide +kernel
      have hl : raw22482step3Labels = labelEmbedding6 ∘ raw22482step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22482step3 raw22482step3Labels raw22482step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4190 node4190Labels := by rfl

def raw22483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22483step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22483step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22483step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22483step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw22483step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22483step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw22483step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22483 raw22483Labels = mixedMoment B node4557 node4557Labels := by
  calc
    mixedMoment B raw22483 raw22483Labels = mixedMoment B raw22483step0 raw22483step0Labels := by
      have hz : ∀ j, raw22483 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22483step0 = (fun i j => raw22483 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22483step0 raw22483; decide +kernel
      have hl : raw22483step0Labels = raw22483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22483 raw22483Labels permutation434 hz
    mixedMoment B raw22483step0 raw22483step0Labels = mixedMoment B raw22483step1 raw22483step1Labels := by
      have hz : ∀ j, raw22483step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22483step1 = (fun i j => raw22483step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22483step1 raw22483step0; decide +kernel
      have hl : raw22483step1Labels = raw22483step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22483step0 raw22483step0Labels permutation80 hz
    mixedMoment B raw22483step1 raw22483step1Labels = mixedMoment B raw22483step2 raw22483step2Labels := by
      have ha : raw22483step2 = (fun i j => raw22483step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22483step2 raw22483step1; decide +kernel
      have hl : raw22483step2Labels = raw22483step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22483step1 raw22483step1Labels permutation9 permutation3
    mixedMoment B raw22483step2 raw22483step2Labels = mixedMoment B raw22483step3 raw22483step3Labels := by
      have ha : raw22483step3 = raw22483step2 := by apply Matrix.ext; unfold raw22483step3 raw22483step2; decide +kernel
      have hl : raw22483step2Labels = labelEmbedding6 ∘ raw22483step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22483step2 raw22483step2Labels raw22483step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4557 node4557Labels := by rfl

def raw22484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22484step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22484step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22484step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22484step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw22484step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22484step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw22484step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22484 raw22484Labels = mixedMoment B node4557 node4557Labels := by
  calc
    mixedMoment B raw22484 raw22484Labels = mixedMoment B raw22484step0 raw22484step0Labels := by
      have hz : ∀ j, raw22484 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22484step0 = (fun i j => raw22484 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22484step0 raw22484; decide +kernel
      have hl : raw22484step0Labels = raw22484Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22484 raw22484Labels permutation434 hz
    mixedMoment B raw22484step0 raw22484step0Labels = mixedMoment B raw22484step1 raw22484step1Labels := by
      have hz : ∀ j, raw22484step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22484step1 = (fun i j => raw22484step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22484step1 raw22484step0; decide +kernel
      have hl : raw22484step1Labels = raw22484step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22484step0 raw22484step0Labels permutation56 hz
    mixedMoment B raw22484step1 raw22484step1Labels = mixedMoment B raw22484step2 raw22484step2Labels := by
      have ha : raw22484step2 = (fun i j => raw22484step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22484step2 raw22484step1; decide +kernel
      have hl : raw22484step2Labels = raw22484step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22484step1 raw22484step1Labels permutation9 permutation3
    mixedMoment B raw22484step2 raw22484step2Labels = mixedMoment B raw22484step3 raw22484step3Labels := by
      have ha : raw22484step3 = raw22484step2 := by apply Matrix.ext; unfold raw22484step3 raw22484step2; decide +kernel
      have hl : raw22484step2Labels = labelEmbedding6 ∘ raw22484step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22484step2 raw22484step2Labels raw22484step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4557 node4557Labels := by rfl

def raw22485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22485step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22485step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22485step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22485step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw22485step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22485step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw22485step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22485 raw22485Labels = mixedMoment B node4557 node4557Labels := by
  calc
    mixedMoment B raw22485 raw22485Labels = mixedMoment B raw22485step0 raw22485step0Labels := by
      have hz : ∀ j, raw22485 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22485step0 = (fun i j => raw22485 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22485step0 raw22485; decide +kernel
      have hl : raw22485step0Labels = raw22485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22485 raw22485Labels permutation346 hz
    mixedMoment B raw22485step0 raw22485step0Labels = mixedMoment B raw22485step1 raw22485step1Labels := by
      have hz : ∀ j, raw22485step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22485step1 = (fun i j => raw22485step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22485step1 raw22485step0; decide +kernel
      have hl : raw22485step1Labels = raw22485step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22485step0 raw22485step0Labels permutation56 hz
    mixedMoment B raw22485step1 raw22485step1Labels = mixedMoment B raw22485step2 raw22485step2Labels := by
      have ha : raw22485step2 = (fun i j => raw22485step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22485step2 raw22485step1; decide +kernel
      have hl : raw22485step2Labels = raw22485step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22485step1 raw22485step1Labels permutation9 permutation3
    mixedMoment B raw22485step2 raw22485step2Labels = mixedMoment B raw22485step3 raw22485step3Labels := by
      have ha : raw22485step3 = raw22485step2 := by apply Matrix.ext; unfold raw22485step3 raw22485step2; decide +kernel
      have hl : raw22485step2Labels = labelEmbedding6 ∘ raw22485step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22485step2 raw22485step2Labels raw22485step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4557 node4557Labels := by rfl

def raw22486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw22486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw22486step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22486step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw22486step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22486step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![3, -3, 0], ![1, 1, -2]]
def raw22486step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22486step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw22486step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw22486step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw22486step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22486 raw22486Labels = mixedMoment B node4621 node4621Labels := by
  calc
    mixedMoment B raw22486 raw22486Labels = mixedMoment B raw22486step0 raw22486step0Labels := by
      have hz : ∀ j, raw22486 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22486step0 = (fun i j => raw22486 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22486step0 raw22486; decide +kernel
      have hl : raw22486step0Labels = raw22486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22486 raw22486Labels permutation434 hz
    mixedMoment B raw22486step0 raw22486step0Labels = mixedMoment B raw22486step1 raw22486step1Labels := by
      have hz : ∀ j, raw22486step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22486step1 = (fun i j => raw22486step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22486step1 raw22486step0; decide +kernel
      have hl : raw22486step1Labels = raw22486step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22486step0 raw22486step0Labels permutation80 hz
    mixedMoment B raw22486step1 raw22486step1Labels = mixedMoment B raw22486step2 raw22486step2Labels := by
      have hz : ∀ j, raw22486step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22486step2 = (fun i j => raw22486step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22486step2 raw22486step1; decide +kernel
      have hl : raw22486step2Labels = raw22486step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22486step1 raw22486step1Labels permutation14 hz
    mixedMoment B raw22486step2 raw22486step2Labels = mixedMoment B raw22486step3 raw22486step3Labels := by
      have ha : raw22486step3 = (fun i j => raw22486step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22486step3 raw22486step2; decide +kernel
      have hl : raw22486step3Labels = raw22486step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22486step2 raw22486step2Labels permutation3 permutation3
    mixedMoment B raw22486step3 raw22486step3Labels = mixedMoment B raw22486step4 raw22486step4Labels := by
      have ha : raw22486step4 = raw22486step3 := by apply Matrix.ext; unfold raw22486step4 raw22486step3; decide +kernel
      have hl : raw22486step3Labels = labelEmbedding6 ∘ raw22486step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22486step3 raw22486step3Labels raw22486step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4621 node4621Labels := by rfl

def raw22487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22487Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22487step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22487step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22487step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22487step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw22487step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22487 raw22487Labels = mixedMoment B node2968 node2968Labels := by
  calc
    mixedMoment B raw22487 raw22487Labels = mixedMoment B raw22487step0 raw22487step0Labels := by
      have hz : ∀ j, raw22487 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22487step0 = (fun i j => raw22487 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22487step0 raw22487; decide +kernel
      have hl : raw22487step0Labels = raw22487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22487 raw22487Labels permutation434 hz
    mixedMoment B raw22487step0 raw22487step0Labels = mixedMoment B raw22487step1 raw22487step1Labels := by
      have hz : ∀ j, raw22487step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22487step1 = (fun i j => raw22487step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22487step1 raw22487step0; decide +kernel
      have hl : raw22487step1Labels = raw22487step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22487step0 raw22487step0Labels permutation80 hz
    mixedMoment B raw22487step1 raw22487step1Labels = mixedMoment B raw22487step2 raw22487step2Labels := by
      have ha : raw22487step2 = (fun i j => raw22487step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22487step2 raw22487step1; decide +kernel
      have hl : raw22487step2Labels = raw22487step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22487step1 raw22487step1Labels permutation9 permutation3
    _ = mixedMoment B node2968 node2968Labels := by rfl

def raw22488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22488Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22488step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22488step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22488step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22488step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw22488step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22488 raw22488Labels = mixedMoment B node2968 node2968Labels := by
  calc
    mixedMoment B raw22488 raw22488Labels = mixedMoment B raw22488step0 raw22488step0Labels := by
      have hz : ∀ j, raw22488 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22488step0 = (fun i j => raw22488 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22488step0 raw22488; decide +kernel
      have hl : raw22488step0Labels = raw22488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22488 raw22488Labels permutation434 hz
    mixedMoment B raw22488step0 raw22488step0Labels = mixedMoment B raw22488step1 raw22488step1Labels := by
      have hz : ∀ j, raw22488step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22488step1 = (fun i j => raw22488step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22488step1 raw22488step0; decide +kernel
      have hl : raw22488step1Labels = raw22488step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22488step0 raw22488step0Labels permutation56 hz
    mixedMoment B raw22488step1 raw22488step1Labels = mixedMoment B raw22488step2 raw22488step2Labels := by
      have ha : raw22488step2 = (fun i j => raw22488step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22488step2 raw22488step1; decide +kernel
      have hl : raw22488step2Labels = raw22488step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22488step1 raw22488step1Labels permutation9 permutation3
    _ = mixedMoment B node2968 node2968Labels := by rfl

def raw22489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22489Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22489step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22489step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22489step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22489step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw22489step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22489 raw22489Labels = mixedMoment B node2968 node2968Labels := by
  calc
    mixedMoment B raw22489 raw22489Labels = mixedMoment B raw22489step0 raw22489step0Labels := by
      have hz : ∀ j, raw22489 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22489step0 = (fun i j => raw22489 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22489step0 raw22489; decide +kernel
      have hl : raw22489step0Labels = raw22489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22489 raw22489Labels permutation346 hz
    mixedMoment B raw22489step0 raw22489step0Labels = mixedMoment B raw22489step1 raw22489step1Labels := by
      have hz : ∀ j, raw22489step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22489step1 = (fun i j => raw22489step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22489step1 raw22489step0; decide +kernel
      have hl : raw22489step1Labels = raw22489step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22489step0 raw22489step0Labels permutation56 hz
    mixedMoment B raw22489step1 raw22489step1Labels = mixedMoment B raw22489step2 raw22489step2Labels := by
      have ha : raw22489step2 = (fun i j => raw22489step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22489step2 raw22489step1; decide +kernel
      have hl : raw22489step2Labels = raw22489step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22489step1 raw22489step1Labels permutation9 permutation3
    _ = mixedMoment B node2968 node2968Labels := by rfl

def raw22490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22490Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22490step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22490step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22490step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22490step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22490step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22490 raw22490Labels = mixedMoment B node613 node613Labels := by
  calc
    mixedMoment B raw22490 raw22490Labels = mixedMoment B raw22490step0 raw22490step0Labels := by
      have hz : ∀ j, raw22490 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22490step0 = (fun i j => raw22490 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22490step0 raw22490; decide +kernel
      have hl : raw22490step0Labels = raw22490Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22490 raw22490Labels permutation434 hz
    mixedMoment B raw22490step0 raw22490step0Labels = mixedMoment B raw22490step1 raw22490step1Labels := by
      have hz : ∀ j, raw22490step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22490step1 = (fun i j => raw22490step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22490step1 raw22490step0; decide +kernel
      have hl : raw22490step1Labels = raw22490step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22490step0 raw22490step0Labels permutation80 hz
    mixedMoment B raw22490step1 raw22490step1Labels = mixedMoment B raw22490step2 raw22490step2Labels := by
      have ha : raw22490step2 = (fun i j => raw22490step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22490step2 raw22490step1; decide +kernel
      have hl : raw22490step2Labels = raw22490step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22490step1 raw22490step1Labels permutation9 permutation3
    _ = mixedMoment B node613 node613Labels := by rfl

def raw22491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22491Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22491step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22491step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22491 raw22491Labels = mixedMoment B node1138 node1138Labels := by
  calc
    mixedMoment B raw22491 raw22491Labels = mixedMoment B raw22491step0 raw22491step0Labels := by
      have hz : ∀ j, raw22491 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22491step0 = (fun i j => raw22491 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22491step0 raw22491; decide +kernel
      have hl : raw22491step0Labels = raw22491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22491 raw22491Labels permutation434 hz
    mixedMoment B raw22491step0 raw22491step0Labels = mixedMoment B raw22491step1 raw22491step1Labels := by
      have ha : raw22491step1 = (fun i j => raw22491step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22491step1 raw22491step0; decide +kernel
      have hl : raw22491step1Labels = raw22491step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22491step0 raw22491step0Labels permutation39 permutation3
    _ = mixedMoment B node1138 node1138Labels := by rfl

def raw22492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22492Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22492step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22492 raw22492Labels = mixedMoment B node1138 node1138Labels := by
  calc
    mixedMoment B raw22492 raw22492Labels = mixedMoment B raw22492step0 raw22492step0Labels := by
      have hz : ∀ j, raw22492 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22492step0 = (fun i j => raw22492 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22492step0 raw22492; decide +kernel
      have hl : raw22492step0Labels = raw22492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22492 raw22492Labels permutation346 hz
    mixedMoment B raw22492step0 raw22492step0Labels = mixedMoment B raw22492step1 raw22492step1Labels := by
      have ha : raw22492step1 = (fun i j => raw22492step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22492step1 raw22492step0; decide +kernel
      have hl : raw22492step1Labels = raw22492step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22492step0 raw22492step0Labels permutation39 permutation3
    _ = mixedMoment B node1138 node1138Labels := by rfl

def raw22493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw22493Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw22493step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22493step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw22493step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22493step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw22493step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22493 raw22493Labels = mixedMoment B node1294 node1294Labels := by
  calc
    mixedMoment B raw22493 raw22493Labels = mixedMoment B raw22493step0 raw22493step0Labels := by
      have hz : ∀ j, raw22493 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22493step0 = (fun i j => raw22493 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22493step0 raw22493; decide +kernel
      have hl : raw22493step0Labels = raw22493Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22493 raw22493Labels permutation434 hz
    mixedMoment B raw22493step0 raw22493step0Labels = mixedMoment B raw22493step1 raw22493step1Labels := by
      have hz : ∀ j, raw22493step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22493step1 = (fun i j => raw22493step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22493step1 raw22493step0; decide +kernel
      have hl : raw22493step1Labels = raw22493step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22493step0 raw22493step0Labels permutation80 hz
    mixedMoment B raw22493step1 raw22493step1Labels = mixedMoment B raw22493step2 raw22493step2Labels := by
      have ha : raw22493step2 = (fun i j => raw22493step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22493step2 raw22493step1; decide +kernel
      have hl : raw22493step2Labels = raw22493step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22493step1 raw22493step1Labels permutation12 permutation3
    _ = mixedMoment B node1294 node1294Labels := by rfl

def raw22494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22494Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22494step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22494step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22494step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22494step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22494step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22494 raw22494Labels = mixedMoment B node613 node613Labels := by
  calc
    mixedMoment B raw22494 raw22494Labels = mixedMoment B raw22494step0 raw22494step0Labels := by
      have hz : ∀ j, raw22494 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22494step0 = (fun i j => raw22494 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22494step0 raw22494; decide +kernel
      have hl : raw22494step0Labels = raw22494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22494 raw22494Labels permutation434 hz
    mixedMoment B raw22494step0 raw22494step0Labels = mixedMoment B raw22494step1 raw22494step1Labels := by
      have hz : ∀ j, raw22494step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22494step1 = (fun i j => raw22494step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22494step1 raw22494step0; decide +kernel
      have hl : raw22494step1Labels = raw22494step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22494step0 raw22494step0Labels permutation56 hz
    mixedMoment B raw22494step1 raw22494step1Labels = mixedMoment B raw22494step2 raw22494step2Labels := by
      have ha : raw22494step2 = (fun i j => raw22494step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22494step2 raw22494step1; decide +kernel
      have hl : raw22494step2Labels = raw22494step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22494step1 raw22494step1Labels permutation9 permutation3
    _ = mixedMoment B node613 node613Labels := by rfl

def raw22495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22495Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22495step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22495step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22495 raw22495Labels = mixedMoment B node1138 node1138Labels := by
  calc
    mixedMoment B raw22495 raw22495Labels = mixedMoment B raw22495step0 raw22495step0Labels := by
      have hz : ∀ j, raw22495 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22495step0 = (fun i j => raw22495 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22495step0 raw22495; decide +kernel
      have hl : raw22495step0Labels = raw22495Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22495 raw22495Labels permutation434 hz
    mixedMoment B raw22495step0 raw22495step0Labels = mixedMoment B raw22495step1 raw22495step1Labels := by
      have ha : raw22495step1 = (fun i j => raw22495step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22495step1 raw22495step0; decide +kernel
      have hl : raw22495step1Labels = raw22495step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22495step0 raw22495step0Labels permutation33 permutation3
    _ = mixedMoment B node1138 node1138Labels := by rfl

def raw22496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22496Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22496step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22496step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22496 raw22496Labels = mixedMoment B node1138 node1138Labels := by
  calc
    mixedMoment B raw22496 raw22496Labels = mixedMoment B raw22496step0 raw22496step0Labels := by
      have hz : ∀ j, raw22496 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22496step0 = (fun i j => raw22496 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22496step0 raw22496; decide +kernel
      have hl : raw22496step0Labels = raw22496Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22496 raw22496Labels permutation265 hz
    mixedMoment B raw22496step0 raw22496step0Labels = mixedMoment B raw22496step1 raw22496step1Labels := by
      have ha : raw22496step1 = (fun i j => raw22496step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22496step1 raw22496step0; decide +kernel
      have hl : raw22496step1Labels = raw22496step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22496step0 raw22496step0Labels permutation39 permutation3
    _ = mixedMoment B node1138 node1138Labels := by rfl

def raw22497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw22497Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw22497step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22497step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw22497step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22497step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw22497step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22497 raw22497Labels = mixedMoment B node1294 node1294Labels := by
  calc
    mixedMoment B raw22497 raw22497Labels = mixedMoment B raw22497step0 raw22497step0Labels := by
      have hz : ∀ j, raw22497 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22497step0 = (fun i j => raw22497 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22497step0 raw22497; decide +kernel
      have hl : raw22497step0Labels = raw22497Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22497 raw22497Labels permutation434 hz
    mixedMoment B raw22497step0 raw22497step0Labels = mixedMoment B raw22497step1 raw22497step1Labels := by
      have hz : ∀ j, raw22497step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22497step1 = (fun i j => raw22497step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22497step1 raw22497step0; decide +kernel
      have hl : raw22497step1Labels = raw22497step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22497step0 raw22497step0Labels permutation56 hz
    mixedMoment B raw22497step1 raw22497step1Labels = mixedMoment B raw22497step2 raw22497step2Labels := by
      have ha : raw22497step2 = (fun i j => raw22497step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22497step2 raw22497step1; decide +kernel
      have hl : raw22497step2Labels = raw22497step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22497step1 raw22497step1Labels permutation12 permutation3
    _ = mixedMoment B node1294 node1294Labels := by rfl

def raw22498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22498Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22498step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22498step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22498step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22498step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22498step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22498 raw22498Labels = mixedMoment B node613 node613Labels := by
  calc
    mixedMoment B raw22498 raw22498Labels = mixedMoment B raw22498step0 raw22498step0Labels := by
      have hz : ∀ j, raw22498 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22498step0 = (fun i j => raw22498 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22498step0 raw22498; decide +kernel
      have hl : raw22498step0Labels = raw22498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22498 raw22498Labels permutation346 hz
    mixedMoment B raw22498step0 raw22498step0Labels = mixedMoment B raw22498step1 raw22498step1Labels := by
      have hz : ∀ j, raw22498step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22498step1 = (fun i j => raw22498step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22498step1 raw22498step0; decide +kernel
      have hl : raw22498step1Labels = raw22498step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22498step0 raw22498step0Labels permutation56 hz
    mixedMoment B raw22498step1 raw22498step1Labels = mixedMoment B raw22498step2 raw22498step2Labels := by
      have ha : raw22498step2 = (fun i j => raw22498step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22498step2 raw22498step1; decide +kernel
      have hl : raw22498step2Labels = raw22498step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22498step1 raw22498step1Labels permutation9 permutation3
    _ = mixedMoment B node613 node613Labels := by rfl

def raw22499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22499Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22499step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22499step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22499step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22499 raw22499Labels = mixedMoment B node1138 node1138Labels := by
  calc
    mixedMoment B raw22499 raw22499Labels = mixedMoment B raw22499step0 raw22499step0Labels := by
      have hz : ∀ j, raw22499 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22499step0 = (fun i j => raw22499 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22499step0 raw22499; decide +kernel
      have hl : raw22499step0Labels = raw22499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22499 raw22499Labels permutation346 hz
    mixedMoment B raw22499step0 raw22499step0Labels = mixedMoment B raw22499step1 raw22499step1Labels := by
      have ha : raw22499step1 = (fun i j => raw22499step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22499step1 raw22499step0; decide +kernel
      have hl : raw22499step1Labels = raw22499step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22499step0 raw22499step0Labels permutation33 permutation3
    _ = mixedMoment B node1138 node1138Labels := by rfl

def raw22500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22500Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw22500step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22500step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22500 raw22500Labels = mixedMoment B node1138 node1138Labels := by
  calc
    mixedMoment B raw22500 raw22500Labels = mixedMoment B raw22500step0 raw22500step0Labels := by
      have hz : ∀ j, raw22500 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22500step0 = (fun i j => raw22500 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22500step0 raw22500; decide +kernel
      have hl : raw22500step0Labels = raw22500Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22500 raw22500Labels permutation265 hz
    mixedMoment B raw22500step0 raw22500step0Labels = mixedMoment B raw22500step1 raw22500step1Labels := by
      have ha : raw22500step1 = (fun i j => raw22500step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22500step1 raw22500step0; decide +kernel
      have hl : raw22500step1Labels = raw22500step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22500step0 raw22500step0Labels permutation33 permutation3
    _ = mixedMoment B node1138 node1138Labels := by rfl

def raw22501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22501Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22501step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22501step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22501step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22501step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![3, -3, 0], ![2, 0, -2]]
def raw22501step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22501step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw22501step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22501 raw22501Labels = mixedMoment B node618 node618Labels := by
  calc
    mixedMoment B raw22501 raw22501Labels = mixedMoment B raw22501step0 raw22501step0Labels := by
      have hz : ∀ j, raw22501 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22501step0 = (fun i j => raw22501 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22501step0 raw22501; decide +kernel
      have hl : raw22501step0Labels = raw22501Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22501 raw22501Labels permutation434 hz
    mixedMoment B raw22501step0 raw22501step0Labels = mixedMoment B raw22501step1 raw22501step1Labels := by
      have hz : ∀ j, raw22501step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22501step1 = (fun i j => raw22501step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22501step1 raw22501step0; decide +kernel
      have hl : raw22501step1Labels = raw22501step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22501step0 raw22501step0Labels permutation80 hz
    mixedMoment B raw22501step1 raw22501step1Labels = mixedMoment B raw22501step2 raw22501step2Labels := by
      have hz : ∀ j, raw22501step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22501step2 = (fun i j => raw22501step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22501step2 raw22501step1; decide +kernel
      have hl : raw22501step2Labels = raw22501step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22501step1 raw22501step1Labels permutation14 hz
    mixedMoment B raw22501step2 raw22501step2Labels = mixedMoment B raw22501step3 raw22501step3Labels := by
      have ha : raw22501step3 = (fun i j => raw22501step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22501step3 raw22501step2; decide +kernel
      have hl : raw22501step3Labels = raw22501step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22501step2 raw22501step2Labels permutation3 permutation3
    _ = mixedMoment B node618 node618Labels := by rfl

def raw22502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22502Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22502step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22502step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22502step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22502step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw22502step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22502 raw22502Labels = mixedMoment B node1143 node1143Labels := by
  calc
    mixedMoment B raw22502 raw22502Labels = mixedMoment B raw22502step0 raw22502step0Labels := by
      have hz : ∀ j, raw22502 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22502step0 = (fun i j => raw22502 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22502step0 raw22502; decide +kernel
      have hl : raw22502step0Labels = raw22502Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22502 raw22502Labels permutation434 hz
    mixedMoment B raw22502step0 raw22502step0Labels = mixedMoment B raw22502step1 raw22502step1Labels := by
      have hz : ∀ j, raw22502step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22502step1 = (fun i j => raw22502step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22502step1 raw22502step0; decide +kernel
      have hl : raw22502step1Labels = raw22502step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22502step0 raw22502step0Labels permutation80 hz
    mixedMoment B raw22502step1 raw22502step1Labels = mixedMoment B raw22502step2 raw22502step2Labels := by
      have ha : raw22502step2 = (fun i j => raw22502step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22502step2 raw22502step1; decide +kernel
      have hl : raw22502step2Labels = raw22502step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22502step1 raw22502step1Labels permutation9 permutation3
    _ = mixedMoment B node1143 node1143Labels := by rfl

def raw22503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22503Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22503step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22503step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22503step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22503step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw22503step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22503 raw22503Labels = mixedMoment B node1143 node1143Labels := by
  calc
    mixedMoment B raw22503 raw22503Labels = mixedMoment B raw22503step0 raw22503step0Labels := by
      have hz : ∀ j, raw22503 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22503step0 = (fun i j => raw22503 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22503step0 raw22503; decide +kernel
      have hl : raw22503step0Labels = raw22503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22503 raw22503Labels permutation434 hz
    mixedMoment B raw22503step0 raw22503step0Labels = mixedMoment B raw22503step1 raw22503step1Labels := by
      have hz : ∀ j, raw22503step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22503step1 = (fun i j => raw22503step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22503step1 raw22503step0; decide +kernel
      have hl : raw22503step1Labels = raw22503step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22503step0 raw22503step0Labels permutation56 hz
    mixedMoment B raw22503step1 raw22503step1Labels = mixedMoment B raw22503step2 raw22503step2Labels := by
      have ha : raw22503step2 = (fun i j => raw22503step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22503step2 raw22503step1; decide +kernel
      have hl : raw22503step2Labels = raw22503step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22503step1 raw22503step1Labels permutation9 permutation3
    _ = mixedMoment B node1143 node1143Labels := by rfl

def raw22504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22504Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22504step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22504step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw22504step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22504step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw22504step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22504 raw22504Labels = mixedMoment B node1143 node1143Labels := by
  calc
    mixedMoment B raw22504 raw22504Labels = mixedMoment B raw22504step0 raw22504step0Labels := by
      have hz : ∀ j, raw22504 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22504step0 = (fun i j => raw22504 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22504step0 raw22504; decide +kernel
      have hl : raw22504step0Labels = raw22504Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22504 raw22504Labels permutation346 hz
    mixedMoment B raw22504step0 raw22504step0Labels = mixedMoment B raw22504step1 raw22504step1Labels := by
      have hz : ∀ j, raw22504step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22504step1 = (fun i j => raw22504step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22504step1 raw22504step0; decide +kernel
      have hl : raw22504step1Labels = raw22504step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22504step0 raw22504step0Labels permutation56 hz
    mixedMoment B raw22504step1 raw22504step1Labels = mixedMoment B raw22504step2 raw22504step2Labels := by
      have ha : raw22504step2 = (fun i j => raw22504step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22504step2 raw22504step1; decide +kernel
      have hl : raw22504step2Labels = raw22504step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22504step1 raw22504step1Labels permutation9 permutation3
    _ = mixedMoment B node1143 node1143Labels := by rfl

def raw22505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw22505Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw22505step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22505step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw22505step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22505step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![3, -3, 0], ![1, 1, -2]]
def raw22505step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22505step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw22505step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22505 raw22505Labels = mixedMoment B node1297 node1297Labels := by
  calc
    mixedMoment B raw22505 raw22505Labels = mixedMoment B raw22505step0 raw22505step0Labels := by
      have hz : ∀ j, raw22505 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22505step0 = (fun i j => raw22505 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22505step0 raw22505; decide +kernel
      have hl : raw22505step0Labels = raw22505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22505 raw22505Labels permutation434 hz
    mixedMoment B raw22505step0 raw22505step0Labels = mixedMoment B raw22505step1 raw22505step1Labels := by
      have hz : ∀ j, raw22505step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22505step1 = (fun i j => raw22505step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22505step1 raw22505step0; decide +kernel
      have hl : raw22505step1Labels = raw22505step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22505step0 raw22505step0Labels permutation80 hz
    mixedMoment B raw22505step1 raw22505step1Labels = mixedMoment B raw22505step2 raw22505step2Labels := by
      have hz : ∀ j, raw22505step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22505step2 = (fun i j => raw22505step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22505step2 raw22505step1; decide +kernel
      have hl : raw22505step2Labels = raw22505step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22505step1 raw22505step1Labels permutation14 hz
    mixedMoment B raw22505step2 raw22505step2Labels = mixedMoment B raw22505step3 raw22505step3Labels := by
      have ha : raw22505step3 = (fun i j => raw22505step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw22505step3 raw22505step2; decide +kernel
      have hl : raw22505step3Labels = raw22505step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22505step2 raw22505step2Labels permutation3 permutation3
    _ = mixedMoment B node1297 node1297Labels := by rfl

def raw22506 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22506Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22506step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22506step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22506step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22506step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22506step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22506step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22506step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22506 raw22506Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw22506 raw22506Labels = mixedMoment B raw22506step0 raw22506step0Labels := by
      have hz : ∀ j, raw22506 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22506step0 = (fun i j => raw22506 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22506step0 raw22506; decide +kernel
      have hl : raw22506step0Labels = raw22506Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22506 raw22506Labels permutation434 hz
    mixedMoment B raw22506step0 raw22506step0Labels = mixedMoment B raw22506step1 raw22506step1Labels := by
      have hz : ∀ j, raw22506step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22506step1 = (fun i j => raw22506step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22506step1 raw22506step0; decide +kernel
      have hl : raw22506step1Labels = raw22506step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22506step0 raw22506step0Labels permutation80 hz
    mixedMoment B raw22506step1 raw22506step1Labels = mixedMoment B raw22506step2 raw22506step2Labels := by
      have ha : raw22506step2 = (fun i j => raw22506step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22506step2 raw22506step1; decide +kernel
      have hl : raw22506step2Labels = raw22506step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22506step1 raw22506step1Labels permutation9 permutation7
    mixedMoment B raw22506step2 raw22506step2Labels = mixedMoment B raw22506step3 raw22506step3Labels := by
      have ha : raw22506step3 = raw22506step2 := by apply Matrix.ext; unfold raw22506step3 raw22506step2; decide +kernel
      have hl : raw22506step2Labels = labelEmbedding10 ∘ raw22506step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22506step2 raw22506step2Labels raw22506step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4466 node4466Labels := by rfl

def raw22507 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22507Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22507step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22507step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22507step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22507step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22507step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22507step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22507step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22507 raw22507Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw22507 raw22507Labels = mixedMoment B raw22507step0 raw22507step0Labels := by
      have hz : ∀ j, raw22507 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22507step0 = (fun i j => raw22507 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22507step0 raw22507; decide +kernel
      have hl : raw22507step0Labels = raw22507Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22507 raw22507Labels permutation434 hz
    mixedMoment B raw22507step0 raw22507step0Labels = mixedMoment B raw22507step1 raw22507step1Labels := by
      have hz : ∀ j, raw22507step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22507step1 = (fun i j => raw22507step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22507step1 raw22507step0; decide +kernel
      have hl : raw22507step1Labels = raw22507step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22507step0 raw22507step0Labels permutation56 hz
    mixedMoment B raw22507step1 raw22507step1Labels = mixedMoment B raw22507step2 raw22507step2Labels := by
      have ha : raw22507step2 = (fun i j => raw22507step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22507step2 raw22507step1; decide +kernel
      have hl : raw22507step2Labels = raw22507step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22507step1 raw22507step1Labels permutation9 permutation7
    mixedMoment B raw22507step2 raw22507step2Labels = mixedMoment B raw22507step3 raw22507step3Labels := by
      have ha : raw22507step3 = raw22507step2 := by apply Matrix.ext; unfold raw22507step3 raw22507step2; decide +kernel
      have hl : raw22507step2Labels = labelEmbedding10 ∘ raw22507step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22507step2 raw22507step2Labels raw22507step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4466 node4466Labels := by rfl

def raw22508 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22508Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22508step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22508step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22508step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22508step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22508step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22508step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22508step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22508 raw22508Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw22508 raw22508Labels = mixedMoment B raw22508step0 raw22508step0Labels := by
      have hz : ∀ j, raw22508 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22508step0 = (fun i j => raw22508 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22508step0 raw22508; decide +kernel
      have hl : raw22508step0Labels = raw22508Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22508 raw22508Labels permutation346 hz
    mixedMoment B raw22508step0 raw22508step0Labels = mixedMoment B raw22508step1 raw22508step1Labels := by
      have hz : ∀ j, raw22508step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22508step1 = (fun i j => raw22508step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22508step1 raw22508step0; decide +kernel
      have hl : raw22508step1Labels = raw22508step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22508step0 raw22508step0Labels permutation56 hz
    mixedMoment B raw22508step1 raw22508step1Labels = mixedMoment B raw22508step2 raw22508step2Labels := by
      have ha : raw22508step2 = (fun i j => raw22508step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22508step2 raw22508step1; decide +kernel
      have hl : raw22508step2Labels = raw22508step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22508step1 raw22508step1Labels permutation9 permutation7
    mixedMoment B raw22508step2 raw22508step2Labels = mixedMoment B raw22508step3 raw22508step3Labels := by
      have ha : raw22508step3 = raw22508step2 := by apply Matrix.ext; unfold raw22508step3 raw22508step2; decide +kernel
      have hl : raw22508step2Labels = labelEmbedding10 ∘ raw22508step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22508step2 raw22508step2Labels raw22508step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4466 node4466Labels := by rfl

def raw22509 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22509Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22509step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22509step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22509step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22509step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-3, 1, 2], ![0, -2, 2]]
def raw22509step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22509step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw22509step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22509step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw22509step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22509 raw22509Labels = mixedMoment B node4510 node4510Labels := by
  calc
    mixedMoment B raw22509 raw22509Labels = mixedMoment B raw22509step0 raw22509step0Labels := by
      have hz : ∀ j, raw22509 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22509step0 = (fun i j => raw22509 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22509step0 raw22509; decide +kernel
      have hl : raw22509step0Labels = raw22509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22509 raw22509Labels permutation434 hz
    mixedMoment B raw22509step0 raw22509step0Labels = mixedMoment B raw22509step1 raw22509step1Labels := by
      have hz : ∀ j, raw22509step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22509step1 = (fun i j => raw22509step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22509step1 raw22509step0; decide +kernel
      have hl : raw22509step1Labels = raw22509step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22509step0 raw22509step0Labels permutation80 hz
    mixedMoment B raw22509step1 raw22509step1Labels = mixedMoment B raw22509step2 raw22509step2Labels := by
      have hz : ∀ j, raw22509step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22509step2 = (fun i j => raw22509step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22509step2 raw22509step1; decide +kernel
      have hl : raw22509step2Labels = raw22509step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22509step1 raw22509step1Labels permutation14 hz
    mixedMoment B raw22509step2 raw22509step2Labels = mixedMoment B raw22509step3 raw22509step3Labels := by
      have ha : raw22509step3 = (fun i j => raw22509step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22509step3 raw22509step2; decide +kernel
      have hl : raw22509step3Labels = raw22509step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22509step2 raw22509step2Labels permutation3 permutation7
    mixedMoment B raw22509step3 raw22509step3Labels = mixedMoment B raw22509step4 raw22509step4Labels := by
      have ha : raw22509step4 = raw22509step3 := by apply Matrix.ext; unfold raw22509step4 raw22509step3; decide +kernel
      have hl : raw22509step3Labels = labelEmbedding10 ∘ raw22509step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22509step3 raw22509step3Labels raw22509step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4510 node4510Labels := by rfl

def raw22510 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22510Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22510step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22510step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22510step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22510step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 0, 2], ![-1, -1, 2]]
def raw22510step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22510step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw22510step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22510step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw22510step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22510 raw22510Labels = mixedMoment B node4511 node4511Labels := by
  calc
    mixedMoment B raw22510 raw22510Labels = mixedMoment B raw22510step0 raw22510step0Labels := by
      have hz : ∀ j, raw22510 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22510step0 = (fun i j => raw22510 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22510step0 raw22510; decide +kernel
      have hl : raw22510step0Labels = raw22510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22510 raw22510Labels permutation434 hz
    mixedMoment B raw22510step0 raw22510step0Labels = mixedMoment B raw22510step1 raw22510step1Labels := by
      have hz : ∀ j, raw22510step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22510step1 = (fun i j => raw22510step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22510step1 raw22510step0; decide +kernel
      have hl : raw22510step1Labels = raw22510step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22510step0 raw22510step0Labels permutation80 hz
    mixedMoment B raw22510step1 raw22510step1Labels = mixedMoment B raw22510step2 raw22510step2Labels := by
      have hz : ∀ j, raw22510step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22510step2 = (fun i j => raw22510step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22510step2 raw22510step1; decide +kernel
      have hl : raw22510step2Labels = raw22510step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22510step1 raw22510step1Labels permutation14 hz
    mixedMoment B raw22510step2 raw22510step2Labels = mixedMoment B raw22510step3 raw22510step3Labels := by
      have ha : raw22510step3 = (fun i j => raw22510step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22510step3 raw22510step2; decide +kernel
      have hl : raw22510step3Labels = raw22510step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22510step2 raw22510step2Labels permutation3 permutation7
    mixedMoment B raw22510step3 raw22510step3Labels = mixedMoment B raw22510step4 raw22510step4Labels := by
      have ha : raw22510step4 = raw22510step3 := by apply Matrix.ext; unfold raw22510step4 raw22510step3; decide +kernel
      have hl : raw22510step3Labels = labelEmbedding10 ∘ raw22510step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22510step3 raw22510step3Labels raw22510step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4511 node4511Labels := by rfl

def raw22511 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22511Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22511step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22511step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22511step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22511step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22511step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22511step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22511step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22511 raw22511Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw22511 raw22511Labels = mixedMoment B raw22511step0 raw22511step0Labels := by
      have hz : ∀ j, raw22511 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22511step0 = (fun i j => raw22511 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22511step0 raw22511; decide +kernel
      have hl : raw22511step0Labels = raw22511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22511 raw22511Labels permutation434 hz
    mixedMoment B raw22511step0 raw22511step0Labels = mixedMoment B raw22511step1 raw22511step1Labels := by
      have hz : ∀ j, raw22511step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22511step1 = (fun i j => raw22511step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22511step1 raw22511step0; decide +kernel
      have hl : raw22511step1Labels = raw22511step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22511step0 raw22511step0Labels permutation80 hz
    mixedMoment B raw22511step1 raw22511step1Labels = mixedMoment B raw22511step2 raw22511step2Labels := by
      have ha : raw22511step2 = (fun i j => raw22511step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22511step2 raw22511step1; decide +kernel
      have hl : raw22511step2Labels = raw22511step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22511step1 raw22511step1Labels permutation8 permutation6
    mixedMoment B raw22511step2 raw22511step2Labels = mixedMoment B raw22511step3 raw22511step3Labels := by
      have ha : raw22511step3 = raw22511step2 := by apply Matrix.ext; unfold raw22511step3 raw22511step2; decide +kernel
      have hl : raw22511step2Labels = labelEmbedding9 ∘ raw22511step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22511step2 raw22511step2Labels raw22511step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4466 node4466Labels := by rfl

def raw22512 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22512Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22512step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22512step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22512step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22512step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22512step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22512 raw22512Labels = mixedMoment B node4592 node4592Labels := by
  calc
    mixedMoment B raw22512 raw22512Labels = mixedMoment B raw22512step0 raw22512step0Labels := by
      have hz : ∀ j, raw22512 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22512step0 = (fun i j => raw22512 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22512step0 raw22512; decide +kernel
      have hl : raw22512step0Labels = raw22512Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22512 raw22512Labels permutation434 hz
    mixedMoment B raw22512step0 raw22512step0Labels = mixedMoment B raw22512step1 raw22512step1Labels := by
      have ha : raw22512step1 = (fun i j => raw22512step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22512step1 raw22512step0; decide +kernel
      have hl : raw22512step1Labels = raw22512step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22512step0 raw22512step0Labels permutation38 permutation6
    mixedMoment B raw22512step1 raw22512step1Labels = mixedMoment B raw22512step2 raw22512step2Labels := by
      have ha : raw22512step2 = raw22512step1 := by apply Matrix.ext; unfold raw22512step2 raw22512step1; decide +kernel
      have hl : raw22512step1Labels = labelEmbedding9 ∘ raw22512step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22512step1 raw22512step1Labels raw22512step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4592 node4592Labels := by rfl

def raw22513 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22513Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22513step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22513step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22513step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22513step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22513 raw22513Labels = mixedMoment B node4592 node4592Labels := by
  calc
    mixedMoment B raw22513 raw22513Labels = mixedMoment B raw22513step0 raw22513step0Labels := by
      have hz : ∀ j, raw22513 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22513step0 = (fun i j => raw22513 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22513step0 raw22513; decide +kernel
      have hl : raw22513step0Labels = raw22513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22513 raw22513Labels permutation346 hz
    mixedMoment B raw22513step0 raw22513step0Labels = mixedMoment B raw22513step1 raw22513step1Labels := by
      have ha : raw22513step1 = (fun i j => raw22513step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22513step1 raw22513step0; decide +kernel
      have hl : raw22513step1Labels = raw22513step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22513step0 raw22513step0Labels permutation38 permutation6
    mixedMoment B raw22513step1 raw22513step1Labels = mixedMoment B raw22513step2 raw22513step2Labels := by
      have ha : raw22513step2 = raw22513step1 := by apply Matrix.ext; unfold raw22513step2 raw22513step1; decide +kernel
      have hl : raw22513step1Labels = labelEmbedding9 ∘ raw22513step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22513step1 raw22513step1Labels raw22513step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4592 node4592Labels := by rfl

def raw22514 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22514Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22514step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22514step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22514step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22514step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22514step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22514step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22514step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22514 raw22514Labels = mixedMoment B node4611 node4611Labels := by
  calc
    mixedMoment B raw22514 raw22514Labels = mixedMoment B raw22514step0 raw22514step0Labels := by
      have hz : ∀ j, raw22514 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22514step0 = (fun i j => raw22514 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22514step0 raw22514; decide +kernel
      have hl : raw22514step0Labels = raw22514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22514 raw22514Labels permutation434 hz
    mixedMoment B raw22514step0 raw22514step0Labels = mixedMoment B raw22514step1 raw22514step1Labels := by
      have hz : ∀ j, raw22514step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22514step1 = (fun i j => raw22514step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22514step1 raw22514step0; decide +kernel
      have hl : raw22514step1Labels = raw22514step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22514step0 raw22514step0Labels permutation80 hz
    mixedMoment B raw22514step1 raw22514step1Labels = mixedMoment B raw22514step2 raw22514step2Labels := by
      have ha : raw22514step2 = (fun i j => raw22514step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22514step2 raw22514step1; decide +kernel
      have hl : raw22514step2Labels = raw22514step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22514step1 raw22514step1Labels permutation9 permutation7
    mixedMoment B raw22514step2 raw22514step2Labels = mixedMoment B raw22514step3 raw22514step3Labels := by
      have ha : raw22514step3 = raw22514step2 := by apply Matrix.ext; unfold raw22514step3 raw22514step2; decide +kernel
      have hl : raw22514step2Labels = labelEmbedding10 ∘ raw22514step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22514step2 raw22514step2Labels raw22514step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4611 node4611Labels := by rfl

def raw22515 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22515Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22515step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22515step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22515step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22515step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22515step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22515step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22515step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22515 raw22515Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw22515 raw22515Labels = mixedMoment B raw22515step0 raw22515step0Labels := by
      have hz : ∀ j, raw22515 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22515step0 = (fun i j => raw22515 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22515step0 raw22515; decide +kernel
      have hl : raw22515step0Labels = raw22515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22515 raw22515Labels permutation434 hz
    mixedMoment B raw22515step0 raw22515step0Labels = mixedMoment B raw22515step1 raw22515step1Labels := by
      have hz : ∀ j, raw22515step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22515step1 = (fun i j => raw22515step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22515step1 raw22515step0; decide +kernel
      have hl : raw22515step1Labels = raw22515step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22515step0 raw22515step0Labels permutation80 hz
    mixedMoment B raw22515step1 raw22515step1Labels = mixedMoment B raw22515step2 raw22515step2Labels := by
      have ha : raw22515step2 = (fun i j => raw22515step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22515step2 raw22515step1; decide +kernel
      have hl : raw22515step2Labels = raw22515step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22515step1 raw22515step1Labels permutation9 permutation7
    mixedMoment B raw22515step2 raw22515step2Labels = mixedMoment B raw22515step3 raw22515step3Labels := by
      have ha : raw22515step3 = raw22515step2 := by apply Matrix.ext; unfold raw22515step3 raw22515step2; decide +kernel
      have hl : raw22515step2Labels = labelEmbedding10 ∘ raw22515step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22515step2 raw22515step2Labels raw22515step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

def raw22516 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22516Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22516step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22516step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22516step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22516step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22516step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22516step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22516step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22516 raw22516Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw22516 raw22516Labels = mixedMoment B raw22516step0 raw22516step0Labels := by
      have hz : ∀ j, raw22516 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22516step0 = (fun i j => raw22516 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22516step0 raw22516; decide +kernel
      have hl : raw22516step0Labels = raw22516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22516 raw22516Labels permutation434 hz
    mixedMoment B raw22516step0 raw22516step0Labels = mixedMoment B raw22516step1 raw22516step1Labels := by
      have hz : ∀ j, raw22516step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22516step1 = (fun i j => raw22516step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22516step1 raw22516step0; decide +kernel
      have hl : raw22516step1Labels = raw22516step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22516step0 raw22516step0Labels permutation56 hz
    mixedMoment B raw22516step1 raw22516step1Labels = mixedMoment B raw22516step2 raw22516step2Labels := by
      have ha : raw22516step2 = (fun i j => raw22516step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22516step2 raw22516step1; decide +kernel
      have hl : raw22516step2Labels = raw22516step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22516step1 raw22516step1Labels permutation8 permutation6
    mixedMoment B raw22516step2 raw22516step2Labels = mixedMoment B raw22516step3 raw22516step3Labels := by
      have ha : raw22516step3 = raw22516step2 := by apply Matrix.ext; unfold raw22516step3 raw22516step2; decide +kernel
      have hl : raw22516step2Labels = labelEmbedding9 ∘ raw22516step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22516step2 raw22516step2Labels raw22516step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4466 node4466Labels := by rfl

def raw22517 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22517Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22517step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22517step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22517step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22517step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22517 raw22517Labels = mixedMoment B node4592 node4592Labels := by
  calc
    mixedMoment B raw22517 raw22517Labels = mixedMoment B raw22517step0 raw22517step0Labels := by
      have hz : ∀ j, raw22517 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22517step0 = (fun i j => raw22517 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22517step0 raw22517; decide +kernel
      have hl : raw22517step0Labels = raw22517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22517 raw22517Labels permutation434 hz
    mixedMoment B raw22517step0 raw22517step0Labels = mixedMoment B raw22517step1 raw22517step1Labels := by
      have ha : raw22517step1 = (fun i j => raw22517step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22517step1 raw22517step0; decide +kernel
      have hl : raw22517step1Labels = raw22517step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22517step0 raw22517step0Labels permutation32 permutation6
    mixedMoment B raw22517step1 raw22517step1Labels = mixedMoment B raw22517step2 raw22517step2Labels := by
      have ha : raw22517step2 = raw22517step1 := by apply Matrix.ext; unfold raw22517step2 raw22517step1; decide +kernel
      have hl : raw22517step1Labels = labelEmbedding9 ∘ raw22517step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22517step1 raw22517step1Labels raw22517step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4592 node4592Labels := by rfl

def raw22518 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22518Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22518step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22518step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22518step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22518step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22518step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22518 raw22518Labels = mixedMoment B node4592 node4592Labels := by
  calc
    mixedMoment B raw22518 raw22518Labels = mixedMoment B raw22518step0 raw22518step0Labels := by
      have hz : ∀ j, raw22518 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22518step0 = (fun i j => raw22518 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22518step0 raw22518; decide +kernel
      have hl : raw22518step0Labels = raw22518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22518 raw22518Labels permutation265 hz
    mixedMoment B raw22518step0 raw22518step0Labels = mixedMoment B raw22518step1 raw22518step1Labels := by
      have ha : raw22518step1 = (fun i j => raw22518step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22518step1 raw22518step0; decide +kernel
      have hl : raw22518step1Labels = raw22518step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22518step0 raw22518step0Labels permutation38 permutation6
    mixedMoment B raw22518step1 raw22518step1Labels = mixedMoment B raw22518step2 raw22518step2Labels := by
      have ha : raw22518step2 = raw22518step1 := by apply Matrix.ext; unfold raw22518step2 raw22518step1; decide +kernel
      have hl : raw22518step1Labels = labelEmbedding9 ∘ raw22518step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22518step1 raw22518step1Labels raw22518step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4592 node4592Labels := by rfl

def raw22519 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22519Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22519step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22519step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22519step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22519step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22519step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22519step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22519step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22519 raw22519Labels = mixedMoment B node4611 node4611Labels := by
  calc
    mixedMoment B raw22519 raw22519Labels = mixedMoment B raw22519step0 raw22519step0Labels := by
      have hz : ∀ j, raw22519 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22519step0 = (fun i j => raw22519 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22519step0 raw22519; decide +kernel
      have hl : raw22519step0Labels = raw22519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22519 raw22519Labels permutation434 hz
    mixedMoment B raw22519step0 raw22519step0Labels = mixedMoment B raw22519step1 raw22519step1Labels := by
      have hz : ∀ j, raw22519step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22519step1 = (fun i j => raw22519step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22519step1 raw22519step0; decide +kernel
      have hl : raw22519step1Labels = raw22519step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22519step0 raw22519step0Labels permutation56 hz
    mixedMoment B raw22519step1 raw22519step1Labels = mixedMoment B raw22519step2 raw22519step2Labels := by
      have ha : raw22519step2 = (fun i j => raw22519step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22519step2 raw22519step1; decide +kernel
      have hl : raw22519step2Labels = raw22519step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22519step1 raw22519step1Labels permutation9 permutation7
    mixedMoment B raw22519step2 raw22519step2Labels = mixedMoment B raw22519step3 raw22519step3Labels := by
      have ha : raw22519step3 = raw22519step2 := by apply Matrix.ext; unfold raw22519step3 raw22519step2; decide +kernel
      have hl : raw22519step2Labels = labelEmbedding10 ∘ raw22519step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22519step2 raw22519step2Labels raw22519step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4611 node4611Labels := by rfl

def raw22520 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22520Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22520step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22520step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22520step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22520step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22520step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22520step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22520step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22520 raw22520Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw22520 raw22520Labels = mixedMoment B raw22520step0 raw22520step0Labels := by
      have hz : ∀ j, raw22520 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22520step0 = (fun i j => raw22520 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22520step0 raw22520; decide +kernel
      have hl : raw22520step0Labels = raw22520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22520 raw22520Labels permutation434 hz
    mixedMoment B raw22520step0 raw22520step0Labels = mixedMoment B raw22520step1 raw22520step1Labels := by
      have hz : ∀ j, raw22520step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22520step1 = (fun i j => raw22520step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22520step1 raw22520step0; decide +kernel
      have hl : raw22520step1Labels = raw22520step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22520step0 raw22520step0Labels permutation56 hz
    mixedMoment B raw22520step1 raw22520step1Labels = mixedMoment B raw22520step2 raw22520step2Labels := by
      have ha : raw22520step2 = (fun i j => raw22520step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22520step2 raw22520step1; decide +kernel
      have hl : raw22520step2Labels = raw22520step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22520step1 raw22520step1Labels permutation9 permutation7
    mixedMoment B raw22520step2 raw22520step2Labels = mixedMoment B raw22520step3 raw22520step3Labels := by
      have ha : raw22520step3 = raw22520step2 := by apply Matrix.ext; unfold raw22520step3 raw22520step2; decide +kernel
      have hl : raw22520step2Labels = labelEmbedding10 ∘ raw22520step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22520step2 raw22520step2Labels raw22520step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

def raw22521 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22521Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22521step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22521step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22521step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22521step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22521step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22521step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22521step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22521 raw22521Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw22521 raw22521Labels = mixedMoment B raw22521step0 raw22521step0Labels := by
      have hz : ∀ j, raw22521 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22521step0 = (fun i j => raw22521 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22521step0 raw22521; decide +kernel
      have hl : raw22521step0Labels = raw22521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22521 raw22521Labels permutation346 hz
    mixedMoment B raw22521step0 raw22521step0Labels = mixedMoment B raw22521step1 raw22521step1Labels := by
      have hz : ∀ j, raw22521step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22521step1 = (fun i j => raw22521step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22521step1 raw22521step0; decide +kernel
      have hl : raw22521step1Labels = raw22521step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22521step0 raw22521step0Labels permutation56 hz
    mixedMoment B raw22521step1 raw22521step1Labels = mixedMoment B raw22521step2 raw22521step2Labels := by
      have ha : raw22521step2 = (fun i j => raw22521step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22521step2 raw22521step1; decide +kernel
      have hl : raw22521step2Labels = raw22521step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22521step1 raw22521step1Labels permutation8 permutation6
    mixedMoment B raw22521step2 raw22521step2Labels = mixedMoment B raw22521step3 raw22521step3Labels := by
      have ha : raw22521step3 = raw22521step2 := by apply Matrix.ext; unfold raw22521step3 raw22521step2; decide +kernel
      have hl : raw22521step2Labels = labelEmbedding9 ∘ raw22521step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22521step2 raw22521step2Labels raw22521step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4466 node4466Labels := by rfl

def raw22522 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22522Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22522step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22522step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22522step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22522step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22522step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22522 raw22522Labels = mixedMoment B node4592 node4592Labels := by
  calc
    mixedMoment B raw22522 raw22522Labels = mixedMoment B raw22522step0 raw22522step0Labels := by
      have hz : ∀ j, raw22522 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22522step0 = (fun i j => raw22522 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22522step0 raw22522; decide +kernel
      have hl : raw22522step0Labels = raw22522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22522 raw22522Labels permutation346 hz
    mixedMoment B raw22522step0 raw22522step0Labels = mixedMoment B raw22522step1 raw22522step1Labels := by
      have ha : raw22522step1 = (fun i j => raw22522step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22522step1 raw22522step0; decide +kernel
      have hl : raw22522step1Labels = raw22522step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22522step0 raw22522step0Labels permutation32 permutation6
    mixedMoment B raw22522step1 raw22522step1Labels = mixedMoment B raw22522step2 raw22522step2Labels := by
      have ha : raw22522step2 = raw22522step1 := by apply Matrix.ext; unfold raw22522step2 raw22522step1; decide +kernel
      have hl : raw22522step1Labels = labelEmbedding9 ∘ raw22522step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22522step1 raw22522step1Labels raw22522step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4592 node4592Labels := by rfl

def raw22523 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22523Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22523step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22523step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22523step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22523step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw22523step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22523 raw22523Labels = mixedMoment B node4592 node4592Labels := by
  calc
    mixedMoment B raw22523 raw22523Labels = mixedMoment B raw22523step0 raw22523step0Labels := by
      have hz : ∀ j, raw22523 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22523step0 = (fun i j => raw22523 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22523step0 raw22523; decide +kernel
      have hl : raw22523step0Labels = raw22523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22523 raw22523Labels permutation265 hz
    mixedMoment B raw22523step0 raw22523step0Labels = mixedMoment B raw22523step1 raw22523step1Labels := by
      have ha : raw22523step1 = (fun i j => raw22523step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22523step1 raw22523step0; decide +kernel
      have hl : raw22523step1Labels = raw22523step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22523step0 raw22523step0Labels permutation32 permutation6
    mixedMoment B raw22523step1 raw22523step1Labels = mixedMoment B raw22523step2 raw22523step2Labels := by
      have ha : raw22523step2 = raw22523step1 := by apply Matrix.ext; unfold raw22523step2 raw22523step1; decide +kernel
      have hl : raw22523step1Labels = labelEmbedding9 ∘ raw22523step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22523step1 raw22523step1Labels raw22523step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4592 node4592Labels := by rfl

def raw22524 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22524Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22524step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22524step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22524step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22524step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22524step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22524step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22524step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22524 raw22524Labels = mixedMoment B node4611 node4611Labels := by
  calc
    mixedMoment B raw22524 raw22524Labels = mixedMoment B raw22524step0 raw22524step0Labels := by
      have hz : ∀ j, raw22524 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22524step0 = (fun i j => raw22524 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22524step0 raw22524; decide +kernel
      have hl : raw22524step0Labels = raw22524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22524 raw22524Labels permutation346 hz
    mixedMoment B raw22524step0 raw22524step0Labels = mixedMoment B raw22524step1 raw22524step1Labels := by
      have hz : ∀ j, raw22524step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22524step1 = (fun i j => raw22524step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22524step1 raw22524step0; decide +kernel
      have hl : raw22524step1Labels = raw22524step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22524step0 raw22524step0Labels permutation56 hz
    mixedMoment B raw22524step1 raw22524step1Labels = mixedMoment B raw22524step2 raw22524step2Labels := by
      have ha : raw22524step2 = (fun i j => raw22524step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22524step2 raw22524step1; decide +kernel
      have hl : raw22524step2Labels = raw22524step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22524step1 raw22524step1Labels permutation9 permutation7
    mixedMoment B raw22524step2 raw22524step2Labels = mixedMoment B raw22524step3 raw22524step3Labels := by
      have ha : raw22524step3 = raw22524step2 := by apply Matrix.ext; unfold raw22524step3 raw22524step2; decide +kernel
      have hl : raw22524step2Labels = labelEmbedding10 ∘ raw22524step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22524step2 raw22524step2Labels raw22524step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4611 node4611Labels := by rfl

def raw22525 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22525Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22525step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22525step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22525step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22525step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22525step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22525step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22525 raw22525Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw22525 raw22525Labels = mixedMoment B raw22525step0 raw22525step0Labels := by
      have hz : ∀ j, raw22525 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22525step0 = (fun i j => raw22525 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22525step0 raw22525; decide +kernel
      have hl : raw22525step0Labels = raw22525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22525 raw22525Labels permutation346 hz
    mixedMoment B raw22525step0 raw22525step0Labels = mixedMoment B raw22525step1 raw22525step1Labels := by
      have hz : ∀ j, raw22525step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22525step1 = (fun i j => raw22525step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22525step1 raw22525step0; decide +kernel
      have hl : raw22525step1Labels = raw22525step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22525step0 raw22525step0Labels permutation56 hz
    mixedMoment B raw22525step1 raw22525step1Labels = mixedMoment B raw22525step2 raw22525step2Labels := by
      have ha : raw22525step2 = (fun i j => raw22525step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22525step2 raw22525step1; decide +kernel
      have hl : raw22525step2Labels = raw22525step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22525step1 raw22525step1Labels permutation9 permutation7
    mixedMoment B raw22525step2 raw22525step2Labels = mixedMoment B raw22525step3 raw22525step3Labels := by
      have ha : raw22525step3 = raw22525step2 := by apply Matrix.ext; unfold raw22525step3 raw22525step2; decide +kernel
      have hl : raw22525step2Labels = labelEmbedding10 ∘ raw22525step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22525step2 raw22525step2Labels raw22525step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

def raw22526 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22526Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22526step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22526step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22526step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22526step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-1, -1, 2], ![0, -2, 2]]
def raw22526step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22526step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw22526step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22526step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -1, -1], ![2, 0, -2]]
def raw22526step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22526 raw22526Labels = mixedMoment B node4511 node4511Labels := by
  calc
    mixedMoment B raw22526 raw22526Labels = mixedMoment B raw22526step0 raw22526step0Labels := by
      have hz : ∀ j, raw22526 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22526step0 = (fun i j => raw22526 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22526step0 raw22526; decide +kernel
      have hl : raw22526step0Labels = raw22526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22526 raw22526Labels permutation434 hz
    mixedMoment B raw22526step0 raw22526step0Labels = mixedMoment B raw22526step1 raw22526step1Labels := by
      have hz : ∀ j, raw22526step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22526step1 = (fun i j => raw22526step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22526step1 raw22526step0; decide +kernel
      have hl : raw22526step1Labels = raw22526step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22526step0 raw22526step0Labels permutation80 hz
    mixedMoment B raw22526step1 raw22526step1Labels = mixedMoment B raw22526step2 raw22526step2Labels := by
      have hz : ∀ j, raw22526step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22526step2 = (fun i j => raw22526step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22526step2 raw22526step1; decide +kernel
      have hl : raw22526step2Labels = raw22526step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22526step1 raw22526step1Labels permutation14 hz
    mixedMoment B raw22526step2 raw22526step2Labels = mixedMoment B raw22526step3 raw22526step3Labels := by
      have ha : raw22526step3 = (fun i j => raw22526step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22526step3 raw22526step2; decide +kernel
      have hl : raw22526step3Labels = raw22526step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22526step2 raw22526step2Labels permutation2 permutation6
    mixedMoment B raw22526step3 raw22526step3Labels = mixedMoment B raw22526step4 raw22526step4Labels := by
      have ha : raw22526step4 = raw22526step3 := by apply Matrix.ext; unfold raw22526step4 raw22526step3; decide +kernel
      have hl : raw22526step3Labels = labelEmbedding9 ∘ raw22526step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22526step3 raw22526step3Labels raw22526step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4511 node4511Labels := by rfl

def raw22527 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22527Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22527step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22527step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw22527step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22527step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22527step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw22527step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22527step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22527 raw22527Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw22527 raw22527Labels = mixedMoment B raw22527step0 raw22527step0Labels := by
      have hz : ∀ j, raw22527 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22527step0 = (fun i j => raw22527 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22527step0 raw22527; decide +kernel
      have hl : raw22527step0Labels = raw22527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22527 raw22527Labels permutation434 hz
    mixedMoment B raw22527step0 raw22527step0Labels = mixedMoment B raw22527step1 raw22527step1Labels := by
      have hz : ∀ j, raw22527step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22527step1 = (fun i j => raw22527step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22527step1 raw22527step0; decide +kernel
      have hl : raw22527step1Labels = raw22527step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22527step0 raw22527step0Labels permutation80 hz
    mixedMoment B raw22527step1 raw22527step1Labels = mixedMoment B raw22527step2 raw22527step2Labels := by
      have ha : raw22527step2 = (fun i j => raw22527step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw22527step2 raw22527step1; decide +kernel
      have hl : raw22527step2Labels = raw22527step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22527step1 raw22527step1Labels permutation8 permutation6
    mixedMoment B raw22527step2 raw22527step2Labels = mixedMoment B raw22527step3 raw22527step3Labels := by
      have ha : raw22527step3 = raw22527step2 := by apply Matrix.ext; unfold raw22527step3 raw22527step2; decide +kernel
      have hl : raw22527step2Labels = labelEmbedding9 ∘ raw22527step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22527step2 raw22527step2Labels raw22527step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
