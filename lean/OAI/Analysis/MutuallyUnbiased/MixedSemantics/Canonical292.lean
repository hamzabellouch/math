import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw37376 : Matrix (Fin 6) (Fin 2) ℤ := ![![5, -5], ![0, 0], ![0, 0], ![0, 0], ![-2, 2], ![-3, 3]]
def raw37376Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37376step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![5, -5], ![0, 0], ![0, 0], ![-2, 2], ![-3, 3]]
def raw37376step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37376step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![5, -5], ![0, 0], ![-2, 2], ![-3, 3]]
def raw37376step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37376step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![5, -5], ![-2, 2], ![-3, 3]]
def raw37376step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37376step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![3, -3]]
def raw37376step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37376 raw37376Labels = mixedMoment B node4061 node4061Labels := by
  calc
    mixedMoment B raw37376 raw37376Labels = mixedMoment B raw37376step0 raw37376step0Labels := by
      have hz : ∀ j, raw37376 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37376step0 = (fun i j => raw37376 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37376step0 raw37376; decide +kernel
      have hl : raw37376step0Labels = raw37376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37376 raw37376Labels permutation434 hz
    mixedMoment B raw37376step0 raw37376step0Labels = mixedMoment B raw37376step1 raw37376step1Labels := by
      have hz : ∀ j, raw37376step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37376step1 = (fun i j => raw37376step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37376step1 raw37376step0; decide +kernel
      have hl : raw37376step1Labels = raw37376step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37376step0 raw37376step0Labels permutation80 hz
    mixedMoment B raw37376step1 raw37376step1Labels = mixedMoment B raw37376step2 raw37376step2Labels := by
      have hz : ∀ j, raw37376step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37376step2 = (fun i j => raw37376step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37376step2 raw37376step1; decide +kernel
      have hl : raw37376step2Labels = raw37376step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37376step1 raw37376step1Labels permutation14 hz
    mixedMoment B raw37376step2 raw37376step2Labels = mixedMoment B raw37376step3 raw37376step3Labels := by
      have ha : raw37376step3 = -raw37376step2 := by apply Matrix.ext; change ∀ i j, raw37376step3 i j = -(raw37376step2 i j); unfold raw37376step3 raw37376step2; decide +kernel
      have hl : raw37376step3Labels = raw37376step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4061 node4061Labels := by rfl

def raw37377 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37377Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37377step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37377step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37377step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37377step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-2, 0, 2], ![-1, -2, 3]]
def raw37377step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37377step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, -2, 3], ![-2, 0, 2]]
def raw37377step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37377step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 2, -3], ![2, 0, -2]]
def raw37377step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37377 raw37377Labels = mixedMoment B node1539 node1539Labels := by
  calc
    mixedMoment B raw37377 raw37377Labels = mixedMoment B raw37377step0 raw37377step0Labels := by
      have hz : ∀ j, raw37377 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37377step0 = (fun i j => raw37377 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37377step0 raw37377; decide +kernel
      have hl : raw37377step0Labels = raw37377Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37377 raw37377Labels permutation434 hz
    mixedMoment B raw37377step0 raw37377step0Labels = mixedMoment B raw37377step1 raw37377step1Labels := by
      have hz : ∀ j, raw37377step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37377step1 = (fun i j => raw37377step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37377step1 raw37377step0; decide +kernel
      have hl : raw37377step1Labels = raw37377step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37377step0 raw37377step0Labels permutation80 hz
    mixedMoment B raw37377step1 raw37377step1Labels = mixedMoment B raw37377step2 raw37377step2Labels := by
      have hz : ∀ j, raw37377step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37377step2 = (fun i j => raw37377step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37377step2 raw37377step1; decide +kernel
      have hl : raw37377step2Labels = raw37377step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37377step1 raw37377step1Labels permutation14 hz
    mixedMoment B raw37377step2 raw37377step2Labels = mixedMoment B raw37377step3 raw37377step3Labels := by
      have ha : raw37377step3 = (fun i j => raw37377step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37377step3 raw37377step2; decide +kernel
      have hl : raw37377step3Labels = raw37377step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37377step2 raw37377step2Labels permutation3 permutation2
    mixedMoment B raw37377step3 raw37377step3Labels = mixedMoment B raw37377step4 raw37377step4Labels := by
      have ha : raw37377step4 = -raw37377step3 := by apply Matrix.ext; change ∀ i j, raw37377step4 i j = -(raw37377step3 i j); unfold raw37377step4 raw37377step3; decide +kernel
      have hl : raw37377step4Labels = raw37377step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1539 node1539Labels := by rfl

def raw37378 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37378Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37378step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37378step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37378step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37378step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw37378step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37378step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw37378step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37378 raw37378Labels = mixedMoment B node1523 node1523Labels := by
  calc
    mixedMoment B raw37378 raw37378Labels = mixedMoment B raw37378step0 raw37378step0Labels := by
      have hz : ∀ j, raw37378 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37378step0 = (fun i j => raw37378 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37378step0 raw37378; decide +kernel
      have hl : raw37378step0Labels = raw37378Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37378 raw37378Labels permutation434 hz
    mixedMoment B raw37378step0 raw37378step0Labels = mixedMoment B raw37378step1 raw37378step1Labels := by
      have hz : ∀ j, raw37378step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37378step1 = (fun i j => raw37378step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37378step1 raw37378step0; decide +kernel
      have hl : raw37378step1Labels = raw37378step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37378step0 raw37378step0Labels permutation80 hz
    mixedMoment B raw37378step1 raw37378step1Labels = mixedMoment B raw37378step2 raw37378step2Labels := by
      have ha : raw37378step2 = (fun i j => raw37378step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37378step2 raw37378step1; decide +kernel
      have hl : raw37378step2Labels = raw37378step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37378step1 raw37378step1Labels permutation10 permutation4
    mixedMoment B raw37378step2 raw37378step2Labels = mixedMoment B raw37378step3 raw37378step3Labels := by
      have ha : raw37378step3 = -raw37378step2 := by apply Matrix.ext; change ∀ i j, raw37378step3 i j = -(raw37378step2 i j); unfold raw37378step3 raw37378step2; decide +kernel
      have hl : raw37378step3Labels = raw37378step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1523 node1523Labels := by rfl

def raw37379 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37379Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37379step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37379step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37379step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37379step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw37379step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37379step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw37379step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37379 raw37379Labels = mixedMoment B node1523 node1523Labels := by
  calc
    mixedMoment B raw37379 raw37379Labels = mixedMoment B raw37379step0 raw37379step0Labels := by
      have hz : ∀ j, raw37379 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37379step0 = (fun i j => raw37379 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37379step0 raw37379; decide +kernel
      have hl : raw37379step0Labels = raw37379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37379 raw37379Labels permutation434 hz
    mixedMoment B raw37379step0 raw37379step0Labels = mixedMoment B raw37379step1 raw37379step1Labels := by
      have hz : ∀ j, raw37379step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37379step1 = (fun i j => raw37379step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37379step1 raw37379step0; decide +kernel
      have hl : raw37379step1Labels = raw37379step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37379step0 raw37379step0Labels permutation56 hz
    mixedMoment B raw37379step1 raw37379step1Labels = mixedMoment B raw37379step2 raw37379step2Labels := by
      have ha : raw37379step2 = (fun i j => raw37379step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37379step2 raw37379step1; decide +kernel
      have hl : raw37379step2Labels = raw37379step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37379step1 raw37379step1Labels permutation10 permutation4
    mixedMoment B raw37379step2 raw37379step2Labels = mixedMoment B raw37379step3 raw37379step3Labels := by
      have ha : raw37379step3 = -raw37379step2 := by apply Matrix.ext; change ∀ i j, raw37379step3 i j = -(raw37379step2 i j); unfold raw37379step3 raw37379step2; decide +kernel
      have hl : raw37379step3Labels = raw37379step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1523 node1523Labels := by rfl

def raw37380 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37380Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37380step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37380step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-2, 0, 2], ![-1, -2, 3]]
def raw37380step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37380step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw37380step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37380step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw37380step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37380 raw37380Labels = mixedMoment B node1523 node1523Labels := by
  calc
    mixedMoment B raw37380 raw37380Labels = mixedMoment B raw37380step0 raw37380step0Labels := by
      have hz : ∀ j, raw37380 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37380step0 = (fun i j => raw37380 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37380step0 raw37380; decide +kernel
      have hl : raw37380step0Labels = raw37380Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37380 raw37380Labels permutation346 hz
    mixedMoment B raw37380step0 raw37380step0Labels = mixedMoment B raw37380step1 raw37380step1Labels := by
      have hz : ∀ j, raw37380step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37380step1 = (fun i j => raw37380step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37380step1 raw37380step0; decide +kernel
      have hl : raw37380step1Labels = raw37380step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37380step0 raw37380step0Labels permutation56 hz
    mixedMoment B raw37380step1 raw37380step1Labels = mixedMoment B raw37380step2 raw37380step2Labels := by
      have ha : raw37380step2 = (fun i j => raw37380step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37380step2 raw37380step1; decide +kernel
      have hl : raw37380step2Labels = raw37380step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37380step1 raw37380step1Labels permutation10 permutation4
    mixedMoment B raw37380step2 raw37380step2Labels = mixedMoment B raw37380step3 raw37380step3Labels := by
      have ha : raw37380step3 = -raw37380step2 := by apply Matrix.ext; change ∀ i j, raw37380step3 i j = -(raw37380step2 i j); unfold raw37380step3 raw37380step2; decide +kernel
      have hl : raw37380step3Labels = raw37380step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1523 node1523Labels := by rfl

def raw37381 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37381Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37381step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37381step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37381step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37381step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 3, -5], ![-1, -1, 2], ![-1, -2, 3]]
def raw37381step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37381step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, -1, 2], ![-2, -1, 3]]
def raw37381step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37381step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 1, -2], ![2, 1, -3]]
def raw37381step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37381 raw37381Labels = mixedMoment B node1538 node1538Labels := by
  calc
    mixedMoment B raw37381 raw37381Labels = mixedMoment B raw37381step0 raw37381step0Labels := by
      have hz : ∀ j, raw37381 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37381step0 = (fun i j => raw37381 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37381step0 raw37381; decide +kernel
      have hl : raw37381step0Labels = raw37381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37381 raw37381Labels permutation434 hz
    mixedMoment B raw37381step0 raw37381step0Labels = mixedMoment B raw37381step1 raw37381step1Labels := by
      have hz : ∀ j, raw37381step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37381step1 = (fun i j => raw37381step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37381step1 raw37381step0; decide +kernel
      have hl : raw37381step1Labels = raw37381step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37381step0 raw37381step0Labels permutation80 hz
    mixedMoment B raw37381step1 raw37381step1Labels = mixedMoment B raw37381step2 raw37381step2Labels := by
      have hz : ∀ j, raw37381step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37381step2 = (fun i j => raw37381step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37381step2 raw37381step1; decide +kernel
      have hl : raw37381step2Labels = raw37381step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37381step1 raw37381step1Labels permutation14 hz
    mixedMoment B raw37381step2 raw37381step2Labels = mixedMoment B raw37381step3 raw37381step3Labels := by
      have ha : raw37381step3 = (fun i j => raw37381step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37381step3 raw37381step2; decide +kernel
      have hl : raw37381step3Labels = raw37381step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37381step2 raw37381step2Labels permutation2 permutation4
    mixedMoment B raw37381step3 raw37381step3Labels = mixedMoment B raw37381step4 raw37381step4Labels := by
      have ha : raw37381step4 = -raw37381step3 := by apply Matrix.ext; change ∀ i j, raw37381step4 i j = -(raw37381step3 i j); unfold raw37381step4 raw37381step3; decide +kernel
      have hl : raw37381step4Labels = raw37381step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1538 node1538Labels := by rfl

def raw37382 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37382Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37382step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37382step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37382step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37382step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 3, -5], ![-2, 0, 2], ![0, -3, 3]]
def raw37382step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37382step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-3, 0, 3]]
def raw37382step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37382step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![3, 0, -3]]
def raw37382step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37382 raw37382Labels = mixedMoment B node1527 node1527Labels := by
  calc
    mixedMoment B raw37382 raw37382Labels = mixedMoment B raw37382step0 raw37382step0Labels := by
      have hz : ∀ j, raw37382 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37382step0 = (fun i j => raw37382 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37382step0 raw37382; decide +kernel
      have hl : raw37382step0Labels = raw37382Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37382 raw37382Labels permutation434 hz
    mixedMoment B raw37382step0 raw37382step0Labels = mixedMoment B raw37382step1 raw37382step1Labels := by
      have hz : ∀ j, raw37382step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37382step1 = (fun i j => raw37382step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37382step1 raw37382step0; decide +kernel
      have hl : raw37382step1Labels = raw37382step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37382step0 raw37382step0Labels permutation80 hz
    mixedMoment B raw37382step1 raw37382step1Labels = mixedMoment B raw37382step2 raw37382step2Labels := by
      have hz : ∀ j, raw37382step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37382step2 = (fun i j => raw37382step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37382step2 raw37382step1; decide +kernel
      have hl : raw37382step2Labels = raw37382step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37382step1 raw37382step1Labels permutation14 hz
    mixedMoment B raw37382step2 raw37382step2Labels = mixedMoment B raw37382step3 raw37382step3Labels := by
      have ha : raw37382step3 = (fun i j => raw37382step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37382step3 raw37382step2; decide +kernel
      have hl : raw37382step3Labels = raw37382step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37382step2 raw37382step2Labels permutation2 permutation4
    mixedMoment B raw37382step3 raw37382step3Labels = mixedMoment B raw37382step4 raw37382step4Labels := by
      have ha : raw37382step4 = -raw37382step3 := by apply Matrix.ext; change ∀ i j, raw37382step4 i j = -(raw37382step3 i j); unfold raw37382step4 raw37382step3; decide +kernel
      have hl : raw37382step4Labels = raw37382step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1527 node1527Labels := by rfl

def raw37383 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37383Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37383step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37383step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37383step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37383step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, -1, 2], ![-2, -1, 3]]
def raw37383step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37383step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 1, -2], ![2, 1, -3]]
def raw37383step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37383 raw37383Labels = mixedMoment B node1538 node1538Labels := by
  calc
    mixedMoment B raw37383 raw37383Labels = mixedMoment B raw37383step0 raw37383step0Labels := by
      have hz : ∀ j, raw37383 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37383step0 = (fun i j => raw37383 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37383step0 raw37383; decide +kernel
      have hl : raw37383step0Labels = raw37383Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37383 raw37383Labels permutation434 hz
    mixedMoment B raw37383step0 raw37383step0Labels = mixedMoment B raw37383step1 raw37383step1Labels := by
      have hz : ∀ j, raw37383step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37383step1 = (fun i j => raw37383step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37383step1 raw37383step0; decide +kernel
      have hl : raw37383step1Labels = raw37383step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37383step0 raw37383step0Labels permutation80 hz
    mixedMoment B raw37383step1 raw37383step1Labels = mixedMoment B raw37383step2 raw37383step2Labels := by
      have hz : ∀ j, raw37383step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37383step2 = (fun i j => raw37383step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37383step2 raw37383step1; decide +kernel
      have hl : raw37383step2Labels = raw37383step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37383step1 raw37383step1Labels permutation14 hz
    mixedMoment B raw37383step2 raw37383step2Labels = mixedMoment B raw37383step3 raw37383step3Labels := by
      have ha : raw37383step3 = -raw37383step2 := by apply Matrix.ext; change ∀ i j, raw37383step3 i j = -(raw37383step2 i j); unfold raw37383step3 raw37383step2; decide +kernel
      have hl : raw37383step3Labels = raw37383step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1538 node1538Labels := by rfl

def raw37384 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37384Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37384step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37384step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37384step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37384step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37384step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37384step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw37384step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37384 raw37384Labels = mixedMoment B node1533 node1533Labels := by
  calc
    mixedMoment B raw37384 raw37384Labels = mixedMoment B raw37384step0 raw37384step0Labels := by
      have hz : ∀ j, raw37384 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37384step0 = (fun i j => raw37384 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37384step0 raw37384; decide +kernel
      have hl : raw37384step0Labels = raw37384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37384 raw37384Labels permutation434 hz
    mixedMoment B raw37384step0 raw37384step0Labels = mixedMoment B raw37384step1 raw37384step1Labels := by
      have hz : ∀ j, raw37384step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37384step1 = (fun i j => raw37384step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37384step1 raw37384step0; decide +kernel
      have hl : raw37384step1Labels = raw37384step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37384step0 raw37384step0Labels permutation80 hz
    mixedMoment B raw37384step1 raw37384step1Labels = mixedMoment B raw37384step2 raw37384step2Labels := by
      have ha : raw37384step2 = (fun i j => raw37384step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37384step2 raw37384step1; decide +kernel
      have hl : raw37384step2Labels = raw37384step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37384step1 raw37384step1Labels permutation8 permutation4
    mixedMoment B raw37384step2 raw37384step2Labels = mixedMoment B raw37384step3 raw37384step3Labels := by
      have ha : raw37384step3 = -raw37384step2 := by apply Matrix.ext; change ∀ i j, raw37384step3 i j = -(raw37384step2 i j); unfold raw37384step3 raw37384step2; decide +kernel
      have hl : raw37384step3Labels = raw37384step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1533 node1533Labels := by rfl

def raw37385 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37385Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37385step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37385step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37385step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37385step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37385step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37385step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw37385step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37385 raw37385Labels = mixedMoment B node1533 node1533Labels := by
  calc
    mixedMoment B raw37385 raw37385Labels = mixedMoment B raw37385step0 raw37385step0Labels := by
      have hz : ∀ j, raw37385 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37385step0 = (fun i j => raw37385 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37385step0 raw37385; decide +kernel
      have hl : raw37385step0Labels = raw37385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37385 raw37385Labels permutation434 hz
    mixedMoment B raw37385step0 raw37385step0Labels = mixedMoment B raw37385step1 raw37385step1Labels := by
      have hz : ∀ j, raw37385step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37385step1 = (fun i j => raw37385step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37385step1 raw37385step0; decide +kernel
      have hl : raw37385step1Labels = raw37385step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37385step0 raw37385step0Labels permutation56 hz
    mixedMoment B raw37385step1 raw37385step1Labels = mixedMoment B raw37385step2 raw37385step2Labels := by
      have ha : raw37385step2 = (fun i j => raw37385step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37385step2 raw37385step1; decide +kernel
      have hl : raw37385step2Labels = raw37385step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37385step1 raw37385step1Labels permutation8 permutation4
    mixedMoment B raw37385step2 raw37385step2Labels = mixedMoment B raw37385step3 raw37385step3Labels := by
      have ha : raw37385step3 = -raw37385step2 := by apply Matrix.ext; change ∀ i j, raw37385step3 i j = -(raw37385step2 i j); unfold raw37385step3 raw37385step2; decide +kernel
      have hl : raw37385step3Labels = raw37385step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1533 node1533Labels := by rfl

def raw37386 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37386Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37386step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37386step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37386step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37386step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37386step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37386step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw37386step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37386 raw37386Labels = mixedMoment B node1533 node1533Labels := by
  calc
    mixedMoment B raw37386 raw37386Labels = mixedMoment B raw37386step0 raw37386step0Labels := by
      have hz : ∀ j, raw37386 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37386step0 = (fun i j => raw37386 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37386step0 raw37386; decide +kernel
      have hl : raw37386step0Labels = raw37386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37386 raw37386Labels permutation346 hz
    mixedMoment B raw37386step0 raw37386step0Labels = mixedMoment B raw37386step1 raw37386step1Labels := by
      have hz : ∀ j, raw37386step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37386step1 = (fun i j => raw37386step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37386step1 raw37386step0; decide +kernel
      have hl : raw37386step1Labels = raw37386step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37386step0 raw37386step0Labels permutation56 hz
    mixedMoment B raw37386step1 raw37386step1Labels = mixedMoment B raw37386step2 raw37386step2Labels := by
      have ha : raw37386step2 = (fun i j => raw37386step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37386step2 raw37386step1; decide +kernel
      have hl : raw37386step2Labels = raw37386step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37386step1 raw37386step1Labels permutation8 permutation4
    mixedMoment B raw37386step2 raw37386step2Labels = mixedMoment B raw37386step3 raw37386step3Labels := by
      have ha : raw37386step3 = -raw37386step2 := by apply Matrix.ext; change ∀ i j, raw37386step3 i j = -(raw37386step2 i j); unfold raw37386step3 raw37386step2; decide +kernel
      have hl : raw37386step3Labels = raw37386step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1533 node1533Labels := by rfl

def raw37387 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37387Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37387step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37387step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37387step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37387step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw37387step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37387step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw37387step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37387 raw37387Labels = mixedMoment B node685 node685Labels := by
  calc
    mixedMoment B raw37387 raw37387Labels = mixedMoment B raw37387step0 raw37387step0Labels := by
      have hz : ∀ j, raw37387 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37387step0 = (fun i j => raw37387 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37387step0 raw37387; decide +kernel
      have hl : raw37387step0Labels = raw37387Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37387 raw37387Labels permutation434 hz
    mixedMoment B raw37387step0 raw37387step0Labels = mixedMoment B raw37387step1 raw37387step1Labels := by
      have hz : ∀ j, raw37387step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37387step1 = (fun i j => raw37387step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37387step1 raw37387step0; decide +kernel
      have hl : raw37387step1Labels = raw37387step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37387step0 raw37387step0Labels permutation80 hz
    mixedMoment B raw37387step1 raw37387step1Labels = mixedMoment B raw37387step2 raw37387step2Labels := by
      have ha : raw37387step2 = (fun i j => raw37387step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37387step2 raw37387step1; decide +kernel
      have hl : raw37387step2Labels = raw37387step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37387step1 raw37387step1Labels permutation9 permutation4
    mixedMoment B raw37387step2 raw37387step2Labels = mixedMoment B raw37387step3 raw37387step3Labels := by
      have ha : raw37387step3 = -raw37387step2 := by apply Matrix.ext; change ∀ i j, raw37387step3 i j = -(raw37387step2 i j); unfold raw37387step3 raw37387step2; decide +kernel
      have hl : raw37387step3Labels = raw37387step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node685 node685Labels := by rfl

def raw37388 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37388Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37388step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37388step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37388step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37388step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw37388step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37388step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw37388step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37388 raw37388Labels = mixedMoment B node685 node685Labels := by
  calc
    mixedMoment B raw37388 raw37388Labels = mixedMoment B raw37388step0 raw37388step0Labels := by
      have hz : ∀ j, raw37388 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37388step0 = (fun i j => raw37388 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37388step0 raw37388; decide +kernel
      have hl : raw37388step0Labels = raw37388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37388 raw37388Labels permutation434 hz
    mixedMoment B raw37388step0 raw37388step0Labels = mixedMoment B raw37388step1 raw37388step1Labels := by
      have hz : ∀ j, raw37388step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37388step1 = (fun i j => raw37388step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37388step1 raw37388step0; decide +kernel
      have hl : raw37388step1Labels = raw37388step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37388step0 raw37388step0Labels permutation56 hz
    mixedMoment B raw37388step1 raw37388step1Labels = mixedMoment B raw37388step2 raw37388step2Labels := by
      have ha : raw37388step2 = (fun i j => raw37388step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37388step2 raw37388step1; decide +kernel
      have hl : raw37388step2Labels = raw37388step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37388step1 raw37388step1Labels permutation9 permutation4
    mixedMoment B raw37388step2 raw37388step2Labels = mixedMoment B raw37388step3 raw37388step3Labels := by
      have ha : raw37388step3 = -raw37388step2 := by apply Matrix.ext; change ∀ i j, raw37388step3 i j = -(raw37388step2 i j); unfold raw37388step3 raw37388step2; decide +kernel
      have hl : raw37388step3Labels = raw37388step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node685 node685Labels := by rfl

def raw37389 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37389Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37389step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37389step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, -2, 2], ![-2, -1, 3]]
def raw37389step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37389step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw37389step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37389step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw37389step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37389 raw37389Labels = mixedMoment B node685 node685Labels := by
  calc
    mixedMoment B raw37389 raw37389Labels = mixedMoment B raw37389step0 raw37389step0Labels := by
      have hz : ∀ j, raw37389 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37389step0 = (fun i j => raw37389 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37389step0 raw37389; decide +kernel
      have hl : raw37389step0Labels = raw37389Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37389 raw37389Labels permutation346 hz
    mixedMoment B raw37389step0 raw37389step0Labels = mixedMoment B raw37389step1 raw37389step1Labels := by
      have hz : ∀ j, raw37389step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37389step1 = (fun i j => raw37389step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37389step1 raw37389step0; decide +kernel
      have hl : raw37389step1Labels = raw37389step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37389step0 raw37389step0Labels permutation56 hz
    mixedMoment B raw37389step1 raw37389step1Labels = mixedMoment B raw37389step2 raw37389step2Labels := by
      have ha : raw37389step2 = (fun i j => raw37389step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37389step2 raw37389step1; decide +kernel
      have hl : raw37389step2Labels = raw37389step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37389step1 raw37389step1Labels permutation9 permutation4
    mixedMoment B raw37389step2 raw37389step2Labels = mixedMoment B raw37389step3 raw37389step3Labels := by
      have ha : raw37389step3 = -raw37389step2 := by apply Matrix.ext; change ∀ i j, raw37389step3 i j = -(raw37389step2 i j); unfold raw37389step3 raw37389step2; decide +kernel
      have hl : raw37389step3Labels = raw37389step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node685 node685Labels := by rfl

def raw37390 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, -1, 3]]
def raw37390Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, -1, 3]]
def raw37390step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37390step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -3, 2], ![-2, -1, 3]]
def raw37390step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37390step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 4, -5], ![1, -3, 2], ![-2, -1, 3]]
def raw37390step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37390step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 1, -5], ![-1, -2, 3], ![-3, 1, 2]]
def raw37390step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37390step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 2, -3], ![3, -1, -2]]
def raw37390step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37390 raw37390Labels = mixedMoment B node694 node694Labels := by
  calc
    mixedMoment B raw37390 raw37390Labels = mixedMoment B raw37390step0 raw37390step0Labels := by
      have hz : ∀ j, raw37390 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37390step0 = (fun i j => raw37390 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37390step0 raw37390; decide +kernel
      have hl : raw37390step0Labels = raw37390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37390 raw37390Labels permutation434 hz
    mixedMoment B raw37390step0 raw37390step0Labels = mixedMoment B raw37390step1 raw37390step1Labels := by
      have hz : ∀ j, raw37390step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37390step1 = (fun i j => raw37390step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37390step1 raw37390step0; decide +kernel
      have hl : raw37390step1Labels = raw37390step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37390step0 raw37390step0Labels permutation80 hz
    mixedMoment B raw37390step1 raw37390step1Labels = mixedMoment B raw37390step2 raw37390step2Labels := by
      have hz : ∀ j, raw37390step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37390step2 = (fun i j => raw37390step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37390step2 raw37390step1; decide +kernel
      have hl : raw37390step2Labels = raw37390step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37390step1 raw37390step1Labels permutation14 hz
    mixedMoment B raw37390step2 raw37390step2Labels = mixedMoment B raw37390step3 raw37390step3Labels := by
      have ha : raw37390step3 = (fun i j => raw37390step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37390step3 raw37390step2; decide +kernel
      have hl : raw37390step3Labels = raw37390step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37390step2 raw37390step2Labels permutation3 permutation4
    mixedMoment B raw37390step3 raw37390step3Labels = mixedMoment B raw37390step4 raw37390step4Labels := by
      have ha : raw37390step4 = -raw37390step3 := by apply Matrix.ext; change ∀ i j, raw37390step4 i j = -(raw37390step3 i j); unfold raw37390step4 raw37390step3; decide +kernel
      have hl : raw37390step4Labels = raw37390step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node694 node694Labels := by rfl

def raw37391 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37391Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37391step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37391step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37391step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37391step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 4, -5], ![0, -2, 2], ![-1, -2, 3]]
def raw37391step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37391step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 1, -5], ![-2, 0, 2], ![-2, -1, 3]]
def raw37391step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37391step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![2, 0, -2], ![2, 1, -3]]
def raw37391step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37391 raw37391Labels = mixedMoment B node696 node696Labels := by
  calc
    mixedMoment B raw37391 raw37391Labels = mixedMoment B raw37391step0 raw37391step0Labels := by
      have hz : ∀ j, raw37391 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37391step0 = (fun i j => raw37391 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37391step0 raw37391; decide +kernel
      have hl : raw37391step0Labels = raw37391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37391 raw37391Labels permutation434 hz
    mixedMoment B raw37391step0 raw37391step0Labels = mixedMoment B raw37391step1 raw37391step1Labels := by
      have hz : ∀ j, raw37391step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37391step1 = (fun i j => raw37391step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37391step1 raw37391step0; decide +kernel
      have hl : raw37391step1Labels = raw37391step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37391step0 raw37391step0Labels permutation80 hz
    mixedMoment B raw37391step1 raw37391step1Labels = mixedMoment B raw37391step2 raw37391step2Labels := by
      have hz : ∀ j, raw37391step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37391step2 = (fun i j => raw37391step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37391step2 raw37391step1; decide +kernel
      have hl : raw37391step2Labels = raw37391step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37391step1 raw37391step1Labels permutation14 hz
    mixedMoment B raw37391step2 raw37391step2Labels = mixedMoment B raw37391step3 raw37391step3Labels := by
      have ha : raw37391step3 = (fun i j => raw37391step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37391step3 raw37391step2; decide +kernel
      have hl : raw37391step3Labels = raw37391step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37391step2 raw37391step2Labels permutation2 permutation4
    mixedMoment B raw37391step3 raw37391step3Labels = mixedMoment B raw37391step4 raw37391step4Labels := by
      have ha : raw37391step4 = -raw37391step3 := by apply Matrix.ext; change ∀ i j, raw37391step4 i j = -(raw37391step3 i j); unfold raw37391step4 raw37391step3; decide +kernel
      have hl : raw37391step4Labels = raw37391step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node696 node696Labels := by rfl

def raw37392 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37392Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37392step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37392step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37392step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37392step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-2, 0, 2], ![-2, -1, 3]]
def raw37392step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37392step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![2, 0, -2], ![2, 1, -3]]
def raw37392step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37392 raw37392Labels = mixedMoment B node1496 node1496Labels := by
  calc
    mixedMoment B raw37392 raw37392Labels = mixedMoment B raw37392step0 raw37392step0Labels := by
      have hz : ∀ j, raw37392 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37392step0 = (fun i j => raw37392 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37392step0 raw37392; decide +kernel
      have hl : raw37392step0Labels = raw37392Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37392 raw37392Labels permutation434 hz
    mixedMoment B raw37392step0 raw37392step0Labels = mixedMoment B raw37392step1 raw37392step1Labels := by
      have hz : ∀ j, raw37392step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37392step1 = (fun i j => raw37392step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37392step1 raw37392step0; decide +kernel
      have hl : raw37392step1Labels = raw37392step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37392step0 raw37392step0Labels permutation80 hz
    mixedMoment B raw37392step1 raw37392step1Labels = mixedMoment B raw37392step2 raw37392step2Labels := by
      have ha : raw37392step2 = (fun i j => raw37392step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37392step2 raw37392step1; decide +kernel
      have hl : raw37392step2Labels = raw37392step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37392step1 raw37392step1Labels permutation8 permutation4
    mixedMoment B raw37392step2 raw37392step2Labels = mixedMoment B raw37392step3 raw37392step3Labels := by
      have ha : raw37392step3 = -raw37392step2 := by apply Matrix.ext; change ∀ i j, raw37392step3 i j = -(raw37392step2 i j); unfold raw37392step3 raw37392step2; decide +kernel
      have hl : raw37392step3Labels = raw37392step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1496 node1496Labels := by rfl

def raw37393 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37393Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37393step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37393step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37393step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37393step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-2, 0, 2], ![-2, -1, 3]]
def raw37393step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37393step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![2, 0, -2], ![2, 1, -3]]
def raw37393step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37393 raw37393Labels = mixedMoment B node1496 node1496Labels := by
  calc
    mixedMoment B raw37393 raw37393Labels = mixedMoment B raw37393step0 raw37393step0Labels := by
      have hz : ∀ j, raw37393 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37393step0 = (fun i j => raw37393 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37393step0 raw37393; decide +kernel
      have hl : raw37393step0Labels = raw37393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37393 raw37393Labels permutation434 hz
    mixedMoment B raw37393step0 raw37393step0Labels = mixedMoment B raw37393step1 raw37393step1Labels := by
      have hz : ∀ j, raw37393step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37393step1 = (fun i j => raw37393step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37393step1 raw37393step0; decide +kernel
      have hl : raw37393step1Labels = raw37393step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37393step0 raw37393step0Labels permutation56 hz
    mixedMoment B raw37393step1 raw37393step1Labels = mixedMoment B raw37393step2 raw37393step2Labels := by
      have ha : raw37393step2 = (fun i j => raw37393step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37393step2 raw37393step1; decide +kernel
      have hl : raw37393step2Labels = raw37393step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37393step1 raw37393step1Labels permutation8 permutation4
    mixedMoment B raw37393step2 raw37393step2Labels = mixedMoment B raw37393step3 raw37393step3Labels := by
      have ha : raw37393step3 = -raw37393step2 := by apply Matrix.ext; change ∀ i j, raw37393step3 i j = -(raw37393step2 i j); unfold raw37393step3 raw37393step2; decide +kernel
      have hl : raw37393step3Labels = raw37393step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1496 node1496Labels := by rfl

def raw37394 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37394Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37394step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37394step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, -2, 2], ![-1, -2, 3]]
def raw37394step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37394step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-2, 0, 2], ![-2, -1, 3]]
def raw37394step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37394step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![2, 0, -2], ![2, 1, -3]]
def raw37394step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37394 raw37394Labels = mixedMoment B node1496 node1496Labels := by
  calc
    mixedMoment B raw37394 raw37394Labels = mixedMoment B raw37394step0 raw37394step0Labels := by
      have hz : ∀ j, raw37394 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37394step0 = (fun i j => raw37394 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37394step0 raw37394; decide +kernel
      have hl : raw37394step0Labels = raw37394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37394 raw37394Labels permutation346 hz
    mixedMoment B raw37394step0 raw37394step0Labels = mixedMoment B raw37394step1 raw37394step1Labels := by
      have hz : ∀ j, raw37394step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37394step1 = (fun i j => raw37394step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37394step1 raw37394step0; decide +kernel
      have hl : raw37394step1Labels = raw37394step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37394step0 raw37394step0Labels permutation56 hz
    mixedMoment B raw37394step1 raw37394step1Labels = mixedMoment B raw37394step2 raw37394step2Labels := by
      have ha : raw37394step2 = (fun i j => raw37394step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37394step2 raw37394step1; decide +kernel
      have hl : raw37394step2Labels = raw37394step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37394step1 raw37394step1Labels permutation8 permutation4
    mixedMoment B raw37394step2 raw37394step2Labels = mixedMoment B raw37394step3 raw37394step3Labels := by
      have ha : raw37394step3 = -raw37394step2 := by apply Matrix.ext; change ∀ i j, raw37394step3 i j = -(raw37394step2 i j); unfold raw37394step3 raw37394step2; decide +kernel
      have hl : raw37394step3Labels = raw37394step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1496 node1496Labels := by rfl

def raw37395 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37395Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37395step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37395step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37395step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37395step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37395step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37395step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw37395step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37395 raw37395Labels = mixedMoment B node684 node684Labels := by
  calc
    mixedMoment B raw37395 raw37395Labels = mixedMoment B raw37395step0 raw37395step0Labels := by
      have hz : ∀ j, raw37395 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37395step0 = (fun i j => raw37395 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37395step0 raw37395; decide +kernel
      have hl : raw37395step0Labels = raw37395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37395 raw37395Labels permutation434 hz
    mixedMoment B raw37395step0 raw37395step0Labels = mixedMoment B raw37395step1 raw37395step1Labels := by
      have hz : ∀ j, raw37395step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37395step1 = (fun i j => raw37395step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37395step1 raw37395step0; decide +kernel
      have hl : raw37395step1Labels = raw37395step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37395step0 raw37395step0Labels permutation80 hz
    mixedMoment B raw37395step1 raw37395step1Labels = mixedMoment B raw37395step2 raw37395step2Labels := by
      have ha : raw37395step2 = (fun i j => raw37395step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37395step2 raw37395step1; decide +kernel
      have hl : raw37395step2Labels = raw37395step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37395step1 raw37395step1Labels permutation8 permutation4
    mixedMoment B raw37395step2 raw37395step2Labels = mixedMoment B raw37395step3 raw37395step3Labels := by
      have ha : raw37395step3 = -raw37395step2 := by apply Matrix.ext; change ∀ i j, raw37395step3 i j = -(raw37395step2 i j); unfold raw37395step3 raw37395step2; decide +kernel
      have hl : raw37395step3Labels = raw37395step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node684 node684Labels := by rfl

def raw37396 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37396Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37396step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37396step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37396step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37396step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37396step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37396step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw37396step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37396 raw37396Labels = mixedMoment B node684 node684Labels := by
  calc
    mixedMoment B raw37396 raw37396Labels = mixedMoment B raw37396step0 raw37396step0Labels := by
      have hz : ∀ j, raw37396 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37396step0 = (fun i j => raw37396 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37396step0 raw37396; decide +kernel
      have hl : raw37396step0Labels = raw37396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37396 raw37396Labels permutation434 hz
    mixedMoment B raw37396step0 raw37396step0Labels = mixedMoment B raw37396step1 raw37396step1Labels := by
      have hz : ∀ j, raw37396step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37396step1 = (fun i j => raw37396step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37396step1 raw37396step0; decide +kernel
      have hl : raw37396step1Labels = raw37396step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37396step0 raw37396step0Labels permutation56 hz
    mixedMoment B raw37396step1 raw37396step1Labels = mixedMoment B raw37396step2 raw37396step2Labels := by
      have ha : raw37396step2 = (fun i j => raw37396step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37396step2 raw37396step1; decide +kernel
      have hl : raw37396step2Labels = raw37396step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37396step1 raw37396step1Labels permutation8 permutation4
    mixedMoment B raw37396step2 raw37396step2Labels = mixedMoment B raw37396step3 raw37396step3Labels := by
      have ha : raw37396step3 = -raw37396step2 := by apply Matrix.ext; change ∀ i j, raw37396step3 i j = -(raw37396step2 i j); unfold raw37396step3 raw37396step2; decide +kernel
      have hl : raw37396step3Labels = raw37396step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node684 node684Labels := by rfl

def raw37397 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37397Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37397step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37397step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw37397step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37397step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw37397step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37397step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw37397step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37397 raw37397Labels = mixedMoment B node684 node684Labels := by
  calc
    mixedMoment B raw37397 raw37397Labels = mixedMoment B raw37397step0 raw37397step0Labels := by
      have hz : ∀ j, raw37397 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37397step0 = (fun i j => raw37397 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37397step0 raw37397; decide +kernel
      have hl : raw37397step0Labels = raw37397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37397 raw37397Labels permutation346 hz
    mixedMoment B raw37397step0 raw37397step0Labels = mixedMoment B raw37397step1 raw37397step1Labels := by
      have hz : ∀ j, raw37397step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37397step1 = (fun i j => raw37397step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37397step1 raw37397step0; decide +kernel
      have hl : raw37397step1Labels = raw37397step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37397step0 raw37397step0Labels permutation56 hz
    mixedMoment B raw37397step1 raw37397step1Labels = mixedMoment B raw37397step2 raw37397step2Labels := by
      have ha : raw37397step2 = (fun i j => raw37397step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37397step2 raw37397step1; decide +kernel
      have hl : raw37397step2Labels = raw37397step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37397step1 raw37397step1Labels permutation8 permutation4
    mixedMoment B raw37397step2 raw37397step2Labels = mixedMoment B raw37397step3 raw37397step3Labels := by
      have ha : raw37397step3 = -raw37397step2 := by apply Matrix.ext; change ∀ i j, raw37397step3 i j = -(raw37397step2 i j); unfold raw37397step3 raw37397step2; decide +kernel
      have hl : raw37397step3Labels = raw37397step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node684 node684Labels := by rfl

def raw37398 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37398Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37398step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37398step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37398step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37398step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 4, -5], ![-1, -1, 2], ![0, -3, 3]]
def raw37398step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37398step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 1, -5], ![-1, -1, 2], ![-3, 0, 3]]
def raw37398step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37398step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 1, -2], ![3, 0, -3]]
def raw37398step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37398 raw37398Labels = mixedMoment B node693 node693Labels := by
  calc
    mixedMoment B raw37398 raw37398Labels = mixedMoment B raw37398step0 raw37398step0Labels := by
      have hz : ∀ j, raw37398 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37398step0 = (fun i j => raw37398 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37398step0 raw37398; decide +kernel
      have hl : raw37398step0Labels = raw37398Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37398 raw37398Labels permutation434 hz
    mixedMoment B raw37398step0 raw37398step0Labels = mixedMoment B raw37398step1 raw37398step1Labels := by
      have hz : ∀ j, raw37398step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37398step1 = (fun i j => raw37398step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37398step1 raw37398step0; decide +kernel
      have hl : raw37398step1Labels = raw37398step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37398step0 raw37398step0Labels permutation80 hz
    mixedMoment B raw37398step1 raw37398step1Labels = mixedMoment B raw37398step2 raw37398step2Labels := by
      have hz : ∀ j, raw37398step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37398step2 = (fun i j => raw37398step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37398step2 raw37398step1; decide +kernel
      have hl : raw37398step2Labels = raw37398step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37398step1 raw37398step1Labels permutation14 hz
    mixedMoment B raw37398step2 raw37398step2Labels = mixedMoment B raw37398step3 raw37398step3Labels := by
      have ha : raw37398step3 = (fun i j => raw37398step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37398step3 raw37398step2; decide +kernel
      have hl : raw37398step3Labels = raw37398step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37398step2 raw37398step2Labels permutation2 permutation4
    mixedMoment B raw37398step3 raw37398step3Labels = mixedMoment B raw37398step4 raw37398step4Labels := by
      have ha : raw37398step4 = -raw37398step3 := by apply Matrix.ext; change ∀ i j, raw37398step4 i j = -(raw37398step3 i j); unfold raw37398step4 raw37398step3; decide +kernel
      have hl : raw37398step4Labels = raw37398step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node693 node693Labels := by rfl

def raw37399 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37399Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37399step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37399step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37399step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37399step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, -1, 2], ![-3, 0, 3]]
def raw37399step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37399step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 1, -2], ![3, 0, -3]]
def raw37399step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37399 raw37399Labels = mixedMoment B node1495 node1495Labels := by
  calc
    mixedMoment B raw37399 raw37399Labels = mixedMoment B raw37399step0 raw37399step0Labels := by
      have hz : ∀ j, raw37399 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37399step0 = (fun i j => raw37399 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37399step0 raw37399; decide +kernel
      have hl : raw37399step0Labels = raw37399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37399 raw37399Labels permutation434 hz
    mixedMoment B raw37399step0 raw37399step0Labels = mixedMoment B raw37399step1 raw37399step1Labels := by
      have hz : ∀ j, raw37399step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37399step1 = (fun i j => raw37399step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37399step1 raw37399step0; decide +kernel
      have hl : raw37399step1Labels = raw37399step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37399step0 raw37399step0Labels permutation80 hz
    mixedMoment B raw37399step1 raw37399step1Labels = mixedMoment B raw37399step2 raw37399step2Labels := by
      have ha : raw37399step2 = (fun i j => raw37399step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37399step2 raw37399step1; decide +kernel
      have hl : raw37399step2Labels = raw37399step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37399step1 raw37399step1Labels permutation8 permutation4
    mixedMoment B raw37399step2 raw37399step2Labels = mixedMoment B raw37399step3 raw37399step3Labels := by
      have ha : raw37399step3 = -raw37399step2 := by apply Matrix.ext; change ∀ i j, raw37399step3 i j = -(raw37399step2 i j); unfold raw37399step3 raw37399step2; decide +kernel
      have hl : raw37399step3Labels = raw37399step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1495 node1495Labels := by rfl

def raw37400 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37400Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37400step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37400step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37400step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37400step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, -1, 2], ![-3, 0, 3]]
def raw37400step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37400step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 1, -2], ![3, 0, -3]]
def raw37400step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37400 raw37400Labels = mixedMoment B node1495 node1495Labels := by
  calc
    mixedMoment B raw37400 raw37400Labels = mixedMoment B raw37400step0 raw37400step0Labels := by
      have hz : ∀ j, raw37400 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37400step0 = (fun i j => raw37400 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37400step0 raw37400; decide +kernel
      have hl : raw37400step0Labels = raw37400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37400 raw37400Labels permutation434 hz
    mixedMoment B raw37400step0 raw37400step0Labels = mixedMoment B raw37400step1 raw37400step1Labels := by
      have hz : ∀ j, raw37400step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37400step1 = (fun i j => raw37400step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37400step1 raw37400step0; decide +kernel
      have hl : raw37400step1Labels = raw37400step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37400step0 raw37400step0Labels permutation56 hz
    mixedMoment B raw37400step1 raw37400step1Labels = mixedMoment B raw37400step2 raw37400step2Labels := by
      have ha : raw37400step2 = (fun i j => raw37400step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37400step2 raw37400step1; decide +kernel
      have hl : raw37400step2Labels = raw37400step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37400step1 raw37400step1Labels permutation8 permutation4
    mixedMoment B raw37400step2 raw37400step2Labels = mixedMoment B raw37400step3 raw37400step3Labels := by
      have ha : raw37400step3 = -raw37400step2 := by apply Matrix.ext; change ∀ i j, raw37400step3 i j = -(raw37400step2 i j); unfold raw37400step3 raw37400step2; decide +kernel
      have hl : raw37400step3Labels = raw37400step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1495 node1495Labels := by rfl

def raw37401 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37401Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37401step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37401step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![-1, -1, 2], ![0, -3, 3]]
def raw37401step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37401step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, -1, 2], ![-3, 0, 3]]
def raw37401step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37401step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 1, -2], ![3, 0, -3]]
def raw37401step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37401 raw37401Labels = mixedMoment B node1495 node1495Labels := by
  calc
    mixedMoment B raw37401 raw37401Labels = mixedMoment B raw37401step0 raw37401step0Labels := by
      have hz : ∀ j, raw37401 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37401step0 = (fun i j => raw37401 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37401step0 raw37401; decide +kernel
      have hl : raw37401step0Labels = raw37401Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37401 raw37401Labels permutation346 hz
    mixedMoment B raw37401step0 raw37401step0Labels = mixedMoment B raw37401step1 raw37401step1Labels := by
      have hz : ∀ j, raw37401step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37401step1 = (fun i j => raw37401step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37401step1 raw37401step0; decide +kernel
      have hl : raw37401step1Labels = raw37401step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37401step0 raw37401step0Labels permutation56 hz
    mixedMoment B raw37401step1 raw37401step1Labels = mixedMoment B raw37401step2 raw37401step2Labels := by
      have ha : raw37401step2 = (fun i j => raw37401step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37401step2 raw37401step1; decide +kernel
      have hl : raw37401step2Labels = raw37401step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37401step1 raw37401step1Labels permutation8 permutation4
    mixedMoment B raw37401step2 raw37401step2Labels = mixedMoment B raw37401step3 raw37401step3Labels := by
      have ha : raw37401step3 = -raw37401step2 := by apply Matrix.ext; change ∀ i j, raw37401step3 i j = -(raw37401step2 i j); unfold raw37401step3 raw37401step2; decide +kernel
      have hl : raw37401step3Labels = raw37401step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1495 node1495Labels := by rfl

def raw37402 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37402Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37402step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37402step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37402step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37402step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![0, -2, 2], ![-1, 1, 0], ![-3, 0, 3]]
def raw37402step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37402step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw37402step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37402 raw37402Labels = mixedMoment B node676 node676Labels := by
  calc
    mixedMoment B raw37402 raw37402Labels = mixedMoment B raw37402step0 raw37402step0Labels := by
      have hz : ∀ j, raw37402 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37402step0 = (fun i j => raw37402 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37402step0 raw37402; decide +kernel
      have hl : raw37402step0Labels = raw37402Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37402 raw37402Labels permutation434 hz
    mixedMoment B raw37402step0 raw37402step0Labels = mixedMoment B raw37402step1 raw37402step1Labels := by
      have hz : ∀ j, raw37402step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37402step1 = (fun i j => raw37402step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37402step1 raw37402step0; decide +kernel
      have hl : raw37402step1Labels = raw37402step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37402step0 raw37402step0Labels permutation80 hz
    mixedMoment B raw37402step1 raw37402step1Labels = mixedMoment B raw37402step2 raw37402step2Labels := by
      have ha : raw37402step2 = (fun i j => raw37402step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37402step2 raw37402step1; decide +kernel
      have hl : raw37402step2Labels = raw37402step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37402step1 raw37402step1Labels permutation10 permutation4
    mixedMoment B raw37402step2 raw37402step2Labels = mixedMoment B raw37402step3 raw37402step3Labels := by
      have ha : raw37402step3 = -raw37402step2 := by apply Matrix.ext; change ∀ i j, raw37402step3 i j = -(raw37402step2 i j); unfold raw37402step3 raw37402step2; decide +kernel
      have hl : raw37402step3Labels = raw37402step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node676 node676Labels := by rfl

def raw37403 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37403Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37403step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37403step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37403step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37403step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![0, -2, 2], ![-1, 1, 0], ![-3, 0, 3]]
def raw37403step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37403step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw37403step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37403 raw37403Labels = mixedMoment B node676 node676Labels := by
  calc
    mixedMoment B raw37403 raw37403Labels = mixedMoment B raw37403step0 raw37403step0Labels := by
      have hz : ∀ j, raw37403 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37403step0 = (fun i j => raw37403 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37403step0 raw37403; decide +kernel
      have hl : raw37403step0Labels = raw37403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37403 raw37403Labels permutation434 hz
    mixedMoment B raw37403step0 raw37403step0Labels = mixedMoment B raw37403step1 raw37403step1Labels := by
      have hz : ∀ j, raw37403step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37403step1 = (fun i j => raw37403step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37403step1 raw37403step0; decide +kernel
      have hl : raw37403step1Labels = raw37403step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37403step0 raw37403step0Labels permutation56 hz
    mixedMoment B raw37403step1 raw37403step1Labels = mixedMoment B raw37403step2 raw37403step2Labels := by
      have ha : raw37403step2 = (fun i j => raw37403step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37403step2 raw37403step1; decide +kernel
      have hl : raw37403step2Labels = raw37403step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37403step1 raw37403step1Labels permutation10 permutation4
    mixedMoment B raw37403step2 raw37403step2Labels = mixedMoment B raw37403step3 raw37403step3Labels := by
      have ha : raw37403step3 = -raw37403step2 := by apply Matrix.ext; change ∀ i j, raw37403step3 i j = -(raw37403step2 i j); unfold raw37403step3 raw37403step2; decide +kernel
      have hl : raw37403step3Labels = raw37403step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node676 node676Labels := by rfl

def raw37404 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37404Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37404step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37404step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![-2, 0, 2], ![0, -3, 3]]
def raw37404step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37404step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![0, -2, 2], ![-1, 1, 0], ![-3, 0, 3]]
def raw37404step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37404step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw37404step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37404 raw37404Labels = mixedMoment B node676 node676Labels := by
  calc
    mixedMoment B raw37404 raw37404Labels = mixedMoment B raw37404step0 raw37404step0Labels := by
      have hz : ∀ j, raw37404 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37404step0 = (fun i j => raw37404 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37404step0 raw37404; decide +kernel
      have hl : raw37404step0Labels = raw37404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37404 raw37404Labels permutation346 hz
    mixedMoment B raw37404step0 raw37404step0Labels = mixedMoment B raw37404step1 raw37404step1Labels := by
      have hz : ∀ j, raw37404step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37404step1 = (fun i j => raw37404step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37404step1 raw37404step0; decide +kernel
      have hl : raw37404step1Labels = raw37404step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37404step0 raw37404step0Labels permutation56 hz
    mixedMoment B raw37404step1 raw37404step1Labels = mixedMoment B raw37404step2 raw37404step2Labels := by
      have ha : raw37404step2 = (fun i j => raw37404step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37404step2 raw37404step1; decide +kernel
      have hl : raw37404step2Labels = raw37404step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37404step1 raw37404step1Labels permutation10 permutation4
    mixedMoment B raw37404step2 raw37404step2Labels = mixedMoment B raw37404step3 raw37404step3Labels := by
      have ha : raw37404step3 = -raw37404step2 := by apply Matrix.ext; change ∀ i j, raw37404step3 i j = -(raw37404step2 i j); unfold raw37404step3 raw37404step2; decide +kernel
      have hl : raw37404step3Labels = raw37404step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node676 node676Labels := by rfl

def raw37405 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -4, 3]]
def raw37405Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -4, 3]]
def raw37405step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37405step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![-2, 0, 2], ![1, -4, 3]]
def raw37405step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37405step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 4, -5], ![-2, 0, 2], ![1, -4, 3]]
def raw37405step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37405step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 1, -5], ![0, -2, 2], ![-4, 1, 3]]
def raw37405step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37405step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![4, -1, -3]]
def raw37405step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37405 raw37405Labels = mixedMoment B node680 node680Labels := by
  calc
    mixedMoment B raw37405 raw37405Labels = mixedMoment B raw37405step0 raw37405step0Labels := by
      have hz : ∀ j, raw37405 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37405step0 = (fun i j => raw37405 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37405step0 raw37405; decide +kernel
      have hl : raw37405step0Labels = raw37405Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37405 raw37405Labels permutation434 hz
    mixedMoment B raw37405step0 raw37405step0Labels = mixedMoment B raw37405step1 raw37405step1Labels := by
      have hz : ∀ j, raw37405step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37405step1 = (fun i j => raw37405step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37405step1 raw37405step0; decide +kernel
      have hl : raw37405step1Labels = raw37405step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37405step0 raw37405step0Labels permutation80 hz
    mixedMoment B raw37405step1 raw37405step1Labels = mixedMoment B raw37405step2 raw37405step2Labels := by
      have hz : ∀ j, raw37405step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw37405step2 = (fun i j => raw37405step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw37405step2 raw37405step1; decide +kernel
      have hl : raw37405step2Labels = raw37405step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37405step1 raw37405step1Labels permutation14 hz
    mixedMoment B raw37405step2 raw37405step2Labels = mixedMoment B raw37405step3 raw37405step3Labels := by
      have ha : raw37405step3 = (fun i j => raw37405step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37405step3 raw37405step2; decide +kernel
      have hl : raw37405step3Labels = raw37405step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37405step2 raw37405step2Labels permutation2 permutation4
    mixedMoment B raw37405step3 raw37405step3Labels = mixedMoment B raw37405step4 raw37405step4Labels := by
      have ha : raw37405step4 = -raw37405step3 := by apply Matrix.ext; change ∀ i j, raw37405step4 i j = -(raw37405step3 i j); unfold raw37405step4 raw37405step3; decide +kernel
      have hl : raw37405step4Labels = raw37405step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node680 node680Labels := by rfl

def raw37406 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37406Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37406step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37406step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37406step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37406step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37406step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37406step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw37406step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37406 raw37406Labels = mixedMoment B node1518 node1518Labels := by
  calc
    mixedMoment B raw37406 raw37406Labels = mixedMoment B raw37406step0 raw37406step0Labels := by
      have hz : ∀ j, raw37406 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37406step0 = (fun i j => raw37406 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37406step0 raw37406; decide +kernel
      have hl : raw37406step0Labels = raw37406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37406 raw37406Labels permutation346 hz
    mixedMoment B raw37406step0 raw37406step0Labels = mixedMoment B raw37406step1 raw37406step1Labels := by
      have hz : ∀ j, raw37406step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37406step1 = (fun i j => raw37406step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37406step1 raw37406step0; decide +kernel
      have hl : raw37406step1Labels = raw37406step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37406step0 raw37406step0Labels permutation56 hz
    mixedMoment B raw37406step1 raw37406step1Labels = mixedMoment B raw37406step2 raw37406step2Labels := by
      have ha : raw37406step2 = (fun i j => raw37406step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37406step2 raw37406step1; decide +kernel
      have hl : raw37406step2Labels = raw37406step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37406step1 raw37406step1Labels permutation10 permutation2
    mixedMoment B raw37406step2 raw37406step2Labels = mixedMoment B raw37406step3 raw37406step3Labels := by
      have ha : raw37406step3 = -raw37406step2 := by apply Matrix.ext; change ∀ i j, raw37406step3 i j = -(raw37406step2 i j); unfold raw37406step3 raw37406step2; decide +kernel
      have hl : raw37406step3Labels = raw37406step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1518 node1518Labels := by rfl

def raw37407 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37407Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37407step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37407step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw37407step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37407step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw37407step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37407 raw37407Labels = mixedMoment B node1514 node1514Labels := by
  calc
    mixedMoment B raw37407 raw37407Labels = mixedMoment B raw37407step0 raw37407step0Labels := by
      have hz : ∀ j, raw37407 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37407step0 = (fun i j => raw37407 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37407step0 raw37407; decide +kernel
      have hl : raw37407step0Labels = raw37407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37407 raw37407Labels permutation346 hz
    mixedMoment B raw37407step0 raw37407step0Labels = mixedMoment B raw37407step1 raw37407step1Labels := by
      have ha : raw37407step1 = (fun i j => raw37407step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37407step1 raw37407step0; decide +kernel
      have hl : raw37407step1Labels = raw37407step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37407step0 raw37407step0Labels permutation38 permutation4
    mixedMoment B raw37407step1 raw37407step1Labels = mixedMoment B raw37407step2 raw37407step2Labels := by
      have ha : raw37407step2 = -raw37407step1 := by apply Matrix.ext; change ∀ i j, raw37407step2 i j = -(raw37407step1 i j); unfold raw37407step2 raw37407step1; decide +kernel
      have hl : raw37407step2Labels = raw37407step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1514 node1514Labels := by rfl

def raw37408 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37408Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37408step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37408step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw37408step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37408step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw37408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37408 raw37408Labels = mixedMoment B node1514 node1514Labels := by
  calc
    mixedMoment B raw37408 raw37408Labels = mixedMoment B raw37408step0 raw37408step0Labels := by
      have hz : ∀ j, raw37408 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37408step0 = (fun i j => raw37408 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37408step0 raw37408; decide +kernel
      have hl : raw37408step0Labels = raw37408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37408 raw37408Labels permutation265 hz
    mixedMoment B raw37408step0 raw37408step0Labels = mixedMoment B raw37408step1 raw37408step1Labels := by
      have ha : raw37408step1 = (fun i j => raw37408step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37408step1 raw37408step0; decide +kernel
      have hl : raw37408step1Labels = raw37408step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37408step0 raw37408step0Labels permutation38 permutation4
    mixedMoment B raw37408step1 raw37408step1Labels = mixedMoment B raw37408step2 raw37408step2Labels := by
      have ha : raw37408step2 = -raw37408step1 := by apply Matrix.ext; change ∀ i j, raw37408step2 i j = -(raw37408step1 i j); unfold raw37408step2 raw37408step1; decide +kernel
      have hl : raw37408step2Labels = raw37408step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1514 node1514Labels := by rfl

def raw37409 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37409Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37409step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37409step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37409step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37409step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37409step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37409step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37409step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37409 raw37409Labels = mixedMoment B node1535 node1535Labels := by
  calc
    mixedMoment B raw37409 raw37409Labels = mixedMoment B raw37409step0 raw37409step0Labels := by
      have hz : ∀ j, raw37409 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37409step0 = (fun i j => raw37409 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37409step0 raw37409; decide +kernel
      have hl : raw37409step0Labels = raw37409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37409 raw37409Labels permutation346 hz
    mixedMoment B raw37409step0 raw37409step0Labels = mixedMoment B raw37409step1 raw37409step1Labels := by
      have hz : ∀ j, raw37409step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37409step1 = (fun i j => raw37409step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37409step1 raw37409step0; decide +kernel
      have hl : raw37409step1Labels = raw37409step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37409step0 raw37409step0Labels permutation56 hz
    mixedMoment B raw37409step1 raw37409step1Labels = mixedMoment B raw37409step2 raw37409step2Labels := by
      have ha : raw37409step2 = (fun i j => raw37409step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37409step2 raw37409step1; decide +kernel
      have hl : raw37409step2Labels = raw37409step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37409step1 raw37409step1Labels permutation8 permutation4
    mixedMoment B raw37409step2 raw37409step2Labels = mixedMoment B raw37409step3 raw37409step3Labels := by
      have ha : raw37409step3 = -raw37409step2 := by apply Matrix.ext; change ∀ i j, raw37409step3 i j = -(raw37409step2 i j); unfold raw37409step3 raw37409step2; decide +kernel
      have hl : raw37409step3Labels = raw37409step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1535 node1535Labels := by rfl

def raw37410 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, -1, 3]]
def raw37410Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, -1, 3]]
def raw37410step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37410step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![1, -2, 1], ![-2, -1, 3]]
def raw37410step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37410step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw37410step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37410step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw37410step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37410 raw37410Labels = mixedMoment B node1520 node1520Labels := by
  calc
    mixedMoment B raw37410 raw37410Labels = mixedMoment B raw37410step0 raw37410step0Labels := by
      have hz : ∀ j, raw37410 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37410step0 = (fun i j => raw37410 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37410step0 raw37410; decide +kernel
      have hl : raw37410step0Labels = raw37410Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37410 raw37410Labels permutation346 hz
    mixedMoment B raw37410step0 raw37410step0Labels = mixedMoment B raw37410step1 raw37410step1Labels := by
      have hz : ∀ j, raw37410step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37410step1 = (fun i j => raw37410step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37410step1 raw37410step0; decide +kernel
      have hl : raw37410step1Labels = raw37410step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37410step0 raw37410step0Labels permutation56 hz
    mixedMoment B raw37410step1 raw37410step1Labels = mixedMoment B raw37410step2 raw37410step2Labels := by
      have ha : raw37410step2 = (fun i j => raw37410step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37410step2 raw37410step1; decide +kernel
      have hl : raw37410step2Labels = raw37410step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37410step1 raw37410step1Labels permutation9 permutation4
    mixedMoment B raw37410step2 raw37410step2Labels = mixedMoment B raw37410step3 raw37410step3Labels := by
      have ha : raw37410step3 = -raw37410step2 := by apply Matrix.ext; change ∀ i j, raw37410step3 i j = -(raw37410step2 i j); unfold raw37410step3 raw37410step2; decide +kernel
      have hl : raw37410step3Labels = raw37410step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1520 node1520Labels := by rfl

def raw37411 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37411Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37411step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37411step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37411step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37411step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37411step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37411step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw37411step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37411 raw37411Labels = mixedMoment B node1518 node1518Labels := by
  calc
    mixedMoment B raw37411 raw37411Labels = mixedMoment B raw37411step0 raw37411step0Labels := by
      have hz : ∀ j, raw37411 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37411step0 = (fun i j => raw37411 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37411step0 raw37411; decide +kernel
      have hl : raw37411step0Labels = raw37411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37411 raw37411Labels permutation346 hz
    mixedMoment B raw37411step0 raw37411step0Labels = mixedMoment B raw37411step1 raw37411step1Labels := by
      have hz : ∀ j, raw37411step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37411step1 = (fun i j => raw37411step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37411step1 raw37411step0; decide +kernel
      have hl : raw37411step1Labels = raw37411step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37411step0 raw37411step0Labels permutation56 hz
    mixedMoment B raw37411step1 raw37411step1Labels = mixedMoment B raw37411step2 raw37411step2Labels := by
      have ha : raw37411step2 = (fun i j => raw37411step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37411step2 raw37411step1; decide +kernel
      have hl : raw37411step2Labels = raw37411step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37411step1 raw37411step1Labels permutation8 permutation4
    mixedMoment B raw37411step2 raw37411step2Labels = mixedMoment B raw37411step3 raw37411step3Labels := by
      have ha : raw37411step3 = -raw37411step2 := by apply Matrix.ext; change ∀ i j, raw37411step3 i j = -(raw37411step2 i j); unfold raw37411step3 raw37411step2; decide +kernel
      have hl : raw37411step3Labels = raw37411step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1518 node1518Labels := by rfl

def raw37412 : Matrix (Fin 6) (Fin 2) ℤ := ![![5, -5], ![0, 0], ![0, 0], ![-1, 1], ![-1, 1], ![-3, 3]]
def raw37412Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37412step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![5, -5], ![0, 0], ![-1, 1], ![-1, 1], ![-3, 3]]
def raw37412step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37412step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![5, -5], ![-1, 1], ![-1, 1], ![-3, 3]]
def raw37412step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37412step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![3, -3]]
def raw37412step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37412 raw37412Labels = mixedMoment B node4058 node4058Labels := by
  calc
    mixedMoment B raw37412 raw37412Labels = mixedMoment B raw37412step0 raw37412step0Labels := by
      have hz : ∀ j, raw37412 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37412step0 = (fun i j => raw37412 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37412step0 raw37412; decide +kernel
      have hl : raw37412step0Labels = raw37412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37412 raw37412Labels permutation346 hz
    mixedMoment B raw37412step0 raw37412step0Labels = mixedMoment B raw37412step1 raw37412step1Labels := by
      have hz : ∀ j, raw37412step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37412step1 = (fun i j => raw37412step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37412step1 raw37412step0; decide +kernel
      have hl : raw37412step1Labels = raw37412step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37412step0 raw37412step0Labels permutation56 hz
    mixedMoment B raw37412step1 raw37412step1Labels = mixedMoment B raw37412step2 raw37412step2Labels := by
      have ha : raw37412step2 = -raw37412step1 := by apply Matrix.ext; change ∀ i j, raw37412step2 i j = -(raw37412step1 i j); unfold raw37412step2 raw37412step1; decide +kernel
      have hl : raw37412step2Labels = raw37412step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4058 node4058Labels := by rfl

def raw37413 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37413Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37413step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37413step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37413step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37413step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw37413step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37413 raw37413Labels = mixedMoment B node1509 node1509Labels := by
  calc
    mixedMoment B raw37413 raw37413Labels = mixedMoment B raw37413step0 raw37413step0Labels := by
      have hz : ∀ j, raw37413 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37413step0 = (fun i j => raw37413 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37413step0 raw37413; decide +kernel
      have hl : raw37413step0Labels = raw37413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37413 raw37413Labels permutation346 hz
    mixedMoment B raw37413step0 raw37413step0Labels = mixedMoment B raw37413step1 raw37413step1Labels := by
      have hz : ∀ j, raw37413step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37413step1 = (fun i j => raw37413step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37413step1 raw37413step0; decide +kernel
      have hl : raw37413step1Labels = raw37413step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37413step0 raw37413step0Labels permutation56 hz
    mixedMoment B raw37413step1 raw37413step1Labels = mixedMoment B raw37413step2 raw37413step2Labels := by
      have ha : raw37413step2 = -raw37413step1 := by apply Matrix.ext; change ∀ i j, raw37413step2 i j = -(raw37413step1 i j); unfold raw37413step2 raw37413step1; decide +kernel
      have hl : raw37413step2Labels = raw37413step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1509 node1509Labels := by rfl

def raw37414 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37414Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37414step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37414step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37414step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37414step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37414step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37414 raw37414Labels = mixedMoment B node1528 node1528Labels := by
  calc
    mixedMoment B raw37414 raw37414Labels = mixedMoment B raw37414step0 raw37414step0Labels := by
      have hz : ∀ j, raw37414 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37414step0 = (fun i j => raw37414 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37414step0 raw37414; decide +kernel
      have hl : raw37414step0Labels = raw37414Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37414 raw37414Labels permutation346 hz
    mixedMoment B raw37414step0 raw37414step0Labels = mixedMoment B raw37414step1 raw37414step1Labels := by
      have ha : raw37414step1 = (fun i j => raw37414step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37414step1 raw37414step0; decide +kernel
      have hl : raw37414step1Labels = raw37414step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37414step0 raw37414step0Labels permutation50 permutation4
    mixedMoment B raw37414step1 raw37414step1Labels = mixedMoment B raw37414step2 raw37414step2Labels := by
      have ha : raw37414step2 = -raw37414step1 := by apply Matrix.ext; change ∀ i j, raw37414step2 i j = -(raw37414step1 i j); unfold raw37414step2 raw37414step1; decide +kernel
      have hl : raw37414step2Labels = raw37414step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1528 node1528Labels := by rfl

def raw37415 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37415Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37415step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37415step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37415step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37415step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37415step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37415 raw37415Labels = mixedMoment B node1528 node1528Labels := by
  calc
    mixedMoment B raw37415 raw37415Labels = mixedMoment B raw37415step0 raw37415step0Labels := by
      have hz : ∀ j, raw37415 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37415step0 = (fun i j => raw37415 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37415step0 raw37415; decide +kernel
      have hl : raw37415step0Labels = raw37415Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37415 raw37415Labels permutation265 hz
    mixedMoment B raw37415step0 raw37415step0Labels = mixedMoment B raw37415step1 raw37415step1Labels := by
      have ha : raw37415step1 = (fun i j => raw37415step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37415step1 raw37415step0; decide +kernel
      have hl : raw37415step1Labels = raw37415step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37415step0 raw37415step0Labels permutation50 permutation4
    mixedMoment B raw37415step1 raw37415step1Labels = mixedMoment B raw37415step2 raw37415step2Labels := by
      have ha : raw37415step2 = -raw37415step1 := by apply Matrix.ext; change ∀ i j, raw37415step2 i j = -(raw37415step1 i j); unfold raw37415step2 raw37415step1; decide +kernel
      have hl : raw37415step2Labels = raw37415step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1528 node1528Labels := by rfl

def raw37416 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37416Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37416step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -2, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37416step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37416step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw37416step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37416step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw37416step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37416 raw37416Labels = mixedMoment B node1530 node1530Labels := by
  calc
    mixedMoment B raw37416 raw37416Labels = mixedMoment B raw37416step0 raw37416step0Labels := by
      have hz : ∀ j, raw37416 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37416step0 = (fun i j => raw37416 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37416step0 raw37416; decide +kernel
      have hl : raw37416step0Labels = raw37416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37416 raw37416Labels permutation346 hz
    mixedMoment B raw37416step0 raw37416step0Labels = mixedMoment B raw37416step1 raw37416step1Labels := by
      have hz : ∀ j, raw37416step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37416step1 = (fun i j => raw37416step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37416step1 raw37416step0; decide +kernel
      have hl : raw37416step1Labels = raw37416step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37416step0 raw37416step0Labels permutation56 hz
    mixedMoment B raw37416step1 raw37416step1Labels = mixedMoment B raw37416step2 raw37416step2Labels := by
      have ha : raw37416step2 = (fun i j => raw37416step1 (permutation13 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37416step2 raw37416step1; decide +kernel
      have hl : raw37416step2Labels = raw37416step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37416step1 raw37416step1Labels permutation13 permutation4
    mixedMoment B raw37416step2 raw37416step2Labels = mixedMoment B raw37416step3 raw37416step3Labels := by
      have ha : raw37416step3 = -raw37416step2 := by apply Matrix.ext; change ∀ i j, raw37416step3 i j = -(raw37416step2 i j); unfold raw37416step3 raw37416step2; decide +kernel
      have hl : raw37416step3Labels = raw37416step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1530 node1530Labels := by rfl

def raw37417 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 0, 3]]
def raw37417Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 0, 3]]
def raw37417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37417step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, -1, 1], ![1, -2, 1], ![-3, 0, 3]]
def raw37417step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37417step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw37417step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37417step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw37417step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37417 raw37417Labels = mixedMoment B node1530 node1530Labels := by
  calc
    mixedMoment B raw37417 raw37417Labels = mixedMoment B raw37417step0 raw37417step0Labels := by
      have hz : ∀ j, raw37417 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37417step0 = (fun i j => raw37417 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37417step0 raw37417; decide +kernel
      have hl : raw37417step0Labels = raw37417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37417 raw37417Labels permutation346 hz
    mixedMoment B raw37417step0 raw37417step0Labels = mixedMoment B raw37417step1 raw37417step1Labels := by
      have hz : ∀ j, raw37417step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37417step1 = (fun i j => raw37417step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37417step1 raw37417step0; decide +kernel
      have hl : raw37417step1Labels = raw37417step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37417step0 raw37417step0Labels permutation56 hz
    mixedMoment B raw37417step1 raw37417step1Labels = mixedMoment B raw37417step2 raw37417step2Labels := by
      have ha : raw37417step2 = (fun i j => raw37417step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37417step2 raw37417step1; decide +kernel
      have hl : raw37417step2Labels = raw37417step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37417step1 raw37417step1Labels permutation12 permutation4
    mixedMoment B raw37417step2 raw37417step2Labels = mixedMoment B raw37417step3 raw37417step3Labels := by
      have ha : raw37417step3 = -raw37417step2 := by apply Matrix.ext; change ∀ i j, raw37417step3 i j = -(raw37417step2 i j); unfold raw37417step3 raw37417step2; decide +kernel
      have hl : raw37417step3Labels = raw37417step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1530 node1530Labels := by rfl

def raw37418 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37418Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37418step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37418step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37418step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37418step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37418 raw37418Labels = mixedMoment B node1535 node1535Labels := by
  calc
    mixedMoment B raw37418 raw37418Labels = mixedMoment B raw37418step0 raw37418step0Labels := by
      have hz : ∀ j, raw37418 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37418step0 = (fun i j => raw37418 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37418step0 raw37418; decide +kernel
      have hl : raw37418step0Labels = raw37418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37418 raw37418Labels permutation346 hz
    mixedMoment B raw37418step0 raw37418step0Labels = mixedMoment B raw37418step1 raw37418step1Labels := by
      have hz : ∀ j, raw37418step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37418step1 = (fun i j => raw37418step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37418step1 raw37418step0; decide +kernel
      have hl : raw37418step1Labels = raw37418step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37418step0 raw37418step0Labels permutation56 hz
    mixedMoment B raw37418step1 raw37418step1Labels = mixedMoment B raw37418step2 raw37418step2Labels := by
      have ha : raw37418step2 = -raw37418step1 := by apply Matrix.ext; change ∀ i j, raw37418step2 i j = -(raw37418step1 i j); unfold raw37418step2 raw37418step1; decide +kernel
      have hl : raw37418step2Labels = raw37418step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1535 node1535Labels := by rfl

def raw37419 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37419Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37419step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw37419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37419step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw37419step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37419 raw37419Labels = mixedMoment B node1505 node1505Labels := by
  calc
    mixedMoment B raw37419 raw37419Labels = mixedMoment B raw37419step0 raw37419step0Labels := by
      have hz : ∀ j, raw37419 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37419step0 = (fun i j => raw37419 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37419step0 raw37419; decide +kernel
      have hl : raw37419step0Labels = raw37419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37419 raw37419Labels permutation346 hz
    mixedMoment B raw37419step0 raw37419step0Labels = mixedMoment B raw37419step1 raw37419step1Labels := by
      have ha : raw37419step1 = (fun i j => raw37419step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37419step1 raw37419step0; decide +kernel
      have hl : raw37419step1Labels = raw37419step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37419step0 raw37419step0Labels permutation40 permutation4
    mixedMoment B raw37419step1 raw37419step1Labels = mixedMoment B raw37419step2 raw37419step2Labels := by
      have ha : raw37419step2 = -raw37419step1 := by apply Matrix.ext; change ∀ i j, raw37419step2 i j = -(raw37419step1 i j); unfold raw37419step2 raw37419step1; decide +kernel
      have hl : raw37419step2Labels = raw37419step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1505 node1505Labels := by rfl

def raw37420 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37420Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37420step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw37420step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37420step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw37420step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37420 raw37420Labels = mixedMoment B node1505 node1505Labels := by
  calc
    mixedMoment B raw37420 raw37420Labels = mixedMoment B raw37420step0 raw37420step0Labels := by
      have hz : ∀ j, raw37420 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37420step0 = (fun i j => raw37420 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37420step0 raw37420; decide +kernel
      have hl : raw37420step0Labels = raw37420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37420 raw37420Labels permutation265 hz
    mixedMoment B raw37420step0 raw37420step0Labels = mixedMoment B raw37420step1 raw37420step1Labels := by
      have ha : raw37420step1 = (fun i j => raw37420step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37420step1 raw37420step0; decide +kernel
      have hl : raw37420step1Labels = raw37420step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37420step0 raw37420step0Labels permutation40 permutation4
    mixedMoment B raw37420step1 raw37420step1Labels = mixedMoment B raw37420step2 raw37420step2Labels := by
      have ha : raw37420step2 = -raw37420step1 := by apply Matrix.ext; change ∀ i j, raw37420step2 i j = -(raw37420step1 i j); unfold raw37420step2 raw37420step1; decide +kernel
      have hl : raw37420step2Labels = raw37420step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1505 node1505Labels := by rfl

def raw37421 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37421Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37421step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37421step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, -1, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37421step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37421step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37421step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37421step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw37421step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37421 raw37421Labels = mixedMoment B node1518 node1518Labels := by
  calc
    mixedMoment B raw37421 raw37421Labels = mixedMoment B raw37421step0 raw37421step0Labels := by
      have hz : ∀ j, raw37421 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37421step0 = (fun i j => raw37421 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37421step0 raw37421; decide +kernel
      have hl : raw37421step0Labels = raw37421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37421 raw37421Labels permutation346 hz
    mixedMoment B raw37421step0 raw37421step0Labels = mixedMoment B raw37421step1 raw37421step1Labels := by
      have hz : ∀ j, raw37421step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37421step1 = (fun i j => raw37421step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37421step1 raw37421step0; decide +kernel
      have hl : raw37421step1Labels = raw37421step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37421step0 raw37421step0Labels permutation56 hz
    mixedMoment B raw37421step1 raw37421step1Labels = mixedMoment B raw37421step2 raw37421step2Labels := by
      have ha : raw37421step2 = (fun i j => raw37421step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37421step2 raw37421step1; decide +kernel
      have hl : raw37421step2Labels = raw37421step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37421step1 raw37421step1Labels permutation10 permutation4
    mixedMoment B raw37421step2 raw37421step2Labels = mixedMoment B raw37421step3 raw37421step3Labels := by
      have ha : raw37421step3 = -raw37421step2 := by apply Matrix.ext; change ∀ i j, raw37421step3 i j = -(raw37421step2 i j); unfold raw37421step3 raw37421step2; decide +kernel
      have hl : raw37421step3Labels = raw37421step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1518 node1518Labels := by rfl

def raw37422 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37422Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37422step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37422step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37422step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37422step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw37422step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37422step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw37422step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37422 raw37422Labels = mixedMoment B node1509 node1509Labels := by
  calc
    mixedMoment B raw37422 raw37422Labels = mixedMoment B raw37422step0 raw37422step0Labels := by
      have hz : ∀ j, raw37422 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37422step0 = (fun i j => raw37422 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37422step0 raw37422; decide +kernel
      have hl : raw37422step0Labels = raw37422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37422 raw37422Labels permutation346 hz
    mixedMoment B raw37422step0 raw37422step0Labels = mixedMoment B raw37422step1 raw37422step1Labels := by
      have hz : ∀ j, raw37422step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37422step1 = (fun i j => raw37422step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37422step1 raw37422step0; decide +kernel
      have hl : raw37422step1Labels = raw37422step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37422step0 raw37422step0Labels permutation56 hz
    mixedMoment B raw37422step1 raw37422step1Labels = mixedMoment B raw37422step2 raw37422step2Labels := by
      have ha : raw37422step2 = (fun i j => raw37422step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37422step2 raw37422step1; decide +kernel
      have hl : raw37422step2Labels = raw37422step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37422step1 raw37422step1Labels permutation8 permutation4
    mixedMoment B raw37422step2 raw37422step2Labels = mixedMoment B raw37422step3 raw37422step3Labels := by
      have ha : raw37422step3 = -raw37422step2 := by apply Matrix.ext; change ∀ i j, raw37422step3 i j = -(raw37422step2 i j); unfold raw37422step3 raw37422step2; decide +kernel
      have hl : raw37422step3Labels = raw37422step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1509 node1509Labels := by rfl

def raw37423 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37423Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37423step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37423step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37423step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37423step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37423step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37423 raw37423Labels = mixedMoment B node681 node681Labels := by
  calc
    mixedMoment B raw37423 raw37423Labels = mixedMoment B raw37423step0 raw37423step0Labels := by
      have hz : ∀ j, raw37423 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37423step0 = (fun i j => raw37423 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37423step0 raw37423; decide +kernel
      have hl : raw37423step0Labels = raw37423Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37423 raw37423Labels permutation346 hz
    mixedMoment B raw37423step0 raw37423step0Labels = mixedMoment B raw37423step1 raw37423step1Labels := by
      have ha : raw37423step1 = (fun i j => raw37423step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37423step1 raw37423step0; decide +kernel
      have hl : raw37423step1Labels = raw37423step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37423step0 raw37423step0Labels permutation32 permutation4
    mixedMoment B raw37423step1 raw37423step1Labels = mixedMoment B raw37423step2 raw37423step2Labels := by
      have ha : raw37423step2 = -raw37423step1 := by apply Matrix.ext; change ∀ i j, raw37423step2 i j = -(raw37423step1 i j); unfold raw37423step2 raw37423step1; decide +kernel
      have hl : raw37423step2Labels = raw37423step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node681 node681Labels := by rfl

def raw37424 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37424Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37424step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37424step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37424step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37424step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw37424step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37424 raw37424Labels = mixedMoment B node681 node681Labels := by
  calc
    mixedMoment B raw37424 raw37424Labels = mixedMoment B raw37424step0 raw37424step0Labels := by
      have hz : ∀ j, raw37424 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37424step0 = (fun i j => raw37424 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37424step0 raw37424; decide +kernel
      have hl : raw37424step0Labels = raw37424Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37424 raw37424Labels permutation265 hz
    mixedMoment B raw37424step0 raw37424step0Labels = mixedMoment B raw37424step1 raw37424step1Labels := by
      have ha : raw37424step1 = (fun i j => raw37424step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37424step1 raw37424step0; decide +kernel
      have hl : raw37424step1Labels = raw37424step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37424step0 raw37424step0Labels permutation32 permutation4
    mixedMoment B raw37424step1 raw37424step1Labels = mixedMoment B raw37424step2 raw37424step2Labels := by
      have ha : raw37424step2 = -raw37424step1 := by apply Matrix.ext; change ∀ i j, raw37424step2 i j = -(raw37424step1 i j); unfold raw37424step2 raw37424step1; decide +kernel
      have hl : raw37424step2Labels = raw37424step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node681 node681Labels := by rfl

def raw37425 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37425Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37425step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37425step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![1, -2, 1], ![0, -1, 1], ![-2, -1, 3]]
def raw37425step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37425step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 0, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw37425step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37425step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw37425step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37425 raw37425Labels = mixedMoment B node690 node690Labels := by
  calc
    mixedMoment B raw37425 raw37425Labels = mixedMoment B raw37425step0 raw37425step0Labels := by
      have hz : ∀ j, raw37425 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37425step0 = (fun i j => raw37425 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37425step0 raw37425; decide +kernel
      have hl : raw37425step0Labels = raw37425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37425 raw37425Labels permutation346 hz
    mixedMoment B raw37425step0 raw37425step0Labels = mixedMoment B raw37425step1 raw37425step1Labels := by
      have hz : ∀ j, raw37425step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37425step1 = (fun i j => raw37425step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37425step1 raw37425step0; decide +kernel
      have hl : raw37425step1Labels = raw37425step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37425step0 raw37425step0Labels permutation56 hz
    mixedMoment B raw37425step1 raw37425step1Labels = mixedMoment B raw37425step2 raw37425step2Labels := by
      have ha : raw37425step2 = (fun i j => raw37425step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37425step2 raw37425step1; decide +kernel
      have hl : raw37425step2Labels = raw37425step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37425step1 raw37425step1Labels permutation11 permutation4
    mixedMoment B raw37425step2 raw37425step2Labels = mixedMoment B raw37425step3 raw37425step3Labels := by
      have ha : raw37425step3 = -raw37425step2 := by apply Matrix.ext; change ∀ i j, raw37425step3 i j = -(raw37425step2 i j); unfold raw37425step3 raw37425step2; decide +kernel
      have hl : raw37425step3Labels = raw37425step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node690 node690Labels := by rfl

def raw37426 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, -1, 3]]
def raw37426Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, -1, 3]]
def raw37426step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37426step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![0, -1, 1], ![1, -2, 1], ![-2, -1, 3]]
def raw37426step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37426step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 0, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw37426step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37426step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw37426step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37426 raw37426Labels = mixedMoment B node690 node690Labels := by
  calc
    mixedMoment B raw37426 raw37426Labels = mixedMoment B raw37426step0 raw37426step0Labels := by
      have hz : ∀ j, raw37426 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37426step0 = (fun i j => raw37426 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37426step0 raw37426; decide +kernel
      have hl : raw37426step0Labels = raw37426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37426 raw37426Labels permutation346 hz
    mixedMoment B raw37426step0 raw37426step0Labels = mixedMoment B raw37426step1 raw37426step1Labels := by
      have hz : ∀ j, raw37426step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37426step1 = (fun i j => raw37426step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37426step1 raw37426step0; decide +kernel
      have hl : raw37426step1Labels = raw37426step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37426step0 raw37426step0Labels permutation56 hz
    mixedMoment B raw37426step1 raw37426step1Labels = mixedMoment B raw37426step2 raw37426step2Labels := by
      have ha : raw37426step2 = (fun i j => raw37426step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37426step2 raw37426step1; decide +kernel
      have hl : raw37426step2Labels = raw37426step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37426step1 raw37426step1Labels permutation9 permutation4
    mixedMoment B raw37426step2 raw37426step2Labels = mixedMoment B raw37426step3 raw37426step3Labels := by
      have ha : raw37426step3 = -raw37426step2 := by apply Matrix.ext; change ∀ i j, raw37426step3 i j = -(raw37426step2 i j); unfold raw37426step3 raw37426step2; decide +kernel
      have hl : raw37426step3Labels = raw37426step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node690 node690Labels := by rfl

def raw37427 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37427Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37427step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37427step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![0, -1, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37427step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37427step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37427step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37427step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw37427step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37427 raw37427Labels = mixedMoment B node688 node688Labels := by
  calc
    mixedMoment B raw37427 raw37427Labels = mixedMoment B raw37427step0 raw37427step0Labels := by
      have hz : ∀ j, raw37427 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37427step0 = (fun i j => raw37427 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37427step0 raw37427; decide +kernel
      have hl : raw37427step0Labels = raw37427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37427 raw37427Labels permutation346 hz
    mixedMoment B raw37427step0 raw37427step0Labels = mixedMoment B raw37427step1 raw37427step1Labels := by
      have hz : ∀ j, raw37427step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37427step1 = (fun i j => raw37427step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37427step1 raw37427step0; decide +kernel
      have hl : raw37427step1Labels = raw37427step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37427step0 raw37427step0Labels permutation56 hz
    mixedMoment B raw37427step1 raw37427step1Labels = mixedMoment B raw37427step2 raw37427step2Labels := by
      have ha : raw37427step2 = (fun i j => raw37427step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37427step2 raw37427step1; decide +kernel
      have hl : raw37427step2Labels = raw37427step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37427step1 raw37427step1Labels permutation8 permutation4
    mixedMoment B raw37427step2 raw37427step2Labels = mixedMoment B raw37427step3 raw37427step3Labels := by
      have ha : raw37427step3 = -raw37427step2 := by apply Matrix.ext; change ∀ i j, raw37427step3 i j = -(raw37427step2 i j); unfold raw37427step3 raw37427step2; decide +kernel
      have hl : raw37427step3Labels = raw37427step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node688 node688Labels := by rfl

def raw37428 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37428Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37428step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37428step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37428step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37428step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw37428step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37428 raw37428Labels = mixedMoment B node1492 node1492Labels := by
  calc
    mixedMoment B raw37428 raw37428Labels = mixedMoment B raw37428step0 raw37428step0Labels := by
      have hz : ∀ j, raw37428 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37428step0 = (fun i j => raw37428 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37428step0 raw37428; decide +kernel
      have hl : raw37428step0Labels = raw37428Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37428 raw37428Labels permutation346 hz
    mixedMoment B raw37428step0 raw37428step0Labels = mixedMoment B raw37428step1 raw37428step1Labels := by
      have ha : raw37428step1 = (fun i j => raw37428step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37428step1 raw37428step0; decide +kernel
      have hl : raw37428step1Labels = raw37428step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37428step0 raw37428step0Labels permutation32 permutation4
    mixedMoment B raw37428step1 raw37428step1Labels = mixedMoment B raw37428step2 raw37428step2Labels := by
      have ha : raw37428step2 = -raw37428step1 := by apply Matrix.ext; change ∀ i j, raw37428step2 i j = -(raw37428step1 i j); unfold raw37428step2 raw37428step1; decide +kernel
      have hl : raw37428step2Labels = raw37428step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1492 node1492Labels := by rfl

def raw37429 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37429Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -2, 3]]
def raw37429step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37429step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw37429step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37429step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw37429step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37429 raw37429Labels = mixedMoment B node1492 node1492Labels := by
  calc
    mixedMoment B raw37429 raw37429Labels = mixedMoment B raw37429step0 raw37429step0Labels := by
      have hz : ∀ j, raw37429 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37429step0 = (fun i j => raw37429 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37429step0 raw37429; decide +kernel
      have hl : raw37429step0Labels = raw37429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37429 raw37429Labels permutation265 hz
    mixedMoment B raw37429step0 raw37429step0Labels = mixedMoment B raw37429step1 raw37429step1Labels := by
      have ha : raw37429step1 = (fun i j => raw37429step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37429step1 raw37429step0; decide +kernel
      have hl : raw37429step1Labels = raw37429step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37429step0 raw37429step0Labels permutation32 permutation4
    mixedMoment B raw37429step1 raw37429step1Labels = mixedMoment B raw37429step2 raw37429step2Labels := by
      have ha : raw37429step2 = -raw37429step1 := by apply Matrix.ext; change ∀ i j, raw37429step2 i j = -(raw37429step1 i j); unfold raw37429step2 raw37429step1; decide +kernel
      have hl : raw37429step2Labels = raw37429step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1492 node1492Labels := by rfl

def raw37430 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37430Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37430step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw37430step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37430step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw37430step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37430 raw37430Labels = mixedMoment B node663 node663Labels := by
  calc
    mixedMoment B raw37430 raw37430Labels = mixedMoment B raw37430step0 raw37430step0Labels := by
      have hz : ∀ j, raw37430 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37430step0 = (fun i j => raw37430 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37430step0 raw37430; decide +kernel
      have hl : raw37430step0Labels = raw37430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37430 raw37430Labels permutation346 hz
    mixedMoment B raw37430step0 raw37430step0Labels = mixedMoment B raw37430step1 raw37430step1Labels := by
      have ha : raw37430step1 = (fun i j => raw37430step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37430step1 raw37430step0; decide +kernel
      have hl : raw37430step1Labels = raw37430step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37430step0 raw37430step0Labels permutation44 permutation4
    mixedMoment B raw37430step1 raw37430step1Labels = mixedMoment B raw37430step2 raw37430step2Labels := by
      have ha : raw37430step2 = -raw37430step1 := by apply Matrix.ext; change ∀ i j, raw37430step2 i j = -(raw37430step1 i j); unfold raw37430step2 raw37430step1; decide +kernel
      have hl : raw37430step2Labels = raw37430step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node663 node663Labels := by rfl

def raw37431 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37431Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37431step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw37431step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37431step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw37431step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37431 raw37431Labels = mixedMoment B node663 node663Labels := by
  calc
    mixedMoment B raw37431 raw37431Labels = mixedMoment B raw37431step0 raw37431step0Labels := by
      have hz : ∀ j, raw37431 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37431step0 = (fun i j => raw37431 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37431step0 raw37431; decide +kernel
      have hl : raw37431step0Labels = raw37431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37431 raw37431Labels permutation265 hz
    mixedMoment B raw37431step0 raw37431step0Labels = mixedMoment B raw37431step1 raw37431step1Labels := by
      have ha : raw37431step1 = (fun i j => raw37431step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37431step1 raw37431step0; decide +kernel
      have hl : raw37431step1Labels = raw37431step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37431step0 raw37431step0Labels permutation44 permutation4
    mixedMoment B raw37431step1 raw37431step1Labels = mixedMoment B raw37431step2 raw37431step2Labels := by
      have ha : raw37431step2 = -raw37431step1 := by apply Matrix.ext; change ∀ i j, raw37431step2 i j = -(raw37431step1 i j); unfold raw37431step2 raw37431step1; decide +kernel
      have hl : raw37431step2Labels = raw37431step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node663 node663Labels := by rfl

def raw37432 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37432Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37432step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37432step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![1, -2, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw37432step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37432step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-2, 1, 1], ![-2, -1, 3]]
def raw37432step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37432step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw37432step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37432 raw37432Labels = mixedMoment B node671 node671Labels := by
  calc
    mixedMoment B raw37432 raw37432Labels = mixedMoment B raw37432step0 raw37432step0Labels := by
      have hz : ∀ j, raw37432 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37432step0 = (fun i j => raw37432 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37432step0 raw37432; decide +kernel
      have hl : raw37432step0Labels = raw37432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37432 raw37432Labels permutation346 hz
    mixedMoment B raw37432step0 raw37432step0Labels = mixedMoment B raw37432step1 raw37432step1Labels := by
      have hz : ∀ j, raw37432step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37432step1 = (fun i j => raw37432step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37432step1 raw37432step0; decide +kernel
      have hl : raw37432step1Labels = raw37432step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37432step0 raw37432step0Labels permutation56 hz
    mixedMoment B raw37432step1 raw37432step1Labels = mixedMoment B raw37432step2 raw37432step2Labels := by
      have ha : raw37432step2 = (fun i j => raw37432step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37432step2 raw37432step1; decide +kernel
      have hl : raw37432step2Labels = raw37432step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37432step1 raw37432step1Labels permutation10 permutation4
    mixedMoment B raw37432step2 raw37432step2Labels = mixedMoment B raw37432step3 raw37432step3Labels := by
      have ha : raw37432step3 = -raw37432step2 := by apply Matrix.ext; change ∀ i j, raw37432step3 i j = -(raw37432step2 i j); unfold raw37432step3 raw37432step2; decide +kernel
      have hl : raw37432step3Labels = raw37432step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node671 node671Labels := by rfl

def raw37433 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37433Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37433step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37433step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![0, -1, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37433step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37433step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw37433step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37433step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw37433step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37433 raw37433Labels = mixedMoment B node669 node669Labels := by
  calc
    mixedMoment B raw37433 raw37433Labels = mixedMoment B raw37433step0 raw37433step0Labels := by
      have hz : ∀ j, raw37433 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37433step0 = (fun i j => raw37433 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37433step0 raw37433; decide +kernel
      have hl : raw37433step0Labels = raw37433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37433 raw37433Labels permutation346 hz
    mixedMoment B raw37433step0 raw37433step0Labels = mixedMoment B raw37433step1 raw37433step1Labels := by
      have hz : ∀ j, raw37433step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37433step1 = (fun i j => raw37433step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37433step1 raw37433step0; decide +kernel
      have hl : raw37433step1Labels = raw37433step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37433step0 raw37433step0Labels permutation56 hz
    mixedMoment B raw37433step1 raw37433step1Labels = mixedMoment B raw37433step2 raw37433step2Labels := by
      have ha : raw37433step2 = (fun i j => raw37433step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37433step2 raw37433step1; decide +kernel
      have hl : raw37433step2Labels = raw37433step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37433step1 raw37433step1Labels permutation10 permutation4
    mixedMoment B raw37433step2 raw37433step2Labels = mixedMoment B raw37433step3 raw37433step3Labels := by
      have ha : raw37433step3 = -raw37433step2 := by apply Matrix.ext; change ∀ i j, raw37433step3 i j = -(raw37433step2 i j); unfold raw37433step3 raw37433step2; decide +kernel
      have hl : raw37433step3Labels = raw37433step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node669 node669Labels := by rfl

def raw37434 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37434Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37434step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37434step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw37434step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37434step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw37434step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37434 raw37434Labels = mixedMoment B node1489 node1489Labels := by
  calc
    mixedMoment B raw37434 raw37434Labels = mixedMoment B raw37434step0 raw37434step0Labels := by
      have hz : ∀ j, raw37434 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37434step0 = (fun i j => raw37434 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37434step0 raw37434; decide +kernel
      have hl : raw37434step0Labels = raw37434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37434 raw37434Labels permutation346 hz
    mixedMoment B raw37434step0 raw37434step0Labels = mixedMoment B raw37434step1 raw37434step1Labels := by
      have ha : raw37434step1 = (fun i j => raw37434step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37434step1 raw37434step0; decide +kernel
      have hl : raw37434step1Labels = raw37434step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37434step0 raw37434step0Labels permutation34 permutation4
    mixedMoment B raw37434step1 raw37434step1Labels = mixedMoment B raw37434step2 raw37434step2Labels := by
      have ha : raw37434step2 = -raw37434step1 := by apply Matrix.ext; change ∀ i j, raw37434step2 i j = -(raw37434step1 i j); unfold raw37434step2 raw37434step1; decide +kernel
      have hl : raw37434step2Labels = raw37434step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1489 node1489Labels := by rfl

def raw37435 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37435Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37435step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw37435step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37435step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw37435step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37435 raw37435Labels = mixedMoment B node1489 node1489Labels := by
  calc
    mixedMoment B raw37435 raw37435Labels = mixedMoment B raw37435step0 raw37435step0Labels := by
      have hz : ∀ j, raw37435 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37435step0 = (fun i j => raw37435 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37435step0 raw37435; decide +kernel
      have hl : raw37435step0Labels = raw37435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37435 raw37435Labels permutation265 hz
    mixedMoment B raw37435step0 raw37435step0Labels = mixedMoment B raw37435step1 raw37435step1Labels := by
      have ha : raw37435step1 = (fun i j => raw37435step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37435step1 raw37435step0; decide +kernel
      have hl : raw37435step1Labels = raw37435step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37435step0 raw37435step0Labels permutation34 permutation4
    mixedMoment B raw37435step1 raw37435step1Labels = mixedMoment B raw37435step2 raw37435step2Labels := by
      have ha : raw37435step2 = -raw37435step1 := by apply Matrix.ext; change ∀ i j, raw37435step2 i j = -(raw37435step1 i j); unfold raw37435step2 raw37435step1; decide +kernel
      have hl : raw37435step2Labels = raw37435step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1489 node1489Labels := by rfl

def raw37436 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -3, 3]]
def raw37436Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -3, 3]]
def raw37436step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37436step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, -1, 1], ![-2, 1, 1], ![0, -3, 3]]
def raw37436step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37436step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -2, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw37436step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37436step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![3, 0, -3]]
def raw37436step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37436 raw37436Labels = mixedMoment B node1499 node1499Labels := by
  calc
    mixedMoment B raw37436 raw37436Labels = mixedMoment B raw37436step0 raw37436step0Labels := by
      have hz : ∀ j, raw37436 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37436step0 = (fun i j => raw37436 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37436step0 raw37436; decide +kernel
      have hl : raw37436step0Labels = raw37436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37436 raw37436Labels permutation346 hz
    mixedMoment B raw37436step0 raw37436step0Labels = mixedMoment B raw37436step1 raw37436step1Labels := by
      have hz : ∀ j, raw37436step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37436step1 = (fun i j => raw37436step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37436step1 raw37436step0; decide +kernel
      have hl : raw37436step1Labels = raw37436step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37436step0 raw37436step0Labels permutation56 hz
    mixedMoment B raw37436step1 raw37436step1Labels = mixedMoment B raw37436step2 raw37436step2Labels := by
      have ha : raw37436step2 = (fun i j => raw37436step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37436step2 raw37436step1; decide +kernel
      have hl : raw37436step2Labels = raw37436step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37436step1 raw37436step1Labels permutation10 permutation4
    mixedMoment B raw37436step2 raw37436step2Labels = mixedMoment B raw37436step3 raw37436step3Labels := by
      have ha : raw37436step3 = -raw37436step2 := by apply Matrix.ext; change ∀ i j, raw37436step3 i j = -(raw37436step2 i j); unfold raw37436step3 raw37436step2; decide +kernel
      have hl : raw37436step3Labels = raw37436step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1499 node1499Labels := by rfl

def raw37437 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37437Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37437step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37437step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw37437step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37437step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw37437step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37437 raw37437Labels = mixedMoment B node657 node657Labels := by
  calc
    mixedMoment B raw37437 raw37437Labels = mixedMoment B raw37437step0 raw37437step0Labels := by
      have hz : ∀ j, raw37437 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37437step0 = (fun i j => raw37437 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37437step0 raw37437; decide +kernel
      have hl : raw37437step0Labels = raw37437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37437 raw37437Labels permutation346 hz
    mixedMoment B raw37437step0 raw37437step0Labels = mixedMoment B raw37437step1 raw37437step1Labels := by
      have ha : raw37437step1 = (fun i j => raw37437step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37437step1 raw37437step0; decide +kernel
      have hl : raw37437step1Labels = raw37437step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37437step0 raw37437step0Labels permutation40 permutation4
    mixedMoment B raw37437step1 raw37437step1Labels = mixedMoment B raw37437step2 raw37437step2Labels := by
      have ha : raw37437step2 = -raw37437step1 := by apply Matrix.ext; change ∀ i j, raw37437step2 i j = -(raw37437step1 i j); unfold raw37437step2 raw37437step1; decide +kernel
      have hl : raw37437step2Labels = raw37437step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node657 node657Labels := by rfl

def raw37438 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37438Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -3, 3]]
def raw37438step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37438step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw37438step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37438step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw37438step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37438 raw37438Labels = mixedMoment B node657 node657Labels := by
  calc
    mixedMoment B raw37438 raw37438Labels = mixedMoment B raw37438step0 raw37438step0Labels := by
      have hz : ∀ j, raw37438 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37438step0 = (fun i j => raw37438 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37438step0 raw37438; decide +kernel
      have hl : raw37438step0Labels = raw37438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37438 raw37438Labels permutation265 hz
    mixedMoment B raw37438step0 raw37438step0Labels = mixedMoment B raw37438step1 raw37438step1Labels := by
      have ha : raw37438step1 = (fun i j => raw37438step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37438step1 raw37438step0; decide +kernel
      have hl : raw37438step1Labels = raw37438step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37438step0 raw37438step0Labels permutation40 permutation4
    mixedMoment B raw37438step1 raw37438step1Labels = mixedMoment B raw37438step2 raw37438step2Labels := by
      have ha : raw37438step2 = -raw37438step1 := by apply Matrix.ext; change ∀ i j, raw37438step2 i j = -(raw37438step1 i j); unfold raw37438step2 raw37438step1; decide +kernel
      have hl : raw37438step2Labels = raw37438step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node657 node657Labels := by rfl

def raw37439 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -3, 3]]
def raw37439Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -3, 3]]
def raw37439step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37439step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![-1, 0, 1], ![0, -1, 1], ![0, -3, 3]]
def raw37439step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37439step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw37439step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37439step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw37439step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37439 raw37439Labels = mixedMoment B node669 node669Labels := by
  calc
    mixedMoment B raw37439 raw37439Labels = mixedMoment B raw37439step0 raw37439step0Labels := by
      have hz : ∀ j, raw37439 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37439step0 = (fun i j => raw37439 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37439step0 raw37439; decide +kernel
      have hl : raw37439step0Labels = raw37439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37439 raw37439Labels permutation346 hz
    mixedMoment B raw37439step0 raw37439step0Labels = mixedMoment B raw37439step1 raw37439step1Labels := by
      have hz : ∀ j, raw37439step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37439step1 = (fun i j => raw37439step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37439step1 raw37439step0; decide +kernel
      have hl : raw37439step1Labels = raw37439step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37439step0 raw37439step0Labels permutation56 hz
    mixedMoment B raw37439step1 raw37439step1Labels = mixedMoment B raw37439step2 raw37439step2Labels := by
      have ha : raw37439step2 = (fun i j => raw37439step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37439step2 raw37439step1; decide +kernel
      have hl : raw37439step2Labels = raw37439step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37439step1 raw37439step1Labels permutation8 permutation4
    mixedMoment B raw37439step2 raw37439step2Labels = mixedMoment B raw37439step3 raw37439step3Labels := by
      have ha : raw37439step3 = -raw37439step2 := by apply Matrix.ext; change ∀ i j, raw37439step3 i j = -(raw37439step2 i j); unfold raw37439step3 raw37439step2; decide +kernel
      have hl : raw37439step3Labels = raw37439step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node669 node669Labels := by rfl

def raw37440 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -4, 3]]
def raw37440Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -4, 3]]
def raw37440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37440step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![-1, 0, 1], ![-1, 0, 1], ![1, -4, 3]]
def raw37440step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37440step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![0, -1, 1], ![-4, 1, 3]]
def raw37440step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37440step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![0, 1, -1], ![4, -1, -3]]
def raw37440step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37440 raw37440Labels = mixedMoment B node661 node661Labels := by
  calc
    mixedMoment B raw37440 raw37440Labels = mixedMoment B raw37440step0 raw37440step0Labels := by
      have hz : ∀ j, raw37440 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37440step0 = (fun i j => raw37440 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37440step0 raw37440; decide +kernel
      have hl : raw37440step0Labels = raw37440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37440 raw37440Labels permutation346 hz
    mixedMoment B raw37440step0 raw37440step0Labels = mixedMoment B raw37440step1 raw37440step1Labels := by
      have hz : ∀ j, raw37440step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37440step1 = (fun i j => raw37440step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37440step1 raw37440step0; decide +kernel
      have hl : raw37440step1Labels = raw37440step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37440step0 raw37440step0Labels permutation56 hz
    mixedMoment B raw37440step1 raw37440step1Labels = mixedMoment B raw37440step2 raw37440step2Labels := by
      have ha : raw37440step2 = (fun i j => raw37440step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37440step2 raw37440step1; decide +kernel
      have hl : raw37440step2Labels = raw37440step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37440step1 raw37440step1Labels permutation8 permutation4
    mixedMoment B raw37440step2 raw37440step2Labels = mixedMoment B raw37440step3 raw37440step3Labels := by
      have ha : raw37440step3 = -raw37440step2 := by apply Matrix.ext; change ∀ i j, raw37440step3 i j = -(raw37440step2 i j); unfold raw37440step3 raw37440step2; decide +kernel
      have hl : raw37440step3Labels = raw37440step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node661 node661Labels := by rfl

def raw37441 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37441Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37441step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37441step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37441step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw37441step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37441step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw37441step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37441 raw37441Labels = mixedMoment B node1525 node1525Labels := by
  calc
    mixedMoment B raw37441 raw37441Labels = mixedMoment B raw37441step0 raw37441step0Labels := by
      have hz : ∀ j, raw37441 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37441step0 = (fun i j => raw37441 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37441step0 raw37441; decide +kernel
      have hl : raw37441step0Labels = raw37441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37441 raw37441Labels permutation346 hz
    mixedMoment B raw37441step0 raw37441step0Labels = mixedMoment B raw37441step1 raw37441step1Labels := by
      have hz : ∀ j, raw37441step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37441step1 = (fun i j => raw37441step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37441step1 raw37441step0; decide +kernel
      have hl : raw37441step1Labels = raw37441step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37441step0 raw37441step0Labels permutation56 hz
    mixedMoment B raw37441step1 raw37441step1Labels = mixedMoment B raw37441step2 raw37441step2Labels := by
      have ha : raw37441step2 = (fun i j => raw37441step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37441step2 raw37441step1; decide +kernel
      have hl : raw37441step2Labels = raw37441step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37441step1 raw37441step1Labels permutation12 permutation2
    mixedMoment B raw37441step2 raw37441step2Labels = mixedMoment B raw37441step3 raw37441step3Labels := by
      have ha : raw37441step3 = -raw37441step2 := by apply Matrix.ext; change ∀ i j, raw37441step3 i j = -(raw37441step2 i j); unfold raw37441step3 raw37441step2; decide +kernel
      have hl : raw37441step3Labels = raw37441step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1525 node1525Labels := by rfl

def raw37442 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37442Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37442step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw37442step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37442step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37442step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37442 raw37442Labels = mixedMoment B node1511 node1511Labels := by
  calc
    mixedMoment B raw37442 raw37442Labels = mixedMoment B raw37442step0 raw37442step0Labels := by
      have hz : ∀ j, raw37442 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37442step0 = (fun i j => raw37442 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37442step0 raw37442; decide +kernel
      have hl : raw37442step0Labels = raw37442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37442 raw37442Labels permutation346 hz
    mixedMoment B raw37442step0 raw37442step0Labels = mixedMoment B raw37442step1 raw37442step1Labels := by
      have ha : raw37442step1 = (fun i j => raw37442step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37442step1 raw37442step0; decide +kernel
      have hl : raw37442step1Labels = raw37442step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37442step0 raw37442step0Labels permutation40 permutation4
    mixedMoment B raw37442step1 raw37442step1Labels = mixedMoment B raw37442step2 raw37442step2Labels := by
      have ha : raw37442step2 = -raw37442step1 := by apply Matrix.ext; change ∀ i j, raw37442step2 i j = -(raw37442step1 i j); unfold raw37442step2 raw37442step1; decide +kernel
      have hl : raw37442step2Labels = raw37442step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1511 node1511Labels := by rfl

def raw37443 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37443Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37443step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw37443step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37443step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37443step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37443 raw37443Labels = mixedMoment B node1511 node1511Labels := by
  calc
    mixedMoment B raw37443 raw37443Labels = mixedMoment B raw37443step0 raw37443step0Labels := by
      have hz : ∀ j, raw37443 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37443step0 = (fun i j => raw37443 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37443step0 raw37443; decide +kernel
      have hl : raw37443step0Labels = raw37443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37443 raw37443Labels permutation265 hz
    mixedMoment B raw37443step0 raw37443step0Labels = mixedMoment B raw37443step1 raw37443step1Labels := by
      have ha : raw37443step1 = (fun i j => raw37443step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37443step1 raw37443step0; decide +kernel
      have hl : raw37443step1Labels = raw37443step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37443step0 raw37443step0Labels permutation40 permutation4
    mixedMoment B raw37443step1 raw37443step1Labels = mixedMoment B raw37443step2 raw37443step2Labels := by
      have ha : raw37443step2 = -raw37443step1 := by apply Matrix.ext; change ∀ i j, raw37443step2 i j = -(raw37443step1 i j); unfold raw37443step2 raw37443step1; decide +kernel
      have hl : raw37443step2Labels = raw37443step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1511 node1511Labels := by rfl

def raw37444 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37444Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37444step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37444step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, -1, 1], ![-2, 0, 2], ![0, -2, 2]]
def raw37444step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37444step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw37444step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37444step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw37444step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37444 raw37444Labels = mixedMoment B node1525 node1525Labels := by
  calc
    mixedMoment B raw37444 raw37444Labels = mixedMoment B raw37444step0 raw37444step0Labels := by
      have hz : ∀ j, raw37444 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37444step0 = (fun i j => raw37444 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37444step0 raw37444; decide +kernel
      have hl : raw37444step0Labels = raw37444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37444 raw37444Labels permutation346 hz
    mixedMoment B raw37444step0 raw37444step0Labels = mixedMoment B raw37444step1 raw37444step1Labels := by
      have hz : ∀ j, raw37444step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37444step1 = (fun i j => raw37444step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37444step1 raw37444step0; decide +kernel
      have hl : raw37444step1Labels = raw37444step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37444step0 raw37444step0Labels permutation56 hz
    mixedMoment B raw37444step1 raw37444step1Labels = mixedMoment B raw37444step2 raw37444step2Labels := by
      have ha : raw37444step2 = (fun i j => raw37444step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37444step2 raw37444step1; decide +kernel
      have hl : raw37444step2Labels = raw37444step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37444step1 raw37444step1Labels permutation10 permutation4
    mixedMoment B raw37444step2 raw37444step2Labels = mixedMoment B raw37444step3 raw37444step3Labels := by
      have ha : raw37444step3 = -raw37444step2 := by apply Matrix.ext; change ∀ i j, raw37444step3 i j = -(raw37444step2 i j); unfold raw37444step3 raw37444step2; decide +kernel
      have hl : raw37444step3Labels = raw37444step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1525 node1525Labels := by rfl

def raw37445 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, -2, 2]]
def raw37445Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, -2, 2]]
def raw37445step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37445step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![-1, -1, 2], ![0, -2, 2]]
def raw37445step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37445step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw37445step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37445step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37445step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37445 raw37445Labels = mixedMoment B node1519 node1519Labels := by
  calc
    mixedMoment B raw37445 raw37445Labels = mixedMoment B raw37445step0 raw37445step0Labels := by
      have hz : ∀ j, raw37445 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37445step0 = (fun i j => raw37445 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37445step0 raw37445; decide +kernel
      have hl : raw37445step0Labels = raw37445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37445 raw37445Labels permutation346 hz
    mixedMoment B raw37445step0 raw37445step0Labels = mixedMoment B raw37445step1 raw37445step1Labels := by
      have hz : ∀ j, raw37445step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37445step1 = (fun i j => raw37445step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37445step1 raw37445step0; decide +kernel
      have hl : raw37445step1Labels = raw37445step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37445step0 raw37445step0Labels permutation56 hz
    mixedMoment B raw37445step1 raw37445step1Labels = mixedMoment B raw37445step2 raw37445step2Labels := by
      have ha : raw37445step2 = (fun i j => raw37445step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37445step2 raw37445step1; decide +kernel
      have hl : raw37445step2Labels = raw37445step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37445step1 raw37445step1Labels permutation8 permutation4
    mixedMoment B raw37445step2 raw37445step2Labels = mixedMoment B raw37445step3 raw37445step3Labels := by
      have ha : raw37445step3 = -raw37445step2 := by apply Matrix.ext; change ∀ i j, raw37445step3 i j = -(raw37445step2 i j); unfold raw37445step3 raw37445step2; decide +kernel
      have hl : raw37445step3Labels = raw37445step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1519 node1519Labels := by rfl

def raw37446 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2], ![1, -3, 2]]
def raw37446Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2], ![1, -3, 2]]
def raw37446step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37446step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![-2, 0, 2], ![1, -3, 2]]
def raw37446step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37446step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw37446step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37446step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw37446step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37446 raw37446Labels = mixedMoment B node1513 node1513Labels := by
  calc
    mixedMoment B raw37446 raw37446Labels = mixedMoment B raw37446step0 raw37446step0Labels := by
      have hz : ∀ j, raw37446 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37446step0 = (fun i j => raw37446 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37446step0 raw37446; decide +kernel
      have hl : raw37446step0Labels = raw37446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37446 raw37446Labels permutation346 hz
    mixedMoment B raw37446step0 raw37446step0Labels = mixedMoment B raw37446step1 raw37446step1Labels := by
      have hz : ∀ j, raw37446step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37446step1 = (fun i j => raw37446step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37446step1 raw37446step0; decide +kernel
      have hl : raw37446step1Labels = raw37446step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37446step0 raw37446step0Labels permutation56 hz
    mixedMoment B raw37446step1 raw37446step1Labels = mixedMoment B raw37446step2 raw37446step2Labels := by
      have ha : raw37446step2 = (fun i j => raw37446step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37446step2 raw37446step1; decide +kernel
      have hl : raw37446step2Labels = raw37446step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37446step1 raw37446step1Labels permutation8 permutation4
    mixedMoment B raw37446step2 raw37446step2Labels = mixedMoment B raw37446step3 raw37446step3Labels := by
      have ha : raw37446step3 = -raw37446step2 := by apply Matrix.ext; change ∀ i j, raw37446step3 i j = -(raw37446step2 i j); unfold raw37446step3 raw37446step2; decide +kernel
      have hl : raw37446step3Labels = raw37446step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1513 node1513Labels := by rfl

def raw37447 : Matrix (Fin 6) (Fin 2) ℤ := ![![5, -5], ![0, 0], ![0, 0], ![-1, 1], ![-2, 2], ![-2, 2]]
def raw37447Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37447step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![5, -5], ![0, 0], ![-1, 1], ![-2, 2], ![-2, 2]]
def raw37447step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37447step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![5, -5], ![-1, 1], ![-2, 2], ![-2, 2]]
def raw37447step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37447step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![2, -2], ![2, -2]]
def raw37447step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37447 raw37447Labels = mixedMoment B node4059 node4059Labels := by
  calc
    mixedMoment B raw37447 raw37447Labels = mixedMoment B raw37447step0 raw37447step0Labels := by
      have hz : ∀ j, raw37447 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37447step0 = (fun i j => raw37447 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37447step0 raw37447; decide +kernel
      have hl : raw37447step0Labels = raw37447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37447 raw37447Labels permutation346 hz
    mixedMoment B raw37447step0 raw37447step0Labels = mixedMoment B raw37447step1 raw37447step1Labels := by
      have hz : ∀ j, raw37447step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37447step1 = (fun i j => raw37447step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37447step1 raw37447step0; decide +kernel
      have hl : raw37447step1Labels = raw37447step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37447step0 raw37447step0Labels permutation56 hz
    mixedMoment B raw37447step1 raw37447step1Labels = mixedMoment B raw37447step2 raw37447step2Labels := by
      have ha : raw37447step2 = -raw37447step1 := by apply Matrix.ext; change ∀ i j, raw37447step2 i j = -(raw37447step1 i j); unfold raw37447step2 raw37447step1; decide +kernel
      have hl : raw37447step2Labels = raw37447step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4059 node4059Labels := by rfl

def raw37448 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37448Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37448step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37448step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37448step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37448step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw37448step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37448step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37448step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37448 raw37448Labels = mixedMoment B node1519 node1519Labels := by
  calc
    mixedMoment B raw37448 raw37448Labels = mixedMoment B raw37448step0 raw37448step0Labels := by
      have hz : ∀ j, raw37448 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37448step0 = (fun i j => raw37448 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37448step0 raw37448; decide +kernel
      have hl : raw37448step0Labels = raw37448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37448 raw37448Labels permutation346 hz
    mixedMoment B raw37448step0 raw37448step0Labels = mixedMoment B raw37448step1 raw37448step1Labels := by
      have hz : ∀ j, raw37448step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37448step1 = (fun i j => raw37448step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37448step1 raw37448step0; decide +kernel
      have hl : raw37448step1Labels = raw37448step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37448step0 raw37448step0Labels permutation56 hz
    mixedMoment B raw37448step1 raw37448step1Labels = mixedMoment B raw37448step2 raw37448step2Labels := by
      have ha : raw37448step2 = (fun i j => raw37448step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37448step2 raw37448step1; decide +kernel
      have hl : raw37448step2Labels = raw37448step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37448step1 raw37448step1Labels permutation9 permutation2
    mixedMoment B raw37448step2 raw37448step2Labels = mixedMoment B raw37448step3 raw37448step3Labels := by
      have ha : raw37448step3 = -raw37448step2 := by apply Matrix.ext; change ∀ i j, raw37448step3 i j = -(raw37448step2 i j); unfold raw37448step3 raw37448step2; decide +kernel
      have hl : raw37448step3Labels = raw37448step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1519 node1519Labels := by rfl

def raw37449 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37449Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37449step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37449step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37449step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37449step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37449 raw37449Labels = mixedMoment B node1522 node1522Labels := by
  calc
    mixedMoment B raw37449 raw37449Labels = mixedMoment B raw37449step0 raw37449step0Labels := by
      have hz : ∀ j, raw37449 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37449step0 = (fun i j => raw37449 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37449step0 raw37449; decide +kernel
      have hl : raw37449step0Labels = raw37449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37449 raw37449Labels permutation346 hz
    mixedMoment B raw37449step0 raw37449step0Labels = mixedMoment B raw37449step1 raw37449step1Labels := by
      have ha : raw37449step1 = (fun i j => raw37449step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37449step1 raw37449step0; decide +kernel
      have hl : raw37449step1Labels = raw37449step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37449step0 raw37449step0Labels permutation44 permutation4
    mixedMoment B raw37449step1 raw37449step1Labels = mixedMoment B raw37449step2 raw37449step2Labels := by
      have ha : raw37449step2 = -raw37449step1 := by apply Matrix.ext; change ∀ i j, raw37449step2 i j = -(raw37449step1 i j); unfold raw37449step2 raw37449step1; decide +kernel
      have hl : raw37449step2Labels = raw37449step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1522 node1522Labels := by rfl

def raw37450 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37450Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37450step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37450step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37450step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37450step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37450 raw37450Labels = mixedMoment B node1522 node1522Labels := by
  calc
    mixedMoment B raw37450 raw37450Labels = mixedMoment B raw37450step0 raw37450step0Labels := by
      have hz : ∀ j, raw37450 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37450step0 = (fun i j => raw37450 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37450step0 raw37450; decide +kernel
      have hl : raw37450step0Labels = raw37450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37450 raw37450Labels permutation265 hz
    mixedMoment B raw37450step0 raw37450step0Labels = mixedMoment B raw37450step1 raw37450step1Labels := by
      have ha : raw37450step1 = (fun i j => raw37450step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37450step1 raw37450step0; decide +kernel
      have hl : raw37450step1Labels = raw37450step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37450step0 raw37450step0Labels permutation44 permutation4
    mixedMoment B raw37450step1 raw37450step1Labels = mixedMoment B raw37450step2 raw37450step2Labels := by
      have ha : raw37450step2 = -raw37450step1 := by apply Matrix.ext; change ∀ i j, raw37450step2 i j = -(raw37450step1 i j); unfold raw37450step2 raw37450step1; decide +kernel
      have hl : raw37450step2Labels = raw37450step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1522 node1522Labels := by rfl

def raw37451 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37451Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37451step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37451step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![1, -2, 1], ![-2, 0, 2], ![-1, -1, 2]]
def raw37451step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37451step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw37451step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37451step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw37451step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37451 raw37451Labels = mixedMoment B node1526 node1526Labels := by
  calc
    mixedMoment B raw37451 raw37451Labels = mixedMoment B raw37451step0 raw37451step0Labels := by
      have hz : ∀ j, raw37451 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37451step0 = (fun i j => raw37451 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37451step0 raw37451; decide +kernel
      have hl : raw37451step0Labels = raw37451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37451 raw37451Labels permutation346 hz
    mixedMoment B raw37451step0 raw37451step0Labels = mixedMoment B raw37451step1 raw37451step1Labels := by
      have hz : ∀ j, raw37451step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37451step1 = (fun i j => raw37451step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37451step1 raw37451step0; decide +kernel
      have hl : raw37451step1Labels = raw37451step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37451step0 raw37451step0Labels permutation56 hz
    mixedMoment B raw37451step1 raw37451step1Labels = mixedMoment B raw37451step2 raw37451step2Labels := by
      have ha : raw37451step2 = (fun i j => raw37451step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37451step2 raw37451step1; decide +kernel
      have hl : raw37451step2Labels = raw37451step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37451step1 raw37451step1Labels permutation11 permutation4
    mixedMoment B raw37451step2 raw37451step2Labels = mixedMoment B raw37451step3 raw37451step3Labels := by
      have ha : raw37451step3 = -raw37451step2 := by apply Matrix.ext; change ∀ i j, raw37451step3 i j = -(raw37451step2 i j); unfold raw37451step3 raw37451step2; decide +kernel
      have hl : raw37451step3Labels = raw37451step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1526 node1526Labels := by rfl

def raw37452 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37452Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37452step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37452step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37452step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37452step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37452step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw37452step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37452 raw37452Labels = mixedMoment B node1536 node1536Labels := by
  calc
    mixedMoment B raw37452 raw37452Labels = mixedMoment B raw37452step0 raw37452step0Labels := by
      have hz : ∀ j, raw37452 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37452step0 = (fun i j => raw37452 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37452step0 raw37452; decide +kernel
      have hl : raw37452step0Labels = raw37452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37452 raw37452Labels permutation346 hz
    mixedMoment B raw37452step0 raw37452step0Labels = mixedMoment B raw37452step1 raw37452step1Labels := by
      have hz : ∀ j, raw37452step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37452step1 = (fun i j => raw37452step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37452step1 raw37452step0; decide +kernel
      have hl : raw37452step1Labels = raw37452step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37452step0 raw37452step0Labels permutation56 hz
    mixedMoment B raw37452step1 raw37452step1Labels = mixedMoment B raw37452step2 raw37452step2Labels := by
      have ha : raw37452step2 = (fun i j => raw37452step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37452step2 raw37452step1; decide +kernel
      have hl : raw37452step2Labels = raw37452step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37452step1 raw37452step1Labels permutation8 permutation4
    mixedMoment B raw37452step2 raw37452step2Labels = mixedMoment B raw37452step3 raw37452step3Labels := by
      have ha : raw37452step3 = -raw37452step2 := by apply Matrix.ext; change ∀ i j, raw37452step3 i j = -(raw37452step2 i j); unfold raw37452step3 raw37452step2; decide +kernel
      have hl : raw37452step3Labels = raw37452step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1536 node1536Labels := by rfl

def raw37453 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37453Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37453step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37453step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37453step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw37453step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37453 raw37453Labels = mixedMoment B node1536 node1536Labels := by
  calc
    mixedMoment B raw37453 raw37453Labels = mixedMoment B raw37453step0 raw37453step0Labels := by
      have hz : ∀ j, raw37453 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37453step0 = (fun i j => raw37453 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37453step0 raw37453; decide +kernel
      have hl : raw37453step0Labels = raw37453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37453 raw37453Labels permutation346 hz
    mixedMoment B raw37453step0 raw37453step0Labels = mixedMoment B raw37453step1 raw37453step1Labels := by
      have hz : ∀ j, raw37453step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37453step1 = (fun i j => raw37453step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37453step1 raw37453step0; decide +kernel
      have hl : raw37453step1Labels = raw37453step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37453step0 raw37453step0Labels permutation56 hz
    mixedMoment B raw37453step1 raw37453step1Labels = mixedMoment B raw37453step2 raw37453step2Labels := by
      have ha : raw37453step2 = -raw37453step1 := by apply Matrix.ext; change ∀ i j, raw37453step2 i j = -(raw37453step1 i j); unfold raw37453step2 raw37453step1; decide +kernel
      have hl : raw37453step2Labels = raw37453step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1536 node1536Labels := by rfl

def raw37454 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37454Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37454step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37454step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw37454step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37454step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw37454step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37454 raw37454Labels = mixedMoment B node1515 node1515Labels := by
  calc
    mixedMoment B raw37454 raw37454Labels = mixedMoment B raw37454step0 raw37454step0Labels := by
      have hz : ∀ j, raw37454 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37454step0 = (fun i j => raw37454 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37454step0 raw37454; decide +kernel
      have hl : raw37454step0Labels = raw37454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37454 raw37454Labels permutation346 hz
    mixedMoment B raw37454step0 raw37454step0Labels = mixedMoment B raw37454step1 raw37454step1Labels := by
      have ha : raw37454step1 = (fun i j => raw37454step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37454step1 raw37454step0; decide +kernel
      have hl : raw37454step1Labels = raw37454step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37454step0 raw37454step0Labels permutation38 permutation4
    mixedMoment B raw37454step1 raw37454step1Labels = mixedMoment B raw37454step2 raw37454step2Labels := by
      have ha : raw37454step2 = -raw37454step1 := by apply Matrix.ext; change ∀ i j, raw37454step2 i j = -(raw37454step1 i j); unfold raw37454step2 raw37454step1; decide +kernel
      have hl : raw37454step2Labels = raw37454step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1515 node1515Labels := by rfl

def raw37455 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37455Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37455step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37455step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw37455step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37455step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw37455step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37455 raw37455Labels = mixedMoment B node1515 node1515Labels := by
  calc
    mixedMoment B raw37455 raw37455Labels = mixedMoment B raw37455step0 raw37455step0Labels := by
      have hz : ∀ j, raw37455 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37455step0 = (fun i j => raw37455 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37455step0 raw37455; decide +kernel
      have hl : raw37455step0Labels = raw37455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37455 raw37455Labels permutation265 hz
    mixedMoment B raw37455step0 raw37455step0Labels = mixedMoment B raw37455step1 raw37455step1Labels := by
      have ha : raw37455step1 = (fun i j => raw37455step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37455step1 raw37455step0; decide +kernel
      have hl : raw37455step1Labels = raw37455step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37455step0 raw37455step0Labels permutation38 permutation4
    mixedMoment B raw37455step1 raw37455step1Labels = mixedMoment B raw37455step2 raw37455step2Labels := by
      have ha : raw37455step2 = -raw37455step1 := by apply Matrix.ext; change ∀ i j, raw37455step2 i j = -(raw37455step1 i j); unfold raw37455step2 raw37455step1; decide +kernel
      have hl : raw37455step2Labels = raw37455step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1515 node1515Labels := by rfl

def raw37456 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![-1, -1, 2]]
def raw37456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![-1, -1, 2]]
def raw37456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37456step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![0, -2, 2], ![-1, -1, 2]]
def raw37456step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37456step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw37456step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37456step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37456step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37456 raw37456Labels = mixedMoment B node1519 node1519Labels := by
  calc
    mixedMoment B raw37456 raw37456Labels = mixedMoment B raw37456step0 raw37456step0Labels := by
      have hz : ∀ j, raw37456 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37456step0 = (fun i j => raw37456 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37456step0 raw37456; decide +kernel
      have hl : raw37456step0Labels = raw37456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37456 raw37456Labels permutation346 hz
    mixedMoment B raw37456step0 raw37456step0Labels = mixedMoment B raw37456step1 raw37456step1Labels := by
      have hz : ∀ j, raw37456step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37456step1 = (fun i j => raw37456step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37456step1 raw37456step0; decide +kernel
      have hl : raw37456step1Labels = raw37456step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37456step0 raw37456step0Labels permutation56 hz
    mixedMoment B raw37456step1 raw37456step1Labels = mixedMoment B raw37456step2 raw37456step2Labels := by
      have ha : raw37456step2 = (fun i j => raw37456step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37456step2 raw37456step1; decide +kernel
      have hl : raw37456step2Labels = raw37456step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37456step1 raw37456step1Labels permutation9 permutation4
    mixedMoment B raw37456step2 raw37456step2Labels = mixedMoment B raw37456step3 raw37456step3Labels := by
      have ha : raw37456step3 = -raw37456step2 := by apply Matrix.ext; change ∀ i j, raw37456step3 i j = -(raw37456step2 i j); unfold raw37456step3 raw37456step2; decide +kernel
      have hl : raw37456step3Labels = raw37456step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1519 node1519Labels := by rfl

def raw37457 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![-2, 0, 2]]
def raw37457Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![-2, 0, 2]]
def raw37457step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37457step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![0, -1, 1], ![0, -2, 2], ![-2, 0, 2]]
def raw37457step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37457step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw37457step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37457step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw37457step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37457 raw37457Labels = mixedMoment B node1525 node1525Labels := by
  calc
    mixedMoment B raw37457 raw37457Labels = mixedMoment B raw37457step0 raw37457step0Labels := by
      have hz : ∀ j, raw37457 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37457step0 = (fun i j => raw37457 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37457step0 raw37457; decide +kernel
      have hl : raw37457step0Labels = raw37457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37457 raw37457Labels permutation346 hz
    mixedMoment B raw37457step0 raw37457step0Labels = mixedMoment B raw37457step1 raw37457step1Labels := by
      have hz : ∀ j, raw37457step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37457step1 = (fun i j => raw37457step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37457step1 raw37457step0; decide +kernel
      have hl : raw37457step1Labels = raw37457step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37457step0 raw37457step0Labels permutation56 hz
    mixedMoment B raw37457step1 raw37457step1Labels = mixedMoment B raw37457step2 raw37457step2Labels := by
      have ha : raw37457step2 = (fun i j => raw37457step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37457step2 raw37457step1; decide +kernel
      have hl : raw37457step2Labels = raw37457step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37457step1 raw37457step1Labels permutation12 permutation4
    mixedMoment B raw37457step2 raw37457step2Labels = mixedMoment B raw37457step3 raw37457step3Labels := by
      have ha : raw37457step3 = -raw37457step2 := by apply Matrix.ext; change ∀ i j, raw37457step3 i j = -(raw37457step2 i j); unfold raw37457step3 raw37457step2; decide +kernel
      have hl : raw37457step3Labels = raw37457step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1525 node1525Labels := by rfl

def raw37458 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![-2, 0, 2]]
def raw37458Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![-2, 0, 2]]
def raw37458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37458step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw37458step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37458step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37458step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37458 raw37458Labels = mixedMoment B node675 node675Labels := by
  calc
    mixedMoment B raw37458 raw37458Labels = mixedMoment B raw37458step0 raw37458step0Labels := by
      have hz : ∀ j, raw37458 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37458step0 = (fun i j => raw37458 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37458step0 raw37458; decide +kernel
      have hl : raw37458step0Labels = raw37458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37458 raw37458Labels permutation346 hz
    mixedMoment B raw37458step0 raw37458step0Labels = mixedMoment B raw37458step1 raw37458step1Labels := by
      have ha : raw37458step1 = (fun i j => raw37458step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37458step1 raw37458step0; decide +kernel
      have hl : raw37458step1Labels = raw37458step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37458step0 raw37458step0Labels permutation50 permutation4
    mixedMoment B raw37458step1 raw37458step1Labels = mixedMoment B raw37458step2 raw37458step2Labels := by
      have ha : raw37458step2 = -raw37458step1 := by apply Matrix.ext; change ∀ i j, raw37458step2 i j = -(raw37458step1 i j); unfold raw37458step2 raw37458step1; decide +kernel
      have hl : raw37458step2Labels = raw37458step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node675 node675Labels := by rfl

def raw37459 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![-2, 0, 2]]
def raw37459Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![-2, 0, 2]]
def raw37459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37459step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw37459step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37459step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37459step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37459 raw37459Labels = mixedMoment B node675 node675Labels := by
  calc
    mixedMoment B raw37459 raw37459Labels = mixedMoment B raw37459step0 raw37459step0Labels := by
      have hz : ∀ j, raw37459 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37459step0 = (fun i j => raw37459 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37459step0 raw37459; decide +kernel
      have hl : raw37459step0Labels = raw37459Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37459 raw37459Labels permutation265 hz
    mixedMoment B raw37459step0 raw37459step0Labels = mixedMoment B raw37459step1 raw37459step1Labels := by
      have ha : raw37459step1 = (fun i j => raw37459step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37459step1 raw37459step0; decide +kernel
      have hl : raw37459step1Labels = raw37459step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37459step0 raw37459step0Labels permutation50 permutation4
    mixedMoment B raw37459step1 raw37459step1Labels = mixedMoment B raw37459step2 raw37459step2Labels := by
      have ha : raw37459step2 = -raw37459step1 := by apply Matrix.ext; change ∀ i j, raw37459step2 i j = -(raw37459step1 i j); unfold raw37459step2 raw37459step1; decide +kernel
      have hl : raw37459step2Labels = raw37459step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node675 node675Labels := by rfl

def raw37460 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -2, 2], ![-2, 0, 2]]
def raw37460Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -2, 1], ![0, -2, 2], ![-2, 0, 2]]
def raw37460step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37460step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![1, -2, 1], ![0, -2, 2], ![-2, 0, 2]]
def raw37460step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37460step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![0, -2, 2], ![-2, 1, 1], ![-2, 0, 2]]
def raw37460step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37460step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw37460step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37460 raw37460Labels = mixedMoment B node679 node679Labels := by
  calc
    mixedMoment B raw37460 raw37460Labels = mixedMoment B raw37460step0 raw37460step0Labels := by
      have hz : ∀ j, raw37460 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37460step0 = (fun i j => raw37460 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37460step0 raw37460; decide +kernel
      have hl : raw37460step0Labels = raw37460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37460 raw37460Labels permutation346 hz
    mixedMoment B raw37460step0 raw37460step0Labels = mixedMoment B raw37460step1 raw37460step1Labels := by
      have hz : ∀ j, raw37460step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37460step1 = (fun i j => raw37460step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37460step1 raw37460step0; decide +kernel
      have hl : raw37460step1Labels = raw37460step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37460step0 raw37460step0Labels permutation56 hz
    mixedMoment B raw37460step1 raw37460step1Labels = mixedMoment B raw37460step2 raw37460step2Labels := by
      have ha : raw37460step2 = (fun i j => raw37460step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37460step2 raw37460step1; decide +kernel
      have hl : raw37460step2Labels = raw37460step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37460step1 raw37460step1Labels permutation12 permutation4
    mixedMoment B raw37460step2 raw37460step2Labels = mixedMoment B raw37460step3 raw37460step3Labels := by
      have ha : raw37460step3 = -raw37460step2 := by apply Matrix.ext; change ∀ i j, raw37460step3 i j = -(raw37460step2 i j); unfold raw37460step3 raw37460step2; decide +kernel
      have hl : raw37460step3Labels = raw37460step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node679 node679Labels := by rfl

def raw37461 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -3, 2], ![-2, 0, 2]]
def raw37461Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, -1, 1], ![1, -3, 2], ![-2, 0, 2]]
def raw37461step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37461step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![0, -1, 1], ![1, -3, 2], ![-2, 0, 2]]
def raw37461step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37461step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![0, -2, 2], ![-1, 0, 1], ![-3, 1, 2]]
def raw37461step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37461step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, 0, -1], ![3, -1, -2]]
def raw37461step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37461 raw37461Labels = mixedMoment B node678 node678Labels := by
  calc
    mixedMoment B raw37461 raw37461Labels = mixedMoment B raw37461step0 raw37461step0Labels := by
      have hz : ∀ j, raw37461 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37461step0 = (fun i j => raw37461 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37461step0 raw37461; decide +kernel
      have hl : raw37461step0Labels = raw37461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37461 raw37461Labels permutation346 hz
    mixedMoment B raw37461step0 raw37461step0Labels = mixedMoment B raw37461step1 raw37461step1Labels := by
      have hz : ∀ j, raw37461step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37461step1 = (fun i j => raw37461step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37461step1 raw37461step0; decide +kernel
      have hl : raw37461step1Labels = raw37461step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37461step0 raw37461step0Labels permutation56 hz
    mixedMoment B raw37461step1 raw37461step1Labels = mixedMoment B raw37461step2 raw37461step2Labels := by
      have ha : raw37461step2 = (fun i j => raw37461step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37461step2 raw37461step1; decide +kernel
      have hl : raw37461step2Labels = raw37461step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37461step1 raw37461step1Labels permutation12 permutation4
    mixedMoment B raw37461step2 raw37461step2Labels = mixedMoment B raw37461step3 raw37461step3Labels := by
      have ha : raw37461step3 = -raw37461step2 := by apply Matrix.ext; change ∀ i j, raw37461step3 i j = -(raw37461step2 i j); unfold raw37461step3 raw37461step2; decide +kernel
      have hl : raw37461step3Labels = raw37461step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node678 node678Labels := by rfl

def raw37462 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![-1, -1, 2]]
def raw37462Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![-1, -1, 2]]
def raw37462step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37462step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![0, -1, 1], ![0, -2, 2], ![-1, -1, 2]]
def raw37462step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37462step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw37462step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37462step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37462step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37462 raw37462Labels = mixedMoment B node689 node689Labels := by
  calc
    mixedMoment B raw37462 raw37462Labels = mixedMoment B raw37462step0 raw37462step0Labels := by
      have hz : ∀ j, raw37462 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37462step0 = (fun i j => raw37462 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37462step0 raw37462; decide +kernel
      have hl : raw37462step0Labels = raw37462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37462 raw37462Labels permutation346 hz
    mixedMoment B raw37462step0 raw37462step0Labels = mixedMoment B raw37462step1 raw37462step1Labels := by
      have hz : ∀ j, raw37462step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37462step1 = (fun i j => raw37462step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37462step1 raw37462step0; decide +kernel
      have hl : raw37462step1Labels = raw37462step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37462step0 raw37462step0Labels permutation56 hz
    mixedMoment B raw37462step1 raw37462step1Labels = mixedMoment B raw37462step2 raw37462step2Labels := by
      have ha : raw37462step2 = (fun i j => raw37462step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37462step2 raw37462step1; decide +kernel
      have hl : raw37462step2Labels = raw37462step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37462step1 raw37462step1Labels permutation9 permutation4
    mixedMoment B raw37462step2 raw37462step2Labels = mixedMoment B raw37462step3 raw37462step3Labels := by
      have ha : raw37462step3 = -raw37462step2 := by apply Matrix.ext; change ∀ i j, raw37462step3 i j = -(raw37462step2 i j); unfold raw37462step3 raw37462step2; decide +kernel
      have hl : raw37462step3Labels = raw37462step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node689 node689Labels := by rfl

def raw37463 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![-1, -1, 2]]
def raw37463Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![-1, -1, 2]]
def raw37463step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37463step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw37463step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37463step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37463step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37463 raw37463Labels = mixedMoment B node1493 node1493Labels := by
  calc
    mixedMoment B raw37463 raw37463Labels = mixedMoment B raw37463step0 raw37463step0Labels := by
      have hz : ∀ j, raw37463 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37463step0 = (fun i j => raw37463 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37463step0 raw37463; decide +kernel
      have hl : raw37463step0Labels = raw37463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37463 raw37463Labels permutation346 hz
    mixedMoment B raw37463step0 raw37463step0Labels = mixedMoment B raw37463step1 raw37463step1Labels := by
      have ha : raw37463step1 = (fun i j => raw37463step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37463step1 raw37463step0; decide +kernel
      have hl : raw37463step1Labels = raw37463step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37463step0 raw37463step0Labels permutation33 permutation4
    mixedMoment B raw37463step1 raw37463step1Labels = mixedMoment B raw37463step2 raw37463step2Labels := by
      have ha : raw37463step2 = -raw37463step1 := by apply Matrix.ext; change ∀ i j, raw37463step2 i j = -(raw37463step1 i j); unfold raw37463step2 raw37463step1; decide +kernel
      have hl : raw37463step2Labels = raw37463step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1493 node1493Labels := by rfl

def raw37464 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![-1, -1, 2]]
def raw37464Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![-1, -1, 2]]
def raw37464step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37464step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw37464step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37464step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37464step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37464 raw37464Labels = mixedMoment B node1493 node1493Labels := by
  calc
    mixedMoment B raw37464 raw37464Labels = mixedMoment B raw37464step0 raw37464step0Labels := by
      have hz : ∀ j, raw37464 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37464step0 = (fun i j => raw37464 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37464step0 raw37464; decide +kernel
      have hl : raw37464step0Labels = raw37464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37464 raw37464Labels permutation265 hz
    mixedMoment B raw37464step0 raw37464step0Labels = mixedMoment B raw37464step1 raw37464step1Labels := by
      have ha : raw37464step1 = (fun i j => raw37464step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37464step1 raw37464step0; decide +kernel
      have hl : raw37464step1Labels = raw37464step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37464step0 raw37464step0Labels permutation33 permutation4
    mixedMoment B raw37464step1 raw37464step1Labels = mixedMoment B raw37464step2 raw37464step2Labels := by
      have ha : raw37464step2 = -raw37464step1 := by apply Matrix.ext; change ∀ i j, raw37464step2 i j = -(raw37464step1 i j); unfold raw37464step2 raw37464step1; decide +kernel
      have hl : raw37464step2Labels = raw37464step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1493 node1493Labels := by rfl

def raw37465 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37465Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37465step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37465step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37465step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37465step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw37465step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37465 raw37465Labels = mixedMoment B node682 node682Labels := by
  calc
    mixedMoment B raw37465 raw37465Labels = mixedMoment B raw37465step0 raw37465step0Labels := by
      have hz : ∀ j, raw37465 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37465step0 = (fun i j => raw37465 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37465step0 raw37465; decide +kernel
      have hl : raw37465step0Labels = raw37465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37465 raw37465Labels permutation346 hz
    mixedMoment B raw37465step0 raw37465step0Labels = mixedMoment B raw37465step1 raw37465step1Labels := by
      have ha : raw37465step1 = (fun i j => raw37465step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37465step1 raw37465step0; decide +kernel
      have hl : raw37465step1Labels = raw37465step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37465step0 raw37465step0Labels permutation32 permutation4
    mixedMoment B raw37465step1 raw37465step1Labels = mixedMoment B raw37465step2 raw37465step2Labels := by
      have ha : raw37465step2 = -raw37465step1 := by apply Matrix.ext; change ∀ i j, raw37465step2 i j = -(raw37465step1 i j); unfold raw37465step2 raw37465step1; decide +kernel
      have hl : raw37465step2Labels = raw37465step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node682 node682Labels := by rfl

def raw37466 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37466Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37466step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37466step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37466step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37466step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw37466step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37466 raw37466Labels = mixedMoment B node682 node682Labels := by
  calc
    mixedMoment B raw37466 raw37466Labels = mixedMoment B raw37466step0 raw37466step0Labels := by
      have hz : ∀ j, raw37466 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37466step0 = (fun i j => raw37466 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37466step0 raw37466; decide +kernel
      have hl : raw37466step0Labels = raw37466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37466 raw37466Labels permutation265 hz
    mixedMoment B raw37466step0 raw37466step0Labels = mixedMoment B raw37466step1 raw37466step1Labels := by
      have ha : raw37466step1 = (fun i j => raw37466step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37466step1 raw37466step0; decide +kernel
      have hl : raw37466step1Labels = raw37466step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37466step0 raw37466step0Labels permutation32 permutation4
    mixedMoment B raw37466step1 raw37466step1Labels = mixedMoment B raw37466step2 raw37466step2Labels := by
      have ha : raw37466step2 = -raw37466step1 := by apply Matrix.ext; change ∀ i j, raw37466step2 i j = -(raw37466step1 i j); unfold raw37466step2 raw37466step1; decide +kernel
      have hl : raw37466step2Labels = raw37466step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node682 node682Labels := by rfl

def raw37467 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37467Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37467step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37467step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![1, -2, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw37467step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37467step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, -1, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw37467step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37467step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw37467step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37467 raw37467Labels = mixedMoment B node692 node692Labels := by
  calc
    mixedMoment B raw37467 raw37467Labels = mixedMoment B raw37467step0 raw37467step0Labels := by
      have hz : ∀ j, raw37467 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37467step0 = (fun i j => raw37467 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37467step0 raw37467; decide +kernel
      have hl : raw37467step0Labels = raw37467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37467 raw37467Labels permutation346 hz
    mixedMoment B raw37467step0 raw37467step0Labels = mixedMoment B raw37467step1 raw37467step1Labels := by
      have hz : ∀ j, raw37467step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37467step1 = (fun i j => raw37467step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37467step1 raw37467step0; decide +kernel
      have hl : raw37467step1Labels = raw37467step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37467step0 raw37467step0Labels permutation56 hz
    mixedMoment B raw37467step1 raw37467step1Labels = mixedMoment B raw37467step2 raw37467step2Labels := by
      have ha : raw37467step2 = (fun i j => raw37467step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37467step2 raw37467step1; decide +kernel
      have hl : raw37467step2Labels = raw37467step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37467step1 raw37467step1Labels permutation11 permutation4
    mixedMoment B raw37467step2 raw37467step2Labels = mixedMoment B raw37467step3 raw37467step3Labels := by
      have ha : raw37467step3 = -raw37467step2 := by apply Matrix.ext; change ∀ i j, raw37467step3 i j = -(raw37467step2 i j); unfold raw37467step3 raw37467step2; decide +kernel
      have hl : raw37467step3Labels = raw37467step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node692 node692Labels := by rfl

def raw37468 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![0, -2, 2]]
def raw37468Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![0, -2, 2]]
def raw37468step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37468step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![0, -1, 1], ![-1, -1, 2], ![0, -2, 2]]
def raw37468step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37468step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw37468step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37468step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw37468step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37468 raw37468Labels = mixedMoment B node689 node689Labels := by
  calc
    mixedMoment B raw37468 raw37468Labels = mixedMoment B raw37468step0 raw37468step0Labels := by
      have hz : ∀ j, raw37468 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37468step0 = (fun i j => raw37468 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37468step0 raw37468; decide +kernel
      have hl : raw37468step0Labels = raw37468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37468 raw37468Labels permutation346 hz
    mixedMoment B raw37468step0 raw37468step0Labels = mixedMoment B raw37468step1 raw37468step1Labels := by
      have hz : ∀ j, raw37468step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37468step1 = (fun i j => raw37468step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37468step1 raw37468step0; decide +kernel
      have hl : raw37468step1Labels = raw37468step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37468step0 raw37468step0Labels permutation56 hz
    mixedMoment B raw37468step1 raw37468step1Labels = mixedMoment B raw37468step2 raw37468step2Labels := by
      have ha : raw37468step2 = (fun i j => raw37468step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37468step2 raw37468step1; decide +kernel
      have hl : raw37468step2Labels = raw37468step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37468step1 raw37468step1Labels permutation8 permutation4
    mixedMoment B raw37468step2 raw37468step2Labels = mixedMoment B raw37468step3 raw37468step3Labels := by
      have ha : raw37468step3 = -raw37468step2 := by apply Matrix.ext; change ∀ i j, raw37468step3 i j = -(raw37468step2 i j); unfold raw37468step3 raw37468step2; decide +kernel
      have hl : raw37468step3Labels = raw37468step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node689 node689Labels := by rfl

def raw37469 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![-1, -1, 2]]
def raw37469Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2], ![-1, -1, 2]]
def raw37469step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37469step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw37469step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37469step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw37469step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37469 raw37469Labels = mixedMoment B node664 node664Labels := by
  calc
    mixedMoment B raw37469 raw37469Labels = mixedMoment B raw37469step0 raw37469step0Labels := by
      have hz : ∀ j, raw37469 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37469step0 = (fun i j => raw37469 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37469step0 raw37469; decide +kernel
      have hl : raw37469step0Labels = raw37469Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37469 raw37469Labels permutation346 hz
    mixedMoment B raw37469step0 raw37469step0Labels = mixedMoment B raw37469step1 raw37469step1Labels := by
      have ha : raw37469step1 = (fun i j => raw37469step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37469step1 raw37469step0; decide +kernel
      have hl : raw37469step1Labels = raw37469step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37469step0 raw37469step0Labels permutation39 permutation4
    mixedMoment B raw37469step1 raw37469step1Labels = mixedMoment B raw37469step2 raw37469step2Labels := by
      have ha : raw37469step2 = -raw37469step1 := by apply Matrix.ext; change ∀ i j, raw37469step2 i j = -(raw37469step1 i j); unfold raw37469step2 raw37469step1; decide +kernel
      have hl : raw37469step2Labels = raw37469step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node664 node664Labels := by rfl

def raw37470 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2], ![-1, -1, 2]]
def raw37470Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2], ![-1, -1, 2]]
def raw37470step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37470step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw37470step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37470step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw37470step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37470 raw37470Labels = mixedMoment B node664 node664Labels := by
  calc
    mixedMoment B raw37470 raw37470Labels = mixedMoment B raw37470step0 raw37470step0Labels := by
      have hz : ∀ j, raw37470 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37470step0 = (fun i j => raw37470 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37470step0 raw37470; decide +kernel
      have hl : raw37470step0Labels = raw37470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37470 raw37470Labels permutation265 hz
    mixedMoment B raw37470step0 raw37470step0Labels = mixedMoment B raw37470step1 raw37470step1Labels := by
      have ha : raw37470step1 = (fun i j => raw37470step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37470step1 raw37470step0; decide +kernel
      have hl : raw37470step1Labels = raw37470step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37470step0 raw37470step0Labels permutation39 permutation4
    mixedMoment B raw37470step1 raw37470step1Labels = mixedMoment B raw37470step2 raw37470step2Labels := by
      have ha : raw37470step2 = -raw37470step1 := by apply Matrix.ext; change ∀ i j, raw37470step2 i j = -(raw37470step1 i j); unfold raw37470step2 raw37470step1; decide +kernel
      have hl : raw37470step2Labels = raw37470step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node664 node664Labels := by rfl

def raw37471 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -3, 2], ![-1, -1, 2]]
def raw37471Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![-1, 0, 1], ![1, -3, 2], ![-1, -1, 2]]
def raw37471step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37471step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![-1, 0, 1], ![1, -3, 2], ![-1, -1, 2]]
def raw37471step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37471step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, -1, 2], ![-3, 1, 2]]
def raw37471step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37471step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def raw37471step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37471 raw37471Labels = mixedMoment B node670 node670Labels := by
  calc
    mixedMoment B raw37471 raw37471Labels = mixedMoment B raw37471step0 raw37471step0Labels := by
      have hz : ∀ j, raw37471 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37471step0 = (fun i j => raw37471 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37471step0 raw37471; decide +kernel
      have hl : raw37471step0Labels = raw37471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37471 raw37471Labels permutation346 hz
    mixedMoment B raw37471step0 raw37471step0Labels = mixedMoment B raw37471step1 raw37471step1Labels := by
      have hz : ∀ j, raw37471step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37471step1 = (fun i j => raw37471step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37471step1 raw37471step0; decide +kernel
      have hl : raw37471step1Labels = raw37471step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37471step0 raw37471step0Labels permutation56 hz
    mixedMoment B raw37471step1 raw37471step1Labels = mixedMoment B raw37471step2 raw37471step2Labels := by
      have ha : raw37471step2 = (fun i j => raw37471step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37471step2 raw37471step1; decide +kernel
      have hl : raw37471step2Labels = raw37471step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37471step1 raw37471step1Labels permutation9 permutation4
    mixedMoment B raw37471step2 raw37471step2Labels = mixedMoment B raw37471step3 raw37471step3Labels := by
      have ha : raw37471step3 = -raw37471step2 := by apply Matrix.ext; change ∀ i j, raw37471step3 i j = -(raw37471step2 i j); unfold raw37471step3 raw37471step2; decide +kernel
      have hl : raw37471step3Labels = raw37471step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node670 node670Labels := by rfl

def raw37472 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![0, -2, 2]]
def raw37472Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![0, -2, 2]]
def raw37472step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37472step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 4, -5], ![-1, 0, 1], ![0, -2, 2], ![0, -2, 2]]
def raw37472step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37472step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw37472step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37472step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw37472step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37472 raw37472Labels = mixedMoment B node672 node672Labels := by
  calc
    mixedMoment B raw37472 raw37472Labels = mixedMoment B raw37472step0 raw37472step0Labels := by
      have hz : ∀ j, raw37472 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37472step0 = (fun i j => raw37472 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37472step0 raw37472; decide +kernel
      have hl : raw37472step0Labels = raw37472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37472 raw37472Labels permutation346 hz
    mixedMoment B raw37472step0 raw37472step0Labels = mixedMoment B raw37472step1 raw37472step1Labels := by
      have hz : ∀ j, raw37472step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37472step1 = (fun i j => raw37472step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37472step1 raw37472step0; decide +kernel
      have hl : raw37472step1Labels = raw37472step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37472step0 raw37472step0Labels permutation56 hz
    mixedMoment B raw37472step1 raw37472step1Labels = mixedMoment B raw37472step2 raw37472step2Labels := by
      have ha : raw37472step2 = (fun i j => raw37472step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37472step2 raw37472step1; decide +kernel
      have hl : raw37472step2Labels = raw37472step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37472step1 raw37472step1Labels permutation8 permutation4
    mixedMoment B raw37472step2 raw37472step2Labels = mixedMoment B raw37472step3 raw37472step3Labels := by
      have ha : raw37472step3 = -raw37472step2 := by apply Matrix.ext; change ∀ i j, raw37472step3 i j = -(raw37472step2 i j); unfold raw37472step3 raw37472step2; decide +kernel
      have hl : raw37472step3Labels = raw37472step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node672 node672Labels := by rfl

def raw37473 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![0, -2, 2]]
def raw37473Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![0, -2, 2]]
def raw37473step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37473step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw37473step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37473step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw37473step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37473 raw37473Labels = mixedMoment B node1490 node1490Labels := by
  calc
    mixedMoment B raw37473 raw37473Labels = mixedMoment B raw37473step0 raw37473step0Labels := by
      have hz : ∀ j, raw37473 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37473step0 = (fun i j => raw37473 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37473step0 raw37473; decide +kernel
      have hl : raw37473step0Labels = raw37473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37473 raw37473Labels permutation346 hz
    mixedMoment B raw37473step0 raw37473step0Labels = mixedMoment B raw37473step1 raw37473step1Labels := by
      have ha : raw37473step1 = (fun i j => raw37473step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37473step1 raw37473step0; decide +kernel
      have hl : raw37473step1Labels = raw37473step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37473step0 raw37473step0Labels permutation32 permutation4
    mixedMoment B raw37473step1 raw37473step1Labels = mixedMoment B raw37473step2 raw37473step2Labels := by
      have ha : raw37473step2 = -raw37473step1 := by apply Matrix.ext; change ∀ i j, raw37473step2 i j = -(raw37473step1 i j); unfold raw37473step2 raw37473step1; decide +kernel
      have hl : raw37473step2Labels = raw37473step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1490 node1490Labels := by rfl

def raw37474 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![0, -2, 2]]
def raw37474Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![0, -2, 2]]
def raw37474step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37474step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw37474step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37474step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw37474step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37474 raw37474Labels = mixedMoment B node1490 node1490Labels := by
  calc
    mixedMoment B raw37474 raw37474Labels = mixedMoment B raw37474step0 raw37474step0Labels := by
      have hz : ∀ j, raw37474 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37474step0 = (fun i j => raw37474 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37474step0 raw37474; decide +kernel
      have hl : raw37474step0Labels = raw37474Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37474 raw37474Labels permutation265 hz
    mixedMoment B raw37474step0 raw37474step0Labels = mixedMoment B raw37474step1 raw37474step1Labels := by
      have ha : raw37474step1 = (fun i j => raw37474step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37474step1 raw37474step0; decide +kernel
      have hl : raw37474step1Labels = raw37474step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37474step0 raw37474step0Labels permutation32 permutation4
    mixedMoment B raw37474step1 raw37474step1Labels = mixedMoment B raw37474step2 raw37474step2Labels := by
      have ha : raw37474step2 = -raw37474step1 := by apply Matrix.ext; change ∀ i j, raw37474step2 i j = -(raw37474step1 i j); unfold raw37474step2 raw37474step1; decide +kernel
      have hl : raw37474step2Labels = raw37474step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1490 node1490Labels := by rfl

def raw37475 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2], ![0, -2, 2]]
def raw37475Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2], ![0, -2, 2]]
def raw37475step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37475step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 3, -5], ![-2, 1, 1], ![0, -2, 2], ![0, -2, 2]]
def raw37475step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37475step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -2, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw37475step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37475step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![2, 0, -2], ![2, 0, -2]]
def raw37475step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37475 raw37475Labels = mixedMoment B node1500 node1500Labels := by
  calc
    mixedMoment B raw37475 raw37475Labels = mixedMoment B raw37475step0 raw37475step0Labels := by
      have hz : ∀ j, raw37475 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37475step0 = (fun i j => raw37475 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37475step0 raw37475; decide +kernel
      have hl : raw37475step0Labels = raw37475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37475 raw37475Labels permutation346 hz
    mixedMoment B raw37475step0 raw37475step0Labels = mixedMoment B raw37475step1 raw37475step1Labels := by
      have hz : ∀ j, raw37475step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37475step1 = (fun i j => raw37475step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37475step1 raw37475step0; decide +kernel
      have hl : raw37475step1Labels = raw37475step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37475step0 raw37475step0Labels permutation56 hz
    mixedMoment B raw37475step1 raw37475step1Labels = mixedMoment B raw37475step2 raw37475step2Labels := by
      have ha : raw37475step2 = (fun i j => raw37475step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37475step2 raw37475step1; decide +kernel
      have hl : raw37475step2Labels = raw37475step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37475step1 raw37475step1Labels permutation8 permutation4
    mixedMoment B raw37475step2 raw37475step2Labels = mixedMoment B raw37475step3 raw37475step3Labels := by
      have ha : raw37475step3 = -raw37475step2 := by apply Matrix.ext; change ∀ i j, raw37475step3 i j = -(raw37475step2 i j); unfold raw37475step3 raw37475step2; decide +kernel
      have hl : raw37475step3Labels = raw37475step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1500 node1500Labels := by rfl

def raw37476 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw37476Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw37476step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37476step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37476step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37476step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37476step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37476 raw37476Labels = mixedMoment B node1524 node1524Labels := by
  calc
    mixedMoment B raw37476 raw37476Labels = mixedMoment B raw37476step0 raw37476step0Labels := by
      have hz : ∀ j, raw37476 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37476step0 = (fun i j => raw37476 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37476step0 raw37476; decide +kernel
      have hl : raw37476step0Labels = raw37476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37476 raw37476Labels permutation265 hz
    mixedMoment B raw37476step0 raw37476step0Labels = mixedMoment B raw37476step1 raw37476step1Labels := by
      have ha : raw37476step1 = (fun i j => raw37476step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37476step1 raw37476step0; decide +kernel
      have hl : raw37476step1Labels = raw37476step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37476step0 raw37476step0Labels permutation50 permutation2
    mixedMoment B raw37476step1 raw37476step1Labels = mixedMoment B raw37476step2 raw37476step2Labels := by
      have ha : raw37476step2 = -raw37476step1 := by apply Matrix.ext; change ∀ i j, raw37476step2 i j = -(raw37476step1 i j); unfold raw37476step2 raw37476step1; decide +kernel
      have hl : raw37476step2Labels = raw37476step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1524 node1524Labels := by rfl

def raw37477 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw37477Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw37477step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37477step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw37477step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37477 raw37477Labels = mixedMoment B node1501 node1501Labels := by
  calc
    mixedMoment B raw37477 raw37477Labels = mixedMoment B raw37477step0 raw37477step0Labels := by
      have ha : raw37477step0 = (fun i j => raw37477 (permutation184 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37477step0 raw37477; decide +kernel
      have hl : raw37477step0Labels = raw37477Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37477 raw37477Labels permutation184 permutation4
    mixedMoment B raw37477step0 raw37477step0Labels = mixedMoment B raw37477step1 raw37477step1Labels := by
      have ha : raw37477step1 = -raw37477step0 := by apply Matrix.ext; change ∀ i j, raw37477step1 i j = -(raw37477step0 i j); unfold raw37477step1 raw37477step0; decide +kernel
      have hl : raw37477step1Labels = raw37477step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1501 node1501Labels := by rfl

def raw37478 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw37478Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw37478step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw37478step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37478step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37478step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37478 raw37478Labels = mixedMoment B node1507 node1507Labels := by
  calc
    mixedMoment B raw37478 raw37478Labels = mixedMoment B raw37478step0 raw37478step0Labels := by
      have hz : ∀ j, raw37478 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37478step0 = (fun i j => raw37478 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37478step0 raw37478; decide +kernel
      have hl : raw37478step0Labels = raw37478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37478 raw37478Labels permutation265 hz
    mixedMoment B raw37478step0 raw37478step0Labels = mixedMoment B raw37478step1 raw37478step1Labels := by
      have ha : raw37478step1 = (fun i j => raw37478step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37478step1 raw37478step0; decide +kernel
      have hl : raw37478step1Labels = raw37478step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37478step0 raw37478step0Labels permutation40 permutation4
    mixedMoment B raw37478step1 raw37478step1Labels = mixedMoment B raw37478step2 raw37478step2Labels := by
      have ha : raw37478step2 = -raw37478step1 := by apply Matrix.ext; change ∀ i j, raw37478step2 i j = -(raw37478step1 i j); unfold raw37478step2 raw37478step1; decide +kernel
      have hl : raw37478step2Labels = raw37478step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1507 node1507Labels := by rfl

def raw37479 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw37479Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw37479step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37479step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw37479step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37479step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37479step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37479 raw37479Labels = mixedMoment B node1507 node1507Labels := by
  calc
    mixedMoment B raw37479 raw37479Labels = mixedMoment B raw37479step0 raw37479step0Labels := by
      have hz : ∀ j, raw37479 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37479step0 = (fun i j => raw37479 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37479step0 raw37479; decide +kernel
      have hl : raw37479step0Labels = raw37479Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37479 raw37479Labels permutation265 hz
    mixedMoment B raw37479step0 raw37479step0Labels = mixedMoment B raw37479step1 raw37479step1Labels := by
      have ha : raw37479step1 = (fun i j => raw37479step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37479step1 raw37479step0; decide +kernel
      have hl : raw37479step1Labels = raw37479step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37479step0 raw37479step0Labels permutation34 permutation4
    mixedMoment B raw37479step1 raw37479step1Labels = mixedMoment B raw37479step2 raw37479step2Labels := by
      have ha : raw37479step2 = -raw37479step1 := by apply Matrix.ext; change ∀ i j, raw37479step2 i j = -(raw37479step1 i j); unfold raw37479step2 raw37479step1; decide +kernel
      have hl : raw37479step2Labels = raw37479step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1507 node1507Labels := by rfl

def raw37480 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw37480Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw37480step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37480step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw37480step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37480step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37480step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37480 raw37480Labels = mixedMoment B node1507 node1507Labels := by
  calc
    mixedMoment B raw37480 raw37480Labels = mixedMoment B raw37480step0 raw37480step0Labels := by
      have hz : ∀ j, raw37480 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37480step0 = (fun i j => raw37480 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37480step0 raw37480; decide +kernel
      have hl : raw37480step0Labels = raw37480Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37480 raw37480Labels permutation265 hz
    mixedMoment B raw37480step0 raw37480step0Labels = mixedMoment B raw37480step1 raw37480step1Labels := by
      have ha : raw37480step1 = (fun i j => raw37480step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37480step1 raw37480step0; decide +kernel
      have hl : raw37480step1Labels = raw37480step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37480step0 raw37480step0Labels permutation32 permutation4
    mixedMoment B raw37480step1 raw37480step1Labels = mixedMoment B raw37480step2 raw37480step2Labels := by
      have ha : raw37480step2 = -raw37480step1 := by apply Matrix.ext; change ∀ i j, raw37480step2 i j = -(raw37480step1 i j); unfold raw37480step2 raw37480step1; decide +kernel
      have hl : raw37480step2Labels = raw37480step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1507 node1507Labels := by rfl

def raw37481 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw37481Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw37481step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37481step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw37481step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37481step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw37481step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37481 raw37481Labels = mixedMoment B node1503 node1503Labels := by
  calc
    mixedMoment B raw37481 raw37481Labels = mixedMoment B raw37481step0 raw37481step0Labels := by
      have hz : ∀ j, raw37481 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37481step0 = (fun i j => raw37481 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37481step0 raw37481; decide +kernel
      have hl : raw37481step0Labels = raw37481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37481 raw37481Labels permutation265 hz
    mixedMoment B raw37481step0 raw37481step0Labels = mixedMoment B raw37481step1 raw37481step1Labels := by
      have ha : raw37481step1 = (fun i j => raw37481step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37481step1 raw37481step0; decide +kernel
      have hl : raw37481step1Labels = raw37481step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37481step0 raw37481step0Labels permutation32 permutation4
    mixedMoment B raw37481step1 raw37481step1Labels = mixedMoment B raw37481step2 raw37481step2Labels := by
      have ha : raw37481step2 = -raw37481step1 := by apply Matrix.ext; change ∀ i j, raw37481step2 i j = -(raw37481step1 i j); unfold raw37481step2 raw37481step1; decide +kernel
      have hl : raw37481step2Labels = raw37481step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1503 node1503Labels := by rfl

def raw37482 : Matrix (Fin 6) (Fin 2) ℤ := ![![5, -5], ![0, 0], ![-1, 1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw37482Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37482step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![5, -5], ![-1, 1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw37482step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37482step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw37482step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37482 raw37482Labels = mixedMoment B node4057 node4057Labels := by
  calc
    mixedMoment B raw37482 raw37482Labels = mixedMoment B raw37482step0 raw37482step0Labels := by
      have hz : ∀ j, raw37482 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37482step0 = (fun i j => raw37482 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37482step0 raw37482; decide +kernel
      have hl : raw37482step0Labels = raw37482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37482 raw37482Labels permutation265 hz
    mixedMoment B raw37482step0 raw37482step0Labels = mixedMoment B raw37482step1 raw37482step1Labels := by
      have ha : raw37482step1 = -raw37482step0 := by apply Matrix.ext; change ∀ i j, raw37482step1 i j = -(raw37482step0 i j); unfold raw37482step1 raw37482step0; decide +kernel
      have hl : raw37482step1Labels = raw37482step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4057 node4057Labels := by rfl

def raw37483 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw37483Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw37483step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37483step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37483step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37483step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37483step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37483 raw37483Labels = mixedMoment B node1517 node1517Labels := by
  calc
    mixedMoment B raw37483 raw37483Labels = mixedMoment B raw37483step0 raw37483step0Labels := by
      have hz : ∀ j, raw37483 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37483step0 = (fun i j => raw37483 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37483step0 raw37483; decide +kernel
      have hl : raw37483step0Labels = raw37483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37483 raw37483Labels permutation265 hz
    mixedMoment B raw37483step0 raw37483step0Labels = mixedMoment B raw37483step1 raw37483step1Labels := by
      have ha : raw37483step1 = (fun i j => raw37483step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37483step1 raw37483step0; decide +kernel
      have hl : raw37483step1Labels = raw37483step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37483step0 raw37483step0Labels permutation44 permutation2
    mixedMoment B raw37483step1 raw37483step1Labels = mixedMoment B raw37483step2 raw37483step2Labels := by
      have ha : raw37483step2 = -raw37483step1 := by apply Matrix.ext; change ∀ i j, raw37483step2 i j = -(raw37483step1 i j); unfold raw37483step2 raw37483step1; decide +kernel
      have hl : raw37483step2Labels = raw37483step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1517 node1517Labels := by rfl

def raw37484 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw37484Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37484step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37484step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37484step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37484 raw37484Labels = mixedMoment B node1504 node1504Labels := by
  calc
    mixedMoment B raw37484 raw37484Labels = mixedMoment B raw37484step0 raw37484step0Labels := by
      have ha : raw37484step0 = (fun i j => raw37484 (permutation182 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37484step0 raw37484; decide +kernel
      have hl : raw37484step0Labels = raw37484Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37484 raw37484Labels permutation182 permutation4
    mixedMoment B raw37484step0 raw37484step0Labels = mixedMoment B raw37484step1 raw37484step1Labels := by
      have ha : raw37484step1 = -raw37484step0 := by apply Matrix.ext; change ∀ i j, raw37484step1 i j = -(raw37484step0 i j); unfold raw37484step1 raw37484step0; decide +kernel
      have hl : raw37484step1Labels = raw37484step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1504 node1504Labels := by rfl

def raw37485 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw37485Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw37485step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37485step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37485step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37485step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37485step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37485 raw37485Labels = mixedMoment B node1517 node1517Labels := by
  calc
    mixedMoment B raw37485 raw37485Labels = mixedMoment B raw37485step0 raw37485step0Labels := by
      have hz : ∀ j, raw37485 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37485step0 = (fun i j => raw37485 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37485step0 raw37485; decide +kernel
      have hl : raw37485step0Labels = raw37485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37485 raw37485Labels permutation265 hz
    mixedMoment B raw37485step0 raw37485step0Labels = mixedMoment B raw37485step1 raw37485step1Labels := by
      have ha : raw37485step1 = (fun i j => raw37485step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37485step1 raw37485step0; decide +kernel
      have hl : raw37485step1Labels = raw37485step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37485step0 raw37485step0Labels permutation38 permutation4
    mixedMoment B raw37485step1 raw37485step1Labels = mixedMoment B raw37485step2 raw37485step2Labels := by
      have ha : raw37485step2 = -raw37485step1 := by apply Matrix.ext; change ∀ i j, raw37485step2 i j = -(raw37485step1 i j); unfold raw37485step2 raw37485step1; decide +kernel
      have hl : raw37485step2Labels = raw37485step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1517 node1517Labels := by rfl

def raw37486 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw37486Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw37486step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37486step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37486step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37486step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37486step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37486 raw37486Labels = mixedMoment B node1517 node1517Labels := by
  calc
    mixedMoment B raw37486 raw37486Labels = mixedMoment B raw37486step0 raw37486step0Labels := by
      have hz : ∀ j, raw37486 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37486step0 = (fun i j => raw37486 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37486step0 raw37486; decide +kernel
      have hl : raw37486step0Labels = raw37486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37486 raw37486Labels permutation265 hz
    mixedMoment B raw37486step0 raw37486step0Labels = mixedMoment B raw37486step1 raw37486step1Labels := by
      have ha : raw37486step1 = (fun i j => raw37486step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37486step1 raw37486step0; decide +kernel
      have hl : raw37486step1Labels = raw37486step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37486step0 raw37486step0Labels permutation32 permutation4
    mixedMoment B raw37486step1 raw37486step1Labels = mixedMoment B raw37486step2 raw37486step2Labels := by
      have ha : raw37486step2 = -raw37486step1 := by apply Matrix.ext; change ∀ i j, raw37486step2 i j = -(raw37486step1 i j); unfold raw37486step2 raw37486step1; decide +kernel
      have hl : raw37486step2Labels = raw37486step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1517 node1517Labels := by rfl

def raw37487 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw37487Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw37487step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37487step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37487step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37487step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37487 raw37487Labels = mixedMoment B node1508 node1508Labels := by
  calc
    mixedMoment B raw37487 raw37487Labels = mixedMoment B raw37487step0 raw37487step0Labels := by
      have hz : ∀ j, raw37487 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37487step0 = (fun i j => raw37487 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37487step0 raw37487; decide +kernel
      have hl : raw37487step0Labels = raw37487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37487 raw37487Labels permutation265 hz
    mixedMoment B raw37487step0 raw37487step0Labels = mixedMoment B raw37487step1 raw37487step1Labels := by
      have ha : raw37487step1 = (fun i j => raw37487step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37487step1 raw37487step0; decide +kernel
      have hl : raw37487step1Labels = raw37487step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37487step0 raw37487step0Labels permutation33 permutation4
    mixedMoment B raw37487step1 raw37487step1Labels = mixedMoment B raw37487step2 raw37487step2Labels := by
      have ha : raw37487step2 = -raw37487step1 := by apply Matrix.ext; change ∀ i j, raw37487step2 i j = -(raw37487step1 i j); unfold raw37487step2 raw37487step1; decide +kernel
      have hl : raw37487step2Labels = raw37487step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1508 node1508Labels := by rfl

def raw37488 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw37488Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw37488step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw37488step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37488step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37488step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37488 raw37488Labels = mixedMoment B node1507 node1507Labels := by
  calc
    mixedMoment B raw37488 raw37488Labels = mixedMoment B raw37488step0 raw37488step0Labels := by
      have hz : ∀ j, raw37488 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37488step0 = (fun i j => raw37488 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37488step0 raw37488; decide +kernel
      have hl : raw37488step0Labels = raw37488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37488 raw37488Labels permutation265 hz
    mixedMoment B raw37488step0 raw37488step0Labels = mixedMoment B raw37488step1 raw37488step1Labels := by
      have ha : raw37488step1 = (fun i j => raw37488step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37488step1 raw37488step0; decide +kernel
      have hl : raw37488step1Labels = raw37488step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37488step0 raw37488step0Labels permutation40 permutation2
    mixedMoment B raw37488step1 raw37488step1Labels = mixedMoment B raw37488step2 raw37488step2Labels := by
      have ha : raw37488step2 = -raw37488step1 := by apply Matrix.ext; change ∀ i j, raw37488step2 i j = -(raw37488step1 i j); unfold raw37488step2 raw37488step1; decide +kernel
      have hl : raw37488step2Labels = raw37488step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1507 node1507Labels := by rfl

def raw37489 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw37489Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37489step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37489step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37489step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37489step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37489 raw37489Labels = mixedMoment B node1510 node1510Labels := by
  calc
    mixedMoment B raw37489 raw37489Labels = mixedMoment B raw37489step0 raw37489step0Labels := by
      have ha : raw37489step0 = (fun i j => raw37489 (permutation194 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37489step0 raw37489; decide +kernel
      have hl : raw37489step0Labels = raw37489Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37489 raw37489Labels permutation194 permutation4
    mixedMoment B raw37489step0 raw37489step0Labels = mixedMoment B raw37489step1 raw37489step1Labels := by
      have ha : raw37489step1 = -raw37489step0 := by apply Matrix.ext; change ∀ i j, raw37489step1 i j = -(raw37489step0 i j); unfold raw37489step1 raw37489step0; decide +kernel
      have hl : raw37489step1Labels = raw37489step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1510 node1510Labels := by rfl

def raw37490 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw37490Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw37490step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37490step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37490step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37490step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37490 raw37490Labels = mixedMoment B node1524 node1524Labels := by
  calc
    mixedMoment B raw37490 raw37490Labels = mixedMoment B raw37490step0 raw37490step0Labels := by
      have hz : ∀ j, raw37490 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37490step0 = (fun i j => raw37490 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37490step0 raw37490; decide +kernel
      have hl : raw37490step0Labels = raw37490Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37490 raw37490Labels permutation265 hz
    mixedMoment B raw37490step0 raw37490step0Labels = mixedMoment B raw37490step1 raw37490step1Labels := by
      have ha : raw37490step1 = (fun i j => raw37490step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37490step1 raw37490step0; decide +kernel
      have hl : raw37490step1Labels = raw37490step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37490step0 raw37490step0Labels permutation50 permutation4
    mixedMoment B raw37490step1 raw37490step1Labels = mixedMoment B raw37490step2 raw37490step2Labels := by
      have ha : raw37490step2 = -raw37490step1 := by apply Matrix.ext; change ∀ i j, raw37490step2 i j = -(raw37490step1 i j); unfold raw37490step2 raw37490step1; decide +kernel
      have hl : raw37490step2Labels = raw37490step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1524 node1524Labels := by rfl

def raw37491 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw37491Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw37491step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw37491step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37491step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw37491step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37491 raw37491Labels = mixedMoment B node1512 node1512Labels := by
  calc
    mixedMoment B raw37491 raw37491Labels = mixedMoment B raw37491step0 raw37491step0Labels := by
      have hz : ∀ j, raw37491 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37491step0 = (fun i j => raw37491 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37491step0 raw37491; decide +kernel
      have hl : raw37491step0Labels = raw37491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37491 raw37491Labels permutation265 hz
    mixedMoment B raw37491step0 raw37491step0Labels = mixedMoment B raw37491step1 raw37491step1Labels := by
      have ha : raw37491step1 = (fun i j => raw37491step0 (permutation37 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37491step1 raw37491step0; decide +kernel
      have hl : raw37491step1Labels = raw37491step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37491step0 raw37491step0Labels permutation37 permutation4
    mixedMoment B raw37491step1 raw37491step1Labels = mixedMoment B raw37491step2 raw37491step2Labels := by
      have ha : raw37491step2 = -raw37491step1 := by apply Matrix.ext; change ∀ i j, raw37491step2 i j = -(raw37491step1 i j); unfold raw37491step2 raw37491step1; decide +kernel
      have hl : raw37491step2Labels = raw37491step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1512 node1512Labels := by rfl

def raw37492 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw37492Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw37492step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw37492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37492step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw37492step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37492 raw37492Labels = mixedMoment B node1512 node1512Labels := by
  calc
    mixedMoment B raw37492 raw37492Labels = mixedMoment B raw37492step0 raw37492step0Labels := by
      have hz : ∀ j, raw37492 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37492step0 = (fun i j => raw37492 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37492step0 raw37492; decide +kernel
      have hl : raw37492step0Labels = raw37492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37492 raw37492Labels permutation265 hz
    mixedMoment B raw37492step0 raw37492step0Labels = mixedMoment B raw37492step1 raw37492step1Labels := by
      have ha : raw37492step1 = (fun i j => raw37492step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37492step1 raw37492step0; decide +kernel
      have hl : raw37492step1Labels = raw37492step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37492step0 raw37492step0Labels permutation36 permutation4
    mixedMoment B raw37492step1 raw37492step1Labels = mixedMoment B raw37492step2 raw37492step2Labels := by
      have ha : raw37492step2 = -raw37492step1 := by apply Matrix.ext; change ∀ i j, raw37492step2 i j = -(raw37492step1 i j); unfold raw37492step2 raw37492step1; decide +kernel
      have hl : raw37492step2Labels = raw37492step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1512 node1512Labels := by rfl

def raw37493 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw37493Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 1, -5], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37493step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37493step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37493step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37493 raw37493Labels = mixedMoment B node674 node674Labels := by
  calc
    mixedMoment B raw37493 raw37493Labels = mixedMoment B raw37493step0 raw37493step0Labels := by
      have ha : raw37493step0 = (fun i j => raw37493 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37493step0 raw37493; decide +kernel
      have hl : raw37493step0Labels = raw37493Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37493 raw37493Labels permutation246 permutation4
    mixedMoment B raw37493step0 raw37493step0Labels = mixedMoment B raw37493step1 raw37493step1Labels := by
      have ha : raw37493step1 = -raw37493step0 := by apply Matrix.ext; change ∀ i j, raw37493step1 i j = -(raw37493step0 i j); unfold raw37493step1 raw37493step0; decide +kernel
      have hl : raw37493step1Labels = raw37493step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node674 node674Labels := by rfl

def raw37494 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw37494Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw37494step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw37494step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37494step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37494step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37494 raw37494Labels = mixedMoment B node677 node677Labels := by
  calc
    mixedMoment B raw37494 raw37494Labels = mixedMoment B raw37494step0 raw37494step0Labels := by
      have hz : ∀ j, raw37494 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37494step0 = (fun i j => raw37494 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37494step0 raw37494; decide +kernel
      have hl : raw37494step0Labels = raw37494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37494 raw37494Labels permutation265 hz
    mixedMoment B raw37494step0 raw37494step0Labels = mixedMoment B raw37494step1 raw37494step1Labels := by
      have ha : raw37494step1 = (fun i j => raw37494step0 (permutation53 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37494step1 raw37494step0; decide +kernel
      have hl : raw37494step1Labels = raw37494step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37494step0 raw37494step0Labels permutation53 permutation4
    mixedMoment B raw37494step1 raw37494step1Labels = mixedMoment B raw37494step2 raw37494step2Labels := by
      have ha : raw37494step2 = -raw37494step1 := by apply Matrix.ext; change ∀ i j, raw37494step2 i j = -(raw37494step1 i j); unfold raw37494step2 raw37494step1; decide +kernel
      have hl : raw37494step2Labels = raw37494step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node677 node677Labels := by rfl

def raw37495 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw37495Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw37495step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw37495step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37495step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37495step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37495 raw37495Labels = mixedMoment B node677 node677Labels := by
  calc
    mixedMoment B raw37495 raw37495Labels = mixedMoment B raw37495step0 raw37495step0Labels := by
      have hz : ∀ j, raw37495 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37495step0 = (fun i j => raw37495 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37495step0 raw37495; decide +kernel
      have hl : raw37495step0Labels = raw37495Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37495 raw37495Labels permutation265 hz
    mixedMoment B raw37495step0 raw37495step0Labels = mixedMoment B raw37495step1 raw37495step1Labels := by
      have ha : raw37495step1 = (fun i j => raw37495step0 (permutation51 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37495step1 raw37495step0; decide +kernel
      have hl : raw37495step1Labels = raw37495step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37495step0 raw37495step0Labels permutation51 permutation4
    mixedMoment B raw37495step1 raw37495step1Labels = mixedMoment B raw37495step2 raw37495step2Labels := by
      have ha : raw37495step2 = -raw37495step1 := by apply Matrix.ext; change ∀ i j, raw37495step2 i j = -(raw37495step1 i j); unfold raw37495step2 raw37495step1; decide +kernel
      have hl : raw37495step2Labels = raw37495step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node677 node677Labels := by rfl

def raw37496 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw37496Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw37496step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw37496step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37496step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37496step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37496 raw37496Labels = mixedMoment B node677 node677Labels := by
  calc
    mixedMoment B raw37496 raw37496Labels = mixedMoment B raw37496step0 raw37496step0Labels := by
      have hz : ∀ j, raw37496 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37496step0 = (fun i j => raw37496 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37496step0 raw37496; decide +kernel
      have hl : raw37496step0Labels = raw37496Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37496 raw37496Labels permutation265 hz
    mixedMoment B raw37496step0 raw37496step0Labels = mixedMoment B raw37496step1 raw37496step1Labels := by
      have ha : raw37496step1 = (fun i j => raw37496step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37496step1 raw37496step0; decide +kernel
      have hl : raw37496step1Labels = raw37496step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37496step0 raw37496step0Labels permutation50 permutation4
    mixedMoment B raw37496step1 raw37496step1Labels = mixedMoment B raw37496step2 raw37496step2Labels := by
      have ha : raw37496step2 = -raw37496step1 := by apply Matrix.ext; change ∀ i j, raw37496step2 i j = -(raw37496step1 i j); unfold raw37496step2 raw37496step1; decide +kernel
      have hl : raw37496step2Labels = raw37496step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node677 node677Labels := by rfl

def raw37497 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw37497Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw37497step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37497step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37497step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37497 raw37497Labels = mixedMoment B node687 node687Labels := by
  calc
    mixedMoment B raw37497 raw37497Labels = mixedMoment B raw37497step0 raw37497step0Labels := by
      have hz : ∀ j, raw37497 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37497step0 = (fun i j => raw37497 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37497step0 raw37497; decide +kernel
      have hl : raw37497step0Labels = raw37497Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37497 raw37497Labels permutation265 hz
    mixedMoment B raw37497step0 raw37497step0Labels = mixedMoment B raw37497step1 raw37497step1Labels := by
      have ha : raw37497step1 = (fun i j => raw37497step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37497step1 raw37497step0; decide +kernel
      have hl : raw37497step1Labels = raw37497step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37497step0 raw37497step0Labels permutation32 permutation4
    mixedMoment B raw37497step1 raw37497step1Labels = mixedMoment B raw37497step2 raw37497step2Labels := by
      have ha : raw37497step2 = -raw37497step1 := by apply Matrix.ext; change ∀ i j, raw37497step2 i j = -(raw37497step1 i j); unfold raw37497step2 raw37497step1; decide +kernel
      have hl : raw37497step2Labels = raw37497step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node687 node687Labels := by rfl

def raw37498 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw37498Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37498step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37498step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37498 raw37498Labels = mixedMoment B node1491 node1491Labels := by
  calc
    mixedMoment B raw37498 raw37498Labels = mixedMoment B raw37498step0 raw37498step0Labels := by
      have ha : raw37498step0 = (fun i j => raw37498 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37498step0 raw37498; decide +kernel
      have hl : raw37498step0Labels = raw37498Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37498 raw37498Labels permutation152 permutation4
    mixedMoment B raw37498step0 raw37498step0Labels = mixedMoment B raw37498step1 raw37498step1Labels := by
      have ha : raw37498step1 = -raw37498step0 := by apply Matrix.ext; change ∀ i j, raw37498step1 i j = -(raw37498step0 i j); unfold raw37498step1 raw37498step0; decide +kernel
      have hl : raw37498step1Labels = raw37498step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1491 node1491Labels := by rfl

def raw37499 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 3, -5], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37499Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 3, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37499step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37499step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37499step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37499step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37499step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37499 raw37499Labels = mixedMoment B node1517 node1517Labels := by
  calc
    mixedMoment B raw37499 raw37499Labels = mixedMoment B raw37499step0 raw37499step0Labels := by
      have hz : ∀ j, raw37499 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37499step0 = (fun i j => raw37499 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37499step0 raw37499; decide +kernel
      have hl : raw37499step0Labels = raw37499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37499 raw37499Labels permutation265 hz
    mixedMoment B raw37499step0 raw37499step0Labels = mixedMoment B raw37499step1 raw37499step1Labels := by
      have ha : raw37499step1 = (fun i j => raw37499step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37499step1 raw37499step0; decide +kernel
      have hl : raw37499step1Labels = raw37499step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37499step0 raw37499step0Labels permutation44 permutation4
    mixedMoment B raw37499step1 raw37499step1Labels = mixedMoment B raw37499step2 raw37499step2Labels := by
      have ha : raw37499step2 = -raw37499step1 := by apply Matrix.ext; change ∀ i j, raw37499step2 i j = -(raw37499step1 i j); unfold raw37499step2 raw37499step1; decide +kernel
      have hl : raw37499step2Labels = raw37499step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1517 node1517Labels := by rfl

def raw37500 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37500Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37500step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37500step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37500 raw37500Labels = mixedMoment B node662 node662Labels := by
  calc
    mixedMoment B raw37500 raw37500Labels = mixedMoment B raw37500step0 raw37500step0Labels := by
      have ha : raw37500step0 = (fun i j => raw37500 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37500step0 raw37500; decide +kernel
      have hl : raw37500step0Labels = raw37500Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37500 raw37500Labels permutation224 permutation4
    mixedMoment B raw37500step0 raw37500step0Labels = mixedMoment B raw37500step1 raw37500step1Labels := by
      have ha : raw37500step1 = -raw37500step0 := by apply Matrix.ext; change ∀ i j, raw37500step1 i j = -(raw37500step0 i j); unfold raw37500step1 raw37500step0; decide +kernel
      have hl : raw37500step1Labels = raw37500step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node662 node662Labels := by rfl

def raw37501 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37501Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37501step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37501step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37501step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37501step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37501 raw37501Labels = mixedMoment B node668 node668Labels := by
  calc
    mixedMoment B raw37501 raw37501Labels = mixedMoment B raw37501step0 raw37501step0Labels := by
      have hz : ∀ j, raw37501 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37501step0 = (fun i j => raw37501 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37501step0 raw37501; decide +kernel
      have hl : raw37501step0Labels = raw37501Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37501 raw37501Labels permutation265 hz
    mixedMoment B raw37501step0 raw37501step0Labels = mixedMoment B raw37501step1 raw37501step1Labels := by
      have ha : raw37501step1 = (fun i j => raw37501step0 (permutation47 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37501step1 raw37501step0; decide +kernel
      have hl : raw37501step1Labels = raw37501step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37501step0 raw37501step0Labels permutation47 permutation4
    mixedMoment B raw37501step1 raw37501step1Labels = mixedMoment B raw37501step2 raw37501step2Labels := by
      have ha : raw37501step2 = -raw37501step1 := by apply Matrix.ext; change ∀ i j, raw37501step2 i j = -(raw37501step1 i j); unfold raw37501step2 raw37501step1; decide +kernel
      have hl : raw37501step2Labels = raw37501step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node668 node668Labels := by rfl

def raw37502 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37502Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37502step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37502step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37502step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37502 raw37502Labels = mixedMoment B node668 node668Labels := by
  calc
    mixedMoment B raw37502 raw37502Labels = mixedMoment B raw37502step0 raw37502step0Labels := by
      have hz : ∀ j, raw37502 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37502step0 = (fun i j => raw37502 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37502step0 raw37502; decide +kernel
      have hl : raw37502step0Labels = raw37502Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37502 raw37502Labels permutation265 hz
    mixedMoment B raw37502step0 raw37502step0Labels = mixedMoment B raw37502step1 raw37502step1Labels := by
      have ha : raw37502step1 = (fun i j => raw37502step0 (permutation45 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37502step1 raw37502step0; decide +kernel
      have hl : raw37502step1Labels = raw37502step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37502step0 raw37502step0Labels permutation45 permutation4
    mixedMoment B raw37502step1 raw37502step1Labels = mixedMoment B raw37502step2 raw37502step2Labels := by
      have ha : raw37502step2 = -raw37502step1 := by apply Matrix.ext; change ∀ i j, raw37502step2 i j = -(raw37502step1 i j); unfold raw37502step2 raw37502step1; decide +kernel
      have hl : raw37502step2Labels = raw37502step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node668 node668Labels := by rfl

def raw37503 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 4, -5], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw37503Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 4, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw37503step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw37503step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw37503step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37503step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37503 raw37503Labels = mixedMoment B node667 node667Labels := by
  calc
    mixedMoment B raw37503 raw37503Labels = mixedMoment B raw37503step0 raw37503step0Labels := by
      have hz : ∀ j, raw37503 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37503step0 = (fun i j => raw37503 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37503step0 raw37503; decide +kernel
      have hl : raw37503step0Labels = raw37503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37503 raw37503Labels permutation265 hz
    mixedMoment B raw37503step0 raw37503step0Labels = mixedMoment B raw37503step1 raw37503step1Labels := by
      have ha : raw37503step1 = (fun i j => raw37503step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37503step1 raw37503step0; decide +kernel
      have hl : raw37503step1Labels = raw37503step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37503step0 raw37503step0Labels permutation44 permutation4
    mixedMoment B raw37503step1 raw37503step1Labels = mixedMoment B raw37503step2 raw37503step2Labels := by
      have ha : raw37503step2 = -raw37503step1 := by apply Matrix.ext; change ∀ i j, raw37503step2 i j = -(raw37503step1 i j); unfold raw37503step2 raw37503step1; decide +kernel
      have hl : raw37503step2Labels = raw37503step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node667 node667Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
