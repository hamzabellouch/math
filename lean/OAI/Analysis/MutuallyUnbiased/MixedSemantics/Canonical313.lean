import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.ExtraNodes

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw40064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw40064Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw40064step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40064step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw40064step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40064step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40064step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40064 raw40064Labels = mixedMoment B node401 node401Labels := by
  calc
    mixedMoment B raw40064 raw40064Labels = mixedMoment B raw40064step0 raw40064step0Labels := by
      have hz : ∀ j, raw40064 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40064step0 = (fun i j => raw40064 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40064step0 raw40064; decide +kernel
      have hl : raw40064step0Labels = raw40064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40064 raw40064Labels permutation346 hz
    mixedMoment B raw40064step0 raw40064step0Labels = mixedMoment B raw40064step1 raw40064step1Labels := by
      have ha : raw40064step1 = (fun i j => raw40064step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40064step1 raw40064step0; decide +kernel
      have hl : raw40064step1Labels = raw40064step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40064step0 raw40064step0Labels permutation36 permutation4
    mixedMoment B raw40064step1 raw40064step1Labels = mixedMoment B raw40064step2 raw40064step2Labels := by
      have ha : raw40064step2 = -raw40064step1 := by apply Matrix.ext; change ∀ i j, raw40064step2 i j = -(raw40064step1 i j); unfold raw40064step2 raw40064step1; decide +kernel
      have hl : raw40064step2Labels = raw40064step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node401 node401Labels := by rfl

def raw40065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw40065Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw40065step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw40065step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40065step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw40065step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40065 raw40065Labels = mixedMoment B node361 node361Labels := by
  calc
    mixedMoment B raw40065 raw40065Labels = mixedMoment B raw40065step0 raw40065step0Labels := by
      have hz : ∀ j, raw40065 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40065step0 = (fun i j => raw40065 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40065step0 raw40065; decide +kernel
      have hl : raw40065step0Labels = raw40065Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40065 raw40065Labels permutation346 hz
    mixedMoment B raw40065step0 raw40065step0Labels = mixedMoment B raw40065step1 raw40065step1Labels := by
      have ha : raw40065step1 = (fun i j => raw40065step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40065step1 raw40065step0; decide +kernel
      have hl : raw40065step1Labels = raw40065step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40065step0 raw40065step0Labels permutation50 permutation4
    mixedMoment B raw40065step1 raw40065step1Labels = mixedMoment B raw40065step2 raw40065step2Labels := by
      have ha : raw40065step2 = -raw40065step1 := by apply Matrix.ext; change ∀ i j, raw40065step2 i j = -(raw40065step1 i j); unfold raw40065step2 raw40065step1; decide +kernel
      have hl : raw40065step2Labels = raw40065step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node361 node361Labels := by rfl

def raw40066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw40066Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw40066step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40066step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40066step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40066step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40066step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40066 raw40066Labels = mixedMoment B node378 node378Labels := by
  calc
    mixedMoment B raw40066 raw40066Labels = mixedMoment B raw40066step0 raw40066step0Labels := by
      have hz : ∀ j, raw40066 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40066step0 = (fun i j => raw40066 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40066step0 raw40066; decide +kernel
      have hl : raw40066step0Labels = raw40066Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40066 raw40066Labels permutation346 hz
    mixedMoment B raw40066step0 raw40066step0Labels = mixedMoment B raw40066step1 raw40066step1Labels := by
      have ha : raw40066step1 = (fun i j => raw40066step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40066step1 raw40066step0; decide +kernel
      have hl : raw40066step1Labels = raw40066step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40066step0 raw40066step0Labels permutation44 permutation4
    mixedMoment B raw40066step1 raw40066step1Labels = mixedMoment B raw40066step2 raw40066step2Labels := by
      have ha : raw40066step2 = -raw40066step1 := by apply Matrix.ext; change ∀ i j, raw40066step2 i j = -(raw40066step1 i j); unfold raw40066step2 raw40066step1; decide +kernel
      have hl : raw40066step2Labels = raw40066step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node378 node378Labels := by rfl

def raw40067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw40067Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw40067step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40067step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw40067step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40067step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40067step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40067 raw40067Labels = mixedMoment B node403 node403Labels := by
  calc
    mixedMoment B raw40067 raw40067Labels = mixedMoment B raw40067step0 raw40067step0Labels := by
      have hz : ∀ j, raw40067 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40067step0 = (fun i j => raw40067 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40067step0 raw40067; decide +kernel
      have hl : raw40067step0Labels = raw40067Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40067 raw40067Labels permutation346 hz
    mixedMoment B raw40067step0 raw40067step0Labels = mixedMoment B raw40067step1 raw40067step1Labels := by
      have ha : raw40067step1 = (fun i j => raw40067step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40067step1 raw40067step0; decide +kernel
      have hl : raw40067step1Labels = raw40067step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40067step0 raw40067step0Labels permutation35 permutation4
    mixedMoment B raw40067step1 raw40067step1Labels = mixedMoment B raw40067step2 raw40067step2Labels := by
      have ha : raw40067step2 = -raw40067step1 := by apply Matrix.ext; change ∀ i j, raw40067step2 i j = -(raw40067step1 i j); unfold raw40067step2 raw40067step1; decide +kernel
      have hl : raw40067step2Labels = raw40067step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node403 node403Labels := by rfl

def raw40068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40068Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40068step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40068step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw40068step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40068step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40068step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40068 raw40068Labels = mixedMoment B node377 node377Labels := by
  calc
    mixedMoment B raw40068 raw40068Labels = mixedMoment B raw40068step0 raw40068step0Labels := by
      have hz : ∀ j, raw40068 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40068step0 = (fun i j => raw40068 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40068step0 raw40068; decide +kernel
      have hl : raw40068step0Labels = raw40068Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40068 raw40068Labels permutation346 hz
    mixedMoment B raw40068step0 raw40068step0Labels = mixedMoment B raw40068step1 raw40068step1Labels := by
      have ha : raw40068step1 = (fun i j => raw40068step0 (permutation45 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40068step1 raw40068step0; decide +kernel
      have hl : raw40068step1Labels = raw40068step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40068step0 raw40068step0Labels permutation45 permutation4
    mixedMoment B raw40068step1 raw40068step1Labels = mixedMoment B raw40068step2 raw40068step2Labels := by
      have ha : raw40068step2 = -raw40068step1 := by apply Matrix.ext; change ∀ i j, raw40068step2 i j = -(raw40068step1 i j); unfold raw40068step2 raw40068step1; decide +kernel
      have hl : raw40068step2Labels = raw40068step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node377 node377Labels := by rfl

def raw40069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw40069Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw40069step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40069step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40069step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40069 raw40069Labels = mixedMoment B node360 node360Labels := by
  calc
    mixedMoment B raw40069 raw40069Labels = mixedMoment B raw40069step0 raw40069step0Labels := by
      have ha : raw40069step0 = (fun i j => raw40069 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40069step0 raw40069; decide +kernel
      have hl : raw40069step0Labels = raw40069Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40069 raw40069Labels permutation246 permutation4
    mixedMoment B raw40069step0 raw40069step0Labels = mixedMoment B raw40069step1 raw40069step1Labels := by
      have ha : raw40069step1 = -raw40069step0 := by apply Matrix.ext; change ∀ i j, raw40069step1 i j = -(raw40069step0 i j); unfold raw40069step1 raw40069step0; decide +kernel
      have hl : raw40069step1Labels = raw40069step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node360 node360Labels := by rfl

def raw40070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw40070Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw40070step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40070step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40070step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40070 raw40070Labels = mixedMoment B node376 node376Labels := by
  calc
    mixedMoment B raw40070 raw40070Labels = mixedMoment B raw40070step0 raw40070step0Labels := by
      have ha : raw40070step0 = (fun i j => raw40070 (permutation228 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40070step0 raw40070; decide +kernel
      have hl : raw40070step0Labels = raw40070Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40070 raw40070Labels permutation228 permutation4
    mixedMoment B raw40070step0 raw40070step0Labels = mixedMoment B raw40070step1 raw40070step1Labels := by
      have ha : raw40070step1 = -raw40070step0 := by apply Matrix.ext; change ∀ i j, raw40070step1 i j = -(raw40070step0 i j); unfold raw40070step1 raw40070step0; decide +kernel
      have hl : raw40070step1Labels = raw40070step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node376 node376Labels := by rfl

def raw40071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40071Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40071step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40071step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw40071step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40071step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw40071step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40071 raw40071Labels = mixedMoment B node367 node367Labels := by
  calc
    mixedMoment B raw40071 raw40071Labels = mixedMoment B raw40071step0 raw40071step0Labels := by
      have hz : ∀ j, raw40071 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40071step0 = (fun i j => raw40071 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40071step0 raw40071; decide +kernel
      have hl : raw40071step0Labels = raw40071Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40071 raw40071Labels permutation434 hz
    mixedMoment B raw40071step0 raw40071step0Labels = mixedMoment B raw40071step1 raw40071step1Labels := by
      have ha : raw40071step1 = (fun i j => raw40071step0 (permutation54 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40071step1 raw40071step0; decide +kernel
      have hl : raw40071step1Labels = raw40071step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40071step0 raw40071step0Labels permutation54 permutation4
    mixedMoment B raw40071step1 raw40071step1Labels = mixedMoment B raw40071step2 raw40071step2Labels := by
      have ha : raw40071step2 = -raw40071step1 := by apply Matrix.ext; change ∀ i j, raw40071step2 i j = -(raw40071step1 i j); unfold raw40071step2 raw40071step1; decide +kernel
      have hl : raw40071step2Labels = raw40071step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node367 node367Labels := by rfl

def raw40072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw40072Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw40072step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40072step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0]]
def raw40072step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40072step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![2, -2, 0]]
def raw40072step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40072step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -1, 2], ![-2, 2, 0]]
def raw40072step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40072step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw40072step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40072 raw40072Labels = mixedMoment B node420 node420Labels := by
  calc
    mixedMoment B raw40072 raw40072Labels = mixedMoment B raw40072step0 raw40072step0Labels := by
      have hz : ∀ j, raw40072 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40072step0 = (fun i j => raw40072 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40072step0 raw40072; decide +kernel
      have hl : raw40072step0Labels = raw40072Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40072 raw40072Labels permutation520 hz
    mixedMoment B raw40072step0 raw40072step0Labels = mixedMoment B raw40072step1 raw40072step1Labels := by
      have hz : ∀ j, raw40072step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40072step1 = (fun i j => raw40072step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40072step1 raw40072step0; decide +kernel
      have hl : raw40072step1Labels = raw40072step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40072step0 raw40072step0Labels permutation104 hz
    mixedMoment B raw40072step1 raw40072step1Labels = mixedMoment B raw40072step2 raw40072step2Labels := by
      have hz : ∀ j, raw40072step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40072step2 = (fun i j => raw40072step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40072step2 raw40072step1; decide +kernel
      have hl : raw40072step2Labels = raw40072step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40072step1 raw40072step1Labels permutation20 hz
    mixedMoment B raw40072step2 raw40072step2Labels = mixedMoment B raw40072step3 raw40072step3Labels := by
      have ha : raw40072step3 = (fun i j => raw40072step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40072step3 raw40072step2; decide +kernel
      have hl : raw40072step3Labels = raw40072step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40072step2 raw40072step2Labels permutation2 permutation4
    mixedMoment B raw40072step3 raw40072step3Labels = mixedMoment B raw40072step4 raw40072step4Labels := by
      have ha : raw40072step4 = -raw40072step3 := by apply Matrix.ext; change ∀ i j, raw40072step4 i j = -(raw40072step3 i j); unfold raw40072step4 raw40072step3; decide +kernel
      have hl : raw40072step4Labels = raw40072step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node420 node420Labels := by rfl

def raw40073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw40073Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw40073step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40073step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1]]
def raw40073step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40073step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw40073step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40073step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw40073step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40073 raw40073Labels = mixedMoment B node414 node414Labels := by
  calc
    mixedMoment B raw40073 raw40073Labels = mixedMoment B raw40073step0 raw40073step0Labels := by
      have hz : ∀ j, raw40073 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40073step0 = (fun i j => raw40073 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40073step0 raw40073; decide +kernel
      have hl : raw40073step0Labels = raw40073Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40073 raw40073Labels permutation434 hz
    mixedMoment B raw40073step0 raw40073step0Labels = mixedMoment B raw40073step1 raw40073step1Labels := by
      have hz : ∀ j, raw40073step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40073step1 = (fun i j => raw40073step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40073step1 raw40073step0; decide +kernel
      have hl : raw40073step1Labels = raw40073step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40073step0 raw40073step0Labels permutation80 hz
    mixedMoment B raw40073step1 raw40073step1Labels = mixedMoment B raw40073step2 raw40073step2Labels := by
      have ha : raw40073step2 = (fun i j => raw40073step1 (permutation13 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40073step2 raw40073step1; decide +kernel
      have hl : raw40073step2Labels = raw40073step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40073step1 raw40073step1Labels permutation13 permutation4
    mixedMoment B raw40073step2 raw40073step2Labels = mixedMoment B raw40073step3 raw40073step3Labels := by
      have ha : raw40073step3 = -raw40073step2 := by apply Matrix.ext; change ∀ i j, raw40073step3 i j = -(raw40073step2 i j); unfold raw40073step3 raw40073step2; decide +kernel
      have hl : raw40073step3Labels = raw40073step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node414 node414Labels := by rfl

def raw40074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw40074Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw40074step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40074step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, -2, 2], ![2, 0, -2]]
def raw40074step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40074step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw40074step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40074step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw40074step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40074 raw40074Labels = mixedMoment B node369 node369Labels := by
  calc
    mixedMoment B raw40074 raw40074Labels = mixedMoment B raw40074step0 raw40074step0Labels := by
      have hz : ∀ j, raw40074 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40074step0 = (fun i j => raw40074 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40074step0 raw40074; decide +kernel
      have hl : raw40074step0Labels = raw40074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40074 raw40074Labels permutation434 hz
    mixedMoment B raw40074step0 raw40074step0Labels = mixedMoment B raw40074step1 raw40074step1Labels := by
      have hz : ∀ j, raw40074step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40074step1 = (fun i j => raw40074step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40074step1 raw40074step0; decide +kernel
      have hl : raw40074step1Labels = raw40074step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40074step0 raw40074step0Labels permutation80 hz
    mixedMoment B raw40074step1 raw40074step1Labels = mixedMoment B raw40074step2 raw40074step2Labels := by
      have ha : raw40074step2 = (fun i j => raw40074step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40074step2 raw40074step1; decide +kernel
      have hl : raw40074step2Labels = raw40074step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40074step1 raw40074step1Labels permutation12 permutation4
    mixedMoment B raw40074step2 raw40074step2Labels = mixedMoment B raw40074step3 raw40074step3Labels := by
      have ha : raw40074step3 = -raw40074step2 := by apply Matrix.ext; change ∀ i j, raw40074step3 i j = -(raw40074step2 i j); unfold raw40074step3 raw40074step2; decide +kernel
      have hl : raw40074step3Labels = raw40074step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node369 node369Labels := by rfl

def raw40075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw40075Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw40075step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40075step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![1, 0, -1], ![1, -2, 1]]
def raw40075step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40075step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw40075step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40075step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40075step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40075 raw40075Labels = mixedMoment B node390 node390Labels := by
  calc
    mixedMoment B raw40075 raw40075Labels = mixedMoment B raw40075step0 raw40075step0Labels := by
      have hz : ∀ j, raw40075 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40075step0 = (fun i j => raw40075 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40075step0 raw40075; decide +kernel
      have hl : raw40075step0Labels = raw40075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40075 raw40075Labels permutation434 hz
    mixedMoment B raw40075step0 raw40075step0Labels = mixedMoment B raw40075step1 raw40075step1Labels := by
      have hz : ∀ j, raw40075step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40075step1 = (fun i j => raw40075step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40075step1 raw40075step0; decide +kernel
      have hl : raw40075step1Labels = raw40075step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40075step0 raw40075step0Labels permutation80 hz
    mixedMoment B raw40075step1 raw40075step1Labels = mixedMoment B raw40075step2 raw40075step2Labels := by
      have ha : raw40075step2 = (fun i j => raw40075step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40075step2 raw40075step1; decide +kernel
      have hl : raw40075step2Labels = raw40075step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40075step1 raw40075step1Labels permutation10 permutation4
    mixedMoment B raw40075step2 raw40075step2Labels = mixedMoment B raw40075step3 raw40075step3Labels := by
      have ha : raw40075step3 = -raw40075step2 := by apply Matrix.ext; change ∀ i j, raw40075step3 i j = -(raw40075step2 i j); unfold raw40075step3 raw40075step2; decide +kernel
      have hl : raw40075step3Labels = raw40075step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node390 node390Labels := by rfl

def raw40076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40076Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40076step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40076step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0]]
def raw40076step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40076step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw40076step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40076step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw40076step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40076 raw40076Labels = mixedMoment B node416 node416Labels := by
  calc
    mixedMoment B raw40076 raw40076Labels = mixedMoment B raw40076step0 raw40076step0Labels := by
      have hz : ∀ j, raw40076 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40076step0 = (fun i j => raw40076 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40076step0 raw40076; decide +kernel
      have hl : raw40076step0Labels = raw40076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40076 raw40076Labels permutation434 hz
    mixedMoment B raw40076step0 raw40076step0Labels = mixedMoment B raw40076step1 raw40076step1Labels := by
      have hz : ∀ j, raw40076step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40076step1 = (fun i j => raw40076step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40076step1 raw40076step0; decide +kernel
      have hl : raw40076step1Labels = raw40076step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40076step0 raw40076step0Labels permutation80 hz
    mixedMoment B raw40076step1 raw40076step1Labels = mixedMoment B raw40076step2 raw40076step2Labels := by
      have ha : raw40076step2 = (fun i j => raw40076step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40076step2 raw40076step1; decide +kernel
      have hl : raw40076step2Labels = raw40076step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40076step1 raw40076step1Labels permutation11 permutation4
    mixedMoment B raw40076step2 raw40076step2Labels = mixedMoment B raw40076step3 raw40076step3Labels := by
      have ha : raw40076step3 = -raw40076step2 := by apply Matrix.ext; change ∀ i j, raw40076step3 i j = -(raw40076step2 i j); unfold raw40076step3 raw40076step2; decide +kernel
      have hl : raw40076step3Labels = raw40076step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node416 node416Labels := by rfl

def raw40077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw40077Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw40077step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40077step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw40077step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40077step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw40077step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40077 raw40077Labels = mixedMoment B node368 node368Labels := by
  calc
    mixedMoment B raw40077 raw40077Labels = mixedMoment B raw40077step0 raw40077step0Labels := by
      have hz : ∀ j, raw40077 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40077step0 = (fun i j => raw40077 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40077step0 raw40077; decide +kernel
      have hl : raw40077step0Labels = raw40077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40077 raw40077Labels permutation346 hz
    mixedMoment B raw40077step0 raw40077step0Labels = mixedMoment B raw40077step1 raw40077step1Labels := by
      have ha : raw40077step1 = (fun i j => raw40077step0 (permutation53 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40077step1 raw40077step0; decide +kernel
      have hl : raw40077step1Labels = raw40077step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40077step0 raw40077step0Labels permutation53 permutation4
    mixedMoment B raw40077step1 raw40077step1Labels = mixedMoment B raw40077step2 raw40077step2Labels := by
      have ha : raw40077step2 = -raw40077step1 := by apply Matrix.ext; change ∀ i j, raw40077step2 i j = -(raw40077step1 i j); unfold raw40077step2 raw40077step1; decide +kernel
      have hl : raw40077step2Labels = raw40077step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node368 node368Labels := by rfl

def raw40078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw40078Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw40078step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw40078step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40078step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40078step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40078 raw40078Labels = mixedMoment B node387 node387Labels := by
  calc
    mixedMoment B raw40078 raw40078Labels = mixedMoment B raw40078step0 raw40078step0Labels := by
      have hz : ∀ j, raw40078 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40078step0 = (fun i j => raw40078 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40078step0 raw40078; decide +kernel
      have hl : raw40078step0Labels = raw40078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40078 raw40078Labels permutation346 hz
    mixedMoment B raw40078step0 raw40078step0Labels = mixedMoment B raw40078step1 raw40078step1Labels := by
      have ha : raw40078step1 = (fun i j => raw40078step0 (permutation49 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40078step1 raw40078step0; decide +kernel
      have hl : raw40078step1Labels = raw40078step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40078step0 raw40078step0Labels permutation49 permutation4
    mixedMoment B raw40078step1 raw40078step1Labels = mixedMoment B raw40078step2 raw40078step2Labels := by
      have ha : raw40078step2 = -raw40078step1 := by apply Matrix.ext; change ∀ i j, raw40078step2 i j = -(raw40078step1 i j); unfold raw40078step2 raw40078step1; decide +kernel
      have hl : raw40078step2Labels = raw40078step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node387 node387Labels := by rfl

def raw40079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40079Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw40079step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40079step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw40079step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40079 raw40079Labels = mixedMoment B node371 node371Labels := by
  calc
    mixedMoment B raw40079 raw40079Labels = mixedMoment B raw40079step0 raw40079step0Labels := by
      have ha : raw40079step0 = (fun i j => raw40079 (permutation243 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40079step0 raw40079; decide +kernel
      have hl : raw40079step0Labels = raw40079Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40079 raw40079Labels permutation243 permutation4
    mixedMoment B raw40079step0 raw40079step0Labels = mixedMoment B raw40079step1 raw40079step1Labels := by
      have ha : raw40079step1 = -raw40079step0 := by apply Matrix.ext; change ∀ i j, raw40079step1 i j = -(raw40079step0 i j); unfold raw40079step1 raw40079step0; decide +kernel
      have hl : raw40079step1Labels = raw40079step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node371 node371Labels := by rfl

def raw40080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw40080Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw40080step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40080step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![0, 0, 0], ![2, -1, -1]]
def raw40080step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40080step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![2, -1, -1]]
def raw40080step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40080step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-2, -1, 3]]
def raw40080step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40080step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw40080step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40080 raw40080Labels = mixedMoment B node415 node415Labels := by
  calc
    mixedMoment B raw40080 raw40080Labels = mixedMoment B raw40080step0 raw40080step0Labels := by
      have hz : ∀ j, raw40080 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40080step0 = (fun i j => raw40080 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40080step0 raw40080; decide +kernel
      have hl : raw40080step0Labels = raw40080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40080 raw40080Labels permutation520 hz
    mixedMoment B raw40080step0 raw40080step0Labels = mixedMoment B raw40080step1 raw40080step1Labels := by
      have hz : ∀ j, raw40080step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40080step1 = (fun i j => raw40080step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40080step1 raw40080step0; decide +kernel
      have hl : raw40080step1Labels = raw40080step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40080step0 raw40080step0Labels permutation104 hz
    mixedMoment B raw40080step1 raw40080step1Labels = mixedMoment B raw40080step2 raw40080step2Labels := by
      have hz : ∀ j, raw40080step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40080step2 = (fun i j => raw40080step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40080step2 raw40080step1; decide +kernel
      have hl : raw40080step2Labels = raw40080step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40080step1 raw40080step1Labels permutation20 hz
    mixedMoment B raw40080step2 raw40080step2Labels = mixedMoment B raw40080step3 raw40080step3Labels := by
      have ha : raw40080step3 = (fun i j => raw40080step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40080step3 raw40080step2; decide +kernel
      have hl : raw40080step3Labels = raw40080step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40080step2 raw40080step2Labels permutation3 permutation4
    mixedMoment B raw40080step3 raw40080step3Labels = mixedMoment B raw40080step4 raw40080step4Labels := by
      have ha : raw40080step4 = -raw40080step3 := by apply Matrix.ext; change ∀ i j, raw40080step4 i j = -(raw40080step3 i j); unfold raw40080step4 raw40080step3; decide +kernel
      have hl : raw40080step4Labels = raw40080step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node415 node415Labels := by rfl

def raw40081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw40081Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw40081step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40081step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![0, -1, 1], ![2, 0, -2]]
def raw40081step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40081step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw40081step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40081step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw40081step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40081 raw40081Labels = mixedMoment B node316 node316Labels := by
  calc
    mixedMoment B raw40081 raw40081Labels = mixedMoment B raw40081step0 raw40081step0Labels := by
      have hz : ∀ j, raw40081 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40081step0 = (fun i j => raw40081 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40081step0 raw40081; decide +kernel
      have hl : raw40081step0Labels = raw40081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40081 raw40081Labels permutation434 hz
    mixedMoment B raw40081step0 raw40081step0Labels = mixedMoment B raw40081step1 raw40081step1Labels := by
      have hz : ∀ j, raw40081step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40081step1 = (fun i j => raw40081step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40081step1 raw40081step0; decide +kernel
      have hl : raw40081step1Labels = raw40081step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40081step0 raw40081step0Labels permutation80 hz
    mixedMoment B raw40081step1 raw40081step1Labels = mixedMoment B raw40081step2 raw40081step2Labels := by
      have ha : raw40081step2 = (fun i j => raw40081step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40081step2 raw40081step1; decide +kernel
      have hl : raw40081step2Labels = raw40081step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40081step1 raw40081step1Labels permutation17 permutation6
    mixedMoment B raw40081step2 raw40081step2Labels = mixedMoment B raw40081step3 raw40081step3Labels := by
      have ha : raw40081step3 = -raw40081step2 := by apply Matrix.ext; change ∀ i j, raw40081step3 i j = -(raw40081step2 i j); unfold raw40081step3 raw40081step2; decide +kernel
      have hl : raw40081step3Labels = raw40081step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node316 node316Labels := by rfl

def raw40082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw40082Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw40082step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40082step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![1, 0, -1], ![1, -1, 0]]
def raw40082step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40082step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-2, -1, 3]]
def raw40082step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40082step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40082step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40082 raw40082Labels = mixedMoment B node388 node388Labels := by
  calc
    mixedMoment B raw40082 raw40082Labels = mixedMoment B raw40082step0 raw40082step0Labels := by
      have hz : ∀ j, raw40082 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40082step0 = (fun i j => raw40082 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40082step0 raw40082; decide +kernel
      have hl : raw40082step0Labels = raw40082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40082 raw40082Labels permutation434 hz
    mixedMoment B raw40082step0 raw40082step0Labels = mixedMoment B raw40082step1 raw40082step1Labels := by
      have hz : ∀ j, raw40082step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40082step1 = (fun i j => raw40082step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40082step1 raw40082step0; decide +kernel
      have hl : raw40082step1Labels = raw40082step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40082step0 raw40082step0Labels permutation80 hz
    mixedMoment B raw40082step1 raw40082step1Labels = mixedMoment B raw40082step2 raw40082step2Labels := by
      have ha : raw40082step2 = (fun i j => raw40082step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40082step2 raw40082step1; decide +kernel
      have hl : raw40082step2Labels = raw40082step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40082step1 raw40082step1Labels permutation11 permutation4
    mixedMoment B raw40082step2 raw40082step2Labels = mixedMoment B raw40082step3 raw40082step3Labels := by
      have ha : raw40082step3 = -raw40082step2 := by apply Matrix.ext; change ∀ i j, raw40082step3 i j = -(raw40082step2 i j); unfold raw40082step3 raw40082step2; decide +kernel
      have hl : raw40082step3Labels = raw40082step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node388 node388Labels := by rfl

def raw40083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -3, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40083Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -3, 4], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40083step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40083step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -3, 4], ![0, 0, 0], ![2, 0, -2]]
def raw40083step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40083step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -3, 4], ![2, 0, -2]]
def raw40083step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40083step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-2, 2, 0], ![-2, -1, 3]]
def raw40083step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40083step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw40083step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40083 raw40083Labels = mixedMoment B node113 node113Labels := by
  calc
    mixedMoment B raw40083 raw40083Labels = mixedMoment B raw40083step0 raw40083step0Labels := by
      have hz : ∀ j, raw40083 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40083step0 = (fun i j => raw40083 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40083step0 raw40083; decide +kernel
      have hl : raw40083step0Labels = raw40083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40083 raw40083Labels permutation520 hz
    mixedMoment B raw40083step0 raw40083step0Labels = mixedMoment B raw40083step1 raw40083step1Labels := by
      have hz : ∀ j, raw40083step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40083step1 = (fun i j => raw40083step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40083step1 raw40083step0; decide +kernel
      have hl : raw40083step1Labels = raw40083step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40083step0 raw40083step0Labels permutation104 hz
    mixedMoment B raw40083step1 raw40083step1Labels = mixedMoment B raw40083step2 raw40083step2Labels := by
      have hz : ∀ j, raw40083step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40083step2 = (fun i j => raw40083step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40083step2 raw40083step1; decide +kernel
      have hl : raw40083step2Labels = raw40083step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40083step1 raw40083step1Labels permutation20 hz
    mixedMoment B raw40083step2 raw40083step2Labels = mixedMoment B raw40083step3 raw40083step3Labels := by
      have ha : raw40083step3 = (fun i j => raw40083step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40083step3 raw40083step2; decide +kernel
      have hl : raw40083step3Labels = raw40083step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40083step2 raw40083step2Labels permutation5 permutation6
    mixedMoment B raw40083step3 raw40083step3Labels = mixedMoment B raw40083step4 raw40083step4Labels := by
      have ha : raw40083step4 = -raw40083step3 := by apply Matrix.ext; change ∀ i j, raw40083step4 i j = -(raw40083step3 i j); unfold raw40083step4 raw40083step3; decide +kernel
      have hl : raw40083step4Labels = raw40083step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node113 node113Labels := by rfl

def raw40084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40084Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40084step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40084step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40084step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40084step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40084step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40084 raw40084Labels = mixedMoment B node5506 node5506Labels := by
  calc
    mixedMoment B raw40084 raw40084Labels = mixedMoment B raw40084step0 raw40084step0Labels := by
      have hz : ∀ j, raw40084 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40084step0 = (fun i j => raw40084 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40084step0 raw40084; decide +kernel
      have hl : raw40084step0Labels = raw40084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40084 raw40084Labels permutation434 hz
    mixedMoment B raw40084step0 raw40084step0Labels = mixedMoment B raw40084step1 raw40084step1Labels := by
      have hz : ∀ j, raw40084step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40084step1 = (fun i j => raw40084step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40084step1 raw40084step0; decide +kernel
      have hl : raw40084step1Labels = raw40084step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40084step0 raw40084step0Labels permutation80 hz
    mixedMoment B raw40084step1 raw40084step1Labels = mixedMoment B raw40084step2 raw40084step2Labels := by
      have ha : raw40084step2 = (fun i j => raw40084step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw40084step2 raw40084step1; decide +kernel
      have hl : raw40084step2Labels = raw40084step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40084step1 raw40084step1Labels permutation31 permutation5
    _ = mixedMoment B node5506 node5506Labels := by rfl

def raw40085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40085Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40085step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40085step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40085step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40085 raw40085Labels = mixedMoment B node489 node489Labels := by
  calc
    mixedMoment B raw40085 raw40085Labels = mixedMoment B raw40085step0 raw40085step0Labels := by
      have hz : ∀ j, raw40085 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40085step0 = (fun i j => raw40085 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40085step0 raw40085; decide +kernel
      have hl : raw40085step0Labels = raw40085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40085 raw40085Labels permutation346 hz
    mixedMoment B raw40085step0 raw40085step0Labels = mixedMoment B raw40085step1 raw40085step1Labels := by
      have ha : raw40085step1 = (fun i j => raw40085step0 (permutation103 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40085step1 raw40085step0; decide +kernel
      have hl : raw40085step1Labels = raw40085step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40085step0 raw40085step0Labels permutation103 permutation4
    _ = mixedMoment B node489 node489Labels := by rfl

def raw40086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40086Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40086step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw40086step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40086step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40086step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40086 raw40086Labels = mixedMoment B node521 node521Labels := by
  calc
    mixedMoment B raw40086 raw40086Labels = mixedMoment B raw40086step0 raw40086step0Labels := by
      have hz : ∀ j, raw40086 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40086step0 = (fun i j => raw40086 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40086step0 raw40086; decide +kernel
      have hl : raw40086step0Labels = raw40086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40086 raw40086Labels permutation434 hz
    mixedMoment B raw40086step0 raw40086step0Labels = mixedMoment B raw40086step1 raw40086step1Labels := by
      have ha : raw40086step1 = (fun i j => raw40086step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40086step1 raw40086step0; decide +kernel
      have hl : raw40086step1Labels = raw40086step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40086step0 raw40086step0Labels permutation38 permutation4
    mixedMoment B raw40086step1 raw40086step1Labels = mixedMoment B raw40086step2 raw40086step2Labels := by
      have ha : raw40086step2 = -raw40086step1 := by apply Matrix.ext; change ∀ i j, raw40086step2 i j = -(raw40086step1 i j); unfold raw40086step2 raw40086step1; decide +kernel
      have hl : raw40086step2Labels = raw40086step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node521 node521Labels := by rfl

def raw40087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw40087Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40087step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40087 raw40087Labels = mixedMoment B node518 node518Labels := by
  calc
    mixedMoment B raw40087 raw40087Labels = mixedMoment B raw40087step0 raw40087step0Labels := by
      have ha : raw40087step0 = (fun i j => raw40087 (permutation654 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40087step0 raw40087; decide +kernel
      have hl : raw40087step0Labels = raw40087Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40087 raw40087Labels permutation654 permutation4
    _ = mixedMoment B node518 node518Labels := by rfl

def raw40088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40088Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40088step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40088step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40088 raw40088Labels = mixedMoment B node479 node479Labels := by
  calc
    mixedMoment B raw40088 raw40088Labels = mixedMoment B raw40088step0 raw40088step0Labels := by
      have ha : raw40088step0 = (fun i j => raw40088 (permutation511 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40088step0 raw40088; decide +kernel
      have hl : raw40088step0Labels = raw40088Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40088 raw40088Labels permutation511 permutation4
    _ = mixedMoment B node479 node479Labels := by rfl

def raw40089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw40089Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw40089step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0]]
def raw40089step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40089step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![2, -2, 0]]
def raw40089step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40089step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw40089step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40089 raw40089Labels = mixedMoment B node5507 node5507Labels := by
  calc
    mixedMoment B raw40089 raw40089Labels = mixedMoment B raw40089step0 raw40089step0Labels := by
      have hz : ∀ j, raw40089 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40089step0 = (fun i j => raw40089 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40089step0 raw40089; decide +kernel
      have hl : raw40089step0Labels = raw40089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40089 raw40089Labels permutation520 hz
    mixedMoment B raw40089step0 raw40089step0Labels = mixedMoment B raw40089step1 raw40089step1Labels := by
      have hz : ∀ j, raw40089step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40089step1 = (fun i j => raw40089step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40089step1 raw40089step0; decide +kernel
      have hl : raw40089step1Labels = raw40089step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40089step0 raw40089step0Labels permutation104 hz
    mixedMoment B raw40089step1 raw40089step1Labels = mixedMoment B raw40089step2 raw40089step2Labels := by
      have hz : ∀ j, raw40089step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40089step2 = (fun i j => raw40089step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40089step2 raw40089step1; decide +kernel
      have hl : raw40089step2Labels = raw40089step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40089step1 raw40089step1Labels permutation20 hz
    mixedMoment B raw40089step2 raw40089step2Labels = mixedMoment B raw40089step3 raw40089step3Labels := by
      have ha : raw40089step3 = (fun i j => raw40089step2 (permutation7 i) (permutation5 j)) := by apply Matrix.ext; unfold raw40089step3 raw40089step2; decide +kernel
      have hl : raw40089step3Labels = raw40089step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40089step2 raw40089step2Labels permutation7 permutation5
    _ = mixedMoment B node5507 node5507Labels := by rfl

def raw40090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw40090Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw40090step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40090step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1]]
def raw40090step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40090step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw40090step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40090step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw40090step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40090 raw40090Labels = mixedMoment B node528 node528Labels := by
  calc
    mixedMoment B raw40090 raw40090Labels = mixedMoment B raw40090step0 raw40090step0Labels := by
      have hz : ∀ j, raw40090 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40090step0 = (fun i j => raw40090 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40090step0 raw40090; decide +kernel
      have hl : raw40090step0Labels = raw40090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40090 raw40090Labels permutation434 hz
    mixedMoment B raw40090step0 raw40090step0Labels = mixedMoment B raw40090step1 raw40090step1Labels := by
      have hz : ∀ j, raw40090step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40090step1 = (fun i j => raw40090step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40090step1 raw40090step0; decide +kernel
      have hl : raw40090step1Labels = raw40090step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40090step0 raw40090step0Labels permutation80 hz
    mixedMoment B raw40090step1 raw40090step1Labels = mixedMoment B raw40090step2 raw40090step2Labels := by
      have ha : raw40090step2 = (fun i j => raw40090step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40090step2 raw40090step1; decide +kernel
      have hl : raw40090step2Labels = raw40090step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40090step1 raw40090step1Labels permutation31 permutation3
    mixedMoment B raw40090step2 raw40090step2Labels = mixedMoment B raw40090step3 raw40090step3Labels := by
      have ha : raw40090step3 = -raw40090step2 := by apply Matrix.ext; change ∀ i j, raw40090step3 i j = -(raw40090step2 i j); unfold raw40090step3 raw40090step2; decide +kernel
      have hl : raw40090step3Labels = raw40090step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node528 node528Labels := by rfl

def raw40091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw40091Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw40091step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40091step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2]]
def raw40091step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40091step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw40091step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40091step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw40091step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40091 raw40091Labels = mixedMoment B node496 node496Labels := by
  calc
    mixedMoment B raw40091 raw40091Labels = mixedMoment B raw40091step0 raw40091step0Labels := by
      have hz : ∀ j, raw40091 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40091step0 = (fun i j => raw40091 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40091step0 raw40091; decide +kernel
      have hl : raw40091step0Labels = raw40091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40091 raw40091Labels permutation434 hz
    mixedMoment B raw40091step0 raw40091step0Labels = mixedMoment B raw40091step1 raw40091step1Labels := by
      have hz : ∀ j, raw40091step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40091step1 = (fun i j => raw40091step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40091step1 raw40091step0; decide +kernel
      have hl : raw40091step1Labels = raw40091step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40091step0 raw40091step0Labels permutation80 hz
    mixedMoment B raw40091step1 raw40091step1Labels = mixedMoment B raw40091step2 raw40091step2Labels := by
      have ha : raw40091step2 = (fun i j => raw40091step1 (permutation22 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40091step2 raw40091step1; decide +kernel
      have hl : raw40091step2Labels = raw40091step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40091step1 raw40091step1Labels permutation22 permutation6
    mixedMoment B raw40091step2 raw40091step2Labels = mixedMoment B raw40091step3 raw40091step3Labels := by
      have ha : raw40091step3 = -raw40091step2 := by apply Matrix.ext; change ∀ i j, raw40091step3 i j = -(raw40091step2 i j); unfold raw40091step3 raw40091step2; decide +kernel
      have hl : raw40091step3Labels = raw40091step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node496 node496Labels := by rfl

def raw40092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw40092Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw40092step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40092step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40092 raw40092Labels = mixedMoment B node502 node502Labels := by
  calc
    mixedMoment B raw40092 raw40092Labels = mixedMoment B raw40092step0 raw40092step0Labels := by
      have hz : ∀ j, raw40092 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40092step0 = (fun i j => raw40092 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40092step0 raw40092; decide +kernel
      have hl : raw40092step0Labels = raw40092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40092 raw40092Labels permutation346 hz
    mixedMoment B raw40092step0 raw40092step0Labels = mixedMoment B raw40092step1 raw40092step1Labels := by
      have ha : raw40092step1 = (fun i j => raw40092step0 (permutation131 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40092step1 raw40092step0; decide +kernel
      have hl : raw40092step1Labels = raw40092step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40092step0 raw40092step0Labels permutation131 permutation7
    _ = mixedMoment B node502 node502Labels := by rfl

def raw40093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw40093Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw40093step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40093step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40093step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40093step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40093 raw40093Labels = mixedMoment B node514 node514Labels := by
  calc
    mixedMoment B raw40093 raw40093Labels = mixedMoment B raw40093step0 raw40093step0Labels := by
      have hz : ∀ j, raw40093 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40093step0 = (fun i j => raw40093 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40093step0 raw40093; decide +kernel
      have hl : raw40093step0Labels = raw40093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40093 raw40093Labels permutation346 hz
    mixedMoment B raw40093step0 raw40093step0Labels = mixedMoment B raw40093step1 raw40093step1Labels := by
      have ha : raw40093step1 = (fun i j => raw40093step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40093step1 raw40093step0; decide +kernel
      have hl : raw40093step1Labels = raw40093step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40093step0 raw40093step0Labels permutation44 permutation4
    mixedMoment B raw40093step1 raw40093step1Labels = mixedMoment B raw40093step2 raw40093step2Labels := by
      have ha : raw40093step2 = -raw40093step1 := by apply Matrix.ext; change ∀ i j, raw40093step2 i j = -(raw40093step1 i j); unfold raw40093step2 raw40093step1; decide +kernel
      have hl : raw40093step2Labels = raw40093step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node514 node514Labels := by rfl

def raw40094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw40094Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw40094step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40094step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40094step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40094 raw40094Labels = mixedMoment B node483 node483Labels := by
  calc
    mixedMoment B raw40094 raw40094Labels = mixedMoment B raw40094step0 raw40094step0Labels := by
      have hz : ∀ j, raw40094 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40094step0 = (fun i j => raw40094 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40094step0 raw40094; decide +kernel
      have hl : raw40094step0Labels = raw40094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40094 raw40094Labels permutation346 hz
    mixedMoment B raw40094step0 raw40094step0Labels = mixedMoment B raw40094step1 raw40094step1Labels := by
      have ha : raw40094step1 = (fun i j => raw40094step0 (permutation101 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40094step1 raw40094step0; decide +kernel
      have hl : raw40094step1Labels = raw40094step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40094step0 raw40094step0Labels permutation101 permutation4
    _ = mixedMoment B node483 node483Labels := by rfl

def raw40095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw40095Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw40095step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40095step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40095step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40095step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40095step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40095 raw40095Labels = mixedMoment B node438 node438Labels := by
  calc
    mixedMoment B raw40095 raw40095Labels = mixedMoment B raw40095step0 raw40095step0Labels := by
      have hz : ∀ j, raw40095 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40095step0 = (fun i j => raw40095 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40095step0 raw40095; decide +kernel
      have hl : raw40095step0Labels = raw40095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40095 raw40095Labels permutation434 hz
    mixedMoment B raw40095step0 raw40095step0Labels = mixedMoment B raw40095step1 raw40095step1Labels := by
      have ha : raw40095step1 = (fun i j => raw40095step0 (permutation112 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40095step1 raw40095step0; decide +kernel
      have hl : raw40095step1Labels = raw40095step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40095step0 raw40095step0Labels permutation112 permutation6
    mixedMoment B raw40095step1 raw40095step1Labels = mixedMoment B raw40095step2 raw40095step2Labels := by
      have ha : raw40095step2 = -raw40095step1 := by apply Matrix.ext; change ∀ i j, raw40095step2 i j = -(raw40095step1 i j); unfold raw40095step2 raw40095step1; decide +kernel
      have hl : raw40095step2Labels = raw40095step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node438 node438Labels := by rfl

def raw40096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw40096Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw40096step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40096step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40096 raw40096Labels = mixedMoment B node514 node514Labels := by
  calc
    mixedMoment B raw40096 raw40096Labels = mixedMoment B raw40096step0 raw40096step0Labels := by
      have hz : ∀ j, raw40096 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40096step0 = (fun i j => raw40096 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40096step0 raw40096; decide +kernel
      have hl : raw40096step0Labels = raw40096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40096 raw40096Labels permutation434 hz
    mixedMoment B raw40096step0 raw40096step0Labels = mixedMoment B raw40096step1 raw40096step1Labels := by
      have ha : raw40096step1 = (fun i j => raw40096step0 (permutation139 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40096step1 raw40096step0; decide +kernel
      have hl : raw40096step1Labels = raw40096step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40096step0 raw40096step0Labels permutation139 permutation4
    _ = mixedMoment B node514 node514Labels := by rfl

def raw40097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw40097Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw40097step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40097step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40097step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40097 raw40097Labels = mixedMoment B node436 node436Labels := by
  calc
    mixedMoment B raw40097 raw40097Labels = mixedMoment B raw40097step0 raw40097step0Labels := by
      have ha : raw40097step0 = (fun i j => raw40097 (permutation463 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40097step0 raw40097; decide +kernel
      have hl : raw40097step0Labels = raw40097Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40097 raw40097Labels permutation463 permutation6
    mixedMoment B raw40097step0 raw40097step0Labels = mixedMoment B raw40097step1 raw40097step1Labels := by
      have ha : raw40097step1 = -raw40097step0 := by apply Matrix.ext; change ∀ i j, raw40097step1 i j = -(raw40097step0 i j); unfold raw40097step1 raw40097step0; decide +kernel
      have hl : raw40097step1Labels = raw40097step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node436 node436Labels := by rfl

def raw40098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw40098Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw40098step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40098step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1]]
def raw40098step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40098step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![2, -1, -1]]
def raw40098step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40098step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![-1, 2, -1], ![-1, -1, 2]]
def raw40098step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40098step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw40098step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40098 raw40098Labels = mixedMoment B node530 node530Labels := by
  calc
    mixedMoment B raw40098 raw40098Labels = mixedMoment B raw40098step0 raw40098step0Labels := by
      have hz : ∀ j, raw40098 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40098step0 = (fun i j => raw40098 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40098step0 raw40098; decide +kernel
      have hl : raw40098step0Labels = raw40098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40098 raw40098Labels permutation520 hz
    mixedMoment B raw40098step0 raw40098step0Labels = mixedMoment B raw40098step1 raw40098step1Labels := by
      have hz : ∀ j, raw40098step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40098step1 = (fun i j => raw40098step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40098step1 raw40098step0; decide +kernel
      have hl : raw40098step1Labels = raw40098step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40098step0 raw40098step0Labels permutation104 hz
    mixedMoment B raw40098step1 raw40098step1Labels = mixedMoment B raw40098step2 raw40098step2Labels := by
      have hz : ∀ j, raw40098step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40098step2 = (fun i j => raw40098step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40098step2 raw40098step1; decide +kernel
      have hl : raw40098step2Labels = raw40098step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40098step1 raw40098step1Labels permutation20 hz
    mixedMoment B raw40098step2 raw40098step2Labels = mixedMoment B raw40098step3 raw40098step3Labels := by
      have ha : raw40098step3 = (fun i j => raw40098step2 (permutation6 i) (permutation2 j)) := by apply Matrix.ext; unfold raw40098step3 raw40098step2; decide +kernel
      have hl : raw40098step3Labels = raw40098step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40098step2 raw40098step2Labels permutation6 permutation2
    mixedMoment B raw40098step3 raw40098step3Labels = mixedMoment B raw40098step4 raw40098step4Labels := by
      have ha : raw40098step4 = -raw40098step3 := by apply Matrix.ext; change ∀ i j, raw40098step4 i j = -(raw40098step3 i j); unfold raw40098step4 raw40098step3; decide +kernel
      have hl : raw40098step4Labels = raw40098step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node530 node530Labels := by rfl

def raw40099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw40099Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw40099step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40099step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2]]
def raw40099step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40099step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40099step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40099 raw40099Labels = mixedMoment B node503 node503Labels := by
  calc
    mixedMoment B raw40099 raw40099Labels = mixedMoment B raw40099step0 raw40099step0Labels := by
      have hz : ∀ j, raw40099 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40099step0 = (fun i j => raw40099 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40099step0 raw40099; decide +kernel
      have hl : raw40099step0Labels = raw40099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40099 raw40099Labels permutation434 hz
    mixedMoment B raw40099step0 raw40099step0Labels = mixedMoment B raw40099step1 raw40099step1Labels := by
      have hz : ∀ j, raw40099step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40099step1 = (fun i j => raw40099step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40099step1 raw40099step0; decide +kernel
      have hl : raw40099step1Labels = raw40099step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40099step0 raw40099step0Labels permutation80 hz
    mixedMoment B raw40099step1 raw40099step1Labels = mixedMoment B raw40099step2 raw40099step2Labels := by
      have ha : raw40099step2 = (fun i j => raw40099step1 (permutation27 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40099step2 raw40099step1; decide +kernel
      have hl : raw40099step2Labels = raw40099step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40099step1 raw40099step1Labels permutation27 permutation7
    _ = mixedMoment B node503 node503Labels := by rfl

def raw40100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw40100Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw40100step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40100step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, -2, 2], ![2, 1, -3]]
def raw40100step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40100step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw40100step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40100 raw40100Labels = mixedMoment B node355 node355Labels := by
  calc
    mixedMoment B raw40100 raw40100Labels = mixedMoment B raw40100step0 raw40100step0Labels := by
      have hz : ∀ j, raw40100 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40100step0 = (fun i j => raw40100 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40100step0 raw40100; decide +kernel
      have hl : raw40100step0Labels = raw40100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40100 raw40100Labels permutation434 hz
    mixedMoment B raw40100step0 raw40100step0Labels = mixedMoment B raw40100step1 raw40100step1Labels := by
      have hz : ∀ j, raw40100step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40100step1 = (fun i j => raw40100step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40100step1 raw40100step0; decide +kernel
      have hl : raw40100step1Labels = raw40100step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40100step0 raw40100step0Labels permutation80 hz
    mixedMoment B raw40100step1 raw40100step1Labels = mixedMoment B raw40100step2 raw40100step2Labels := by
      have ha : raw40100step2 = (fun i j => raw40100step1 (permutation27 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40100step2 raw40100step1; decide +kernel
      have hl : raw40100step2Labels = raw40100step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40100step1 raw40100step1Labels permutation27 permutation7
    _ = mixedMoment B node355 node355Labels := by rfl

def raw40101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw40101Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw40101step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40101step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![1, 1, -2], ![1, -2, 1]]
def raw40101step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40101step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40101step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40101 raw40101Labels = mixedMoment B node516 node516Labels := by
  calc
    mixedMoment B raw40101 raw40101Labels = mixedMoment B raw40101step0 raw40101step0Labels := by
      have hz : ∀ j, raw40101 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40101step0 = (fun i j => raw40101 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40101step0 raw40101; decide +kernel
      have hl : raw40101step0Labels = raw40101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40101 raw40101Labels permutation434 hz
    mixedMoment B raw40101step0 raw40101step0Labels = mixedMoment B raw40101step1 raw40101step1Labels := by
      have hz : ∀ j, raw40101step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40101step1 = (fun i j => raw40101step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40101step1 raw40101step0; decide +kernel
      have hl : raw40101step1Labels = raw40101step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40101step0 raw40101step0Labels permutation80 hz
    mixedMoment B raw40101step1 raw40101step1Labels = mixedMoment B raw40101step2 raw40101step2Labels := by
      have ha : raw40101step2 = (fun i j => raw40101step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40101step2 raw40101step1; decide +kernel
      have hl : raw40101step2Labels = raw40101step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40101step1 raw40101step1Labels permutation29 permutation4
    _ = mixedMoment B node516 node516Labels := by rfl

def raw40102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw40102Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -1, 2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw40102step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw40102step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40102step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw40102step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40102 raw40102Labels = mixedMoment B node437 node437Labels := by
  calc
    mixedMoment B raw40102 raw40102Labels = mixedMoment B raw40102step0 raw40102step0Labels := by
      have hz : ∀ j, raw40102 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40102step0 = (fun i j => raw40102 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40102step0 raw40102; decide +kernel
      have hl : raw40102step0Labels = raw40102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40102 raw40102Labels permutation346 hz
    mixedMoment B raw40102step0 raw40102step0Labels = mixedMoment B raw40102step1 raw40102step1Labels := by
      have ha : raw40102step1 = (fun i j => raw40102step0 (permutation90 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40102step1 raw40102step0; decide +kernel
      have hl : raw40102step1Labels = raw40102step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40102step0 raw40102step0Labels permutation90 permutation6
    mixedMoment B raw40102step1 raw40102step1Labels = mixedMoment B raw40102step2 raw40102step2Labels := by
      have ha : raw40102step2 = -raw40102step1 := by apply Matrix.ext; change ∀ i j, raw40102step2 i j = -(raw40102step1 i j); unfold raw40102step2 raw40102step1; decide +kernel
      have hl : raw40102step2Labels = raw40102step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node437 node437Labels := by rfl

def raw40103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw40103Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40103step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw40103step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40103step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40103step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40103 raw40103Labels = mixedMoment B node387 node387Labels := by
  calc
    mixedMoment B raw40103 raw40103Labels = mixedMoment B raw40103step0 raw40103step0Labels := by
      have hz : ∀ j, raw40103 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40103step0 = (fun i j => raw40103 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40103step0 raw40103; decide +kernel
      have hl : raw40103step0Labels = raw40103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40103 raw40103Labels permutation434 hz
    mixedMoment B raw40103step0 raw40103step0Labels = mixedMoment B raw40103step1 raw40103step1Labels := by
      have ha : raw40103step1 = (fun i j => raw40103step0 (permutation79 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40103step1 raw40103step0; decide +kernel
      have hl : raw40103step1Labels = raw40103step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40103step0 raw40103step0Labels permutation79 permutation6
    mixedMoment B raw40103step1 raw40103step1Labels = mixedMoment B raw40103step2 raw40103step2Labels := by
      have ha : raw40103step2 = -raw40103step1 := by apply Matrix.ext; change ∀ i j, raw40103step2 i j = -(raw40103step1 i j); unfold raw40103step2 raw40103step1; decide +kernel
      have hl : raw40103step2Labels = raw40103step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node387 node387Labels := by rfl

def raw40104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40104Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40104step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw40104step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40104step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40104step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40104 raw40104Labels = mixedMoment B node310 node310Labels := by
  calc
    mixedMoment B raw40104 raw40104Labels = mixedMoment B raw40104step0 raw40104step0Labels := by
      have ha : raw40104step0 = (fun i j => raw40104 (permutation317 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40104step0 raw40104; decide +kernel
      have hl : raw40104step0Labels = raw40104Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40104 raw40104Labels permutation317 permutation6
    mixedMoment B raw40104step0 raw40104step0Labels = mixedMoment B raw40104step1 raw40104step1Labels := by
      have ha : raw40104step1 = -raw40104step0 := by apply Matrix.ext; change ∀ i j, raw40104step1 i j = -(raw40104step0 i j); unfold raw40104step1 raw40104step0; decide +kernel
      have hl : raw40104step1Labels = raw40104step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node310 node310Labels := by rfl

def raw40105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40105Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40105step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 0, 0], ![2, 0, -2]]
def raw40105step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40105step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![2, 0, -2]]
def raw40105step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40105step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -1, 2], ![-2, 2, 0]]
def raw40105step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40105step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw40105step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40105 raw40105Labels = mixedMoment B node420 node420Labels := by
  calc
    mixedMoment B raw40105 raw40105Labels = mixedMoment B raw40105step0 raw40105step0Labels := by
      have hz : ∀ j, raw40105 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40105step0 = (fun i j => raw40105 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40105step0 raw40105; decide +kernel
      have hl : raw40105step0Labels = raw40105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40105 raw40105Labels permutation520 hz
    mixedMoment B raw40105step0 raw40105step0Labels = mixedMoment B raw40105step1 raw40105step1Labels := by
      have hz : ∀ j, raw40105step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40105step1 = (fun i j => raw40105step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40105step1 raw40105step0; decide +kernel
      have hl : raw40105step1Labels = raw40105step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40105step0 raw40105step0Labels permutation104 hz
    mixedMoment B raw40105step1 raw40105step1Labels = mixedMoment B raw40105step2 raw40105step2Labels := by
      have hz : ∀ j, raw40105step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40105step2 = (fun i j => raw40105step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40105step2 raw40105step1; decide +kernel
      have hl : raw40105step2Labels = raw40105step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40105step1 raw40105step1Labels permutation20 hz
    mixedMoment B raw40105step2 raw40105step2Labels = mixedMoment B raw40105step3 raw40105step3Labels := by
      have ha : raw40105step3 = (fun i j => raw40105step2 (permutation4 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40105step3 raw40105step2; decide +kernel
      have hl : raw40105step3Labels = raw40105step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40105step2 raw40105step2Labels permutation4 permutation6
    mixedMoment B raw40105step3 raw40105step3Labels = mixedMoment B raw40105step4 raw40105step4Labels := by
      have ha : raw40105step4 = -raw40105step3 := by apply Matrix.ext; change ∀ i j, raw40105step4 i j = -(raw40105step3 i j); unfold raw40105step4 raw40105step3; decide +kernel
      have hl : raw40105step4Labels = raw40105step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node420 node420Labels := by rfl

def raw40106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw40106Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw40106step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40106step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![1, 1, -2], ![1, -1, 0]]
def raw40106step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40106step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw40106step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40106step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40106step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40106 raw40106Labels = mixedMoment B node390 node390Labels := by
  calc
    mixedMoment B raw40106 raw40106Labels = mixedMoment B raw40106step0 raw40106step0Labels := by
      have hz : ∀ j, raw40106 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40106step0 = (fun i j => raw40106 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40106step0 raw40106; decide +kernel
      have hl : raw40106step0Labels = raw40106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40106 raw40106Labels permutation434 hz
    mixedMoment B raw40106step0 raw40106step0Labels = mixedMoment B raw40106step1 raw40106step1Labels := by
      have hz : ∀ j, raw40106step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40106step1 = (fun i j => raw40106step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40106step1 raw40106step0; decide +kernel
      have hl : raw40106step1Labels = raw40106step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40106step0 raw40106step0Labels permutation80 hz
    mixedMoment B raw40106step1 raw40106step1Labels = mixedMoment B raw40106step2 raw40106step2Labels := by
      have ha : raw40106step2 = (fun i j => raw40106step1 (permutation18 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40106step2 raw40106step1; decide +kernel
      have hl : raw40106step2Labels = raw40106step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40106step1 raw40106step1Labels permutation18 permutation6
    mixedMoment B raw40106step2 raw40106step2Labels = mixedMoment B raw40106step3 raw40106step3Labels := by
      have ha : raw40106step3 = -raw40106step2 := by apply Matrix.ext; change ∀ i j, raw40106step3 i j = -(raw40106step2 i j); unfold raw40106step3 raw40106step2; decide +kernel
      have hl : raw40106step3Labels = raw40106step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node390 node390Labels := by rfl

def raw40107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw40107Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -2, 3], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw40107step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw40107step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40107step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw40107step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40107 raw40107Labels = mixedMoment B node312 node312Labels := by
  calc
    mixedMoment B raw40107 raw40107Labels = mixedMoment B raw40107step0 raw40107step0Labels := by
      have hz : ∀ j, raw40107 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40107step0 = (fun i j => raw40107 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40107step0 raw40107; decide +kernel
      have hl : raw40107step0Labels = raw40107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40107 raw40107Labels permutation346 hz
    mixedMoment B raw40107step0 raw40107step0Labels = mixedMoment B raw40107step1 raw40107step1Labels := by
      have ha : raw40107step1 = (fun i j => raw40107step0 (permutation66 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40107step1 raw40107step0; decide +kernel
      have hl : raw40107step1Labels = raw40107step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40107step0 raw40107step0Labels permutation66 permutation6
    mixedMoment B raw40107step1 raw40107step1Labels = mixedMoment B raw40107step2 raw40107step2Labels := by
      have ha : raw40107step2 = -raw40107step1 := by apply Matrix.ext; change ∀ i j, raw40107step2 i j = -(raw40107step1 i j); unfold raw40107step2 raw40107step1; decide +kernel
      have hl : raw40107step2Labels = raw40107step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node312 node312Labels := by rfl

def raw40108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -3, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40108Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -3, 4], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw40108step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40108step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -3, 4], ![0, 1, -1], ![2, 0, -2]]
def raw40108step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40108step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40108step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40108step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40108step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40108 raw40108Labels = mixedMoment B node111 node111Labels := by
  calc
    mixedMoment B raw40108 raw40108Labels = mixedMoment B raw40108step0 raw40108step0Labels := by
      have hz : ∀ j, raw40108 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40108step0 = (fun i j => raw40108 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40108step0 raw40108; decide +kernel
      have hl : raw40108step0Labels = raw40108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40108 raw40108Labels permutation520 hz
    mixedMoment B raw40108step0 raw40108step0Labels = mixedMoment B raw40108step1 raw40108step1Labels := by
      have hz : ∀ j, raw40108step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40108step1 = (fun i j => raw40108step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40108step1 raw40108step0; decide +kernel
      have hl : raw40108step1Labels = raw40108step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40108step0 raw40108step0Labels permutation104 hz
    mixedMoment B raw40108step1 raw40108step1Labels = mixedMoment B raw40108step2 raw40108step2Labels := by
      have ha : raw40108step2 = (fun i j => raw40108step1 (permutation16 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40108step2 raw40108step1; decide +kernel
      have hl : raw40108step2Labels = raw40108step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40108step1 raw40108step1Labels permutation16 permutation6
    mixedMoment B raw40108step2 raw40108step2Labels = mixedMoment B raw40108step3 raw40108step3Labels := by
      have ha : raw40108step3 = -raw40108step2 := by apply Matrix.ext; change ∀ i j, raw40108step3 i j = -(raw40108step2 i j); unfold raw40108step3 raw40108step2; decide +kernel
      have hl : raw40108step3Labels = raw40108step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node111 node111Labels := by rfl

def raw40109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -3, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw40109Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -3, 4], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw40109step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40109step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -3, 4], ![0, 0, 0], ![2, 1, -3]]
def raw40109step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40109step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 2, -1], ![-1, -3, 4], ![2, 1, -3]]
def raw40109step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40109step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, -1, 2], ![-3, 2, 1]]
def raw40109step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40109step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw40109step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40109 raw40109Labels = mixedMoment B node112 node112Labels := by
  calc
    mixedMoment B raw40109 raw40109Labels = mixedMoment B raw40109step0 raw40109step0Labels := by
      have hz : ∀ j, raw40109 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40109step0 = (fun i j => raw40109 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40109step0 raw40109; decide +kernel
      have hl : raw40109step0Labels = raw40109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40109 raw40109Labels permutation520 hz
    mixedMoment B raw40109step0 raw40109step0Labels = mixedMoment B raw40109step1 raw40109step1Labels := by
      have hz : ∀ j, raw40109step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40109step1 = (fun i j => raw40109step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40109step1 raw40109step0; decide +kernel
      have hl : raw40109step1Labels = raw40109step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40109step0 raw40109step0Labels permutation104 hz
    mixedMoment B raw40109step1 raw40109step1Labels = mixedMoment B raw40109step2 raw40109step2Labels := by
      have hz : ∀ j, raw40109step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40109step2 = (fun i j => raw40109step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40109step2 raw40109step1; decide +kernel
      have hl : raw40109step2Labels = raw40109step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40109step1 raw40109step1Labels permutation20 hz
    mixedMoment B raw40109step2 raw40109step2Labels = mixedMoment B raw40109step3 raw40109step3Labels := by
      have ha : raw40109step3 = (fun i j => raw40109step2 (permutation4 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40109step3 raw40109step2; decide +kernel
      have hl : raw40109step3Labels = raw40109step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40109step2 raw40109step2Labels permutation4 permutation6
    mixedMoment B raw40109step3 raw40109step3Labels = mixedMoment B raw40109step4 raw40109step4Labels := by
      have ha : raw40109step4 = -raw40109step3 := by apply Matrix.ext; change ∀ i j, raw40109step4 i j = -(raw40109step3 i j); unfold raw40109step4 raw40109step3; decide +kernel
      have hl : raw40109step4Labels = raw40109step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node112 node112Labels := by rfl

def raw40110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40110Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40110step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40110step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw40110step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40110step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw40110step2Labels : Fin 2 → Fin 1 := ![0, 0]

def raw40110step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw40110step3Labels : Fin 2 → Fin 1 := ![0, 0]

def raw40110step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw40110step4Labels : Fin 2 → Fin 1 := ![0, 0]

theorem canonical40110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40110 raw40110Labels = mixedMoment B node0 node0Labels := by
  calc
    mixedMoment B raw40110 raw40110Labels = mixedMoment B raw40110step0 raw40110step0Labels := by
      have hz : ∀ j, raw40110 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40110step0 = (fun i j => raw40110 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40110step0 raw40110; decide +kernel
      have hl : raw40110step0Labels = raw40110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40110 raw40110Labels permutation520 hz
    mixedMoment B raw40110step0 raw40110step0Labels = mixedMoment B raw40110step1 raw40110step1Labels := by
      have hz : ∀ j, raw40110step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40110step1 = (fun i j => raw40110step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40110step1 raw40110step0; decide +kernel
      have hl : raw40110step1Labels = raw40110step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40110step0 raw40110step0Labels permutation104 hz
    mixedMoment B raw40110step1 raw40110step1Labels = mixedMoment B raw40110step2 raw40110step2Labels := by
      have hz : ∀ i, raw40110step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw40110step2 = (fun i j => raw40110step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw40110step2 raw40110step1; decide +kernel
      have hl : raw40110step2Labels = (fun j => raw40110step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw40110step1 raw40110step1Labels permutation6 hz
    mixedMoment B raw40110step2 raw40110step2Labels = mixedMoment B raw40110step3 raw40110step3Labels := by
      have ha : raw40110step3 = (fun i j => raw40110step2 (permutation26 i) (permutation0 j)) := by apply Matrix.ext; unfold raw40110step3 raw40110step2; decide +kernel
      have hl : raw40110step3Labels = raw40110step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40110step2 raw40110step2Labels permutation26 permutation0
    mixedMoment B raw40110step3 raw40110step3Labels = mixedMoment B raw40110step4 raw40110step4Labels := by
      have ha : raw40110step4 = -raw40110step3 := by apply Matrix.ext; change ∀ i j, raw40110step4 i j = -(raw40110step3 i j); unfold raw40110step4 raw40110step3; decide +kernel
      have hl : raw40110step4Labels = raw40110step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node0 node0Labels := by rfl

def raw40111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40111Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40111step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40111step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw40111step1Labels : Fin 2 → Fin 1 := ![0, 0]

def raw40111step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw40111step2Labels : Fin 2 → Fin 1 := ![0, 0]

def raw40111step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw40111step3Labels : Fin 2 → Fin 1 := ![0, 0]

theorem canonical40111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40111 raw40111Labels = mixedMoment B node3 node3Labels := by
  calc
    mixedMoment B raw40111 raw40111Labels = mixedMoment B raw40111step0 raw40111step0Labels := by
      have hz : ∀ j, raw40111 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40111step0 = (fun i j => raw40111 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40111step0 raw40111; decide +kernel
      have hl : raw40111step0Labels = raw40111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40111 raw40111Labels permutation434 hz
    mixedMoment B raw40111step0 raw40111step0Labels = mixedMoment B raw40111step1 raw40111step1Labels := by
      have hz : ∀ i, raw40111step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw40111step1 = (fun i j => raw40111step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw40111step1 raw40111step0; decide +kernel
      have hl : raw40111step1Labels = (fun j => raw40111step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw40111step0 raw40111step0Labels permutation6 hz
    mixedMoment B raw40111step1 raw40111step1Labels = mixedMoment B raw40111step2 raw40111step2Labels := by
      have ha : raw40111step2 = (fun i j => raw40111step1 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw40111step2 raw40111step1; decide +kernel
      have hl : raw40111step2Labels = raw40111step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40111step1 raw40111step1Labels permutation146 permutation0
    mixedMoment B raw40111step2 raw40111step2Labels = mixedMoment B raw40111step3 raw40111step3Labels := by
      have ha : raw40111step3 = -raw40111step2 := by apply Matrix.ext; change ∀ i j, raw40111step3 i j = -(raw40111step2 i j); unfold raw40111step3 raw40111step2; decide +kernel
      have hl : raw40111step3Labels = raw40111step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3 node3Labels := by rfl

def raw40112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40112Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40112step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40112step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40112 raw40112Labels = mixedMoment B node411 node411Labels := by
  calc
    mixedMoment B raw40112 raw40112Labels = mixedMoment B raw40112step0 raw40112step0Labels := by
      have hz : ∀ j, raw40112 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40112step0 = (fun i j => raw40112 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40112step0 raw40112; decide +kernel
      have hl : raw40112step0Labels = raw40112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40112 raw40112Labels permutation434 hz
    mixedMoment B raw40112step0 raw40112step0Labels = mixedMoment B raw40112step1 raw40112step1Labels := by
      have ha : raw40112step1 = (fun i j => raw40112step0 (permutation122 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40112step1 raw40112step0; decide +kernel
      have hl : raw40112step1Labels = raw40112step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40112step0 raw40112step0Labels permutation122 permutation4
    _ = mixedMoment B node411 node411Labels := by rfl

def raw40113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40113Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40113step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw40113step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40113step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40113step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40113 raw40113Labels = mixedMoment B node492 node492Labels := by
  calc
    mixedMoment B raw40113 raw40113Labels = mixedMoment B raw40113step0 raw40113step0Labels := by
      have ha : raw40113step0 = (fun i j => raw40113 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw40113step0 raw40113; decide +kernel
      have hl : raw40113step0Labels = raw40113Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40113 raw40113Labels permutation683 permutation2
    mixedMoment B raw40113step0 raw40113step0Labels = mixedMoment B raw40113step1 raw40113step1Labels := by
      have ha : raw40113step1 = -raw40113step0 := by apply Matrix.ext; change ∀ i j, raw40113step1 i j = -(raw40113step0 i j); unfold raw40113step1 raw40113step0; decide +kernel
      have hl : raw40113step1Labels = raw40113step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node492 node492Labels := by rfl

def raw40114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw40114Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0]]
def raw40114step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw40114step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40114step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40114step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40114 raw40114Labels = mixedMoment B node265 node265Labels := by
  calc
    mixedMoment B raw40114 raw40114Labels = mixedMoment B raw40114step0 raw40114step0Labels := by
      have hz : ∀ j, raw40114 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40114step0 = (fun i j => raw40114 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40114step0 raw40114; decide +kernel
      have hl : raw40114step0Labels = raw40114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40114 raw40114Labels permutation520 hz
    mixedMoment B raw40114step0 raw40114step0Labels = mixedMoment B raw40114step1 raw40114step1Labels := by
      have ha : raw40114step1 = (fun i j => raw40114step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40114step1 raw40114step0; decide +kernel
      have hl : raw40114step1Labels = raw40114step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40114step0 raw40114step0Labels permutation150 permutation3
    mixedMoment B raw40114step1 raw40114step1Labels = mixedMoment B raw40114step2 raw40114step2Labels := by
      have ha : raw40114step2 = -raw40114step1 := by apply Matrix.ext; change ∀ i j, raw40114step2 i j = -(raw40114step1 i j); unfold raw40114step2 raw40114step1; decide +kernel
      have hl : raw40114step2Labels = raw40114step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node265 node265Labels := by rfl

def raw40115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw40115Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40115step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw40115step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40115step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40115step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40115 raw40115Labels = mixedMoment B node464 node464Labels := by
  calc
    mixedMoment B raw40115 raw40115Labels = mixedMoment B raw40115step0 raw40115step0Labels := by
      have ha : raw40115step0 = (fun i j => raw40115 (permutation687 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40115step0 raw40115; decide +kernel
      have hl : raw40115step0Labels = raw40115Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40115 raw40115Labels permutation687 permutation3
    mixedMoment B raw40115step0 raw40115step0Labels = mixedMoment B raw40115step1 raw40115step1Labels := by
      have ha : raw40115step1 = -raw40115step0 := by apply Matrix.ext; change ∀ i j, raw40115step1 i j = -(raw40115step0 i j); unfold raw40115step1 raw40115step0; decide +kernel
      have hl : raw40115step1Labels = raw40115step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node464 node464Labels := by rfl

def raw40116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw40116Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40116step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40116step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40116 raw40116Labels = mixedMoment B node382 node382Labels := by
  calc
    mixedMoment B raw40116 raw40116Labels = mixedMoment B raw40116step0 raw40116step0Labels := by
      have ha : raw40116step0 = (fun i j => raw40116 (permutation547 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40116step0 raw40116; decide +kernel
      have hl : raw40116step0Labels = raw40116Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40116 raw40116Labels permutation547 permutation4
    _ = mixedMoment B node382 node382Labels := by rfl

def raw40117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw40117Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40117step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw40117step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40117step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40117step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40117 raw40117Labels = mixedMoment B node5509 node5509Labels := by
  calc
    mixedMoment B raw40117 raw40117Labels = mixedMoment B raw40117step0 raw40117step0Labels := by
      have hz : ∀ j, raw40117 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40117step0 = (fun i j => raw40117 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40117step0 raw40117; decide +kernel
      have hl : raw40117step0Labels = raw40117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40117 raw40117Labels permutation434 hz
    mixedMoment B raw40117step0 raw40117step0Labels = mixedMoment B raw40117step1 raw40117step1Labels := by
      have ha : raw40117step1 = (fun i j => raw40117step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40117step1 raw40117step0; decide +kernel
      have hl : raw40117step1Labels = raw40117step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40117step0 raw40117step0Labels permutation150 permutation3
    mixedMoment B raw40117step1 raw40117step1Labels = mixedMoment B raw40117step2 raw40117step2Labels := by
      have ha : raw40117step2 = -raw40117step1 := by apply Matrix.ext; change ∀ i j, raw40117step2 i j = -(raw40117step1 i j); unfold raw40117step2 raw40117step1; decide +kernel
      have hl : raw40117step2Labels = raw40117step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5509 node5509Labels := by rfl

def raw40118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw40118Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2], ![2, 1, -3]]
def raw40118step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw40118step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40118 raw40118Labels = mixedMoment B node386 node386Labels := by
  calc
    mixedMoment B raw40118 raw40118Labels = mixedMoment B raw40118step0 raw40118step0Labels := by
      have hz : ∀ j, raw40118 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40118step0 = (fun i j => raw40118 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40118step0 raw40118; decide +kernel
      have hl : raw40118step0Labels = raw40118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40118 raw40118Labels permutation434 hz
    mixedMoment B raw40118step0 raw40118step0Labels = mixedMoment B raw40118step1 raw40118step1Labels := by
      have ha : raw40118step1 = (fun i j => raw40118step0 (permutation116 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40118step1 raw40118step0; decide +kernel
      have hl : raw40118step1Labels = raw40118step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40118step0 raw40118step0Labels permutation116 permutation4
    _ = mixedMoment B node386 node386Labels := by rfl

def raw40119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40119Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40119step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw40119step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40119step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40119step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40119 raw40119Labels = mixedMoment B node488 node488Labels := by
  calc
    mixedMoment B raw40119 raw40119Labels = mixedMoment B raw40119step0 raw40119step0Labels := by
      have ha : raw40119step0 = (fun i j => raw40119 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw40119step0 raw40119; decide +kernel
      have hl : raw40119step0Labels = raw40119Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40119 raw40119Labels permutation683 permutation2
    mixedMoment B raw40119step0 raw40119step0Labels = mixedMoment B raw40119step1 raw40119step1Labels := by
      have ha : raw40119step1 = -raw40119step0 := by apply Matrix.ext; change ∀ i j, raw40119step1 i j = -(raw40119step0 i j); unfold raw40119step1 raw40119step0; decide +kernel
      have hl : raw40119step1Labels = raw40119step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node488 node488Labels := by rfl

def raw40120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40120Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40120step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40120step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40120 raw40120Labels = mixedMoment B node373 node373Labels := by
  calc
    mixedMoment B raw40120 raw40120Labels = mixedMoment B raw40120step0 raw40120step0Labels := by
      have ha : raw40120step0 = (fun i j => raw40120 (permutation665 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40120step0 raw40120; decide +kernel
      have hl : raw40120step0Labels = raw40120Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40120 raw40120Labels permutation665 permutation7
    _ = mixedMoment B node373 node373Labels := by rfl

def raw40121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40121Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40121step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw40121step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40121step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw40121step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40121 raw40121Labels = mixedMoment B node494 node494Labels := by
  calc
    mixedMoment B raw40121 raw40121Labels = mixedMoment B raw40121step0 raw40121step0Labels := by
      have hz : ∀ j, raw40121 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40121step0 = (fun i j => raw40121 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40121step0 raw40121; decide +kernel
      have hl : raw40121step0Labels = raw40121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40121 raw40121Labels permutation434 hz
    mixedMoment B raw40121step0 raw40121step0Labels = mixedMoment B raw40121step1 raw40121step1Labels := by
      have ha : raw40121step1 = (fun i j => raw40121step0 (permutation146 i) (permutation2 j)) := by apply Matrix.ext; unfold raw40121step1 raw40121step0; decide +kernel
      have hl : raw40121step1Labels = raw40121step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40121step0 raw40121step0Labels permutation146 permutation2
    mixedMoment B raw40121step1 raw40121step1Labels = mixedMoment B raw40121step2 raw40121step2Labels := by
      have ha : raw40121step2 = -raw40121step1 := by apply Matrix.ext; change ∀ i j, raw40121step2 i j = -(raw40121step1 i j); unfold raw40121step2 raw40121step1; decide +kernel
      have hl : raw40121step2Labels = raw40121step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node494 node494Labels := by rfl

def raw40122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40122Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40122step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40122step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40122step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40122step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40122 raw40122Labels = mixedMoment B node373 node373Labels := by
  calc
    mixedMoment B raw40122 raw40122Labels = mixedMoment B raw40122step0 raw40122step0Labels := by
      have ha : raw40122step0 = (fun i j => raw40122 (permutation399 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40122step0 raw40122; decide +kernel
      have hl : raw40122step0Labels = raw40122Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40122 raw40122Labels permutation399 permutation6
    mixedMoment B raw40122step0 raw40122step0Labels = mixedMoment B raw40122step1 raw40122step1Labels := by
      have ha : raw40122step1 = -raw40122step0 := by apply Matrix.ext; change ∀ i j, raw40122step1 i j = -(raw40122step0 i j); unfold raw40122step1 raw40122step0; decide +kernel
      have hl : raw40122step1Labels = raw40122step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node373 node373Labels := by rfl

def raw40123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw40123Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3], ![1, -1, 0], ![2, 1, -3]]
def raw40123step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw40123step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40123step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw40123step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40123 raw40123Labels = mixedMoment B node374 node374Labels := by
  calc
    mixedMoment B raw40123 raw40123Labels = mixedMoment B raw40123step0 raw40123step0Labels := by
      have hz : ∀ j, raw40123 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40123step0 = (fun i j => raw40123 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40123step0 raw40123; decide +kernel
      have hl : raw40123step0Labels = raw40123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40123 raw40123Labels permutation434 hz
    mixedMoment B raw40123step0 raw40123step0Labels = mixedMoment B raw40123step1 raw40123step1Labels := by
      have ha : raw40123step1 = (fun i j => raw40123step0 (permutation92 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40123step1 raw40123step0; decide +kernel
      have hl : raw40123step1Labels = raw40123step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40123step0 raw40123step0Labels permutation92 permutation6
    mixedMoment B raw40123step1 raw40123step1Labels = mixedMoment B raw40123step2 raw40123step2Labels := by
      have ha : raw40123step2 = -raw40123step1 := by apply Matrix.ext; change ∀ i j, raw40123step2 i j = -(raw40123step1 i j); unfold raw40123step2 raw40123step1; decide +kernel
      have hl : raw40123step2Labels = raw40123step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node374 node374Labels := by rfl

def raw40124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40124Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40124step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40124step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40124 raw40124Labels = mixedMoment B node5509 node5509Labels := by
  calc
    mixedMoment B raw40124 raw40124Labels = mixedMoment B raw40124step0 raw40124step0Labels := by
      have hz : ∀ j, raw40124 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40124step0 = (fun i j => raw40124 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40124step0 raw40124; decide +kernel
      have hl : raw40124step0Labels = raw40124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40124 raw40124Labels permutation434 hz
    mixedMoment B raw40124step0 raw40124step0Labels = mixedMoment B raw40124step1 raw40124step1Labels := by
      have ha : raw40124step1 = (fun i j => raw40124step0 (permutation150 i) (permutation5 j)) := by apply Matrix.ext; unfold raw40124step1 raw40124step0; decide +kernel
      have hl : raw40124step1Labels = raw40124step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40124step0 raw40124step0Labels permutation150 permutation5
    _ = mixedMoment B node5509 node5509Labels := by rfl

def raw40125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40125Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40125step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40125 raw40125Labels = mixedMoment B node488 node488Labels := by
  calc
    mixedMoment B raw40125 raw40125Labels = mixedMoment B raw40125step0 raw40125step0Labels := by
      have ha : raw40125step0 = (fun i j => raw40125 (permutation514 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40125step0 raw40125; decide +kernel
      have hl : raw40125step0Labels = raw40125Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40125 raw40125Labels permutation514 permutation4
    _ = mixedMoment B node488 node488Labels := by rfl

def raw40126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw40126Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw40126step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40126step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw40126step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40126step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw40126step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40126step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]
def raw40126step3Labels : Fin 2 → Fin 1 := ![0, 0]

def raw40126step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![2, -2], ![-1, 1], ![-1, 1]]
def raw40126step4Labels : Fin 2 → Fin 1 := ![0, 0]

def raw40126step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw40126step5Labels : Fin 2 → Fin 1 := ![0, 0]

theorem canonical40126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40126 raw40126Labels = mixedMoment B node5 node5Labels := by
  calc
    mixedMoment B raw40126 raw40126Labels = mixedMoment B raw40126step0 raw40126step0Labels := by
      have hz : ∀ j, raw40126 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40126step0 = (fun i j => raw40126 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40126step0 raw40126; decide +kernel
      have hl : raw40126step0Labels = raw40126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40126 raw40126Labels permutation520 hz
    mixedMoment B raw40126step0 raw40126step0Labels = mixedMoment B raw40126step1 raw40126step1Labels := by
      have hz : ∀ j, raw40126step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40126step1 = (fun i j => raw40126step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40126step1 raw40126step0; decide +kernel
      have hl : raw40126step1Labels = raw40126step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40126step0 raw40126step0Labels permutation104 hz
    mixedMoment B raw40126step1 raw40126step1Labels = mixedMoment B raw40126step2 raw40126step2Labels := by
      have hz : ∀ j, raw40126step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40126step2 = (fun i j => raw40126step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40126step2 raw40126step1; decide +kernel
      have hl : raw40126step2Labels = raw40126step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40126step1 raw40126step1Labels permutation20 hz
    mixedMoment B raw40126step2 raw40126step2Labels = mixedMoment B raw40126step3 raw40126step3Labels := by
      have hz : ∀ i, raw40126step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw40126step3 = (fun i j => raw40126step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw40126step3 raw40126step2; decide +kernel
      have hl : raw40126step3Labels = (fun j => raw40126step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw40126step2 raw40126step2Labels permutation6 hz
    mixedMoment B raw40126step3 raw40126step3Labels = mixedMoment B raw40126step4 raw40126step4Labels := by
      have ha : raw40126step4 = (fun i j => raw40126step3 (permutation6 i) (permutation0 j)) := by apply Matrix.ext; unfold raw40126step4 raw40126step3; decide +kernel
      have hl : raw40126step4Labels = raw40126step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40126step3 raw40126step3Labels permutation6 permutation0
    mixedMoment B raw40126step4 raw40126step4Labels = mixedMoment B raw40126step5 raw40126step5Labels := by
      have ha : raw40126step5 = -raw40126step4 := by apply Matrix.ext; change ∀ i j, raw40126step5 i j = -(raw40126step4 i j); unfold raw40126step5 raw40126step4; decide +kernel
      have hl : raw40126step5Labels = raw40126step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5 node5Labels := by rfl

def raw40127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw40127Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw40127step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40127step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1]]
def raw40127step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40127step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw40127step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40127step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40127step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40127 raw40127Labels = mixedMoment B node529 node529Labels := by
  calc
    mixedMoment B raw40127 raw40127Labels = mixedMoment B raw40127step0 raw40127step0Labels := by
      have hz : ∀ j, raw40127 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40127step0 = (fun i j => raw40127 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40127step0 raw40127; decide +kernel
      have hl : raw40127step0Labels = raw40127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40127 raw40127Labels permutation434 hz
    mixedMoment B raw40127step0 raw40127step0Labels = mixedMoment B raw40127step1 raw40127step1Labels := by
      have hz : ∀ j, raw40127step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40127step1 = (fun i j => raw40127step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40127step1 raw40127step0; decide +kernel
      have hl : raw40127step1Labels = raw40127step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40127step0 raw40127step0Labels permutation80 hz
    mixedMoment B raw40127step1 raw40127step1Labels = mixedMoment B raw40127step2 raw40127step2Labels := by
      have ha : raw40127step2 = (fun i j => raw40127step1 (permutation30 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40127step2 raw40127step1; decide +kernel
      have hl : raw40127step2Labels = raw40127step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40127step1 raw40127step1Labels permutation30 permutation3
    mixedMoment B raw40127step2 raw40127step2Labels = mixedMoment B raw40127step3 raw40127step3Labels := by
      have ha : raw40127step3 = -raw40127step2 := by apply Matrix.ext; change ∀ i j, raw40127step3 i j = -(raw40127step2 i j); unfold raw40127step3 raw40127step2; decide +kernel
      have hl : raw40127step3Labels = raw40127step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node529 node529Labels := by rfl

def raw40128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw40128Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw40128step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40128step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2]]
def raw40128step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40128step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw40128step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40128step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw40128step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40128 raw40128Labels = mixedMoment B node505 node505Labels := by
  calc
    mixedMoment B raw40128 raw40128Labels = mixedMoment B raw40128step0 raw40128step0Labels := by
      have hz : ∀ j, raw40128 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40128step0 = (fun i j => raw40128 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40128step0 raw40128; decide +kernel
      have hl : raw40128step0Labels = raw40128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40128 raw40128Labels permutation434 hz
    mixedMoment B raw40128step0 raw40128step0Labels = mixedMoment B raw40128step1 raw40128step1Labels := by
      have hz : ∀ j, raw40128step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40128step1 = (fun i j => raw40128step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40128step1 raw40128step0; decide +kernel
      have hl : raw40128step1Labels = raw40128step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40128step0 raw40128step0Labels permutation80 hz
    mixedMoment B raw40128step1 raw40128step1Labels = mixedMoment B raw40128step2 raw40128step2Labels := by
      have ha : raw40128step2 = (fun i j => raw40128step1 (permutation20 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40128step2 raw40128step1; decide +kernel
      have hl : raw40128step2Labels = raw40128step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40128step1 raw40128step1Labels permutation20 permutation6
    mixedMoment B raw40128step2 raw40128step2Labels = mixedMoment B raw40128step3 raw40128step3Labels := by
      have ha : raw40128step3 = -raw40128step2 := by apply Matrix.ext; change ∀ i j, raw40128step3 i j = -(raw40128step2 i j); unfold raw40128step3 raw40128step2; decide +kernel
      have hl : raw40128step3Labels = raw40128step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node505 node505Labels := by rfl

def raw40129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw40129Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw40129step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40129step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3], ![2, 1, -3]]
def raw40129step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40129step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw40129step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40129step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw40129step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40129 raw40129Labels = mixedMoment B node262 node262Labels := by
  calc
    mixedMoment B raw40129 raw40129Labels = mixedMoment B raw40129step0 raw40129step0Labels := by
      have hz : ∀ j, raw40129 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40129step0 = (fun i j => raw40129 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40129step0 raw40129; decide +kernel
      have hl : raw40129step0Labels = raw40129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40129 raw40129Labels permutation434 hz
    mixedMoment B raw40129step0 raw40129step0Labels = mixedMoment B raw40129step1 raw40129step1Labels := by
      have hz : ∀ j, raw40129step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40129step1 = (fun i j => raw40129step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40129step1 raw40129step0; decide +kernel
      have hl : raw40129step1Labels = raw40129step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40129step0 raw40129step0Labels permutation80 hz
    mixedMoment B raw40129step1 raw40129step1Labels = mixedMoment B raw40129step2 raw40129step2Labels := by
      have ha : raw40129step2 = (fun i j => raw40129step1 (permutation20 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40129step2 raw40129step1; decide +kernel
      have hl : raw40129step2Labels = raw40129step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40129step1 raw40129step1Labels permutation20 permutation6
    mixedMoment B raw40129step2 raw40129step2Labels = mixedMoment B raw40129step3 raw40129step3Labels := by
      have ha : raw40129step3 = -raw40129step2 := by apply Matrix.ext; change ∀ i j, raw40129step3 i j = -(raw40129step2 i j); unfold raw40129step3 raw40129step2; decide +kernel
      have hl : raw40129step3Labels = raw40129step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node262 node262Labels := by rfl

def raw40130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw40130Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw40130step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40130step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -3, 2]]
def raw40130step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40130step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw40130step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40130 raw40130Labels = mixedMoment B node416 node416Labels := by
  calc
    mixedMoment B raw40130 raw40130Labels = mixedMoment B raw40130step0 raw40130step0Labels := by
      have hz : ∀ j, raw40130 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40130step0 = (fun i j => raw40130 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40130step0 raw40130; decide +kernel
      have hl : raw40130step0Labels = raw40130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40130 raw40130Labels permutation434 hz
    mixedMoment B raw40130step0 raw40130step0Labels = mixedMoment B raw40130step1 raw40130step1Labels := by
      have hz : ∀ j, raw40130step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40130step1 = (fun i j => raw40130step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40130step1 raw40130step0; decide +kernel
      have hl : raw40130step1Labels = raw40130step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40130step0 raw40130step0Labels permutation80 hz
    mixedMoment B raw40130step1 raw40130step1Labels = mixedMoment B raw40130step2 raw40130step2Labels := by
      have ha : raw40130step2 = (fun i j => raw40130step1 (permutation26 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40130step2 raw40130step1; decide +kernel
      have hl : raw40130step2Labels = raw40130step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40130step1 raw40130step1Labels permutation26 permutation4
    _ = mixedMoment B node416 node416Labels := by rfl

def raw40131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40131Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40131step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40131step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40131step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40131step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw40131step2Labels : Fin 2 → Fin 1 := ![0, 0]

theorem canonical40131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40131 raw40131Labels = mixedMoment B node7 node7Labels := by
  calc
    mixedMoment B raw40131 raw40131Labels = mixedMoment B raw40131step0 raw40131step0Labels := by
      have hz : ∀ j, raw40131 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40131step0 = (fun i j => raw40131 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40131step0 raw40131; decide +kernel
      have hl : raw40131step0Labels = raw40131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40131 raw40131Labels permutation434 hz
    mixedMoment B raw40131step0 raw40131step0Labels = mixedMoment B raw40131step1 raw40131step1Labels := by
      have hz : ∀ j, raw40131step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40131step1 = (fun i j => raw40131step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40131step1 raw40131step0; decide +kernel
      have hl : raw40131step1Labels = raw40131step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40131step0 raw40131step0Labels permutation80 hz
    mixedMoment B raw40131step1 raw40131step1Labels = mixedMoment B raw40131step2 raw40131step2Labels := by
      have hz : ∀ i, raw40131step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw40131step2 = (fun i j => raw40131step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw40131step2 raw40131step1; decide +kernel
      have hl : raw40131step2Labels = (fun j => raw40131step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw40131step1 raw40131step1Labels permutation6 hz
    _ = mixedMoment B node7 node7Labels := by rfl

def raw40132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw40132Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw40132step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40132step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw40132step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40132step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40132step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40132 raw40132Labels = mixedMoment B node504 node504Labels := by
  calc
    mixedMoment B raw40132 raw40132Labels = mixedMoment B raw40132step0 raw40132step0Labels := by
      have hz : ∀ j, raw40132 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40132step0 = (fun i j => raw40132 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40132step0 raw40132; decide +kernel
      have hl : raw40132step0Labels = raw40132Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40132 raw40132Labels permutation346 hz
    mixedMoment B raw40132step0 raw40132step0Labels = mixedMoment B raw40132step1 raw40132step1Labels := by
      have ha : raw40132step1 = (fun i j => raw40132step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw40132step1 raw40132step0; decide +kernel
      have hl : raw40132step1Labels = raw40132step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40132step0 raw40132step0Labels permutation144 permutation2
    mixedMoment B raw40132step1 raw40132step1Labels = mixedMoment B raw40132step2 raw40132step2Labels := by
      have ha : raw40132step2 = -raw40132step1 := by apply Matrix.ext; change ∀ i j, raw40132step2 i j = -(raw40132step1 i j); unfold raw40132step2 raw40132step1; decide +kernel
      have hl : raw40132step2Labels = raw40132step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node504 node504Labels := by rfl

def raw40133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw40133Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw40133step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40133step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw40133step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40133 raw40133Labels = mixedMoment B node397 node397Labels := by
  calc
    mixedMoment B raw40133 raw40133Labels = mixedMoment B raw40133step0 raw40133step0Labels := by
      have hz : ∀ j, raw40133 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40133step0 = (fun i j => raw40133 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40133step0 raw40133; decide +kernel
      have hl : raw40133step0Labels = raw40133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40133 raw40133Labels permutation346 hz
    mixedMoment B raw40133step0 raw40133step0Labels = mixedMoment B raw40133step1 raw40133step1Labels := by
      have ha : raw40133step1 = (fun i j => raw40133step0 (permutation128 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40133step1 raw40133step0; decide +kernel
      have hl : raw40133step1Labels = raw40133step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40133step0 raw40133step0Labels permutation128 permutation7
    _ = mixedMoment B node397 node397Labels := by rfl

def raw40134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw40134Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw40134step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw40134step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40134 raw40134Labels = mixedMoment B node532 node532Labels := by
  calc
    mixedMoment B raw40134 raw40134Labels = mixedMoment B raw40134step0 raw40134step0Labels := by
      have hz : ∀ j, raw40134 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40134step0 = (fun i j => raw40134 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40134step0 raw40134; decide +kernel
      have hl : raw40134step0Labels = raw40134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40134 raw40134Labels permutation346 hz
    mixedMoment B raw40134step0 raw40134step0Labels = mixedMoment B raw40134step1 raw40134step1Labels := by
      have ha : raw40134step1 = (fun i j => raw40134step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40134step1 raw40134step0; decide +kernel
      have hl : raw40134step1Labels = raw40134step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40134step0 raw40134step0Labels permutation32 permutation3
    _ = mixedMoment B node532 node532Labels := by rfl

def raw40135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw40135Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw40135step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw40135step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40135 raw40135Labels = mixedMoment B node494 node494Labels := by
  calc
    mixedMoment B raw40135 raw40135Labels = mixedMoment B raw40135step0 raw40135step0Labels := by
      have hz : ∀ j, raw40135 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40135step0 = (fun i j => raw40135 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40135step0 raw40135; decide +kernel
      have hl : raw40135step0Labels = raw40135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40135 raw40135Labels permutation346 hz
    mixedMoment B raw40135step0 raw40135step0Labels = mixedMoment B raw40135step1 raw40135step1Labels := by
      have ha : raw40135step1 = (fun i j => raw40135step0 (permutation98 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40135step1 raw40135step0; decide +kernel
      have hl : raw40135step1Labels = raw40135step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40135step0 raw40135step0Labels permutation98 permutation4
    _ = mixedMoment B node494 node494Labels := by rfl

def raw40136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40136Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw40136step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40136step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40136 raw40136Labels = mixedMoment B node531 node531Labels := by
  calc
    mixedMoment B raw40136 raw40136Labels = mixedMoment B raw40136step0 raw40136step0Labels := by
      have ha : raw40136step0 = (fun i j => raw40136 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw40136step0 raw40136; decide +kernel
      have hl : raw40136step0Labels = raw40136Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40136 raw40136Labels permutation583 permutation2
    mixedMoment B raw40136step0 raw40136step0Labels = mixedMoment B raw40136step1 raw40136step1Labels := by
      have ha : raw40136step1 = -raw40136step0 := by apply Matrix.ext; change ∀ i j, raw40136step1 i j = -(raw40136step0 i j); unfold raw40136step1 raw40136step0; decide +kernel
      have hl : raw40136step1Labels = raw40136step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node531 node531Labels := by rfl

def raw40137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw40137Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40137step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw40137step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40137step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40137step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40137 raw40137Labels = mixedMoment B node259 node259Labels := by
  calc
    mixedMoment B raw40137 raw40137Labels = mixedMoment B raw40137step0 raw40137step0Labels := by
      have ha : raw40137step0 = (fun i j => raw40137 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40137step0 raw40137; decide +kernel
      have hl : raw40137step0Labels = raw40137Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40137 raw40137Labels permutation662 permutation3
    mixedMoment B raw40137step0 raw40137step0Labels = mixedMoment B raw40137step1 raw40137step1Labels := by
      have ha : raw40137step1 = -raw40137step0 := by apply Matrix.ext; change ∀ i j, raw40137step1 i j = -(raw40137step0 i j); unfold raw40137step1 raw40137step0; decide +kernel
      have hl : raw40137step1Labels = raw40137step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node259 node259Labels := by rfl

def raw40138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40138Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40138step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw40138step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40138step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40138step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40138 raw40138Labels = mixedMoment B node520 node520Labels := by
  calc
    mixedMoment B raw40138 raw40138Labels = mixedMoment B raw40138step0 raw40138step0Labels := by
      have ha : raw40138step0 = (fun i j => raw40138 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40138step0 raw40138; decide +kernel
      have hl : raw40138step0Labels = raw40138Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40138 raw40138Labels permutation686 permutation3
    mixedMoment B raw40138step0 raw40138step0Labels = mixedMoment B raw40138step1 raw40138step1Labels := by
      have ha : raw40138step1 = -raw40138step0 := by apply Matrix.ext; change ∀ i j, raw40138step1 i j = -(raw40138step0 i j); unfold raw40138step1 raw40138step0; decide +kernel
      have hl : raw40138step1Labels = raw40138step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node520 node520Labels := by rfl

def raw40139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw40139Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40139step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw40139step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40139 raw40139Labels = mixedMoment B node327 node327Labels := by
  calc
    mixedMoment B raw40139 raw40139Labels = mixedMoment B raw40139step0 raw40139step0Labels := by
      have ha : raw40139step0 = (fun i j => raw40139 (permutation647 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40139step0 raw40139; decide +kernel
      have hl : raw40139step0Labels = raw40139Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40139 raw40139Labels permutation647 permutation7
    _ = mixedMoment B node327 node327Labels := by rfl

def raw40140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40140Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40140step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40140step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40140 raw40140Labels = mixedMoment B node376 node376Labels := by
  calc
    mixedMoment B raw40140 raw40140Labels = mixedMoment B raw40140step0 raw40140step0Labels := by
      have ha : raw40140step0 = (fun i j => raw40140 (permutation669 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40140step0 raw40140; decide +kernel
      have hl : raw40140step0Labels = raw40140Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40140 raw40140Labels permutation669 permutation7
    _ = mixedMoment B node376 node376Labels := by rfl

def raw40141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40141Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40141step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40141 raw40141Labels = mixedMoment B node479 node479Labels := by
  calc
    mixedMoment B raw40141 raw40141Labels = mixedMoment B raw40141step0 raw40141step0Labels := by
      have ha : raw40141step0 = (fun i j => raw40141 (permutation659 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40141step0 raw40141; decide +kernel
      have hl : raw40141step0Labels = raw40141Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40141 raw40141Labels permutation659 permutation7
    _ = mixedMoment B node479 node479Labels := by rfl

def raw40142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw40142Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40142step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40142step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40142 raw40142Labels = mixedMoment B node378 node378Labels := by
  calc
    mixedMoment B raw40142 raw40142Labels = mixedMoment B raw40142step0 raw40142step0Labels := by
      have hz : ∀ j, raw40142 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40142step0 = (fun i j => raw40142 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40142step0 raw40142; decide +kernel
      have hl : raw40142step0Labels = raw40142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40142 raw40142Labels permutation434 hz
    mixedMoment B raw40142step0 raw40142step0Labels = mixedMoment B raw40142step1 raw40142step1Labels := by
      have ha : raw40142step1 = (fun i j => raw40142step0 (permutation146 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40142step1 raw40142step0; decide +kernel
      have hl : raw40142step1Labels = raw40142step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40142step0 raw40142step0Labels permutation146 permutation7
    _ = mixedMoment B node378 node378Labels := by rfl

def raw40143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw40143Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40143step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw40143step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40143step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw40143step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40143 raw40143Labels = mixedMoment B node319 node319Labels := by
  calc
    mixedMoment B raw40143 raw40143Labels = mixedMoment B raw40143step0 raw40143step0Labels := by
      have ha : raw40143step0 = (fun i j => raw40143 (permutation375 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40143step0 raw40143; decide +kernel
      have hl : raw40143step0Labels = raw40143Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40143 raw40143Labels permutation375 permutation6
    mixedMoment B raw40143step0 raw40143step0Labels = mixedMoment B raw40143step1 raw40143step1Labels := by
      have ha : raw40143step1 = -raw40143step0 := by apply Matrix.ext; change ∀ i j, raw40143step1 i j = -(raw40143step0 i j); unfold raw40143step1 raw40143step0; decide +kernel
      have hl : raw40143step1Labels = raw40143step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node319 node319Labels := by rfl

def raw40144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40144Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -2, 1]]
def raw40144step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw40144step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40144step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40144step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40144 raw40144Labels = mixedMoment B node489 node489Labels := by
  calc
    mixedMoment B raw40144 raw40144Labels = mixedMoment B raw40144step0 raw40144step0Labels := by
      have hz : ∀ j, raw40144 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40144step0 = (fun i j => raw40144 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40144step0 raw40144; decide +kernel
      have hl : raw40144step0Labels = raw40144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40144 raw40144Labels permutation434 hz
    mixedMoment B raw40144step0 raw40144step0Labels = mixedMoment B raw40144step1 raw40144step1Labels := by
      have ha : raw40144step1 = (fun i j => raw40144step0 (permutation80 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40144step1 raw40144step0; decide +kernel
      have hl : raw40144step1Labels = raw40144step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40144step0 raw40144step0Labels permutation80 permutation4
    mixedMoment B raw40144step1 raw40144step1Labels = mixedMoment B raw40144step2 raw40144step2Labels := by
      have ha : raw40144step2 = -raw40144step1 := by apply Matrix.ext; change ∀ i j, raw40144step2 i j = -(raw40144step1 i j); unfold raw40144step2 raw40144step1; decide +kernel
      have hl : raw40144step2Labels = raw40144step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node489 node489Labels := by rfl

def raw40145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw40145Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40145step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40145step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40145step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40145step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40145 raw40145Labels = mixedMoment B node479 node479Labels := by
  calc
    mixedMoment B raw40145 raw40145Labels = mixedMoment B raw40145step0 raw40145step0Labels := by
      have ha : raw40145step0 = (fun i j => raw40145 (permutation356 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40145step0 raw40145; decide +kernel
      have hl : raw40145step0Labels = raw40145Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40145 raw40145Labels permutation356 permutation4
    mixedMoment B raw40145step0 raw40145step0Labels = mixedMoment B raw40145step1 raw40145step1Labels := by
      have ha : raw40145step1 = -raw40145step0 := by apply Matrix.ext; change ∀ i j, raw40145step1 i j = -(raw40145step0 i j); unfold raw40145step1 raw40145step0; decide +kernel
      have hl : raw40145step1Labels = raw40145step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node479 node479Labels := by rfl

def raw40146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40146Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40146step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40146step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40146 raw40146Labels = mixedMoment B node520 node520Labels := by
  calc
    mixedMoment B raw40146 raw40146Labels = mixedMoment B raw40146step0 raw40146step0Labels := by
      have ha : raw40146step0 = (fun i j => raw40146 (permutation674 i) (permutation5 j)) := by apply Matrix.ext; unfold raw40146step0 raw40146; decide +kernel
      have hl : raw40146step0Labels = raw40146Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40146 raw40146Labels permutation674 permutation5
    _ = mixedMoment B node520 node520Labels := by rfl

def raw40147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw40147Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw40147step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40147step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0]]
def raw40147step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40147step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw40147step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40147step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw40147step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40147 raw40147Labels = mixedMoment B node506 node506Labels := by
  calc
    mixedMoment B raw40147 raw40147Labels = mixedMoment B raw40147step0 raw40147step0Labels := by
      have hz : ∀ j, raw40147 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40147step0 = (fun i j => raw40147 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40147step0 raw40147; decide +kernel
      have hl : raw40147step0Labels = raw40147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40147 raw40147Labels permutation520 hz
    mixedMoment B raw40147step0 raw40147step0Labels = mixedMoment B raw40147step1 raw40147step1Labels := by
      have hz : ∀ j, raw40147step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40147step1 = (fun i j => raw40147step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40147step1 raw40147step0; decide +kernel
      have hl : raw40147step1Labels = raw40147step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40147step0 raw40147step0Labels permutation104 hz
    mixedMoment B raw40147step1 raw40147step1Labels = mixedMoment B raw40147step2 raw40147step2Labels := by
      have ha : raw40147step2 = (fun i j => raw40147step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40147step2 raw40147step1; decide +kernel
      have hl : raw40147step2Labels = raw40147step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40147step1 raw40147step1Labels permutation31 permutation3
    mixedMoment B raw40147step2 raw40147step2Labels = mixedMoment B raw40147step3 raw40147step3Labels := by
      have ha : raw40147step3 = -raw40147step2 := by apply Matrix.ext; change ∀ i j, raw40147step3 i j = -(raw40147step2 i j); unfold raw40147step3 raw40147step2; decide +kernel
      have hl : raw40147step3Labels = raw40147step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node506 node506Labels := by rfl

def raw40148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw40148Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw40148step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw40148step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40148step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw40148step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40148 raw40148Labels = mixedMoment B node526 node526Labels := by
  calc
    mixedMoment B raw40148 raw40148Labels = mixedMoment B raw40148step0 raw40148step0Labels := by
      have hz : ∀ j, raw40148 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40148step0 = (fun i j => raw40148 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40148step0 raw40148; decide +kernel
      have hl : raw40148step0Labels = raw40148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40148 raw40148Labels permutation434 hz
    mixedMoment B raw40148step0 raw40148step0Labels = mixedMoment B raw40148step1 raw40148step1Labels := by
      have ha : raw40148step1 = (fun i j => raw40148step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw40148step1 raw40148step0; decide +kernel
      have hl : raw40148step1Labels = raw40148step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40148step0 raw40148step0Labels permutation144 permutation2
    mixedMoment B raw40148step1 raw40148step1Labels = mixedMoment B raw40148step2 raw40148step2Labels := by
      have ha : raw40148step2 = -raw40148step1 := by apply Matrix.ext; change ∀ i j, raw40148step2 i j = -(raw40148step1 i j); unfold raw40148step2 raw40148step1; decide +kernel
      have hl : raw40148step2Labels = raw40148step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node526 node526Labels := by rfl

def raw40149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw40149Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw40149step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40149step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40149step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40149step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40149step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40149 raw40149Labels = mixedMoment B node490 node490Labels := by
  calc
    mixedMoment B raw40149 raw40149Labels = mixedMoment B raw40149step0 raw40149step0Labels := by
      have hz : ∀ j, raw40149 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40149step0 = (fun i j => raw40149 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40149step0 raw40149; decide +kernel
      have hl : raw40149step0Labels = raw40149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40149 raw40149Labels permutation434 hz
    mixedMoment B raw40149step0 raw40149step0Labels = mixedMoment B raw40149step1 raw40149step1Labels := by
      have ha : raw40149step1 = (fun i j => raw40149step0 (permutation110 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40149step1 raw40149step0; decide +kernel
      have hl : raw40149step1Labels = raw40149step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40149step0 raw40149step0Labels permutation110 permutation6
    mixedMoment B raw40149step1 raw40149step1Labels = mixedMoment B raw40149step2 raw40149step2Labels := by
      have ha : raw40149step2 = -raw40149step1 := by apply Matrix.ext; change ∀ i j, raw40149step2 i j = -(raw40149step1 i j); unfold raw40149step2 raw40149step1; decide +kernel
      have hl : raw40149step2Labels = raw40149step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node490 node490Labels := by rfl

def raw40150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw40150Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -3, 3], ![2, 1, -3]]
def raw40150step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw40150step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40150step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw40150step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40150 raw40150Labels = mixedMoment B node224 node224Labels := by
  calc
    mixedMoment B raw40150 raw40150Labels = mixedMoment B raw40150step0 raw40150step0Labels := by
      have hz : ∀ j, raw40150 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40150step0 = (fun i j => raw40150 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40150step0 raw40150; decide +kernel
      have hl : raw40150step0Labels = raw40150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40150 raw40150Labels permutation434 hz
    mixedMoment B raw40150step0 raw40150step0Labels = mixedMoment B raw40150step1 raw40150step1Labels := by
      have ha : raw40150step1 = (fun i j => raw40150step0 (permutation110 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40150step1 raw40150step0; decide +kernel
      have hl : raw40150step1Labels = raw40150step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40150step0 raw40150step0Labels permutation110 permutation6
    mixedMoment B raw40150step1 raw40150step1Labels = mixedMoment B raw40150step2 raw40150step2Labels := by
      have ha : raw40150step2 = -raw40150step1 := by apply Matrix.ext; change ∀ i j, raw40150step2 i j = -(raw40150step1 i j); unfold raw40150step2 raw40150step1; decide +kernel
      have hl : raw40150step2Labels = raw40150step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node224 node224Labels := by rfl

def raw40151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw40151Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, -3, 2]]
def raw40151step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40151step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40151 raw40151Labels = mixedMoment B node387 node387Labels := by
  calc
    mixedMoment B raw40151 raw40151Labels = mixedMoment B raw40151step0 raw40151step0Labels := by
      have hz : ∀ j, raw40151 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40151step0 = (fun i j => raw40151 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40151step0 raw40151; decide +kernel
      have hl : raw40151step0Labels = raw40151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40151 raw40151Labels permutation434 hz
    mixedMoment B raw40151step0 raw40151step0Labels = mixedMoment B raw40151step1 raw40151step1Labels := by
      have ha : raw40151step1 = (fun i j => raw40151step0 (permutation134 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40151step1 raw40151step0; decide +kernel
      have hl : raw40151step1Labels = raw40151step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40151step0 raw40151step0Labels permutation134 permutation4
    _ = mixedMoment B node387 node387Labels := by rfl

def raw40152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40152Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40152step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw40152step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40152step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw40152step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40152 raw40152Labels = mixedMoment B node532 node532Labels := by
  calc
    mixedMoment B raw40152 raw40152Labels = mixedMoment B raw40152step0 raw40152step0Labels := by
      have hz : ∀ j, raw40152 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40152step0 = (fun i j => raw40152 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40152step0 raw40152; decide +kernel
      have hl : raw40152step0Labels = raw40152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40152 raw40152Labels permutation434 hz
    mixedMoment B raw40152step0 raw40152step0Labels = mixedMoment B raw40152step1 raw40152step1Labels := by
      have ha : raw40152step1 = (fun i j => raw40152step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40152step1 raw40152step0; decide +kernel
      have hl : raw40152step1Labels = raw40152step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40152step0 raw40152step0Labels permutation127 permutation3
    mixedMoment B raw40152step1 raw40152step1Labels = mixedMoment B raw40152step2 raw40152step2Labels := by
      have ha : raw40152step2 = -raw40152step1 := by apply Matrix.ext; change ∀ i j, raw40152step2 i j = -(raw40152step1 i j); unfold raw40152step2 raw40152step1; decide +kernel
      have hl : raw40152step2Labels = raw40152step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node532 node532Labels := by rfl

def raw40153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw40153Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40153step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40153step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40153 raw40153Labels = mixedMoment B node488 node488Labels := by
  calc
    mixedMoment B raw40153 raw40153Labels = mixedMoment B raw40153step0 raw40153step0Labels := by
      have ha : raw40153step0 = (fun i j => raw40153 (permutation626 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40153step0 raw40153; decide +kernel
      have hl : raw40153step0Labels = raw40153Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40153 raw40153Labels permutation626 permutation7
    _ = mixedMoment B node488 node488Labels := by rfl

def raw40154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw40154Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40154step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw40154step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40154 raw40154Labels = mixedMoment B node326 node326Labels := by
  calc
    mixedMoment B raw40154 raw40154Labels = mixedMoment B raw40154step0 raw40154step0Labels := by
      have ha : raw40154step0 = (fun i j => raw40154 (permutation625 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40154step0 raw40154; decide +kernel
      have hl : raw40154step0Labels = raw40154Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40154 raw40154Labels permutation625 permutation7
    _ = mixedMoment B node326 node326Labels := by rfl

def raw40155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw40155Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40155step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw40155step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40155 raw40155Labels = mixedMoment B node533 node533Labels := by
  calc
    mixedMoment B raw40155 raw40155Labels = mixedMoment B raw40155step0 raw40155step0Labels := by
      have ha : raw40155step0 = (fun i j => raw40155 (permutation272 i) (permutation2 j)) := by apply Matrix.ext; unfold raw40155step0 raw40155; decide +kernel
      have hl : raw40155step0Labels = raw40155Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40155 raw40155Labels permutation272 permutation2
    _ = mixedMoment B node533 node533Labels := by rfl

def raw40156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw40156Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40156step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40156step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40156step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40156step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40156 raw40156Labels = mixedMoment B node479 node479Labels := by
  calc
    mixedMoment B raw40156 raw40156Labels = mixedMoment B raw40156step0 raw40156step0Labels := by
      have ha : raw40156step0 = (fun i j => raw40156 (permutation464 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40156step0 raw40156; decide +kernel
      have hl : raw40156step0Labels = raw40156Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40156 raw40156Labels permutation464 permutation6
    mixedMoment B raw40156step0 raw40156step0Labels = mixedMoment B raw40156step1 raw40156step1Labels := by
      have ha : raw40156step1 = -raw40156step0 := by apply Matrix.ext; change ∀ i j, raw40156step1 i j = -(raw40156step0 i j); unfold raw40156step1 raw40156step0; decide +kernel
      have hl : raw40156step1Labels = raw40156step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node479 node479Labels := by rfl

def raw40157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw40157Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw40157step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40157step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![2, 1, -3]]
def raw40157step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40157step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40157step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40157 raw40157Labels = mixedMoment B node405 node405Labels := by
  calc
    mixedMoment B raw40157 raw40157Labels = mixedMoment B raw40157step0 raw40157step0Labels := by
      have hz : ∀ j, raw40157 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40157step0 = (fun i j => raw40157 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40157step0 raw40157; decide +kernel
      have hl : raw40157step0Labels = raw40157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40157 raw40157Labels permutation434 hz
    mixedMoment B raw40157step0 raw40157step0Labels = mixedMoment B raw40157step1 raw40157step1Labels := by
      have hz : ∀ j, raw40157step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40157step1 = (fun i j => raw40157step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40157step1 raw40157step0; decide +kernel
      have hl : raw40157step1Labels = raw40157step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40157step0 raw40157step0Labels permutation80 hz
    mixedMoment B raw40157step1 raw40157step1Labels = mixedMoment B raw40157step2 raw40157step2Labels := by
      have ha : raw40157step2 = (fun i j => raw40157step1 (permutation26 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40157step2 raw40157step1; decide +kernel
      have hl : raw40157step2Labels = raw40157step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40157step1 raw40157step1Labels permutation26 permutation7
    _ = mixedMoment B node405 node405Labels := by rfl

def raw40158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw40158Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw40158step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40158step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40158 raw40158Labels = mixedMoment B node403 node403Labels := by
  calc
    mixedMoment B raw40158 raw40158Labels = mixedMoment B raw40158step0 raw40158step0Labels := by
      have hz : ∀ j, raw40158 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40158step0 = (fun i j => raw40158 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40158step0 raw40158; decide +kernel
      have hl : raw40158step0Labels = raw40158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40158 raw40158Labels permutation346 hz
    mixedMoment B raw40158step0 raw40158step0Labels = mixedMoment B raw40158step1 raw40158step1Labels := by
      have ha : raw40158step1 = (fun i j => raw40158step0 (permutation131 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40158step1 raw40158step0; decide +kernel
      have hl : raw40158step1Labels = raw40158step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40158step0 raw40158step0Labels permutation131 permutation7
    _ = mixedMoment B node403 node403Labels := by rfl

def raw40159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw40159Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw40159step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40159step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40159 raw40159Labels = mixedMoment B node387 node387Labels := by
  calc
    mixedMoment B raw40159 raw40159Labels = mixedMoment B raw40159step0 raw40159step0Labels := by
      have hz : ∀ j, raw40159 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40159step0 = (fun i j => raw40159 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40159step0 raw40159; decide +kernel
      have hl : raw40159step0Labels = raw40159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40159 raw40159Labels permutation346 hz
    mixedMoment B raw40159step0 raw40159step0Labels = mixedMoment B raw40159step1 raw40159step1Labels := by
      have ha : raw40159step1 = (fun i j => raw40159step0 (permutation104 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40159step1 raw40159step0; decide +kernel
      have hl : raw40159step1Labels = raw40159step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40159step0 raw40159step0Labels permutation104 permutation6
    _ = mixedMoment B node387 node387Labels := by rfl

def raw40160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw40160Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw40160step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw40160step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40160 raw40160Labels = mixedMoment B node526 node526Labels := by
  calc
    mixedMoment B raw40160 raw40160Labels = mixedMoment B raw40160step0 raw40160step0Labels := by
      have hz : ∀ j, raw40160 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40160step0 = (fun i j => raw40160 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40160step0 raw40160; decide +kernel
      have hl : raw40160step0Labels = raw40160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40160 raw40160Labels permutation346 hz
    mixedMoment B raw40160step0 raw40160step0Labels = mixedMoment B raw40160step1 raw40160step1Labels := by
      have ha : raw40160step1 = (fun i j => raw40160step0 (permutation108 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40160step1 raw40160step0; decide +kernel
      have hl : raw40160step1Labels = raw40160step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40160step0 raw40160step0Labels permutation108 permutation6
    _ = mixedMoment B node526 node526Labels := by rfl

def raw40161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw40161Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw40161step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40161step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40161step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40161 raw40161Labels = mixedMoment B node377 node377Labels := by
  calc
    mixedMoment B raw40161 raw40161Labels = mixedMoment B raw40161step0 raw40161step0Labels := by
      have hz : ∀ j, raw40161 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40161step0 = (fun i j => raw40161 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40161step0 raw40161; decide +kernel
      have hl : raw40161step0Labels = raw40161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40161 raw40161Labels permutation346 hz
    mixedMoment B raw40161step0 raw40161step0Labels = mixedMoment B raw40161step1 raw40161step1Labels := by
      have ha : raw40161step1 = (fun i j => raw40161step0 (permutation108 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40161step1 raw40161step0; decide +kernel
      have hl : raw40161step1Labels = raw40161step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40161step0 raw40161step0Labels permutation108 permutation6
    _ = mixedMoment B node377 node377Labels := by rfl

def raw40162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw40162Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40162step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40162step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40162 raw40162Labels = mixedMoment B node520 node520Labels := by
  calc
    mixedMoment B raw40162 raw40162Labels = mixedMoment B raw40162step0 raw40162step0Labels := by
      have ha : raw40162step0 = (fun i j => raw40162 (permutation572 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40162step0 raw40162; decide +kernel
      have hl : raw40162step0Labels = raw40162Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40162 raw40162Labels permutation572 permutation7
    _ = mixedMoment B node520 node520Labels := by rfl

def raw40163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw40163Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw40163step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40163step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0]]
def raw40163step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40163step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw40163step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40163step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw40163step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40163 raw40163Labels = mixedMoment B node496 node496Labels := by
  calc
    mixedMoment B raw40163 raw40163Labels = mixedMoment B raw40163step0 raw40163step0Labels := by
      have hz : ∀ j, raw40163 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40163step0 = (fun i j => raw40163 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40163step0 raw40163; decide +kernel
      have hl : raw40163step0Labels = raw40163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40163 raw40163Labels permutation520 hz
    mixedMoment B raw40163step0 raw40163step0Labels = mixedMoment B raw40163step1 raw40163step1Labels := by
      have hz : ∀ j, raw40163step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40163step1 = (fun i j => raw40163step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40163step1 raw40163step0; decide +kernel
      have hl : raw40163step1Labels = raw40163step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40163step0 raw40163step0Labels permutation104 hz
    mixedMoment B raw40163step1 raw40163step1Labels = mixedMoment B raw40163step2 raw40163step2Labels := by
      have ha : raw40163step2 = (fun i j => raw40163step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40163step2 raw40163step1; decide +kernel
      have hl : raw40163step2Labels = raw40163step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40163step1 raw40163step1Labels permutation20 permutation4
    mixedMoment B raw40163step2 raw40163step2Labels = mixedMoment B raw40163step3 raw40163step3Labels := by
      have ha : raw40163step3 = -raw40163step2 := by apply Matrix.ext; change ∀ i j, raw40163step3 i j = -(raw40163step2 i j); unfold raw40163step3 raw40163step2; decide +kernel
      have hl : raw40163step3Labels = raw40163step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node496 node496Labels := by rfl

def raw40164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw40164Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, -2, 2], ![2, 0, -2]]
def raw40164step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40164step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40164step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40164step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40164 raw40164Labels = mixedMoment B node432 node432Labels := by
  calc
    mixedMoment B raw40164 raw40164Labels = mixedMoment B raw40164step0 raw40164step0Labels := by
      have hz : ∀ j, raw40164 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40164step0 = (fun i j => raw40164 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40164step0 raw40164; decide +kernel
      have hl : raw40164step0Labels = raw40164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40164 raw40164Labels permutation434 hz
    mixedMoment B raw40164step0 raw40164step0Labels = mixedMoment B raw40164step1 raw40164step1Labels := by
      have ha : raw40164step1 = (fun i j => raw40164step0 (permutation111 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40164step1 raw40164step0; decide +kernel
      have hl : raw40164step1Labels = raw40164step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40164step0 raw40164step0Labels permutation111 permutation6
    mixedMoment B raw40164step1 raw40164step1Labels = mixedMoment B raw40164step2 raw40164step2Labels := by
      have ha : raw40164step2 = -raw40164step1 := by apply Matrix.ext; change ∀ i j, raw40164step2 i j = -(raw40164step1 i j); unfold raw40164step2 raw40164step1; decide +kernel
      have hl : raw40164step2Labels = raw40164step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node432 node432Labels := by rfl

def raw40165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw40165Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw40165step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw40165step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40165step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40165step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40165 raw40165Labels = mixedMoment B node483 node483Labels := by
  calc
    mixedMoment B raw40165 raw40165Labels = mixedMoment B raw40165step0 raw40165step0Labels := by
      have hz : ∀ j, raw40165 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40165step0 = (fun i j => raw40165 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40165step0 raw40165; decide +kernel
      have hl : raw40165step0Labels = raw40165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40165 raw40165Labels permutation434 hz
    mixedMoment B raw40165step0 raw40165step0Labels = mixedMoment B raw40165step1 raw40165step1Labels := by
      have ha : raw40165step1 = (fun i j => raw40165step0 (permutation82 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40165step1 raw40165step0; decide +kernel
      have hl : raw40165step1Labels = raw40165step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40165step0 raw40165step0Labels permutation82 permutation4
    mixedMoment B raw40165step1 raw40165step1Labels = mixedMoment B raw40165step2 raw40165step2Labels := by
      have ha : raw40165step2 = -raw40165step1 := by apply Matrix.ext; change ∀ i j, raw40165step2 i j = -(raw40165step1 i j); unfold raw40165step2 raw40165step1; decide +kernel
      have hl : raw40165step2Labels = raw40165step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node483 node483Labels := by rfl

def raw40166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw40166Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw40166step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40166step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40166step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40166 raw40166Labels = mixedMoment B node429 node429Labels := by
  calc
    mixedMoment B raw40166 raw40166Labels = mixedMoment B raw40166step0 raw40166step0Labels := by
      have ha : raw40166step0 = (fun i j => raw40166 (permutation454 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40166step0 raw40166; decide +kernel
      have hl : raw40166step0Labels = raw40166Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40166 raw40166Labels permutation454 permutation6
    mixedMoment B raw40166step0 raw40166step0Labels = mixedMoment B raw40166step1 raw40166step1Labels := by
      have ha : raw40166step1 = -raw40166step0 := by apply Matrix.ext; change ∀ i j, raw40166step1 i j = -(raw40166step0 i j); unfold raw40166step1 raw40166step0; decide +kernel
      have hl : raw40166step1Labels = raw40166step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node429 node429Labels := by rfl

def raw40167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw40167Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw40167step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40167step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40167 raw40167Labels = mixedMoment B node489 node489Labels := by
  calc
    mixedMoment B raw40167 raw40167Labels = mixedMoment B raw40167step0 raw40167step0Labels := by
      have hz : ∀ j, raw40167 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40167step0 = (fun i j => raw40167 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40167step0 raw40167; decide +kernel
      have hl : raw40167step0Labels = raw40167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40167 raw40167Labels permutation434 hz
    mixedMoment B raw40167step0 raw40167step0Labels = mixedMoment B raw40167step1 raw40167step1Labels := by
      have ha : raw40167step1 = (fun i j => raw40167step0 (permutation141 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40167step1 raw40167step0; decide +kernel
      have hl : raw40167step1Labels = raw40167step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40167step0 raw40167step0Labels permutation141 permutation7
    _ = mixedMoment B node489 node489Labels := by rfl

def raw40168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw40168Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40168step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw40168step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw40168step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40168 raw40168Labels = mixedMoment B node526 node526Labels := by
  calc
    mixedMoment B raw40168 raw40168Labels = mixedMoment B raw40168step0 raw40168step0Labels := by
      have hz : ∀ j, raw40168 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40168step0 = (fun i j => raw40168 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40168step0 raw40168; decide +kernel
      have hl : raw40168step0Labels = raw40168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40168 raw40168Labels permutation434 hz
    mixedMoment B raw40168step0 raw40168step0Labels = mixedMoment B raw40168step1 raw40168step1Labels := by
      have ha : raw40168step1 = (fun i j => raw40168step0 (permutation75 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40168step1 raw40168step0; decide +kernel
      have hl : raw40168step1Labels = raw40168step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40168step0 raw40168step0Labels permutation75 permutation6
    mixedMoment B raw40168step1 raw40168step1Labels = mixedMoment B raw40168step2 raw40168step2Labels := by
      have ha : raw40168step2 = -raw40168step1 := by apply Matrix.ext; change ∀ i j, raw40168step2 i j = -(raw40168step1 i j); unfold raw40168step2 raw40168step1; decide +kernel
      have hl : raw40168step2Labels = raw40168step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node526 node526Labels := by rfl

def raw40169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40169Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40169step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw40169step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40169step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40169step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40169 raw40169Labels = mixedMoment B node520 node520Labels := by
  calc
    mixedMoment B raw40169 raw40169Labels = mixedMoment B raw40169step0 raw40169step0Labels := by
      have ha : raw40169step0 = (fun i j => raw40169 (permutation308 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40169step0 raw40169; decide +kernel
      have hl : raw40169step0Labels = raw40169Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40169 raw40169Labels permutation308 permutation6
    mixedMoment B raw40169step0 raw40169step0Labels = mixedMoment B raw40169step1 raw40169step1Labels := by
      have ha : raw40169step1 = -raw40169step0 := by apply Matrix.ext; change ∀ i j, raw40169step1 i j = -(raw40169step0 i j); unfold raw40169step1 raw40169step0; decide +kernel
      have hl : raw40169step1Labels = raw40169step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node520 node520Labels := by rfl

def raw40170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw40170Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw40170step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40170step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![2, 1, -3]]
def raw40170step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40170step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40170step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40170 raw40170Labels = mixedMoment B node404 node404Labels := by
  calc
    mixedMoment B raw40170 raw40170Labels = mixedMoment B raw40170step0 raw40170step0Labels := by
      have hz : ∀ j, raw40170 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40170step0 = (fun i j => raw40170 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40170step0 raw40170; decide +kernel
      have hl : raw40170step0Labels = raw40170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40170 raw40170Labels permutation434 hz
    mixedMoment B raw40170step0 raw40170step0Labels = mixedMoment B raw40170step1 raw40170step1Labels := by
      have hz : ∀ j, raw40170step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40170step1 = (fun i j => raw40170step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40170step1 raw40170step0; decide +kernel
      have hl : raw40170step1Labels = raw40170step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40170step0 raw40170step0Labels permutation80 hz
    mixedMoment B raw40170step1 raw40170step1Labels = mixedMoment B raw40170step2 raw40170step2Labels := by
      have ha : raw40170step2 = (fun i j => raw40170step1 (permutation27 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40170step2 raw40170step1; decide +kernel
      have hl : raw40170step2Labels = raw40170step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40170step1 raw40170step1Labels permutation27 permutation7
    _ = mixedMoment B node404 node404Labels := by rfl

def raw40171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 2, -4]]
def raw40171Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![2, 2, -4]]
def raw40171step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40171step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2], ![2, 2, -4]]
def raw40171step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40171step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw40171step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40171 raw40171Labels = mixedMoment B node149 node149Labels := by
  calc
    mixedMoment B raw40171 raw40171Labels = mixedMoment B raw40171step0 raw40171step0Labels := by
      have hz : ∀ j, raw40171 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40171step0 = (fun i j => raw40171 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40171step0 raw40171; decide +kernel
      have hl : raw40171step0Labels = raw40171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40171 raw40171Labels permutation434 hz
    mixedMoment B raw40171step0 raw40171step0Labels = mixedMoment B raw40171step1 raw40171step1Labels := by
      have hz : ∀ j, raw40171step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40171step1 = (fun i j => raw40171step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40171step1 raw40171step0; decide +kernel
      have hl : raw40171step1Labels = raw40171step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40171step0 raw40171step0Labels permutation80 hz
    mixedMoment B raw40171step1 raw40171step1Labels = mixedMoment B raw40171step2 raw40171step2Labels := by
      have ha : raw40171step2 = (fun i j => raw40171step1 (permutation26 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40171step2 raw40171step1; decide +kernel
      have hl : raw40171step2Labels = raw40171step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40171step1 raw40171step1Labels permutation26 permutation6
    _ = mixedMoment B node149 node149Labels := by rfl

def raw40172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw40172Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw40172step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40172step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![1, 2, -3], ![1, -2, 1]]
def raw40172step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40172step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40172step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40172 raw40172Labels = mixedMoment B node390 node390Labels := by
  calc
    mixedMoment B raw40172 raw40172Labels = mixedMoment B raw40172step0 raw40172step0Labels := by
      have hz : ∀ j, raw40172 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40172step0 = (fun i j => raw40172 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40172step0 raw40172; decide +kernel
      have hl : raw40172step0Labels = raw40172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40172 raw40172Labels permutation434 hz
    mixedMoment B raw40172step0 raw40172step0Labels = mixedMoment B raw40172step1 raw40172step1Labels := by
      have hz : ∀ j, raw40172step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40172step1 = (fun i j => raw40172step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40172step1 raw40172step0; decide +kernel
      have hl : raw40172step1Labels = raw40172step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40172step0 raw40172step0Labels permutation80 hz
    mixedMoment B raw40172step1 raw40172step1Labels = mixedMoment B raw40172step2 raw40172step2Labels := by
      have ha : raw40172step2 = (fun i j => raw40172step1 (permutation21 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40172step2 raw40172step1; decide +kernel
      have hl : raw40172step2Labels = raw40172step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40172step1 raw40172step1Labels permutation21 permutation6
    _ = mixedMoment B node390 node390Labels := by rfl

def raw40173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw40173Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw40173step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40173step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![1, 1, -2], ![1, -1, 0]]
def raw40173step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40173step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw40173step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40173 raw40173Labels = mixedMoment B node527 node527Labels := by
  calc
    mixedMoment B raw40173 raw40173Labels = mixedMoment B raw40173step0 raw40173step0Labels := by
      have hz : ∀ j, raw40173 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40173step0 = (fun i j => raw40173 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40173step0 raw40173; decide +kernel
      have hl : raw40173step0Labels = raw40173Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40173 raw40173Labels permutation434 hz
    mixedMoment B raw40173step0 raw40173step0Labels = mixedMoment B raw40173step1 raw40173step1Labels := by
      have hz : ∀ j, raw40173step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40173step1 = (fun i j => raw40173step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40173step1 raw40173step0; decide +kernel
      have hl : raw40173step1Labels = raw40173step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40173step0 raw40173step0Labels permutation80 hz
    mixedMoment B raw40173step1 raw40173step1Labels = mixedMoment B raw40173step2 raw40173step2Labels := by
      have ha : raw40173step2 = (fun i j => raw40173step1 (permutation21 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40173step2 raw40173step1; decide +kernel
      have hl : raw40173step2Labels = raw40173step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40173step1 raw40173step1Labels permutation21 permutation6
    _ = mixedMoment B node527 node527Labels := by rfl

def raw40174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw40174Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw40174step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw40174step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40174step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40174step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40174 raw40174Labels = mixedMoment B node521 node521Labels := by
  calc
    mixedMoment B raw40174 raw40174Labels = mixedMoment B raw40174step0 raw40174step0Labels := by
      have hz : ∀ j, raw40174 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40174step0 = (fun i j => raw40174 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40174step0 raw40174; decide +kernel
      have hl : raw40174step0Labels = raw40174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40174 raw40174Labels permutation346 hz
    mixedMoment B raw40174step0 raw40174step0Labels = mixedMoment B raw40174step1 raw40174step1Labels := by
      have ha : raw40174step1 = (fun i j => raw40174step0 (permutation63 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40174step1 raw40174step0; decide +kernel
      have hl : raw40174step1Labels = raw40174step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40174step0 raw40174step0Labels permutation63 permutation6
    mixedMoment B raw40174step1 raw40174step1Labels = mixedMoment B raw40174step2 raw40174step2Labels := by
      have ha : raw40174step2 = -raw40174step1 := by apply Matrix.ext; change ∀ i j, raw40174step2 i j = -(raw40174step1 i j); unfold raw40174step2 raw40174step1; decide +kernel
      have hl : raw40174step2Labels = raw40174step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node521 node521Labels := by rfl

def raw40175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw40175Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw40175step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw40175step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40175 raw40175Labels = mixedMoment B node325 node325Labels := by
  calc
    mixedMoment B raw40175 raw40175Labels = mixedMoment B raw40175step0 raw40175step0Labels := by
      have hz : ∀ j, raw40175 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40175step0 = (fun i j => raw40175 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40175step0 raw40175; decide +kernel
      have hl : raw40175step0Labels = raw40175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40175 raw40175Labels permutation346 hz
    mixedMoment B raw40175step0 raw40175step0Labels = mixedMoment B raw40175step1 raw40175step1Labels := by
      have ha : raw40175step1 = (fun i j => raw40175step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40175step1 raw40175step0; decide +kernel
      have hl : raw40175step1Labels = raw40175step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40175step0 raw40175step0Labels permutation122 permutation6
    _ = mixedMoment B node325 node325Labels := by rfl

def raw40176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw40176Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw40176step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40176step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![2, -1, -1]]
def raw40176step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40176step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw40176step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40176step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw40176step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40176 raw40176Labels = mixedMoment B node402 node402Labels := by
  calc
    mixedMoment B raw40176 raw40176Labels = mixedMoment B raw40176step0 raw40176step0Labels := by
      have hz : ∀ j, raw40176 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40176step0 = (fun i j => raw40176 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40176step0 raw40176; decide +kernel
      have hl : raw40176step0Labels = raw40176Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40176 raw40176Labels permutation520 hz
    mixedMoment B raw40176step0 raw40176step0Labels = mixedMoment B raw40176step1 raw40176step1Labels := by
      have hz : ∀ j, raw40176step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40176step1 = (fun i j => raw40176step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40176step1 raw40176step0; decide +kernel
      have hl : raw40176step1Labels = raw40176step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40176step0 raw40176step0Labels permutation104 hz
    mixedMoment B raw40176step1 raw40176step1Labels = mixedMoment B raw40176step2 raw40176step2Labels := by
      have ha : raw40176step2 = (fun i j => raw40176step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40176step2 raw40176step1; decide +kernel
      have hl : raw40176step2Labels = raw40176step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40176step1 raw40176step1Labels permutation15 permutation6
    mixedMoment B raw40176step2 raw40176step2Labels = mixedMoment B raw40176step3 raw40176step3Labels := by
      have ha : raw40176step3 = -raw40176step2 := by apply Matrix.ext; change ∀ i j, raw40176step3 i j = -(raw40176step2 i j); unfold raw40176step3 raw40176step2; decide +kernel
      have hl : raw40176step3Labels = raw40176step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node402 node402Labels := by rfl

def raw40177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw40177Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![0, -1, 1], ![2, 0, -2]]
def raw40177step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40177step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40177step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40177step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40177 raw40177Labels = mixedMoment B node306 node306Labels := by
  calc
    mixedMoment B raw40177 raw40177Labels = mixedMoment B raw40177step0 raw40177step0Labels := by
      have hz : ∀ j, raw40177 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40177step0 = (fun i j => raw40177 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40177step0 raw40177; decide +kernel
      have hl : raw40177step0Labels = raw40177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40177 raw40177Labels permutation434 hz
    mixedMoment B raw40177step0 raw40177step0Labels = mixedMoment B raw40177step1 raw40177step1Labels := by
      have ha : raw40177step1 = (fun i j => raw40177step0 (permutation69 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40177step1 raw40177step0; decide +kernel
      have hl : raw40177step1Labels = raw40177step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40177step0 raw40177step0Labels permutation69 permutation6
    mixedMoment B raw40177step1 raw40177step1Labels = mixedMoment B raw40177step2 raw40177step2Labels := by
      have ha : raw40177step2 = -raw40177step1 := by apply Matrix.ext; change ∀ i j, raw40177step2 i j = -(raw40177step1 i j); unfold raw40177step2 raw40177step1; decide +kernel
      have hl : raw40177step2Labels = raw40177step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node306 node306Labels := by rfl

def raw40178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw40178Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw40178step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw40178step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40178step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40178step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40178 raw40178Labels = mixedMoment B node377 node377Labels := by
  calc
    mixedMoment B raw40178 raw40178Labels = mixedMoment B raw40178step0 raw40178step0Labels := by
      have hz : ∀ j, raw40178 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40178step0 = (fun i j => raw40178 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40178step0 raw40178; decide +kernel
      have hl : raw40178step0Labels = raw40178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40178 raw40178Labels permutation434 hz
    mixedMoment B raw40178step0 raw40178step0Labels = mixedMoment B raw40178step1 raw40178step1Labels := by
      have ha : raw40178step1 = (fun i j => raw40178step0 (permutation75 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40178step1 raw40178step0; decide +kernel
      have hl : raw40178step1Labels = raw40178step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40178step0 raw40178step0Labels permutation75 permutation6
    mixedMoment B raw40178step1 raw40178step1Labels = mixedMoment B raw40178step2 raw40178step2Labels := by
      have ha : raw40178step2 = -raw40178step1 := by apply Matrix.ext; change ∀ i j, raw40178step2 i j = -(raw40178step1 i j); unfold raw40178step2 raw40178step1; decide +kernel
      have hl : raw40178step2Labels = raw40178step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node377 node377Labels := by rfl

def raw40179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40179Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw40179step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40179step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40179step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40179 raw40179Labels = mixedMoment B node301 node301Labels := by
  calc
    mixedMoment B raw40179 raw40179Labels = mixedMoment B raw40179step0 raw40179step0Labels := by
      have ha : raw40179step0 = (fun i j => raw40179 (permutation308 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40179step0 raw40179; decide +kernel
      have hl : raw40179step0Labels = raw40179Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40179 raw40179Labels permutation308 permutation6
    mixedMoment B raw40179step0 raw40179step0Labels = mixedMoment B raw40179step1 raw40179step1Labels := by
      have ha : raw40179step1 = -raw40179step0 := by apply Matrix.ext; change ∀ i j, raw40179step1 i j = -(raw40179step0 i j); unfold raw40179step1 raw40179step0; decide +kernel
      have hl : raw40179step1Labels = raw40179step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node301 node301Labels := by rfl

def raw40180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40180Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40180step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw40180step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40180step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40180step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40180 raw40180Labels = mixedMoment B node376 node376Labels := by
  calc
    mixedMoment B raw40180 raw40180Labels = mixedMoment B raw40180step0 raw40180step0Labels := by
      have ha : raw40180step0 = (fun i j => raw40180 (permutation337 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40180step0 raw40180; decide +kernel
      have hl : raw40180step0Labels = raw40180Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40180 raw40180Labels permutation337 permutation6
    mixedMoment B raw40180step0 raw40180step0Labels = mixedMoment B raw40180step1 raw40180step1Labels := by
      have ha : raw40180step1 = -raw40180step0 := by apply Matrix.ext; change ∀ i j, raw40180step1 i j = -(raw40180step0 i j); unfold raw40180step1 raw40180step0; decide +kernel
      have hl : raw40180step1Labels = raw40180step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node376 node376Labels := by rfl

def raw40181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40181Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw40181step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40181step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![2, 0, -2]]
def raw40181step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40181step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40181step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40181step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40181step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40181 raw40181Labels = mixedMoment B node405 node405Labels := by
  calc
    mixedMoment B raw40181 raw40181Labels = mixedMoment B raw40181step0 raw40181step0Labels := by
      have hz : ∀ j, raw40181 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40181step0 = (fun i j => raw40181 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40181step0 raw40181; decide +kernel
      have hl : raw40181step0Labels = raw40181Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40181 raw40181Labels permutation520 hz
    mixedMoment B raw40181step0 raw40181step0Labels = mixedMoment B raw40181step1 raw40181step1Labels := by
      have hz : ∀ j, raw40181step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40181step1 = (fun i j => raw40181step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40181step1 raw40181step0; decide +kernel
      have hl : raw40181step1Labels = raw40181step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40181step0 raw40181step0Labels permutation104 hz
    mixedMoment B raw40181step1 raw40181step1Labels = mixedMoment B raw40181step2 raw40181step2Labels := by
      have ha : raw40181step2 = (fun i j => raw40181step1 (permutation14 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40181step2 raw40181step1; decide +kernel
      have hl : raw40181step2Labels = raw40181step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40181step1 raw40181step1Labels permutation14 permutation6
    mixedMoment B raw40181step2 raw40181step2Labels = mixedMoment B raw40181step3 raw40181step3Labels := by
      have ha : raw40181step3 = -raw40181step2 := by apply Matrix.ext; change ∀ i j, raw40181step3 i j = -(raw40181step2 i j); unfold raw40181step3 raw40181step2; decide +kernel
      have hl : raw40181step3Labels = raw40181step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node405 node405Labels := by rfl

def raw40182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw40182Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![0, -1, 1], ![2, 1, -3]]
def raw40182step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40182step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw40182step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40182step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw40182step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40182 raw40182Labels = mixedMoment B node305 node305Labels := by
  calc
    mixedMoment B raw40182 raw40182Labels = mixedMoment B raw40182step0 raw40182step0Labels := by
      have hz : ∀ j, raw40182 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40182step0 = (fun i j => raw40182 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40182step0 raw40182; decide +kernel
      have hl : raw40182step0Labels = raw40182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40182 raw40182Labels permutation434 hz
    mixedMoment B raw40182step0 raw40182step0Labels = mixedMoment B raw40182step1 raw40182step1Labels := by
      have ha : raw40182step1 = (fun i j => raw40182step0 (permutation68 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40182step1 raw40182step0; decide +kernel
      have hl : raw40182step1Labels = raw40182step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40182step0 raw40182step0Labels permutation68 permutation6
    mixedMoment B raw40182step1 raw40182step1Labels = mixedMoment B raw40182step2 raw40182step2Labels := by
      have ha : raw40182step2 = -raw40182step1 := by apply Matrix.ext; change ∀ i j, raw40182step2 i j = -(raw40182step1 i j); unfold raw40182step2 raw40182step1; decide +kernel
      have hl : raw40182step2Labels = raw40182step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node305 node305Labels := by rfl

def raw40183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw40183Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw40183step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40183step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40183step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40183step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40183 raw40183Labels = mixedMoment B node378 node378Labels := by
  calc
    mixedMoment B raw40183 raw40183Labels = mixedMoment B raw40183step0 raw40183step0Labels := by
      have hz : ∀ j, raw40183 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40183step0 = (fun i j => raw40183 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40183step0 raw40183; decide +kernel
      have hl : raw40183step0Labels = raw40183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40183 raw40183Labels permutation434 hz
    mixedMoment B raw40183step0 raw40183step0Labels = mixedMoment B raw40183step1 raw40183step1Labels := by
      have ha : raw40183step1 = (fun i j => raw40183step0 (permutation74 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40183step1 raw40183step0; decide +kernel
      have hl : raw40183step1Labels = raw40183step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40183step0 raw40183step0Labels permutation74 permutation6
    mixedMoment B raw40183step1 raw40183step1Labels = mixedMoment B raw40183step2 raw40183step2Labels := by
      have ha : raw40183step2 = -raw40183step1 := by apply Matrix.ext; change ∀ i j, raw40183step2 i j = -(raw40183step1 i j); unfold raw40183step2 raw40183step1; decide +kernel
      have hl : raw40183step2Labels = raw40183step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node378 node378Labels := by rfl

def raw40184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw40184Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw40184step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40184step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![2, 1, -3]]
def raw40184step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40184step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![2, 1, -3]]
def raw40184step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40184step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-3, 2, 1]]
def raw40184step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40184step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw40184step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40184 raw40184Labels = mixedMoment B node407 node407Labels := by
  calc
    mixedMoment B raw40184 raw40184Labels = mixedMoment B raw40184step0 raw40184step0Labels := by
      have hz : ∀ j, raw40184 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40184step0 = (fun i j => raw40184 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40184step0 raw40184; decide +kernel
      have hl : raw40184step0Labels = raw40184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40184 raw40184Labels permutation520 hz
    mixedMoment B raw40184step0 raw40184step0Labels = mixedMoment B raw40184step1 raw40184step1Labels := by
      have hz : ∀ j, raw40184step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40184step1 = (fun i j => raw40184step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40184step1 raw40184step0; decide +kernel
      have hl : raw40184step1Labels = raw40184step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40184step0 raw40184step0Labels permutation104 hz
    mixedMoment B raw40184step1 raw40184step1Labels = mixedMoment B raw40184step2 raw40184step2Labels := by
      have hz : ∀ j, raw40184step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40184step2 = (fun i j => raw40184step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40184step2 raw40184step1; decide +kernel
      have hl : raw40184step2Labels = raw40184step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40184step1 raw40184step1Labels permutation20 hz
    mixedMoment B raw40184step2 raw40184step2Labels = mixedMoment B raw40184step3 raw40184step3Labels := by
      have ha : raw40184step3 = (fun i j => raw40184step2 (permutation4 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40184step3 raw40184step2; decide +kernel
      have hl : raw40184step3Labels = raw40184step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40184step2 raw40184step2Labels permutation4 permutation6
    mixedMoment B raw40184step3 raw40184step3Labels = mixedMoment B raw40184step4 raw40184step4Labels := by
      have ha : raw40184step4 = -raw40184step3 := by apply Matrix.ext; change ∀ i j, raw40184step4 i j = -(raw40184step3 i j); unfold raw40184step4 raw40184step3; decide +kernel
      have hl : raw40184step4Labels = raw40184step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node407 node407Labels := by rfl

def raw40185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw40185Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw40185step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40185step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![1, 2, -3], ![1, -1, 0]]
def raw40185step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40185step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw40185step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40185 raw40185Labels = mixedMoment B node379 node379Labels := by
  calc
    mixedMoment B raw40185 raw40185Labels = mixedMoment B raw40185step0 raw40185step0Labels := by
      have hz : ∀ j, raw40185 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40185step0 = (fun i j => raw40185 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40185step0 raw40185; decide +kernel
      have hl : raw40185step0Labels = raw40185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40185 raw40185Labels permutation434 hz
    mixedMoment B raw40185step0 raw40185step0Labels = mixedMoment B raw40185step1 raw40185step1Labels := by
      have hz : ∀ j, raw40185step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40185step1 = (fun i j => raw40185step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40185step1 raw40185step0; decide +kernel
      have hl : raw40185step1Labels = raw40185step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40185step0 raw40185step0Labels permutation80 hz
    mixedMoment B raw40185step1 raw40185step1Labels = mixedMoment B raw40185step2 raw40185step2Labels := by
      have ha : raw40185step2 = (fun i j => raw40185step1 (permutation21 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40185step2 raw40185step1; decide +kernel
      have hl : raw40185step2Labels = raw40185step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40185step1 raw40185step1Labels permutation21 permutation6
    _ = mixedMoment B node379 node379Labels := by rfl

def raw40186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw40186Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -2, 3], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw40186step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw40186step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40186step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw40186step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40186 raw40186Labels = mixedMoment B node303 node303Labels := by
  calc
    mixedMoment B raw40186 raw40186Labels = mixedMoment B raw40186step0 raw40186step0Labels := by
      have hz : ∀ j, raw40186 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40186step0 = (fun i j => raw40186 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40186step0 raw40186; decide +kernel
      have hl : raw40186step0Labels = raw40186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40186 raw40186Labels permutation346 hz
    mixedMoment B raw40186step0 raw40186step0Labels = mixedMoment B raw40186step1 raw40186step1Labels := by
      have ha : raw40186step1 = (fun i j => raw40186step0 (permutation63 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40186step1 raw40186step0; decide +kernel
      have hl : raw40186step1Labels = raw40186step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40186step0 raw40186step0Labels permutation63 permutation6
    mixedMoment B raw40186step1 raw40186step1Labels = mixedMoment B raw40186step2 raw40186step2Labels := by
      have ha : raw40186step2 = -raw40186step1 := by apply Matrix.ext; change ∀ i j, raw40186step2 i j = -(raw40186step1 i j); unfold raw40186step2 raw40186step1; decide +kernel
      have hl : raw40186step2Labels = raw40186step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node303 node303Labels := by rfl

def raw40187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw40187Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 2, -2], ![0, 0, 0], ![2, 0, -2]]
def raw40187step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40187step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 2, -2], ![2, 0, -2]]
def raw40187step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40187step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40187step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40187step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40187step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40187 raw40187Labels = mixedMoment B node98 node98Labels := by
  calc
    mixedMoment B raw40187 raw40187Labels = mixedMoment B raw40187step0 raw40187step0Labels := by
      have hz : ∀ j, raw40187 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40187step0 = (fun i j => raw40187 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40187step0 raw40187; decide +kernel
      have hl : raw40187step0Labels = raw40187Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40187 raw40187Labels permutation520 hz
    mixedMoment B raw40187step0 raw40187step0Labels = mixedMoment B raw40187step1 raw40187step1Labels := by
      have hz : ∀ j, raw40187step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40187step1 = (fun i j => raw40187step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40187step1 raw40187step0; decide +kernel
      have hl : raw40187step1Labels = raw40187step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40187step0 raw40187step0Labels permutation104 hz
    mixedMoment B raw40187step1 raw40187step1Labels = mixedMoment B raw40187step2 raw40187step2Labels := by
      have ha : raw40187step2 = (fun i j => raw40187step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40187step2 raw40187step1; decide +kernel
      have hl : raw40187step2Labels = raw40187step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40187step1 raw40187step1Labels permutation15 permutation6
    mixedMoment B raw40187step2 raw40187step2Labels = mixedMoment B raw40187step3 raw40187step3Labels := by
      have ha : raw40187step3 = -raw40187step2 := by apply Matrix.ext; change ∀ i j, raw40187step3 i j = -(raw40187step2 i j); unfold raw40187step3 raw40187step2; decide +kernel
      have hl : raw40187step3Labels = raw40187step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node98 node98Labels := by rfl

def raw40188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 2, -4]]
def raw40188Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 0, 0], ![0, 0, 0], ![2, 2, -4]]
def raw40188step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40188step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![0, 0, 0], ![2, 2, -4]]
def raw40188step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40188step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -3, 4], ![2, 2, -4]]
def raw40188step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40188step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw40188step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40188step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw40188step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40188 raw40188Labels = mixedMoment B node100 node100Labels := by
  calc
    mixedMoment B raw40188 raw40188Labels = mixedMoment B raw40188step0 raw40188step0Labels := by
      have hz : ∀ j, raw40188 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40188step0 = (fun i j => raw40188 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40188step0 raw40188; decide +kernel
      have hl : raw40188step0Labels = raw40188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40188 raw40188Labels permutation520 hz
    mixedMoment B raw40188step0 raw40188step0Labels = mixedMoment B raw40188step1 raw40188step1Labels := by
      have hz : ∀ j, raw40188step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40188step1 = (fun i j => raw40188step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40188step1 raw40188step0; decide +kernel
      have hl : raw40188step1Labels = raw40188step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40188step0 raw40188step0Labels permutation104 hz
    mixedMoment B raw40188step1 raw40188step1Labels = mixedMoment B raw40188step2 raw40188step2Labels := by
      have hz : ∀ j, raw40188step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40188step2 = (fun i j => raw40188step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40188step2 raw40188step1; decide +kernel
      have hl : raw40188step2Labels = raw40188step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40188step1 raw40188step1Labels permutation20 hz
    mixedMoment B raw40188step2 raw40188step2Labels = mixedMoment B raw40188step3 raw40188step3Labels := by
      have ha : raw40188step3 = (fun i j => raw40188step2 (permutation4 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40188step3 raw40188step2; decide +kernel
      have hl : raw40188step3Labels = raw40188step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40188step2 raw40188step2Labels permutation4 permutation6
    mixedMoment B raw40188step3 raw40188step3Labels = mixedMoment B raw40188step4 raw40188step4Labels := by
      have ha : raw40188step4 = -raw40188step3 := by apply Matrix.ext; change ∀ i j, raw40188step4 i j = -(raw40188step3 i j); unfold raw40188step4 raw40188step3; decide +kernel
      have hl : raw40188step4Labels = raw40188step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node100 node100Labels := by rfl

def raw40189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw40189Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40189step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw40189step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40189step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw40189step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40189 raw40189Labels = mixedMoment B node257 node257Labels := by
  calc
    mixedMoment B raw40189 raw40189Labels = mixedMoment B raw40189step0 raw40189step0Labels := by
      have ha : raw40189step0 = (fun i j => raw40189 (permutation434 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40189step0 raw40189; decide +kernel
      have hl : raw40189step0Labels = raw40189Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40189 raw40189Labels permutation434 permutation4
    mixedMoment B raw40189step0 raw40189step0Labels = mixedMoment B raw40189step1 raw40189step1Labels := by
      have ha : raw40189step1 = -raw40189step0 := by apply Matrix.ext; change ∀ i j, raw40189step1 i j = -(raw40189step0 i j); unfold raw40189step1 raw40189step0; decide +kernel
      have hl : raw40189step1Labels = raw40189step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node257 node257Labels := by rfl

def raw40190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw40190Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40190step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw40190step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40190 raw40190Labels = mixedMoment B node242 node242Labels := by
  calc
    mixedMoment B raw40190 raw40190Labels = mixedMoment B raw40190step0 raw40190step0Labels := by
      have ha : raw40190step0 = (fun i j => raw40190 (permutation505 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40190step0 raw40190; decide +kernel
      have hl : raw40190step0Labels = raw40190Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40190 raw40190Labels permutation505 permutation6
    _ = mixedMoment B node242 node242Labels := by rfl

def raw40191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw40191Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw40191step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40191step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical40191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40191 raw40191Labels = mixedMoment B node21 node21Labels := by
  calc
    mixedMoment B raw40191 raw40191Labels = mixedMoment B raw40191step0 raw40191step0Labels := by
      have ha : raw40191step0 = (fun i j => raw40191 (permutation590 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40191step0 raw40191; decide +kernel
      have hl : raw40191step0Labels = raw40191Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40191 raw40191Labels permutation590 permutation6
    _ = mixedMoment B node21 node21Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
