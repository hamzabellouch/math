import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw40576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw40576Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw40576step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40576step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw40576step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40576step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw40576step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40576 raw40576Labels = mixedMoment B node3623 node3623Labels := by
  calc
    mixedMoment B raw40576 raw40576Labels = mixedMoment B raw40576step0 raw40576step0Labels := by
      have hz : ∀ j, raw40576 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40576step0 = (fun i j => raw40576 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40576step0 raw40576; decide +kernel
      have hl : raw40576step0Labels = raw40576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40576 raw40576Labels permutation346 hz
    mixedMoment B raw40576step0 raw40576step0Labels = mixedMoment B raw40576step1 raw40576step1Labels := by
      have hz : ∀ j, raw40576step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40576step1 = (fun i j => raw40576step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40576step1 raw40576step0; decide +kernel
      have hl : raw40576step1Labels = raw40576step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40576step0 raw40576step0Labels permutation56 hz
    mixedMoment B raw40576step1 raw40576step1Labels = mixedMoment B raw40576step2 raw40576step2Labels := by
      have ha : raw40576step2 = (fun i j => raw40576step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40576step2 raw40576step1; decide +kernel
      have hl : raw40576step2Labels = raw40576step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40576step1 raw40576step1Labels permutation8 permutation3
    _ = mixedMoment B node3623 node3623Labels := by rfl

def raw40577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw40577Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw40577step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40577step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw40577step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40577step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw40577step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40577 raw40577Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw40577 raw40577Labels = mixedMoment B raw40577step0 raw40577step0Labels := by
      have hz : ∀ j, raw40577 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40577step0 = (fun i j => raw40577 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40577step0 raw40577; decide +kernel
      have hl : raw40577step0Labels = raw40577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40577 raw40577Labels permutation346 hz
    mixedMoment B raw40577step0 raw40577step0Labels = mixedMoment B raw40577step1 raw40577step1Labels := by
      have hz : ∀ j, raw40577step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40577step1 = (fun i j => raw40577step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40577step1 raw40577step0; decide +kernel
      have hl : raw40577step1Labels = raw40577step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40577step0 raw40577step0Labels permutation56 hz
    mixedMoment B raw40577step1 raw40577step1Labels = mixedMoment B raw40577step2 raw40577step2Labels := by
      have ha : raw40577step2 = (fun i j => raw40577step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40577step2 raw40577step1; decide +kernel
      have hl : raw40577step2Labels = raw40577step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40577step1 raw40577step1Labels permutation8 permutation3
    _ = mixedMoment B node3626 node3626Labels := by rfl

def raw40578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw40578Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw40578step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40578step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw40578step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40578step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw40578step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40578 raw40578Labels = mixedMoment B node3627 node3627Labels := by
  calc
    mixedMoment B raw40578 raw40578Labels = mixedMoment B raw40578step0 raw40578step0Labels := by
      have hz : ∀ j, raw40578 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40578step0 = (fun i j => raw40578 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40578step0 raw40578; decide +kernel
      have hl : raw40578step0Labels = raw40578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40578 raw40578Labels permutation346 hz
    mixedMoment B raw40578step0 raw40578step0Labels = mixedMoment B raw40578step1 raw40578step1Labels := by
      have hz : ∀ j, raw40578step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40578step1 = (fun i j => raw40578step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40578step1 raw40578step0; decide +kernel
      have hl : raw40578step1Labels = raw40578step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40578step0 raw40578step0Labels permutation56 hz
    mixedMoment B raw40578step1 raw40578step1Labels = mixedMoment B raw40578step2 raw40578step2Labels := by
      have ha : raw40578step2 = (fun i j => raw40578step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40578step2 raw40578step1; decide +kernel
      have hl : raw40578step2Labels = raw40578step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40578step1 raw40578step1Labels permutation8 permutation3
    _ = mixedMoment B node3627 node3627Labels := by rfl

def raw40579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw40579Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw40579step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40579step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw40579step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40579step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40579step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40579 raw40579Labels = mixedMoment B node3628 node3628Labels := by
  calc
    mixedMoment B raw40579 raw40579Labels = mixedMoment B raw40579step0 raw40579step0Labels := by
      have hz : ∀ j, raw40579 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40579step0 = (fun i j => raw40579 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40579step0 raw40579; decide +kernel
      have hl : raw40579step0Labels = raw40579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40579 raw40579Labels permutation346 hz
    mixedMoment B raw40579step0 raw40579step0Labels = mixedMoment B raw40579step1 raw40579step1Labels := by
      have hz : ∀ j, raw40579step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40579step1 = (fun i j => raw40579step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40579step1 raw40579step0; decide +kernel
      have hl : raw40579step1Labels = raw40579step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40579step0 raw40579step0Labels permutation56 hz
    mixedMoment B raw40579step1 raw40579step1Labels = mixedMoment B raw40579step2 raw40579step2Labels := by
      have ha : raw40579step2 = (fun i j => raw40579step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40579step2 raw40579step1; decide +kernel
      have hl : raw40579step2Labels = raw40579step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40579step1 raw40579step1Labels permutation8 permutation3
    _ = mixedMoment B node3628 node3628Labels := by rfl

def raw40580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40580Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40580step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40580step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40580step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40580step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw40580step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40580 raw40580Labels = mixedMoment B node3632 node3632Labels := by
  calc
    mixedMoment B raw40580 raw40580Labels = mixedMoment B raw40580step0 raw40580step0Labels := by
      have hz : ∀ j, raw40580 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40580step0 = (fun i j => raw40580 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40580step0 raw40580; decide +kernel
      have hl : raw40580step0Labels = raw40580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40580 raw40580Labels permutation346 hz
    mixedMoment B raw40580step0 raw40580step0Labels = mixedMoment B raw40580step1 raw40580step1Labels := by
      have hz : ∀ j, raw40580step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40580step1 = (fun i j => raw40580step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40580step1 raw40580step0; decide +kernel
      have hl : raw40580step1Labels = raw40580step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40580step0 raw40580step0Labels permutation56 hz
    mixedMoment B raw40580step1 raw40580step1Labels = mixedMoment B raw40580step2 raw40580step2Labels := by
      have ha : raw40580step2 = (fun i j => raw40580step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40580step2 raw40580step1; decide +kernel
      have hl : raw40580step2Labels = raw40580step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40580step1 raw40580step1Labels permutation8 permutation3
    _ = mixedMoment B node3632 node3632Labels := by rfl

def raw40581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw40581Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw40581step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40581step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw40581step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40581 raw40581Labels = mixedMoment B node3619 node3619Labels := by
  calc
    mixedMoment B raw40581 raw40581Labels = mixedMoment B raw40581step0 raw40581step0Labels := by
      have hz : ∀ j, raw40581 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40581step0 = (fun i j => raw40581 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40581step0 raw40581; decide +kernel
      have hl : raw40581step0Labels = raw40581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40581 raw40581Labels permutation265 hz
    mixedMoment B raw40581step0 raw40581step0Labels = mixedMoment B raw40581step1 raw40581step1Labels := by
      have ha : raw40581step1 = (fun i j => raw40581step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40581step1 raw40581step0; decide +kernel
      have hl : raw40581step1Labels = raw40581step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40581step0 raw40581step0Labels permutation32 permutation3
    _ = mixedMoment B node3619 node3619Labels := by rfl

def raw40582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw40582Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw40582step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40582step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw40582step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40582 raw40582Labels = mixedMoment B node3622 node3622Labels := by
  calc
    mixedMoment B raw40582 raw40582Labels = mixedMoment B raw40582step0 raw40582step0Labels := by
      have hz : ∀ j, raw40582 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40582step0 = (fun i j => raw40582 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40582step0 raw40582; decide +kernel
      have hl : raw40582step0Labels = raw40582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40582 raw40582Labels permutation265 hz
    mixedMoment B raw40582step0 raw40582step0Labels = mixedMoment B raw40582step1 raw40582step1Labels := by
      have ha : raw40582step1 = (fun i j => raw40582step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40582step1 raw40582step0; decide +kernel
      have hl : raw40582step1Labels = raw40582step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40582step0 raw40582step0Labels permutation32 permutation3
    _ = mixedMoment B node3622 node3622Labels := by rfl

def raw40583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw40583Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw40583step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40583step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw40583step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40583 raw40583Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw40583 raw40583Labels = mixedMoment B raw40583step0 raw40583step0Labels := by
      have hz : ∀ j, raw40583 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40583step0 = (fun i j => raw40583 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40583step0 raw40583; decide +kernel
      have hl : raw40583step0Labels = raw40583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40583 raw40583Labels permutation265 hz
    mixedMoment B raw40583step0 raw40583step0Labels = mixedMoment B raw40583step1 raw40583step1Labels := by
      have ha : raw40583step1 = (fun i j => raw40583step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40583step1 raw40583step0; decide +kernel
      have hl : raw40583step1Labels = raw40583step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40583step0 raw40583step0Labels permutation32 permutation3
    _ = mixedMoment B node3625 node3625Labels := by rfl

def raw40584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40584Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40584step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40584 raw40584Labels = mixedMoment B node3618 node3618Labels := by
  calc
    mixedMoment B raw40584 raw40584Labels = mixedMoment B raw40584step0 raw40584step0Labels := by
      have ha : raw40584step0 = (fun i j => raw40584 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40584step0 raw40584; decide +kernel
      have hl : raw40584step0Labels = raw40584Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40584 raw40584Labels permutation152 permutation3
    _ = mixedMoment B node3618 node3618Labels := by rfl

def raw40585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40585Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40585step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40585step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40585step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40585step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw40585step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40585step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw40585step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40585 raw40585Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw40585 raw40585Labels = mixedMoment B raw40585step0 raw40585step0Labels := by
      have hz : ∀ j, raw40585 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40585step0 = (fun i j => raw40585 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40585step0 raw40585; decide +kernel
      have hl : raw40585step0Labels = raw40585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40585 raw40585Labels permutation434 hz
    mixedMoment B raw40585step0 raw40585step0Labels = mixedMoment B raw40585step1 raw40585step1Labels := by
      have hz : ∀ j, raw40585step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40585step1 = (fun i j => raw40585step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40585step1 raw40585step0; decide +kernel
      have hl : raw40585step1Labels = raw40585step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40585step0 raw40585step0Labels permutation80 hz
    mixedMoment B raw40585step1 raw40585step1Labels = mixedMoment B raw40585step2 raw40585step2Labels := by
      have ha : raw40585step2 = (fun i j => raw40585step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40585step2 raw40585step1; decide +kernel
      have hl : raw40585step2Labels = raw40585step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40585step1 raw40585step1Labels permutation31 permutation3
    mixedMoment B raw40585step2 raw40585step2Labels = mixedMoment B raw40585step3 raw40585step3Labels := by
      have ha : raw40585step3 = -raw40585step2 := by apply Matrix.ext; change ∀ i j, raw40585step3 i j = -(raw40585step2 i j); unfold raw40585step3 raw40585step2; decide +kernel
      have hl : raw40585step3Labels = raw40585step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2742 node2742Labels := by rfl

def raw40586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40586Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40586step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40586step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40586step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40586step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 0, 1], ![-2, 0, 2]]
def raw40586step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40586step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw40586step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40586 raw40586Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw40586 raw40586Labels = mixedMoment B raw40586step0 raw40586step0Labels := by
      have hz : ∀ j, raw40586 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40586step0 = (fun i j => raw40586 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40586step0 raw40586; decide +kernel
      have hl : raw40586step0Labels = raw40586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40586 raw40586Labels permutation434 hz
    mixedMoment B raw40586step0 raw40586step0Labels = mixedMoment B raw40586step1 raw40586step1Labels := by
      have hz : ∀ j, raw40586step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40586step1 = (fun i j => raw40586step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40586step1 raw40586step0; decide +kernel
      have hl : raw40586step1Labels = raw40586step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40586step0 raw40586step0Labels permutation80 hz
    mixedMoment B raw40586step1 raw40586step1Labels = mixedMoment B raw40586step2 raw40586step2Labels := by
      have ha : raw40586step2 = (fun i j => raw40586step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40586step2 raw40586step1; decide +kernel
      have hl : raw40586step2Labels = raw40586step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40586step1 raw40586step1Labels permutation31 permutation3
    mixedMoment B raw40586step2 raw40586step2Labels = mixedMoment B raw40586step3 raw40586step3Labels := by
      have ha : raw40586step3 = -raw40586step2 := by apply Matrix.ext; change ∀ i j, raw40586step3 i j = -(raw40586step2 i j); unfold raw40586step3 raw40586step2; decide +kernel
      have hl : raw40586step3Labels = raw40586step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw40587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40587Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40587step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40587step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40587step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40587step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40587step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40587 raw40587Labels = mixedMoment B node3817 node3817Labels := by
  calc
    mixedMoment B raw40587 raw40587Labels = mixedMoment B raw40587step0 raw40587step0Labels := by
      have hz : ∀ j, raw40587 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40587step0 = (fun i j => raw40587 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40587step0 raw40587; decide +kernel
      have hl : raw40587step0Labels = raw40587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40587 raw40587Labels permutation434 hz
    mixedMoment B raw40587step0 raw40587step0Labels = mixedMoment B raw40587step1 raw40587step1Labels := by
      have hz : ∀ j, raw40587step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40587step1 = (fun i j => raw40587step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40587step1 raw40587step0; decide +kernel
      have hl : raw40587step1Labels = raw40587step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40587step0 raw40587step0Labels permutation80 hz
    mixedMoment B raw40587step1 raw40587step1Labels = mixedMoment B raw40587step2 raw40587step2Labels := by
      have ha : raw40587step2 = (fun i j => raw40587step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40587step2 raw40587step1; decide +kernel
      have hl : raw40587step2Labels = raw40587step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40587step1 raw40587step1Labels permutation8 permutation3
    _ = mixedMoment B node3817 node3817Labels := by rfl

def raw40588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40588Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40588step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40588step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40588step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40588step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw40588step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40588step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw40588step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40588 raw40588Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw40588 raw40588Labels = mixedMoment B raw40588step0 raw40588step0Labels := by
      have hz : ∀ j, raw40588 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40588step0 = (fun i j => raw40588 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40588step0 raw40588; decide +kernel
      have hl : raw40588step0Labels = raw40588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40588 raw40588Labels permutation434 hz
    mixedMoment B raw40588step0 raw40588step0Labels = mixedMoment B raw40588step1 raw40588step1Labels := by
      have hz : ∀ j, raw40588step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40588step1 = (fun i j => raw40588step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40588step1 raw40588step0; decide +kernel
      have hl : raw40588step1Labels = raw40588step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40588step0 raw40588step0Labels permutation80 hz
    mixedMoment B raw40588step1 raw40588step1Labels = mixedMoment B raw40588step2 raw40588step2Labels := by
      have ha : raw40588step2 = (fun i j => raw40588step1 (permutation22 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40588step2 raw40588step1; decide +kernel
      have hl : raw40588step2Labels = raw40588step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40588step1 raw40588step1Labels permutation22 permutation6
    mixedMoment B raw40588step2 raw40588step2Labels = mixedMoment B raw40588step3 raw40588step3Labels := by
      have ha : raw40588step3 = -raw40588step2 := by apply Matrix.ext; change ∀ i j, raw40588step3 i j = -(raw40588step2 i j); unfold raw40588step3 raw40588step2; decide +kernel
      have hl : raw40588step3Labels = raw40588step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3626 node3626Labels := by rfl

def raw40589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40589Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40589step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40589step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw40589step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40589step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw40589step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40589 raw40589Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw40589 raw40589Labels = mixedMoment B raw40589step0 raw40589step0Labels := by
      have hz : ∀ j, raw40589 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40589step0 = (fun i j => raw40589 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40589step0 raw40589; decide +kernel
      have hl : raw40589step0Labels = raw40589Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40589 raw40589Labels permutation346 hz
    mixedMoment B raw40589step0 raw40589step0Labels = mixedMoment B raw40589step1 raw40589step1Labels := by
      have ha : raw40589step1 = (fun i j => raw40589step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40589step1 raw40589step0; decide +kernel
      have hl : raw40589step1Labels = raw40589step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40589step0 raw40589step0Labels permutation145 permutation3
    mixedMoment B raw40589step1 raw40589step1Labels = mixedMoment B raw40589step2 raw40589step2Labels := by
      have ha : raw40589step2 = -raw40589step1 := by apply Matrix.ext; change ∀ i j, raw40589step2 i j = -(raw40589step1 i j); unfold raw40589step2 raw40589step1; decide +kernel
      have hl : raw40589step2Labels = raw40589step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3077 node3077Labels := by rfl

def raw40590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40590Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40590step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40590step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40590step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40590 raw40590Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw40590 raw40590Labels = mixedMoment B raw40590step0 raw40590step0Labels := by
      have hz : ∀ j, raw40590 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40590step0 = (fun i j => raw40590 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40590step0 raw40590; decide +kernel
      have hl : raw40590step0Labels = raw40590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40590 raw40590Labels permutation346 hz
    mixedMoment B raw40590step0 raw40590step0Labels = mixedMoment B raw40590step1 raw40590step1Labels := by
      have ha : raw40590step1 = (fun i j => raw40590step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40590step1 raw40590step0; decide +kernel
      have hl : raw40590step1Labels = raw40590step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40590step0 raw40590step0Labels permutation32 permutation3
    _ = mixedMoment B node3807 node3807Labels := by rfl

def raw40591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40591Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40591step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40591step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40591 raw40591Labels = mixedMoment B node3808 node3808Labels := by
  calc
    mixedMoment B raw40591 raw40591Labels = mixedMoment B raw40591step0 raw40591step0Labels := by
      have hz : ∀ j, raw40591 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40591step0 = (fun i j => raw40591 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40591step0 raw40591; decide +kernel
      have hl : raw40591step0Labels = raw40591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40591 raw40591Labels permutation346 hz
    mixedMoment B raw40591step0 raw40591step0Labels = mixedMoment B raw40591step1 raw40591step1Labels := by
      have ha : raw40591step1 = (fun i j => raw40591step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40591step1 raw40591step0; decide +kernel
      have hl : raw40591step1Labels = raw40591step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40591step0 raw40591step0Labels permutation32 permutation3
    _ = mixedMoment B node3808 node3808Labels := by rfl

def raw40592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40592Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40592step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40592step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40592 raw40592Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw40592 raw40592Labels = mixedMoment B raw40592step0 raw40592step0Labels := by
      have hz : ∀ j, raw40592 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40592step0 = (fun i j => raw40592 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40592step0 raw40592; decide +kernel
      have hl : raw40592step0Labels = raw40592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40592 raw40592Labels permutation346 hz
    mixedMoment B raw40592step0 raw40592step0Labels = mixedMoment B raw40592step1 raw40592step1Labels := by
      have ha : raw40592step1 = (fun i j => raw40592step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40592step1 raw40592step0; decide +kernel
      have hl : raw40592step1Labels = raw40592step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40592step0 raw40592step0Labels permutation32 permutation3
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw40593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40593Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40593step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40593step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40593step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40593 raw40593Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw40593 raw40593Labels = mixedMoment B raw40593step0 raw40593step0Labels := by
      have hz : ∀ j, raw40593 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40593step0 = (fun i j => raw40593 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40593step0 raw40593; decide +kernel
      have hl : raw40593step0Labels = raw40593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40593 raw40593Labels permutation346 hz
    mixedMoment B raw40593step0 raw40593step0Labels = mixedMoment B raw40593step1 raw40593step1Labels := by
      have ha : raw40593step1 = (fun i j => raw40593step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40593step1 raw40593step0; decide +kernel
      have hl : raw40593step1Labels = raw40593step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40593step0 raw40593step0Labels permutation32 permutation3
    _ = mixedMoment B node3813 node3813Labels := by rfl

def raw40594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40594Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40594step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40594step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40594 raw40594Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw40594 raw40594Labels = mixedMoment B raw40594step0 raw40594step0Labels := by
      have hz : ∀ j, raw40594 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40594step0 = (fun i j => raw40594 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40594step0 raw40594; decide +kernel
      have hl : raw40594step0Labels = raw40594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40594 raw40594Labels permutation346 hz
    mixedMoment B raw40594step0 raw40594step0Labels = mixedMoment B raw40594step1 raw40594step1Labels := by
      have ha : raw40594step1 = (fun i j => raw40594step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40594step1 raw40594step0; decide +kernel
      have hl : raw40594step1Labels = raw40594step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40594step0 raw40594step0Labels permutation32 permutation3
    _ = mixedMoment B node3814 node3814Labels := by rfl

def raw40595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40595Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40595step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40595step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40595step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40595 raw40595Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw40595 raw40595Labels = mixedMoment B raw40595step0 raw40595step0Labels := by
      have hz : ∀ j, raw40595 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40595step0 = (fun i j => raw40595 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40595step0 raw40595; decide +kernel
      have hl : raw40595step0Labels = raw40595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40595 raw40595Labels permutation346 hz
    mixedMoment B raw40595step0 raw40595step0Labels = mixedMoment B raw40595step1 raw40595step1Labels := by
      have ha : raw40595step1 = (fun i j => raw40595step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40595step1 raw40595step0; decide +kernel
      have hl : raw40595step1Labels = raw40595step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40595step0 raw40595step0Labels permutation32 permutation3
    _ = mixedMoment B node3816 node3816Labels := by rfl

def raw40596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40596Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40596step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40596step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40596 raw40596Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw40596 raw40596Labels = mixedMoment B raw40596step0 raw40596step0Labels := by
      have ha : raw40596step0 = (fun i j => raw40596 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40596step0 raw40596; decide +kernel
      have hl : raw40596step0Labels = raw40596Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40596 raw40596Labels permutation152 permutation3
    _ = mixedMoment B node3800 node3800Labels := by rfl

def raw40597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40597Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40597step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40597 raw40597Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw40597 raw40597Labels = mixedMoment B raw40597step0 raw40597step0Labels := by
      have ha : raw40597step0 = (fun i j => raw40597 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40597step0 raw40597; decide +kernel
      have hl : raw40597step0Labels = raw40597Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40597 raw40597Labels permutation152 permutation3
    _ = mixedMoment B node3801 node3801Labels := by rfl

def raw40598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw40598Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw40598step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40598 raw40598Labels = mixedMoment B node3805 node3805Labels := by
  calc
    mixedMoment B raw40598 raw40598Labels = mixedMoment B raw40598step0 raw40598step0Labels := by
      have ha : raw40598step0 = (fun i j => raw40598 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40598step0 raw40598; decide +kernel
      have hl : raw40598step0Labels = raw40598Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40598 raw40598Labels permutation152 permutation3
    _ = mixedMoment B node3805 node3805Labels := by rfl

def raw40599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40599Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40599step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40599step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40599 raw40599Labels = mixedMoment B node3806 node3806Labels := by
  calc
    mixedMoment B raw40599 raw40599Labels = mixedMoment B raw40599step0 raw40599step0Labels := by
      have ha : raw40599step0 = (fun i j => raw40599 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40599step0 raw40599; decide +kernel
      have hl : raw40599step0Labels = raw40599Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40599 raw40599Labels permutation152 permutation3
    _ = mixedMoment B node3806 node3806Labels := by rfl

def raw40600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40600Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40600step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40600 raw40600Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw40600 raw40600Labels = mixedMoment B raw40600step0 raw40600step0Labels := by
      have ha : raw40600step0 = (fun i j => raw40600 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40600step0 raw40600; decide +kernel
      have hl : raw40600step0Labels = raw40600Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40600 raw40600Labels permutation152 permutation3
    _ = mixedMoment B node3812 node3812Labels := by rfl

def raw40601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40601Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw40601step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40601step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0]]
def raw40601step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40601step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw40601step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40601step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40601step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40601 raw40601Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw40601 raw40601Labels = mixedMoment B raw40601step0 raw40601step0Labels := by
      have hz : ∀ j, raw40601 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40601step0 = (fun i j => raw40601 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40601step0 raw40601; decide +kernel
      have hl : raw40601step0Labels = raw40601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40601 raw40601Labels permutation520 hz
    mixedMoment B raw40601step0 raw40601step0Labels = mixedMoment B raw40601step1 raw40601step1Labels := by
      have hz : ∀ j, raw40601step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40601step1 = (fun i j => raw40601step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40601step1 raw40601step0; decide +kernel
      have hl : raw40601step1Labels = raw40601step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40601step0 raw40601step0Labels permutation104 hz
    mixedMoment B raw40601step1 raw40601step1Labels = mixedMoment B raw40601step2 raw40601step2Labels := by
      have ha : raw40601step2 = (fun i j => raw40601step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40601step2 raw40601step1; decide +kernel
      have hl : raw40601step2Labels = raw40601step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40601step1 raw40601step1Labels permutation31 permutation3
    mixedMoment B raw40601step2 raw40601step2Labels = mixedMoment B raw40601step3 raw40601step3Labels := by
      have ha : raw40601step3 = -raw40601step2 := by apply Matrix.ext; change ∀ i j, raw40601step3 i j = -(raw40601step2 i j); unfold raw40601step3 raw40601step2; decide +kernel
      have hl : raw40601step3Labels = raw40601step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2264 node2264Labels := by rfl

def raw40602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40602Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw40602step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw40602step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40602step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40602step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40602 raw40602Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw40602 raw40602Labels = mixedMoment B raw40602step0 raw40602step0Labels := by
      have hz : ∀ j, raw40602 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40602step0 = (fun i j => raw40602 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40602step0 raw40602; decide +kernel
      have hl : raw40602step0Labels = raw40602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40602 raw40602Labels permutation434 hz
    mixedMoment B raw40602step0 raw40602step0Labels = mixedMoment B raw40602step1 raw40602step1Labels := by
      have ha : raw40602step1 = (fun i j => raw40602step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40602step1 raw40602step0; decide +kernel
      have hl : raw40602step1Labels = raw40602step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40602step0 raw40602step0Labels permutation151 permutation3
    mixedMoment B raw40602step1 raw40602step1Labels = mixedMoment B raw40602step2 raw40602step2Labels := by
      have ha : raw40602step2 = -raw40602step1 := by apply Matrix.ext; change ∀ i j, raw40602step2 i j = -(raw40602step1 i j); unfold raw40602step2 raw40602step1; decide +kernel
      have hl : raw40602step2Labels = raw40602step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw40603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40603Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![3, -1, -2]]
def raw40603step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40603step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw40603step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40603step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40603step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40603 raw40603Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw40603 raw40603Labels = mixedMoment B raw40603step0 raw40603step0Labels := by
      have hz : ∀ j, raw40603 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40603step0 = (fun i j => raw40603 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40603step0 raw40603; decide +kernel
      have hl : raw40603step0Labels = raw40603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40603 raw40603Labels permutation434 hz
    mixedMoment B raw40603step0 raw40603step0Labels = mixedMoment B raw40603step1 raw40603step1Labels := by
      have ha : raw40603step1 = (fun i j => raw40603step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40603step1 raw40603step0; decide +kernel
      have hl : raw40603step1Labels = raw40603step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40603step0 raw40603step0Labels permutation151 permutation3
    mixedMoment B raw40603step1 raw40603step1Labels = mixedMoment B raw40603step2 raw40603step2Labels := by
      have ha : raw40603step2 = -raw40603step1 := by apply Matrix.ext; change ∀ i j, raw40603step2 i j = -(raw40603step1 i j); unfold raw40603step2 raw40603step1; decide +kernel
      have hl : raw40603step2Labels = raw40603step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3038 node3038Labels := by rfl

def raw40604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40604Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw40604step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw40604step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40604step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40604step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40604 raw40604Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw40604 raw40604Labels = mixedMoment B raw40604step0 raw40604step0Labels := by
      have hz : ∀ j, raw40604 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40604step0 = (fun i j => raw40604 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40604step0 raw40604; decide +kernel
      have hl : raw40604step0Labels = raw40604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40604 raw40604Labels permutation434 hz
    mixedMoment B raw40604step0 raw40604step0Labels = mixedMoment B raw40604step1 raw40604step1Labels := by
      have ha : raw40604step1 = (fun i j => raw40604step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40604step1 raw40604step0; decide +kernel
      have hl : raw40604step1Labels = raw40604step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40604step0 raw40604step0Labels permutation151 permutation3
    mixedMoment B raw40604step1 raw40604step1Labels = mixedMoment B raw40604step2 raw40604step2Labels := by
      have ha : raw40604step2 = -raw40604step1 := by apply Matrix.ext; change ∀ i j, raw40604step2 i j = -(raw40604step1 i j); unfold raw40604step2 raw40604step1; decide +kernel
      have hl : raw40604step2Labels = raw40604step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3807 node3807Labels := by rfl

def raw40605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40605Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw40605step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40605step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40605step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40605 raw40605Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw40605 raw40605Labels = mixedMoment B raw40605step0 raw40605step0Labels := by
      have hz : ∀ j, raw40605 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40605step0 = (fun i j => raw40605 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40605step0 raw40605; decide +kernel
      have hl : raw40605step0Labels = raw40605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40605 raw40605Labels permutation434 hz
    mixedMoment B raw40605step0 raw40605step0Labels = mixedMoment B raw40605step1 raw40605step1Labels := by
      have ha : raw40605step1 = (fun i j => raw40605step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40605step1 raw40605step0; decide +kernel
      have hl : raw40605step1Labels = raw40605step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40605step0 raw40605step0Labels permutation32 permutation3
    _ = mixedMoment B node3845 node3845Labels := by rfl

def raw40606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40606Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw40606step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw40606step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40606step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40606step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40606 raw40606Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw40606 raw40606Labels = mixedMoment B raw40606step0 raw40606step0Labels := by
      have hz : ∀ j, raw40606 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40606step0 = (fun i j => raw40606 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40606step0 raw40606; decide +kernel
      have hl : raw40606step0Labels = raw40606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40606 raw40606Labels permutation434 hz
    mixedMoment B raw40606step0 raw40606step0Labels = mixedMoment B raw40606step1 raw40606step1Labels := by
      have ha : raw40606step1 = (fun i j => raw40606step0 (permutation110 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40606step1 raw40606step0; decide +kernel
      have hl : raw40606step1Labels = raw40606step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40606step0 raw40606step0Labels permutation110 permutation6
    mixedMoment B raw40606step1 raw40606step1Labels = mixedMoment B raw40606step2 raw40606step2Labels := by
      have ha : raw40606step2 = -raw40606step1 := by apply Matrix.ext; change ∀ i j, raw40606step2 i j = -(raw40606step1 i j); unfold raw40606step2 raw40606step1; decide +kernel
      have hl : raw40606step2Labels = raw40606step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3541 node3541Labels := by rfl

def raw40607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40607Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40607step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40607step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40607 raw40607Labels = mixedMoment B node3837 node3837Labels := by
  calc
    mixedMoment B raw40607 raw40607Labels = mixedMoment B raw40607step0 raw40607step0Labels := by
      have ha : raw40607step0 = (fun i j => raw40607 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40607step0 raw40607; decide +kernel
      have hl : raw40607step0Labels = raw40607Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40607 raw40607Labels permutation152 permutation3
    _ = mixedMoment B node3837 node3837Labels := by rfl

def raw40608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40608Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40608step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40608step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40608 raw40608Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw40608 raw40608Labels = mixedMoment B raw40608step0 raw40608step0Labels := by
      have ha : raw40608step0 = (fun i j => raw40608 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40608step0 raw40608; decide +kernel
      have hl : raw40608step0Labels = raw40608Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40608 raw40608Labels permutation152 permutation3
    _ = mixedMoment B node3838 node3838Labels := by rfl

def raw40609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40609Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40609step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40609 raw40609Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw40609 raw40609Labels = mixedMoment B raw40609step0 raw40609step0Labels := by
      have ha : raw40609step0 = (fun i j => raw40609 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40609step0 raw40609; decide +kernel
      have hl : raw40609step0Labels = raw40609Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40609 raw40609Labels permutation152 permutation3
    _ = mixedMoment B node3839 node3839Labels := by rfl

def raw40610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40610Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40610step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40610step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40610 raw40610Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw40610 raw40610Labels = mixedMoment B raw40610step0 raw40610step0Labels := by
      have ha : raw40610step0 = (fun i j => raw40610 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40610step0 raw40610; decide +kernel
      have hl : raw40610step0Labels = raw40610Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40610 raw40610Labels permutation152 permutation3
    _ = mixedMoment B node3840 node3840Labels := by rfl

def raw40611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40611Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40611step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40611step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40611 raw40611Labels = mixedMoment B node3841 node3841Labels := by
  calc
    mixedMoment B raw40611 raw40611Labels = mixedMoment B raw40611step0 raw40611step0Labels := by
      have ha : raw40611step0 = (fun i j => raw40611 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40611step0 raw40611; decide +kernel
      have hl : raw40611step0Labels = raw40611Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40611 raw40611Labels permutation152 permutation3
    _ = mixedMoment B node3841 node3841Labels := by rfl

def raw40612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40612Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40612step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40612step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40612 raw40612Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw40612 raw40612Labels = mixedMoment B raw40612step0 raw40612step0Labels := by
      have ha : raw40612step0 = (fun i j => raw40612 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40612step0 raw40612; decide +kernel
      have hl : raw40612step0Labels = raw40612Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40612 raw40612Labels permutation152 permutation3
    _ = mixedMoment B node3843 node3843Labels := by rfl

def raw40613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40613Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40613step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40613step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40613 raw40613Labels = mixedMoment B node3844 node3844Labels := by
  calc
    mixedMoment B raw40613 raw40613Labels = mixedMoment B raw40613step0 raw40613step0Labels := by
      have ha : raw40613step0 = (fun i j => raw40613 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40613step0 raw40613; decide +kernel
      have hl : raw40613step0Labels = raw40613Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40613 raw40613Labels permutation152 permutation3
    _ = mixedMoment B node3844 node3844Labels := by rfl

def raw40614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw40614Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw40614step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40614step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![2, 1, -3]]
def raw40614step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40614step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40614step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40614 raw40614Labels = mixedMoment B node3052 node3052Labels := by
  calc
    mixedMoment B raw40614 raw40614Labels = mixedMoment B raw40614step0 raw40614step0Labels := by
      have hz : ∀ j, raw40614 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40614step0 = (fun i j => raw40614 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40614step0 raw40614; decide +kernel
      have hl : raw40614step0Labels = raw40614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40614 raw40614Labels permutation434 hz
    mixedMoment B raw40614step0 raw40614step0Labels = mixedMoment B raw40614step1 raw40614step1Labels := by
      have hz : ∀ j, raw40614step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40614step1 = (fun i j => raw40614step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40614step1 raw40614step0; decide +kernel
      have hl : raw40614step1Labels = raw40614step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40614step0 raw40614step0Labels permutation80 hz
    mixedMoment B raw40614step1 raw40614step1Labels = mixedMoment B raw40614step2 raw40614step2Labels := by
      have ha : raw40614step2 = (fun i j => raw40614step1 (permutation26 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40614step2 raw40614step1; decide +kernel
      have hl : raw40614step2Labels = raw40614step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40614step1 raw40614step1Labels permutation26 permutation6
    _ = mixedMoment B node3052 node3052Labels := by rfl

def raw40615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw40615Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw40615step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40615step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw40615step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40615 raw40615Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw40615 raw40615Labels = mixedMoment B raw40615step0 raw40615step0Labels := by
      have hz : ∀ j, raw40615 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40615step0 = (fun i j => raw40615 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40615step0 raw40615; decide +kernel
      have hl : raw40615step0Labels = raw40615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40615 raw40615Labels permutation346 hz
    mixedMoment B raw40615step0 raw40615step0Labels = mixedMoment B raw40615step1 raw40615step1Labels := by
      have ha : raw40615step1 = (fun i j => raw40615step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40615step1 raw40615step0; decide +kernel
      have hl : raw40615step1Labels = raw40615step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40615step0 raw40615step0Labels permutation32 permutation3
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw40616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw40616Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw40616step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40616step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40616 raw40616Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw40616 raw40616Labels = mixedMoment B raw40616step0 raw40616step0Labels := by
      have hz : ∀ j, raw40616 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40616step0 = (fun i j => raw40616 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40616step0 raw40616; decide +kernel
      have hl : raw40616step0Labels = raw40616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40616 raw40616Labels permutation346 hz
    mixedMoment B raw40616step0 raw40616step0Labels = mixedMoment B raw40616step1 raw40616step1Labels := by
      have ha : raw40616step1 = (fun i j => raw40616step0 (permutation128 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40616step1 raw40616step0; decide +kernel
      have hl : raw40616step1Labels = raw40616step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40616step0 raw40616step0Labels permutation128 permutation6
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw40617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40617Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40617step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw40617step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40617 raw40617Labels = mixedMoment B node3854 node3854Labels := by
  calc
    mixedMoment B raw40617 raw40617Labels = mixedMoment B raw40617step0 raw40617step0Labels := by
      have hz : ∀ j, raw40617 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40617step0 = (fun i j => raw40617 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40617step0 raw40617; decide +kernel
      have hl : raw40617step0Labels = raw40617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40617 raw40617Labels permutation346 hz
    mixedMoment B raw40617step0 raw40617step0Labels = mixedMoment B raw40617step1 raw40617step1Labels := by
      have ha : raw40617step1 = (fun i j => raw40617step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40617step1 raw40617step0; decide +kernel
      have hl : raw40617step1Labels = raw40617step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40617step0 raw40617step0Labels permutation32 permutation3
    _ = mixedMoment B node3854 node3854Labels := by rfl

def raw40618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40618Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40618step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40618step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40618step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40618 raw40618Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw40618 raw40618Labels = mixedMoment B raw40618step0 raw40618step0Labels := by
      have hz : ∀ j, raw40618 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40618step0 = (fun i j => raw40618 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40618step0 raw40618; decide +kernel
      have hl : raw40618step0Labels = raw40618Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40618 raw40618Labels permutation346 hz
    mixedMoment B raw40618step0 raw40618step0Labels = mixedMoment B raw40618step1 raw40618step1Labels := by
      have ha : raw40618step1 = (fun i j => raw40618step0 (permutation132 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40618step1 raw40618step0; decide +kernel
      have hl : raw40618step1Labels = raw40618step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40618step0 raw40618step0Labels permutation132 permutation6
    _ = mixedMoment B node3038 node3038Labels := by rfl

def raw40619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40619Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40619step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw40619step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40619 raw40619Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw40619 raw40619Labels = mixedMoment B raw40619step0 raw40619step0Labels := by
      have ha : raw40619step0 = (fun i j => raw40619 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40619step0 raw40619; decide +kernel
      have hl : raw40619step0Labels = raw40619Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40619 raw40619Labels permutation152 permutation3
    _ = mixedMoment B node3846 node3846Labels := by rfl

def raw40620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40620Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40620step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40620 raw40620Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw40620 raw40620Labels = mixedMoment B raw40620step0 raw40620step0Labels := by
      have ha : raw40620step0 = (fun i j => raw40620 (permutation599 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40620step0 raw40620; decide +kernel
      have hl : raw40620step0Labels = raw40620Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40620 raw40620Labels permutation599 permutation6
    _ = mixedMoment B node3037 node3037Labels := by rfl

def raw40621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw40621Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40621step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw40621step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40621 raw40621Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw40621 raw40621Labels = mixedMoment B raw40621step0 raw40621step0Labels := by
      have ha : raw40621step0 = (fun i j => raw40621 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40621step0 raw40621; decide +kernel
      have hl : raw40621step0Labels = raw40621Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40621 raw40621Labels permutation152 permutation3
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw40622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw40622Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40622step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40622step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40622 raw40622Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw40622 raw40622Labels = mixedMoment B raw40622step0 raw40622step0Labels := by
      have ha : raw40622step0 = (fun i j => raw40622 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40622step0 raw40622; decide +kernel
      have hl : raw40622step0Labels = raw40622Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40622 raw40622Labels permutation152 permutation3
    _ = mixedMoment B node3849 node3849Labels := by rfl

def raw40623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw40623Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw40623step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40623step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40623step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40623 raw40623Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw40623 raw40623Labels = mixedMoment B raw40623step0 raw40623step0Labels := by
      have ha : raw40623step0 = (fun i j => raw40623 (permutation380 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40623step0 raw40623; decide +kernel
      have hl : raw40623step0Labels = raw40623Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40623 raw40623Labels permutation380 permutation6
    mixedMoment B raw40623step0 raw40623step0Labels = mixedMoment B raw40623step1 raw40623step1Labels := by
      have ha : raw40623step1 = -raw40623step0 := by apply Matrix.ext; change ∀ i j, raw40623step1 i j = -(raw40623step0 i j); unfold raw40623step1 raw40623step0; decide +kernel
      have hl : raw40623step1Labels = raw40623step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3840 node3840Labels := by rfl

def raw40624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw40624Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw40624step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40624step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw40624step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40624step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw40624step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40624step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw40624step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40624 raw40624Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw40624 raw40624Labels = mixedMoment B raw40624step0 raw40624step0Labels := by
      have hz : ∀ j, raw40624 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40624step0 = (fun i j => raw40624 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40624step0 raw40624; decide +kernel
      have hl : raw40624step0Labels = raw40624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40624 raw40624Labels permutation520 hz
    mixedMoment B raw40624step0 raw40624step0Labels = mixedMoment B raw40624step1 raw40624step1Labels := by
      have hz : ∀ j, raw40624step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40624step1 = (fun i j => raw40624step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40624step1 raw40624step0; decide +kernel
      have hl : raw40624step1Labels = raw40624step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40624step0 raw40624step0Labels permutation104 hz
    mixedMoment B raw40624step1 raw40624step1Labels = mixedMoment B raw40624step2 raw40624step2Labels := by
      have ha : raw40624step2 = (fun i j => raw40624step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40624step2 raw40624step1; decide +kernel
      have hl : raw40624step2Labels = raw40624step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40624step1 raw40624step1Labels permutation31 permutation3
    mixedMoment B raw40624step2 raw40624step2Labels = mixedMoment B raw40624step3 raw40624step3Labels := by
      have ha : raw40624step3 = -raw40624step2 := by apply Matrix.ext; change ∀ i j, raw40624step3 i j = -(raw40624step2 i j); unfold raw40624step3 raw40624step2; decide +kernel
      have hl : raw40624step3Labels = raw40624step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2765 node2765Labels := by rfl

def raw40625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw40625Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw40625step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw40625step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw40625step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40625 raw40625Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw40625 raw40625Labels = mixedMoment B raw40625step0 raw40625step0Labels := by
      have hz : ∀ j, raw40625 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40625step0 = (fun i j => raw40625 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40625step0 raw40625; decide +kernel
      have hl : raw40625step0Labels = raw40625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40625 raw40625Labels permutation434 hz
    mixedMoment B raw40625step0 raw40625step0Labels = mixedMoment B raw40625step1 raw40625step1Labels := by
      have ha : raw40625step1 = (fun i j => raw40625step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40625step1 raw40625step0; decide +kernel
      have hl : raw40625step1Labels = raw40625step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40625step0 raw40625step0Labels permutation151 permutation3
    mixedMoment B raw40625step1 raw40625step1Labels = mixedMoment B raw40625step2 raw40625step2Labels := by
      have ha : raw40625step2 = -raw40625step1 := by apply Matrix.ext; change ∀ i j, raw40625step2 i j = -(raw40625step1 i j); unfold raw40625step2 raw40625step1; decide +kernel
      have hl : raw40625step2Labels = raw40625step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3086 node3086Labels := by rfl

def raw40626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw40626Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40626step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw40626step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40626step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw40626step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40626 raw40626Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw40626 raw40626Labels = mixedMoment B raw40626step0 raw40626step0Labels := by
      have hz : ∀ j, raw40626 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40626step0 = (fun i j => raw40626 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40626step0 raw40626; decide +kernel
      have hl : raw40626step0Labels = raw40626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40626 raw40626Labels permutation434 hz
    mixedMoment B raw40626step0 raw40626step0Labels = mixedMoment B raw40626step1 raw40626step1Labels := by
      have ha : raw40626step1 = (fun i j => raw40626step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40626step1 raw40626step0; decide +kernel
      have hl : raw40626step1Labels = raw40626step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40626step0 raw40626step0Labels permutation151 permutation3
    mixedMoment B raw40626step1 raw40626step1Labels = mixedMoment B raw40626step2 raw40626step2Labels := by
      have ha : raw40626step2 = -raw40626step1 := by apply Matrix.ext; change ∀ i j, raw40626step2 i j = -(raw40626step1 i j); unfold raw40626step2 raw40626step1; decide +kernel
      have hl : raw40626step2Labels = raw40626step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw40627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw40627Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw40627step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40627step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw40627step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40627 raw40627Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw40627 raw40627Labels = mixedMoment B raw40627step0 raw40627step0Labels := by
      have hz : ∀ j, raw40627 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40627step0 = (fun i j => raw40627 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40627step0 raw40627; decide +kernel
      have hl : raw40627step0Labels = raw40627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40627 raw40627Labels permutation434 hz
    mixedMoment B raw40627step0 raw40627step0Labels = mixedMoment B raw40627step1 raw40627step1Labels := by
      have ha : raw40627step1 = (fun i j => raw40627step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40627step1 raw40627step0; decide +kernel
      have hl : raw40627step1Labels = raw40627step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40627step0 raw40627step0Labels permutation32 permutation3
    _ = mixedMoment B node3877 node3877Labels := by rfl

def raw40628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40628Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40628step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40628 raw40628Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw40628 raw40628Labels = mixedMoment B raw40628step0 raw40628step0Labels := by
      have ha : raw40628step0 = (fun i j => raw40628 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40628step0 raw40628; decide +kernel
      have hl : raw40628step0Labels = raw40628Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40628 raw40628Labels permutation152 permutation3
    _ = mixedMoment B node3871 node3871Labels := by rfl

def raw40629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40629Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40629step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40629 raw40629Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw40629 raw40629Labels = mixedMoment B raw40629step0 raw40629step0Labels := by
      have ha : raw40629step0 = (fun i j => raw40629 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40629step0 raw40629; decide +kernel
      have hl : raw40629step0Labels = raw40629Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40629 raw40629Labels permutation152 permutation3
    _ = mixedMoment B node3872 node3872Labels := by rfl

def raw40630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw40630Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw40630step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40630 raw40630Labels = mixedMoment B node3874 node3874Labels := by
  calc
    mixedMoment B raw40630 raw40630Labels = mixedMoment B raw40630step0 raw40630step0Labels := by
      have ha : raw40630step0 = (fun i j => raw40630 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40630step0 raw40630; decide +kernel
      have hl : raw40630step0Labels = raw40630Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40630 raw40630Labels permutation152 permutation3
    _ = mixedMoment B node3874 node3874Labels := by rfl

def raw40631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40631Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40631step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40631 raw40631Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw40631 raw40631Labels = mixedMoment B raw40631step0 raw40631step0Labels := by
      have ha : raw40631step0 = (fun i j => raw40631 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40631step0 raw40631; decide +kernel
      have hl : raw40631step0Labels = raw40631Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40631 raw40631Labels permutation152 permutation3
    _ = mixedMoment B node3875 node3875Labels := by rfl

def raw40632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw40632Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw40632step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40632step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw40632step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40632step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw40632step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40632 raw40632Labels = mixedMoment B node3886 node3886Labels := by
  calc
    mixedMoment B raw40632 raw40632Labels = mixedMoment B raw40632step0 raw40632step0Labels := by
      have hz : ∀ j, raw40632 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40632step0 = (fun i j => raw40632 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40632step0 raw40632; decide +kernel
      have hl : raw40632step0Labels = raw40632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40632 raw40632Labels permutation434 hz
    mixedMoment B raw40632step0 raw40632step0Labels = mixedMoment B raw40632step1 raw40632step1Labels := by
      have hz : ∀ j, raw40632step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40632step1 = (fun i j => raw40632step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40632step1 raw40632step0; decide +kernel
      have hl : raw40632step1Labels = raw40632step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40632step0 raw40632step0Labels permutation80 hz
    mixedMoment B raw40632step1 raw40632step1Labels = mixedMoment B raw40632step2 raw40632step2Labels := by
      have ha : raw40632step2 = (fun i j => raw40632step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40632step2 raw40632step1; decide +kernel
      have hl : raw40632step2Labels = raw40632step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40632step1 raw40632step1Labels permutation8 permutation3
    _ = mixedMoment B node3886 node3886Labels := by rfl

def raw40633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw40633Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw40633step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40633step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw40633step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40633step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40633step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40633 raw40633Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw40633 raw40633Labels = mixedMoment B raw40633step0 raw40633step0Labels := by
      have hz : ∀ j, raw40633 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40633step0 = (fun i j => raw40633 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40633step0 raw40633; decide +kernel
      have hl : raw40633step0Labels = raw40633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40633 raw40633Labels permutation434 hz
    mixedMoment B raw40633step0 raw40633step0Labels = mixedMoment B raw40633step1 raw40633step1Labels := by
      have hz : ∀ j, raw40633step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40633step1 = (fun i j => raw40633step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40633step1 raw40633step0; decide +kernel
      have hl : raw40633step1Labels = raw40633step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40633step0 raw40633step0Labels permutation80 hz
    mixedMoment B raw40633step1 raw40633step1Labels = mixedMoment B raw40633step2 raw40633step2Labels := by
      have ha : raw40633step2 = (fun i j => raw40633step1 (permutation27 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40633step2 raw40633step1; decide +kernel
      have hl : raw40633step2Labels = raw40633step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40633step1 raw40633step1Labels permutation27 permutation6
    _ = mixedMoment B node3055 node3055Labels := by rfl

def raw40634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40634Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40634step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40634 raw40634Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw40634 raw40634Labels = mixedMoment B raw40634step0 raw40634step0Labels := by
      have hz : ∀ j, raw40634 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40634step0 = (fun i j => raw40634 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40634step0 raw40634; decide +kernel
      have hl : raw40634step0Labels = raw40634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40634 raw40634Labels permutation346 hz
    mixedMoment B raw40634step0 raw40634step0Labels = mixedMoment B raw40634step1 raw40634step1Labels := by
      have ha : raw40634step1 = (fun i j => raw40634step0 (permutation133 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40634step1 raw40634step0; decide +kernel
      have hl : raw40634step1Labels = raw40634step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40634step0 raw40634step0Labels permutation133 permutation6
    _ = mixedMoment B node3039 node3039Labels := by rfl

def raw40635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw40635Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw40635step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw40635step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40635 raw40635Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw40635 raw40635Labels = mixedMoment B raw40635step0 raw40635step0Labels := by
      have hz : ∀ j, raw40635 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40635step0 = (fun i j => raw40635 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40635step0 raw40635; decide +kernel
      have hl : raw40635step0Labels = raw40635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40635 raw40635Labels permutation346 hz
    mixedMoment B raw40635step0 raw40635step0Labels = mixedMoment B raw40635step1 raw40635step1Labels := by
      have ha : raw40635step1 = (fun i j => raw40635step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40635step1 raw40635step0; decide +kernel
      have hl : raw40635step1Labels = raw40635step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40635step0 raw40635step0Labels permutation32 permutation3
    _ = mixedMoment B node3884 node3884Labels := by rfl

def raw40636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw40636Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw40636step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40636step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40636step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40636 raw40636Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw40636 raw40636Labels = mixedMoment B raw40636step0 raw40636step0Labels := by
      have hz : ∀ j, raw40636 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40636step0 = (fun i j => raw40636 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40636step0 raw40636; decide +kernel
      have hl : raw40636step0Labels = raw40636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40636 raw40636Labels permutation346 hz
    mixedMoment B raw40636step0 raw40636step0Labels = mixedMoment B raw40636step1 raw40636step1Labels := by
      have ha : raw40636step1 = (fun i j => raw40636step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40636step1 raw40636step0; decide +kernel
      have hl : raw40636step1Labels = raw40636step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40636step0 raw40636step0Labels permutation32 permutation3
    _ = mixedMoment B node3885 node3885Labels := by rfl

def raw40637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw40637Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw40637step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40637step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![3, -1, -2]]
def raw40637step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40637step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 3, -1]]
def raw40637step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40637step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw40637step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40637 raw40637Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw40637 raw40637Labels = mixedMoment B raw40637step0 raw40637step0Labels := by
      have hz : ∀ j, raw40637 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40637step0 = (fun i j => raw40637 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40637step0 raw40637; decide +kernel
      have hl : raw40637step0Labels = raw40637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40637 raw40637Labels permutation520 hz
    mixedMoment B raw40637step0 raw40637step0Labels = mixedMoment B raw40637step1 raw40637step1Labels := by
      have hz : ∀ j, raw40637step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40637step1 = (fun i j => raw40637step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40637step1 raw40637step0; decide +kernel
      have hl : raw40637step1Labels = raw40637step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40637step0 raw40637step0Labels permutation104 hz
    mixedMoment B raw40637step1 raw40637step1Labels = mixedMoment B raw40637step2 raw40637step2Labels := by
      have ha : raw40637step2 = (fun i j => raw40637step1 (permutation14 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40637step2 raw40637step1; decide +kernel
      have hl : raw40637step2Labels = raw40637step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40637step1 raw40637step1Labels permutation14 permutation6
    mixedMoment B raw40637step2 raw40637step2Labels = mixedMoment B raw40637step3 raw40637step3Labels := by
      have ha : raw40637step3 = -raw40637step2 := by apply Matrix.ext; change ∀ i j, raw40637step3 i j = -(raw40637step2 i j); unfold raw40637step3 raw40637step2; decide +kernel
      have hl : raw40637step3Labels = raw40637step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2777 node2777Labels := by rfl

def raw40638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40638Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40638step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw40638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40638step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw40638step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40638 raw40638Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw40638 raw40638Labels = mixedMoment B raw40638step0 raw40638step0Labels := by
      have hz : ∀ j, raw40638 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40638step0 = (fun i j => raw40638 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40638step0 raw40638; decide +kernel
      have hl : raw40638step0Labels = raw40638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40638 raw40638Labels permutation434 hz
    mixedMoment B raw40638step0 raw40638step0Labels = mixedMoment B raw40638step1 raw40638step1Labels := by
      have ha : raw40638step1 = (fun i j => raw40638step0 (permutation61 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40638step1 raw40638step0; decide +kernel
      have hl : raw40638step1Labels = raw40638step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40638step0 raw40638step0Labels permutation61 permutation6
    mixedMoment B raw40638step1 raw40638step1Labels = mixedMoment B raw40638step2 raw40638step2Labels := by
      have ha : raw40638step2 = -raw40638step1 := by apply Matrix.ext; change ∀ i j, raw40638step2 i j = -(raw40638step1 i j); unfold raw40638step2 raw40638step1; decide +kernel
      have hl : raw40638step2Labels = raw40638step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw40639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40639Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40639step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw40639step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40639step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40639step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40639 raw40639Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw40639 raw40639Labels = mixedMoment B raw40639step0 raw40639step0Labels := by
      have hz : ∀ j, raw40639 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40639step0 = (fun i j => raw40639 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40639step0 raw40639; decide +kernel
      have hl : raw40639step0Labels = raw40639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40639 raw40639Labels permutation434 hz
    mixedMoment B raw40639step0 raw40639step0Labels = mixedMoment B raw40639step1 raw40639step1Labels := by
      have ha : raw40639step1 = (fun i j => raw40639step0 (permutation68 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40639step1 raw40639step0; decide +kernel
      have hl : raw40639step1Labels = raw40639step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40639step0 raw40639step0Labels permutation68 permutation6
    mixedMoment B raw40639step1 raw40639step1Labels = mixedMoment B raw40639step2 raw40639step2Labels := by
      have ha : raw40639step2 = -raw40639step1 := by apply Matrix.ext; change ∀ i j, raw40639step2 i j = -(raw40639step1 i j); unfold raw40639step2 raw40639step1; decide +kernel
      have hl : raw40639step2Labels = raw40639step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2732 node2732Labels := by rfl

def raw40640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40640Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40640step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw40640step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40640step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40640step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40640 raw40640Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw40640 raw40640Labels = mixedMoment B raw40640step0 raw40640step0Labels := by
      have ha : raw40640step0 = (fun i j => raw40640 (permutation336 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40640step0 raw40640; decide +kernel
      have hl : raw40640step0Labels = raw40640Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40640 raw40640Labels permutation336 permutation6
    mixedMoment B raw40640step0 raw40640step0Labels = mixedMoment B raw40640step1 raw40640step1Labels := by
      have ha : raw40640step1 = -raw40640step0 := by apply Matrix.ext; change ∀ i j, raw40640step1 i j = -(raw40640step0 i j); unfold raw40640step1 raw40640step0; decide +kernel
      have hl : raw40640step1Labels = raw40640step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2730 node2730Labels := by rfl

def raw40641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw40641Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw40641step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, -1, 0], ![2, 1, -3]]
def raw40641step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40641step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw40641step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40641step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw40641step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40641 raw40641Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw40641 raw40641Labels = mixedMoment B raw40641step0 raw40641step0Labels := by
      have hz : ∀ j, raw40641 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40641step0 = (fun i j => raw40641 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40641step0 raw40641; decide +kernel
      have hl : raw40641step0Labels = raw40641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40641 raw40641Labels permutation434 hz
    mixedMoment B raw40641step0 raw40641step0Labels = mixedMoment B raw40641step1 raw40641step1Labels := by
      have hz : ∀ j, raw40641step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40641step1 = (fun i j => raw40641step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40641step1 raw40641step0; decide +kernel
      have hl : raw40641step1Labels = raw40641step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40641step0 raw40641step0Labels permutation80 hz
    mixedMoment B raw40641step1 raw40641step1Labels = mixedMoment B raw40641step2 raw40641step2Labels := by
      have ha : raw40641step2 = (fun i j => raw40641step1 (permutation16 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40641step2 raw40641step1; decide +kernel
      have hl : raw40641step2Labels = raw40641step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40641step1 raw40641step1Labels permutation16 permutation6
    mixedMoment B raw40641step2 raw40641step2Labels = mixedMoment B raw40641step3 raw40641step3Labels := by
      have ha : raw40641step3 = -raw40641step2 := by apply Matrix.ext; change ∀ i j, raw40641step3 i j = -(raw40641step2 i j); unfold raw40641step3 raw40641step2; decide +kernel
      have hl : raw40641step3Labels = raw40641step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2734 node2734Labels := by rfl

def raw40642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw40642Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw40642step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw40642step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40642step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40642step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40642 raw40642Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw40642 raw40642Labels = mixedMoment B raw40642step0 raw40642step0Labels := by
      have hz : ∀ j, raw40642 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40642step0 = (fun i j => raw40642 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40642step0 raw40642; decide +kernel
      have hl : raw40642step0Labels = raw40642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40642 raw40642Labels permutation346 hz
    mixedMoment B raw40642step0 raw40642step0Labels = mixedMoment B raw40642step1 raw40642step1Labels := by
      have ha : raw40642step1 = (fun i j => raw40642step0 (permutation75 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40642step1 raw40642step0; decide +kernel
      have hl : raw40642step1Labels = raw40642step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40642step0 raw40642step0Labels permutation75 permutation6
    mixedMoment B raw40642step1 raw40642step1Labels = mixedMoment B raw40642step2 raw40642step2Labels := by
      have ha : raw40642step2 = -raw40642step1 := by apply Matrix.ext; change ∀ i j, raw40642step2 i j = -(raw40642step1 i j); unfold raw40642step2 raw40642step1; decide +kernel
      have hl : raw40642step2Labels = raw40642step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2731 node2731Labels := by rfl

def raw40643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw40643Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw40643step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40643step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1]]
def raw40643step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40643step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![2, -3, 1]]
def raw40643step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40643step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![-2, 0, 2]]
def raw40643step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40643step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![2, 0, -2]]
def raw40643step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40643 raw40643Labels = mixedMoment B node3629 node3629Labels := by
  calc
    mixedMoment B raw40643 raw40643Labels = mixedMoment B raw40643step0 raw40643step0Labels := by
      have hz : ∀ j, raw40643 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40643step0 = (fun i j => raw40643 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40643step0 raw40643; decide +kernel
      have hl : raw40643step0Labels = raw40643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40643 raw40643Labels permutation520 hz
    mixedMoment B raw40643step0 raw40643step0Labels = mixedMoment B raw40643step1 raw40643step1Labels := by
      have hz : ∀ j, raw40643step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40643step1 = (fun i j => raw40643step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40643step1 raw40643step0; decide +kernel
      have hl : raw40643step1Labels = raw40643step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40643step0 raw40643step0Labels permutation104 hz
    mixedMoment B raw40643step1 raw40643step1Labels = mixedMoment B raw40643step2 raw40643step2Labels := by
      have hz : ∀ j, raw40643step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40643step2 = (fun i j => raw40643step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40643step2 raw40643step1; decide +kernel
      have hl : raw40643step2Labels = raw40643step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40643step1 raw40643step1Labels permutation20 hz
    mixedMoment B raw40643step2 raw40643step2Labels = mixedMoment B raw40643step3 raw40643step3Labels := by
      have ha : raw40643step3 = (fun i j => raw40643step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40643step3 raw40643step2; decide +kernel
      have hl : raw40643step3Labels = raw40643step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40643step2 raw40643step2Labels permutation7 permutation3
    mixedMoment B raw40643step3 raw40643step3Labels = mixedMoment B raw40643step4 raw40643step4Labels := by
      have ha : raw40643step4 = -raw40643step3 := by apply Matrix.ext; change ∀ i j, raw40643step4 i j = -(raw40643step3 i j); unfold raw40643step4 raw40643step3; decide +kernel
      have hl : raw40643step4Labels = raw40643step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3629 node3629Labels := by rfl

def raw40644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw40644Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw40644step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40644step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0]]
def raw40644step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40644step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw40644step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40644 raw40644Labels = mixedMoment B node3905 node3905Labels := by
  calc
    mixedMoment B raw40644 raw40644Labels = mixedMoment B raw40644step0 raw40644step0Labels := by
      have hz : ∀ j, raw40644 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40644step0 = (fun i j => raw40644 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40644step0 raw40644; decide +kernel
      have hl : raw40644step0Labels = raw40644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40644 raw40644Labels permutation434 hz
    mixedMoment B raw40644step0 raw40644step0Labels = mixedMoment B raw40644step1 raw40644step1Labels := by
      have hz : ∀ j, raw40644step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40644step1 = (fun i j => raw40644step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40644step1 raw40644step0; decide +kernel
      have hl : raw40644step1Labels = raw40644step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40644step0 raw40644step0Labels permutation80 hz
    mixedMoment B raw40644step1 raw40644step1Labels = mixedMoment B raw40644step2 raw40644step2Labels := by
      have ha : raw40644step2 = (fun i j => raw40644step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40644step2 raw40644step1; decide +kernel
      have hl : raw40644step2Labels = raw40644step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40644step1 raw40644step1Labels permutation8 permutation3
    _ = mixedMoment B node3905 node3905Labels := by rfl

def raw40645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw40645Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw40645step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40645step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1]]
def raw40645step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40645step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw40645step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40645 raw40645Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw40645 raw40645Labels = mixedMoment B raw40645step0 raw40645step0Labels := by
      have hz : ∀ j, raw40645 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40645step0 = (fun i j => raw40645 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40645step0 raw40645; decide +kernel
      have hl : raw40645step0Labels = raw40645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40645 raw40645Labels permutation434 hz
    mixedMoment B raw40645step0 raw40645step0Labels = mixedMoment B raw40645step1 raw40645step1Labels := by
      have hz : ∀ j, raw40645step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40645step1 = (fun i j => raw40645step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40645step1 raw40645step0; decide +kernel
      have hl : raw40645step1Labels = raw40645step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40645step0 raw40645step0Labels permutation80 hz
    mixedMoment B raw40645step1 raw40645step1Labels = mixedMoment B raw40645step2 raw40645step2Labels := by
      have ha : raw40645step2 = (fun i j => raw40645step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40645step2 raw40645step1; decide +kernel
      have hl : raw40645step2Labels = raw40645step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40645step1 raw40645step1Labels permutation8 permutation3
    _ = mixedMoment B node3907 node3907Labels := by rfl

def raw40646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw40646Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw40646step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, -3, 3], ![2, 0, -2]]
def raw40646step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40646step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw40646step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40646step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40646step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40646 raw40646Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw40646 raw40646Labels = mixedMoment B raw40646step0 raw40646step0Labels := by
      have hz : ∀ j, raw40646 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40646step0 = (fun i j => raw40646 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40646step0 raw40646; decide +kernel
      have hl : raw40646step0Labels = raw40646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40646 raw40646Labels permutation434 hz
    mixedMoment B raw40646step0 raw40646step0Labels = mixedMoment B raw40646step1 raw40646step1Labels := by
      have hz : ∀ j, raw40646step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40646step1 = (fun i j => raw40646step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40646step1 raw40646step0; decide +kernel
      have hl : raw40646step1Labels = raw40646step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40646step0 raw40646step0Labels permutation80 hz
    mixedMoment B raw40646step1 raw40646step1Labels = mixedMoment B raw40646step2 raw40646step2Labels := by
      have ha : raw40646step2 = (fun i j => raw40646step1 (permutation20 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40646step2 raw40646step1; decide +kernel
      have hl : raw40646step2Labels = raw40646step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40646step1 raw40646step1Labels permutation20 permutation6
    mixedMoment B raw40646step2 raw40646step2Labels = mixedMoment B raw40646step3 raw40646step3Labels := by
      have ha : raw40646step3 = -raw40646step2 := by apply Matrix.ext; change ∀ i j, raw40646step3 i j = -(raw40646step2 i j); unfold raw40646step3 raw40646step2; decide +kernel
      have hl : raw40646step3Labels = raw40646step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2279 node2279Labels := by rfl

def raw40647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2]]
def raw40647Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2]]
def raw40647step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40647step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, -3, 2]]
def raw40647step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40647step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw40647step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40647step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw40647step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40647 raw40647Labels = mixedMoment B node3632 node3632Labels := by
  calc
    mixedMoment B raw40647 raw40647Labels = mixedMoment B raw40647step0 raw40647step0Labels := by
      have hz : ∀ j, raw40647 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40647step0 = (fun i j => raw40647 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40647step0 raw40647; decide +kernel
      have hl : raw40647step0Labels = raw40647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40647 raw40647Labels permutation434 hz
    mixedMoment B raw40647step0 raw40647step0Labels = mixedMoment B raw40647step1 raw40647step1Labels := by
      have hz : ∀ j, raw40647step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40647step1 = (fun i j => raw40647step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40647step1 raw40647step0; decide +kernel
      have hl : raw40647step1Labels = raw40647step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40647step0 raw40647step0Labels permutation80 hz
    mixedMoment B raw40647step1 raw40647step1Labels = mixedMoment B raw40647step2 raw40647step2Labels := by
      have ha : raw40647step2 = (fun i j => raw40647step1 (permutation27 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40647step2 raw40647step1; decide +kernel
      have hl : raw40647step2Labels = raw40647step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40647step1 raw40647step1Labels permutation27 permutation6
    mixedMoment B raw40647step2 raw40647step2Labels = mixedMoment B raw40647step3 raw40647step3Labels := by
      have ha : raw40647step3 = -raw40647step2 := by apply Matrix.ext; change ∀ i j, raw40647step3 i j = -(raw40647step2 i j); unfold raw40647step3 raw40647step2; decide +kernel
      have hl : raw40647step3Labels = raw40647step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3632 node3632Labels := by rfl

def raw40648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40648Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40648step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40648step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40648step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40648step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw40648step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40648 raw40648Labels = mixedMoment B node3908 node3908Labels := by
  calc
    mixedMoment B raw40648 raw40648Labels = mixedMoment B raw40648step0 raw40648step0Labels := by
      have hz : ∀ j, raw40648 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40648step0 = (fun i j => raw40648 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40648step0 raw40648; decide +kernel
      have hl : raw40648step0Labels = raw40648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40648 raw40648Labels permutation434 hz
    mixedMoment B raw40648step0 raw40648step0Labels = mixedMoment B raw40648step1 raw40648step1Labels := by
      have hz : ∀ j, raw40648step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40648step1 = (fun i j => raw40648step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40648step1 raw40648step0; decide +kernel
      have hl : raw40648step1Labels = raw40648step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40648step0 raw40648step0Labels permutation80 hz
    mixedMoment B raw40648step1 raw40648step1Labels = mixedMoment B raw40648step2 raw40648step2Labels := by
      have ha : raw40648step2 = (fun i j => raw40648step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40648step2 raw40648step1; decide +kernel
      have hl : raw40648step2Labels = raw40648step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40648step1 raw40648step1Labels permutation8 permutation3
    _ = mixedMoment B node3908 node3908Labels := by rfl

def raw40649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw40649Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw40649step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw40649step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40649step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40649 raw40649Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw40649 raw40649Labels = mixedMoment B raw40649step0 raw40649step0Labels := by
      have hz : ∀ j, raw40649 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40649step0 = (fun i j => raw40649 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40649step0 raw40649; decide +kernel
      have hl : raw40649step0Labels = raw40649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40649 raw40649Labels permutation346 hz
    mixedMoment B raw40649step0 raw40649step0Labels = mixedMoment B raw40649step1 raw40649step1Labels := by
      have ha : raw40649step1 = (fun i j => raw40649step0 (permutation116 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40649step1 raw40649step0; decide +kernel
      have hl : raw40649step1Labels = raw40649step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40649step0 raw40649step0Labels permutation116 permutation6
    mixedMoment B raw40649step1 raw40649step1Labels = mixedMoment B raw40649step2 raw40649step2Labels := by
      have ha : raw40649step2 = -raw40649step1 := by apply Matrix.ext; change ∀ i j, raw40649step2 i j = -(raw40649step1 i j); unfold raw40649step2 raw40649step1; decide +kernel
      have hl : raw40649step2Labels = raw40649step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3814 node3814Labels := by rfl

def raw40650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw40650Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw40650step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw40650step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40650 raw40650Labels = mixedMoment B node3903 node3903Labels := by
  calc
    mixedMoment B raw40650 raw40650Labels = mixedMoment B raw40650step0 raw40650step0Labels := by
      have hz : ∀ j, raw40650 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40650step0 = (fun i j => raw40650 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40650step0 raw40650; decide +kernel
      have hl : raw40650step0Labels = raw40650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40650 raw40650Labels permutation346 hz
    mixedMoment B raw40650step0 raw40650step0Labels = mixedMoment B raw40650step1 raw40650step1Labels := by
      have ha : raw40650step1 = (fun i j => raw40650step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40650step1 raw40650step0; decide +kernel
      have hl : raw40650step1Labels = raw40650step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40650step0 raw40650step0Labels permutation32 permutation3
    _ = mixedMoment B node3903 node3903Labels := by rfl

def raw40651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw40651Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw40651step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40651step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40651 raw40651Labels = mixedMoment B node3904 node3904Labels := by
  calc
    mixedMoment B raw40651 raw40651Labels = mixedMoment B raw40651step0 raw40651step0Labels := by
      have hz : ∀ j, raw40651 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40651step0 = (fun i j => raw40651 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40651step0 raw40651; decide +kernel
      have hl : raw40651step0Labels = raw40651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40651 raw40651Labels permutation346 hz
    mixedMoment B raw40651step0 raw40651step0Labels = mixedMoment B raw40651step1 raw40651step1Labels := by
      have ha : raw40651step1 = (fun i j => raw40651step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40651step1 raw40651step0; decide +kernel
      have hl : raw40651step1Labels = raw40651step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40651step0 raw40651step0Labels permutation32 permutation3
    _ = mixedMoment B node3904 node3904Labels := by rfl

def raw40652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40652Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40652step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw40652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40652 raw40652Labels = mixedMoment B node3906 node3906Labels := by
  calc
    mixedMoment B raw40652 raw40652Labels = mixedMoment B raw40652step0 raw40652step0Labels := by
      have hz : ∀ j, raw40652 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40652step0 = (fun i j => raw40652 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40652step0 raw40652; decide +kernel
      have hl : raw40652step0Labels = raw40652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40652 raw40652Labels permutation346 hz
    mixedMoment B raw40652step0 raw40652step0Labels = mixedMoment B raw40652step1 raw40652step1Labels := by
      have ha : raw40652step1 = (fun i j => raw40652step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40652step1 raw40652step0; decide +kernel
      have hl : raw40652step1Labels = raw40652step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40652step0 raw40652step0Labels permutation32 permutation3
    _ = mixedMoment B node3906 node3906Labels := by rfl

def raw40653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]
def raw40653Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]
def raw40653step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40653step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw40653step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40653step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40653step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40653 raw40653Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw40653 raw40653Labels = mixedMoment B raw40653step0 raw40653step0Labels := by
      have hz : ∀ j, raw40653 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40653step0 = (fun i j => raw40653 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40653step0 raw40653; decide +kernel
      have hl : raw40653step0Labels = raw40653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40653 raw40653Labels permutation346 hz
    mixedMoment B raw40653step0 raw40653step0Labels = mixedMoment B raw40653step1 raw40653step1Labels := by
      have ha : raw40653step1 = (fun i j => raw40653step0 (permutation83 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40653step1 raw40653step0; decide +kernel
      have hl : raw40653step1Labels = raw40653step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40653step0 raw40653step0Labels permutation83 permutation6
    mixedMoment B raw40653step1 raw40653step1Labels = mixedMoment B raw40653step2 raw40653step2Labels := by
      have ha : raw40653step2 = -raw40653step1 := by apply Matrix.ext; change ∀ i j, raw40653step2 i j = -(raw40653step1 i j); unfold raw40653step2 raw40653step1; decide +kernel
      have hl : raw40653step2Labels = raw40653step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2277 node2277Labels := by rfl

def raw40654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw40654Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw40654step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40654 raw40654Labels = mixedMoment B node3901 node3901Labels := by
  calc
    mixedMoment B raw40654 raw40654Labels = mixedMoment B raw40654step0 raw40654step0Labels := by
      have ha : raw40654step0 = (fun i j => raw40654 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40654step0 raw40654; decide +kernel
      have hl : raw40654step0Labels = raw40654Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40654 raw40654Labels permutation152 permutation3
    _ = mixedMoment B node3901 node3901Labels := by rfl

def raw40655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw40655Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw40655step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40655step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw40655step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40655 raw40655Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw40655 raw40655Labels = mixedMoment B raw40655step0 raw40655step0Labels := by
      have ha : raw40655step0 = (fun i j => raw40655 (permutation468 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40655step0 raw40655; decide +kernel
      have hl : raw40655step0Labels = raw40655Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40655 raw40655Labels permutation468 permutation6
    mixedMoment B raw40655step0 raw40655step0Labels = mixedMoment B raw40655step1 raw40655step1Labels := by
      have ha : raw40655step1 = -raw40655step0 := by apply Matrix.ext; change ∀ i j, raw40655step1 i j = -(raw40655step0 i j); unfold raw40655step1 raw40655step0; decide +kernel
      have hl : raw40655step1Labels = raw40655step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3812 node3812Labels := by rfl

def raw40656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw40656Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw40656step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40656step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw40656step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40656step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -3, 3], ![2, 1, -3]]
def raw40656step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40656step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw40656step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40656step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw40656step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40656 raw40656Labels = mixedMoment B node2281 node2281Labels := by
  calc
    mixedMoment B raw40656 raw40656Labels = mixedMoment B raw40656step0 raw40656step0Labels := by
      have hz : ∀ j, raw40656 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40656step0 = (fun i j => raw40656 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40656step0 raw40656; decide +kernel
      have hl : raw40656step0Labels = raw40656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40656 raw40656Labels permutation434 hz
    mixedMoment B raw40656step0 raw40656step0Labels = mixedMoment B raw40656step1 raw40656step1Labels := by
      have hz : ∀ j, raw40656step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40656step1 = (fun i j => raw40656step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40656step1 raw40656step0; decide +kernel
      have hl : raw40656step1Labels = raw40656step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40656step0 raw40656step0Labels permutation80 hz
    mixedMoment B raw40656step1 raw40656step1Labels = mixedMoment B raw40656step2 raw40656step2Labels := by
      have hz : ∀ j, raw40656step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40656step2 = (fun i j => raw40656step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40656step2 raw40656step1; decide +kernel
      have hl : raw40656step2Labels = raw40656step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40656step1 raw40656step1Labels permutation14 hz
    mixedMoment B raw40656step2 raw40656step2Labels = mixedMoment B raw40656step3 raw40656step3Labels := by
      have ha : raw40656step3 = (fun i j => raw40656step2 (permutation4 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40656step3 raw40656step2; decide +kernel
      have hl : raw40656step3Labels = raw40656step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40656step2 raw40656step2Labels permutation4 permutation6
    mixedMoment B raw40656step3 raw40656step3Labels = mixedMoment B raw40656step4 raw40656step4Labels := by
      have ha : raw40656step4 = -raw40656step3 := by apply Matrix.ext; change ∀ i j, raw40656step4 i j = -(raw40656step3 i j); unfold raw40656step4 raw40656step3; decide +kernel
      have hl : raw40656step4Labels = raw40656step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2281 node2281Labels := by rfl

def raw40657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw40657Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw40657step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40657step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw40657step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40657step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![1, 1, -2], ![1, -3, 2]]
def raw40657step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40657step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-2, 1, 1]]
def raw40657step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40657step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]
def raw40657step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40657 raw40657Labels = mixedMoment B node3633 node3633Labels := by
  calc
    mixedMoment B raw40657 raw40657Labels = mixedMoment B raw40657step0 raw40657step0Labels := by
      have hz : ∀ j, raw40657 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40657step0 = (fun i j => raw40657 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40657step0 raw40657; decide +kernel
      have hl : raw40657step0Labels = raw40657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40657 raw40657Labels permutation434 hz
    mixedMoment B raw40657step0 raw40657step0Labels = mixedMoment B raw40657step1 raw40657step1Labels := by
      have hz : ∀ j, raw40657step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40657step1 = (fun i j => raw40657step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40657step1 raw40657step0; decide +kernel
      have hl : raw40657step1Labels = raw40657step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40657step0 raw40657step0Labels permutation80 hz
    mixedMoment B raw40657step1 raw40657step1Labels = mixedMoment B raw40657step2 raw40657step2Labels := by
      have hz : ∀ j, raw40657step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40657step2 = (fun i j => raw40657step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40657step2 raw40657step1; decide +kernel
      have hl : raw40657step2Labels = raw40657step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40657step1 raw40657step1Labels permutation14 hz
    mixedMoment B raw40657step2 raw40657step2Labels = mixedMoment B raw40657step3 raw40657step3Labels := by
      have ha : raw40657step3 = (fun i j => raw40657step2 (permutation6 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40657step3 raw40657step2; decide +kernel
      have hl : raw40657step3Labels = raw40657step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40657step2 raw40657step2Labels permutation6 permutation6
    mixedMoment B raw40657step3 raw40657step3Labels = mixedMoment B raw40657step4 raw40657step4Labels := by
      have ha : raw40657step4 = -raw40657step3 := by apply Matrix.ext; change ∀ i j, raw40657step4 i j = -(raw40657step3 i j); unfold raw40657step4 raw40657step3; decide +kernel
      have hl : raw40657step4Labels = raw40657step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3633 node3633Labels := by rfl

def raw40658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw40658Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw40658step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40658step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw40658step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40658step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw40658step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40658 raw40658Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw40658 raw40658Labels = mixedMoment B raw40658step0 raw40658step0Labels := by
      have hz : ∀ j, raw40658 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40658step0 = (fun i j => raw40658 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40658step0 raw40658; decide +kernel
      have hl : raw40658step0Labels = raw40658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40658 raw40658Labels permutation346 hz
    mixedMoment B raw40658step0 raw40658step0Labels = mixedMoment B raw40658step1 raw40658step1Labels := by
      have hz : ∀ j, raw40658step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40658step1 = (fun i j => raw40658step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40658step1 raw40658step0; decide +kernel
      have hl : raw40658step1Labels = raw40658step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40658step0 raw40658step0Labels permutation56 hz
    mixedMoment B raw40658step1 raw40658step1Labels = mixedMoment B raw40658step2 raw40658step2Labels := by
      have ha : raw40658step2 = (fun i j => raw40658step1 (permutation26 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40658step2 raw40658step1; decide +kernel
      have hl : raw40658step2Labels = raw40658step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40658step1 raw40658step1Labels permutation26 permutation6
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw40659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw40659Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw40659step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40659step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1]]
def raw40659step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40659step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw40659step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40659 raw40659Labels = mixedMoment B node3913 node3913Labels := by
  calc
    mixedMoment B raw40659 raw40659Labels = mixedMoment B raw40659step0 raw40659step0Labels := by
      have hz : ∀ j, raw40659 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40659step0 = (fun i j => raw40659 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40659step0 raw40659; decide +kernel
      have hl : raw40659step0Labels = raw40659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40659 raw40659Labels permutation346 hz
    mixedMoment B raw40659step0 raw40659step0Labels = mixedMoment B raw40659step1 raw40659step1Labels := by
      have hz : ∀ j, raw40659step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40659step1 = (fun i j => raw40659step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40659step1 raw40659step0; decide +kernel
      have hl : raw40659step1Labels = raw40659step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40659step0 raw40659step0Labels permutation56 hz
    mixedMoment B raw40659step1 raw40659step1Labels = mixedMoment B raw40659step2 raw40659step2Labels := by
      have ha : raw40659step2 = (fun i j => raw40659step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40659step2 raw40659step1; decide +kernel
      have hl : raw40659step2Labels = raw40659step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40659step1 raw40659step1Labels permutation8 permutation3
    _ = mixedMoment B node3913 node3913Labels := by rfl

def raw40660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw40660Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw40660step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40660step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw40660step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40660step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1]]
def raw40660step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40660step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw40660step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40660 raw40660Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw40660 raw40660Labels = mixedMoment B raw40660step0 raw40660step0Labels := by
      have hz : ∀ j, raw40660 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40660step0 = (fun i j => raw40660 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40660step0 raw40660; decide +kernel
      have hl : raw40660step0Labels = raw40660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40660 raw40660Labels permutation346 hz
    mixedMoment B raw40660step0 raw40660step0Labels = mixedMoment B raw40660step1 raw40660step1Labels := by
      have hz : ∀ j, raw40660step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40660step1 = (fun i j => raw40660step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40660step1 raw40660step0; decide +kernel
      have hl : raw40660step1Labels = raw40660step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40660step0 raw40660step0Labels permutation56 hz
    mixedMoment B raw40660step1 raw40660step1Labels = mixedMoment B raw40660step2 raw40660step2Labels := by
      have ha : raw40660step2 = (fun i j => raw40660step1 (permutation18 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40660step2 raw40660step1; decide +kernel
      have hl : raw40660step2Labels = raw40660step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40660step1 raw40660step1Labels permutation18 permutation6
    mixedMoment B raw40660step2 raw40660step2Labels = mixedMoment B raw40660step3 raw40660step3Labels := by
      have ha : raw40660step3 = -raw40660step2 := by apply Matrix.ext; change ∀ i j, raw40660step3 i j = -(raw40660step2 i j); unfold raw40660step3 raw40660step2; decide +kernel
      have hl : raw40660step3Labels = raw40660step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3907 node3907Labels := by rfl

def raw40661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![1, 1, -2], ![1, 0, -1]]
def raw40661Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -3, 3], ![1, 1, -2], ![1, 0, -1]]
def raw40661step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40661step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -3, 3], ![1, 1, -2], ![1, 0, -1]]
def raw40661step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40661step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw40661step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40661step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40661step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40661 raw40661Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw40661 raw40661Labels = mixedMoment B raw40661step0 raw40661step0Labels := by
      have hz : ∀ j, raw40661 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40661step0 = (fun i j => raw40661 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40661step0 raw40661; decide +kernel
      have hl : raw40661step0Labels = raw40661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40661 raw40661Labels permutation346 hz
    mixedMoment B raw40661step0 raw40661step0Labels = mixedMoment B raw40661step1 raw40661step1Labels := by
      have hz : ∀ j, raw40661step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40661step1 = (fun i j => raw40661step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40661step1 raw40661step0; decide +kernel
      have hl : raw40661step1Labels = raw40661step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40661step0 raw40661step0Labels permutation56 hz
    mixedMoment B raw40661step1 raw40661step1Labels = mixedMoment B raw40661step2 raw40661step2Labels := by
      have ha : raw40661step2 = (fun i j => raw40661step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40661step2 raw40661step1; decide +kernel
      have hl : raw40661step2Labels = raw40661step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40661step1 raw40661step1Labels permutation15 permutation6
    mixedMoment B raw40661step2 raw40661step2Labels = mixedMoment B raw40661step3 raw40661step3Labels := by
      have ha : raw40661step3 = -raw40661step2 := by apply Matrix.ext; change ∀ i j, raw40661step3 i j = -(raw40661step2 i j); unfold raw40661step3 raw40661step2; decide +kernel
      have hl : raw40661step3Labels = raw40661step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2278 node2278Labels := by rfl

def raw40662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw40662Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw40662step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw40662step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40662 raw40662Labels = mixedMoment B node3910 node3910Labels := by
  calc
    mixedMoment B raw40662 raw40662Labels = mixedMoment B raw40662step0 raw40662step0Labels := by
      have hz : ∀ j, raw40662 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40662step0 = (fun i j => raw40662 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40662step0 raw40662; decide +kernel
      have hl : raw40662step0Labels = raw40662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40662 raw40662Labels permutation265 hz
    mixedMoment B raw40662step0 raw40662step0Labels = mixedMoment B raw40662step1 raw40662step1Labels := by
      have ha : raw40662step1 = (fun i j => raw40662step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40662step1 raw40662step0; decide +kernel
      have hl : raw40662step1Labels = raw40662step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40662step0 raw40662step0Labels permutation32 permutation3
    _ = mixedMoment B node3910 node3910Labels := by rfl

def raw40663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw40663Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw40663step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40663step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw40663step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40663step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40663step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40663 raw40663Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw40663 raw40663Labels = mixedMoment B raw40663step0 raw40663step0Labels := by
      have hz : ∀ j, raw40663 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40663step0 = (fun i j => raw40663 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40663step0 raw40663; decide +kernel
      have hl : raw40663step0Labels = raw40663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40663 raw40663Labels permutation265 hz
    mixedMoment B raw40663step0 raw40663step0Labels = mixedMoment B raw40663step1 raw40663step1Labels := by
      have ha : raw40663step1 = (fun i j => raw40663step0 (permutation87 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40663step1 raw40663step0; decide +kernel
      have hl : raw40663step1Labels = raw40663step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40663step0 raw40663step0Labels permutation87 permutation6
    mixedMoment B raw40663step1 raw40663step1Labels = mixedMoment B raw40663step2 raw40663step2Labels := by
      have ha : raw40663step2 = -raw40663step1 := by apply Matrix.ext; change ∀ i j, raw40663step2 i j = -(raw40663step1 i j); unfold raw40663step2 raw40663step1; decide +kernel
      have hl : raw40663step2Labels = raw40663step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3813 node3813Labels := by rfl

def raw40664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40664Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40664step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40664step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![3, -3, 0]]
def raw40664step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40664step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![3, -3, 0]]
def raw40664step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40664step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -1, 2], ![-2, 1, 1]]
def raw40664step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40664step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw40664step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40664 raw40664Labels = mixedMoment B node2293 node2293Labels := by
  calc
    mixedMoment B raw40664 raw40664Labels = mixedMoment B raw40664step0 raw40664step0Labels := by
      have hz : ∀ j, raw40664 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40664step0 = (fun i j => raw40664 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40664step0 raw40664; decide +kernel
      have hl : raw40664step0Labels = raw40664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40664 raw40664Labels permutation520 hz
    mixedMoment B raw40664step0 raw40664step0Labels = mixedMoment B raw40664step1 raw40664step1Labels := by
      have hz : ∀ j, raw40664step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40664step1 = (fun i j => raw40664step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40664step1 raw40664step0; decide +kernel
      have hl : raw40664step1Labels = raw40664step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40664step0 raw40664step0Labels permutation104 hz
    mixedMoment B raw40664step1 raw40664step1Labels = mixedMoment B raw40664step2 raw40664step2Labels := by
      have hz : ∀ j, raw40664step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40664step2 = (fun i j => raw40664step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40664step2 raw40664step1; decide +kernel
      have hl : raw40664step2Labels = raw40664step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40664step1 raw40664step1Labels permutation20 hz
    mixedMoment B raw40664step2 raw40664step2Labels = mixedMoment B raw40664step3 raw40664step3Labels := by
      have ha : raw40664step3 = (fun i j => raw40664step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40664step3 raw40664step2; decide +kernel
      have hl : raw40664step3Labels = raw40664step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40664step2 raw40664step2Labels permutation7 permutation3
    mixedMoment B raw40664step3 raw40664step3Labels = mixedMoment B raw40664step4 raw40664step4Labels := by
      have ha : raw40664step4 = -raw40664step3 := by apply Matrix.ext; change ∀ i j, raw40664step4 i j = -(raw40664step3 i j); unfold raw40664step4 raw40664step3; decide +kernel
      have hl : raw40664step4Labels = raw40664step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2293 node2293Labels := by rfl

def raw40665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40665Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40665step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40665step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![3, -2, -1]]
def raw40665step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40665step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw40665step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40665step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40665step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40665 raw40665Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw40665 raw40665Labels = mixedMoment B raw40665step0 raw40665step0Labels := by
      have hz : ∀ j, raw40665 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40665step0 = (fun i j => raw40665 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40665step0 raw40665; decide +kernel
      have hl : raw40665step0Labels = raw40665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40665 raw40665Labels permutation434 hz
    mixedMoment B raw40665step0 raw40665step0Labels = mixedMoment B raw40665step1 raw40665step1Labels := by
      have hz : ∀ j, raw40665step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40665step1 = (fun i j => raw40665step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40665step1 raw40665step0; decide +kernel
      have hl : raw40665step1Labels = raw40665step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40665step0 raw40665step0Labels permutation80 hz
    mixedMoment B raw40665step1 raw40665step1Labels = mixedMoment B raw40665step2 raw40665step2Labels := by
      have ha : raw40665step2 = (fun i j => raw40665step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40665step2 raw40665step1; decide +kernel
      have hl : raw40665step2Labels = raw40665step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40665step1 raw40665step1Labels permutation31 permutation3
    mixedMoment B raw40665step2 raw40665step2Labels = mixedMoment B raw40665step3 raw40665step3Labels := by
      have ha : raw40665step3 = -raw40665step2 := by apply Matrix.ext; change ∀ i j, raw40665step3 i j = -(raw40665step2 i j); unfold raw40665step3 raw40665step2; decide +kernel
      have hl : raw40665step3Labels = raw40665step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2743 node2743Labels := by rfl

def raw40666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40666Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40666step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40666step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![3, -1, -2]]
def raw40666step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40666step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, -1, 2], ![-2, 1, 1]]
def raw40666step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40666step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40666step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40666 raw40666Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw40666 raw40666Labels = mixedMoment B raw40666step0 raw40666step0Labels := by
      have hz : ∀ j, raw40666 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40666step0 = (fun i j => raw40666 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40666step0 raw40666; decide +kernel
      have hl : raw40666step0Labels = raw40666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40666 raw40666Labels permutation434 hz
    mixedMoment B raw40666step0 raw40666step0Labels = mixedMoment B raw40666step1 raw40666step1Labels := by
      have hz : ∀ j, raw40666step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40666step1 = (fun i j => raw40666step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40666step1 raw40666step0; decide +kernel
      have hl : raw40666step1Labels = raw40666step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40666step0 raw40666step0Labels permutation80 hz
    mixedMoment B raw40666step1 raw40666step1Labels = mixedMoment B raw40666step2 raw40666step2Labels := by
      have ha : raw40666step2 = (fun i j => raw40666step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40666step2 raw40666step1; decide +kernel
      have hl : raw40666step2Labels = raw40666step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40666step1 raw40666step1Labels permutation31 permutation3
    mixedMoment B raw40666step2 raw40666step2Labels = mixedMoment B raw40666step3 raw40666step3Labels := by
      have ha : raw40666step3 = -raw40666step2 := by apply Matrix.ext; change ∀ i j, raw40666step3 i j = -(raw40666step2 i j); unfold raw40666step3 raw40666step2; decide +kernel
      have hl : raw40666step3Labels = raw40666step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3055 node3055Labels := by rfl

def raw40667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40667Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40667step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40667step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw40667step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40667step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw40667step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40667step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40667step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40667 raw40667Labels = mixedMoment B node3817 node3817Labels := by
  calc
    mixedMoment B raw40667 raw40667Labels = mixedMoment B raw40667step0 raw40667step0Labels := by
      have hz : ∀ j, raw40667 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40667step0 = (fun i j => raw40667 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40667step0 raw40667; decide +kernel
      have hl : raw40667step0Labels = raw40667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40667 raw40667Labels permutation434 hz
    mixedMoment B raw40667step0 raw40667step0Labels = mixedMoment B raw40667step1 raw40667step1Labels := by
      have hz : ∀ j, raw40667step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40667step1 = (fun i j => raw40667step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40667step1 raw40667step0; decide +kernel
      have hl : raw40667step1Labels = raw40667step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40667step0 raw40667step0Labels permutation80 hz
    mixedMoment B raw40667step1 raw40667step1Labels = mixedMoment B raw40667step2 raw40667step2Labels := by
      have ha : raw40667step2 = (fun i j => raw40667step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40667step2 raw40667step1; decide +kernel
      have hl : raw40667step2Labels = raw40667step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40667step1 raw40667step1Labels permutation31 permutation3
    mixedMoment B raw40667step2 raw40667step2Labels = mixedMoment B raw40667step3 raw40667step3Labels := by
      have ha : raw40667step3 = -raw40667step2 := by apply Matrix.ext; change ∀ i j, raw40667step3 i j = -(raw40667step2 i j); unfold raw40667step3 raw40667step2; decide +kernel
      have hl : raw40667step3Labels = raw40667step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3817 node3817Labels := by rfl

def raw40668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40668Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40668step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40668step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw40668step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40668step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40668step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40668 raw40668Labels = mixedMoment B node3963 node3963Labels := by
  calc
    mixedMoment B raw40668 raw40668Labels = mixedMoment B raw40668step0 raw40668step0Labels := by
      have hz : ∀ j, raw40668 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40668step0 = (fun i j => raw40668 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40668step0 raw40668; decide +kernel
      have hl : raw40668step0Labels = raw40668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40668 raw40668Labels permutation434 hz
    mixedMoment B raw40668step0 raw40668step0Labels = mixedMoment B raw40668step1 raw40668step1Labels := by
      have hz : ∀ j, raw40668step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40668step1 = (fun i j => raw40668step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40668step1 raw40668step0; decide +kernel
      have hl : raw40668step1Labels = raw40668step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40668step0 raw40668step0Labels permutation80 hz
    mixedMoment B raw40668step1 raw40668step1Labels = mixedMoment B raw40668step2 raw40668step2Labels := by
      have ha : raw40668step2 = (fun i j => raw40668step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40668step2 raw40668step1; decide +kernel
      have hl : raw40668step2Labels = raw40668step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40668step1 raw40668step1Labels permutation8 permutation3
    _ = mixedMoment B node3963 node3963Labels := by rfl

def raw40669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40669Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40669step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw40669step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40669step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40669 raw40669Labels = mixedMoment B node3078 node3078Labels := by
  calc
    mixedMoment B raw40669 raw40669Labels = mixedMoment B raw40669step0 raw40669step0Labels := by
      have hz : ∀ j, raw40669 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40669step0 = (fun i j => raw40669 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40669step0 raw40669; decide +kernel
      have hl : raw40669step0Labels = raw40669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40669 raw40669Labels permutation346 hz
    mixedMoment B raw40669step0 raw40669step0Labels = mixedMoment B raw40669step1 raw40669step1Labels := by
      have ha : raw40669step1 = (fun i j => raw40669step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40669step1 raw40669step0; decide +kernel
      have hl : raw40669step1Labels = raw40669step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40669step0 raw40669step0Labels permutation145 permutation3
    mixedMoment B raw40669step1 raw40669step1Labels = mixedMoment B raw40669step2 raw40669step2Labels := by
      have ha : raw40669step2 = -raw40669step1 := by apply Matrix.ext; change ∀ i j, raw40669step2 i j = -(raw40669step1 i j); unfold raw40669step2 raw40669step1; decide +kernel
      have hl : raw40669step2Labels = raw40669step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3078 node3078Labels := by rfl

def raw40670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40670Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40670step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw40670step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40670step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40670step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40670 raw40670Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw40670 raw40670Labels = mixedMoment B raw40670step0 raw40670step0Labels := by
      have hz : ∀ j, raw40670 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40670step0 = (fun i j => raw40670 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40670step0 raw40670; decide +kernel
      have hl : raw40670step0Labels = raw40670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40670 raw40670Labels permutation346 hz
    mixedMoment B raw40670step0 raw40670step0Labels = mixedMoment B raw40670step1 raw40670step1Labels := by
      have ha : raw40670step1 = (fun i j => raw40670step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40670step1 raw40670step0; decide +kernel
      have hl : raw40670step1Labels = raw40670step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40670step0 raw40670step0Labels permutation151 permutation3
    mixedMoment B raw40670step1 raw40670step1Labels = mixedMoment B raw40670step2 raw40670step2Labels := by
      have ha : raw40670step2 = -raw40670step1 := by apply Matrix.ext; change ∀ i j, raw40670step2 i j = -(raw40670step1 i j); unfold raw40670step2 raw40670step1; decide +kernel
      have hl : raw40670step2Labels = raw40670step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3845 node3845Labels := by rfl

def raw40671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40671Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40671step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40671step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40671 raw40671Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw40671 raw40671Labels = mixedMoment B raw40671step0 raw40671step0Labels := by
      have hz : ∀ j, raw40671 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40671step0 = (fun i j => raw40671 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40671step0 raw40671; decide +kernel
      have hl : raw40671step0Labels = raw40671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40671 raw40671Labels permutation346 hz
    mixedMoment B raw40671step0 raw40671step0Labels = mixedMoment B raw40671step1 raw40671step1Labels := by
      have ha : raw40671step1 = (fun i j => raw40671step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40671step1 raw40671step0; decide +kernel
      have hl : raw40671step1Labels = raw40671step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40671step0 raw40671step0Labels permutation32 permutation3
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw40672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40672Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40672step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40672step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40672step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40672 raw40672Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw40672 raw40672Labels = mixedMoment B raw40672step0 raw40672step0Labels := by
      have hz : ∀ j, raw40672 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40672step0 = (fun i j => raw40672 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40672step0 raw40672; decide +kernel
      have hl : raw40672step0Labels = raw40672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40672 raw40672Labels permutation346 hz
    mixedMoment B raw40672step0 raw40672step0Labels = mixedMoment B raw40672step1 raw40672step1Labels := by
      have ha : raw40672step1 = (fun i j => raw40672step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40672step1 raw40672step0; decide +kernel
      have hl : raw40672step1Labels = raw40672step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40672step0 raw40672step0Labels permutation32 permutation3
    _ = mixedMoment B node3961 node3961Labels := by rfl

def raw40673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40673Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40673step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40673step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40673 raw40673Labels = mixedMoment B node3962 node3962Labels := by
  calc
    mixedMoment B raw40673 raw40673Labels = mixedMoment B raw40673step0 raw40673step0Labels := by
      have hz : ∀ j, raw40673 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40673step0 = (fun i j => raw40673 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40673step0 raw40673; decide +kernel
      have hl : raw40673step0Labels = raw40673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40673 raw40673Labels permutation346 hz
    mixedMoment B raw40673step0 raw40673step0Labels = mixedMoment B raw40673step1 raw40673step1Labels := by
      have ha : raw40673step1 = (fun i j => raw40673step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40673step1 raw40673step0; decide +kernel
      have hl : raw40673step1Labels = raw40673step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40673step0 raw40673step0Labels permutation32 permutation3
    _ = mixedMoment B node3962 node3962Labels := by rfl

def raw40674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40674Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40674step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40674step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40674 raw40674Labels = mixedMoment B node3953 node3953Labels := by
  calc
    mixedMoment B raw40674 raw40674Labels = mixedMoment B raw40674step0 raw40674step0Labels := by
      have ha : raw40674step0 = (fun i j => raw40674 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40674step0 raw40674; decide +kernel
      have hl : raw40674step0Labels = raw40674Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40674 raw40674Labels permutation152 permutation3
    _ = mixedMoment B node3953 node3953Labels := by rfl

def raw40675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw40675Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40675step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw40675step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40675 raw40675Labels = mixedMoment B node3956 node3956Labels := by
  calc
    mixedMoment B raw40675 raw40675Labels = mixedMoment B raw40675step0 raw40675step0Labels := by
      have ha : raw40675step0 = (fun i j => raw40675 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40675step0 raw40675; decide +kernel
      have hl : raw40675step0Labels = raw40675Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40675 raw40675Labels permutation152 permutation3
    _ = mixedMoment B node3956 node3956Labels := by rfl

def raw40676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40676Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40676step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40676step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40676 raw40676Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw40676 raw40676Labels = mixedMoment B raw40676step0 raw40676step0Labels := by
      have ha : raw40676step0 = (fun i j => raw40676 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40676step0 raw40676; decide +kernel
      have hl : raw40676step0Labels = raw40676Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40676 raw40676Labels permutation152 permutation3
    _ = mixedMoment B node3957 node3957Labels := by rfl

def raw40677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40677Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw40677step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40677step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw40677step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40677step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40677step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40677step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40677step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40677 raw40677Labels = mixedMoment B node2265 node2265Labels := by
  calc
    mixedMoment B raw40677 raw40677Labels = mixedMoment B raw40677step0 raw40677step0Labels := by
      have hz : ∀ j, raw40677 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40677step0 = (fun i j => raw40677 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40677step0 raw40677; decide +kernel
      have hl : raw40677step0Labels = raw40677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40677 raw40677Labels permutation520 hz
    mixedMoment B raw40677step0 raw40677step0Labels = mixedMoment B raw40677step1 raw40677step1Labels := by
      have hz : ∀ j, raw40677step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40677step1 = (fun i j => raw40677step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40677step1 raw40677step0; decide +kernel
      have hl : raw40677step1Labels = raw40677step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40677step0 raw40677step0Labels permutation104 hz
    mixedMoment B raw40677step1 raw40677step1Labels = mixedMoment B raw40677step2 raw40677step2Labels := by
      have ha : raw40677step2 = (fun i j => raw40677step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40677step2 raw40677step1; decide +kernel
      have hl : raw40677step2Labels = raw40677step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40677step1 raw40677step1Labels permutation31 permutation3
    mixedMoment B raw40677step2 raw40677step2Labels = mixedMoment B raw40677step3 raw40677step3Labels := by
      have ha : raw40677step3 = -raw40677step2 := by apply Matrix.ext; change ∀ i j, raw40677step3 i j = -(raw40677step2 i j); unfold raw40677step3 raw40677step2; decide +kernel
      have hl : raw40677step3Labels = raw40677step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2265 node2265Labels := by rfl

def raw40678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40678Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw40678step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40678step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40678step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40678step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40678 raw40678Labels = mixedMoment B node3808 node3808Labels := by
  calc
    mixedMoment B raw40678 raw40678Labels = mixedMoment B raw40678step0 raw40678step0Labels := by
      have hz : ∀ j, raw40678 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40678step0 = (fun i j => raw40678 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40678step0 raw40678; decide +kernel
      have hl : raw40678step0Labels = raw40678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40678 raw40678Labels permutation434 hz
    mixedMoment B raw40678step0 raw40678step0Labels = mixedMoment B raw40678step1 raw40678step1Labels := by
      have ha : raw40678step1 = (fun i j => raw40678step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40678step1 raw40678step0; decide +kernel
      have hl : raw40678step1Labels = raw40678step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40678step0 raw40678step0Labels permutation151 permutation3
    mixedMoment B raw40678step1 raw40678step1Labels = mixedMoment B raw40678step2 raw40678step2Labels := by
      have ha : raw40678step2 = -raw40678step1 := by apply Matrix.ext; change ∀ i j, raw40678step2 i j = -(raw40678step1 i j); unfold raw40678step2 raw40678step1; decide +kernel
      have hl : raw40678step2Labels = raw40678step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3808 node3808Labels := by rfl

def raw40679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40679Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw40679step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40679step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40679step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40679step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40679step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40679 raw40679Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw40679 raw40679Labels = mixedMoment B raw40679step0 raw40679step0Labels := by
      have hz : ∀ j, raw40679 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40679step0 = (fun i j => raw40679 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40679step0 raw40679; decide +kernel
      have hl : raw40679step0Labels = raw40679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40679 raw40679Labels permutation434 hz
    mixedMoment B raw40679step0 raw40679step0Labels = mixedMoment B raw40679step1 raw40679step1Labels := by
      have ha : raw40679step1 = (fun i j => raw40679step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40679step1 raw40679step0; decide +kernel
      have hl : raw40679step1Labels = raw40679step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40679step0 raw40679step0Labels permutation151 permutation3
    mixedMoment B raw40679step1 raw40679step1Labels = mixedMoment B raw40679step2 raw40679step2Labels := by
      have ha : raw40679step2 = -raw40679step1 := by apply Matrix.ext; change ∀ i j, raw40679step2 i j = -(raw40679step1 i j); unfold raw40679step2 raw40679step1; decide +kernel
      have hl : raw40679step2Labels = raw40679step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw40680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40680Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw40680step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40680step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40680step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40680step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40680 raw40680Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw40680 raw40680Labels = mixedMoment B raw40680step0 raw40680step0Labels := by
      have hz : ∀ j, raw40680 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40680step0 = (fun i j => raw40680 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40680step0 raw40680; decide +kernel
      have hl : raw40680step0Labels = raw40680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40680 raw40680Labels permutation434 hz
    mixedMoment B raw40680step0 raw40680step0Labels = mixedMoment B raw40680step1 raw40680step1Labels := by
      have ha : raw40680step1 = (fun i j => raw40680step0 (permutation104 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40680step1 raw40680step0; decide +kernel
      have hl : raw40680step1Labels = raw40680step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40680step0 raw40680step0Labels permutation104 permutation6
    mixedMoment B raw40680step1 raw40680step1Labels = mixedMoment B raw40680step2 raw40680step2Labels := by
      have ha : raw40680step2 = -raw40680step1 := by apply Matrix.ext; change ∀ i j, raw40680step2 i j = -(raw40680step1 i j); unfold raw40680step2 raw40680step1; decide +kernel
      have hl : raw40680step2Labels = raw40680step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw40681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40681Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40681step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40681step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40681 raw40681Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw40681 raw40681Labels = mixedMoment B raw40681step0 raw40681step0Labels := by
      have ha : raw40681step0 = (fun i j => raw40681 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40681step0 raw40681; decide +kernel
      have hl : raw40681step0Labels = raw40681Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40681 raw40681Labels permutation152 permutation3
    _ = mixedMoment B node3972 node3972Labels := by rfl

def raw40682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40682Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40682step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw40682step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40682step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw40682step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40682 raw40682Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw40682 raw40682Labels = mixedMoment B raw40682step0 raw40682step0Labels := by
      have ha : raw40682step0 = (fun i j => raw40682 (permutation439 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40682step0 raw40682; decide +kernel
      have hl : raw40682step0Labels = raw40682Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40682 raw40682Labels permutation439 permutation6
    mixedMoment B raw40682step0 raw40682step0Labels = mixedMoment B raw40682step1 raw40682step1Labels := by
      have ha : raw40682step1 = -raw40682step0 := by apply Matrix.ext; change ∀ i j, raw40682step1 i j = -(raw40682step0 i j); unfold raw40682step1 raw40682step0; decide +kernel
      have hl : raw40682step1Labels = raw40682step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3880 node3880Labels := by rfl

def raw40683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40683Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40683step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40683step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40683step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40683step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40683 raw40683Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw40683 raw40683Labels = mixedMoment B raw40683step0 raw40683step0Labels := by
      have ha : raw40683step0 = (fun i j => raw40683 (permutation443 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40683step0 raw40683; decide +kernel
      have hl : raw40683step0Labels = raw40683Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40683 raw40683Labels permutation443 permutation6
    mixedMoment B raw40683step0 raw40683step0Labels = mixedMoment B raw40683step1 raw40683step1Labels := by
      have ha : raw40683step1 = -raw40683step0 := by apply Matrix.ext; change ∀ i j, raw40683step1 i j = -(raw40683step0 i j); unfold raw40683step1 raw40683step0; decide +kernel
      have hl : raw40683step1Labels = raw40683step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3872 node3872Labels := by rfl

def raw40684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw40684Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw40684step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40684step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -3, 2], ![2, 1, -3]]
def raw40684step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40684step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw40684step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40684 raw40684Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw40684 raw40684Labels = mixedMoment B raw40684step0 raw40684step0Labels := by
      have hz : ∀ j, raw40684 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40684step0 = (fun i j => raw40684 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40684step0 raw40684; decide +kernel
      have hl : raw40684step0Labels = raw40684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40684 raw40684Labels permutation434 hz
    mixedMoment B raw40684step0 raw40684step0Labels = mixedMoment B raw40684step1 raw40684step1Labels := by
      have hz : ∀ j, raw40684step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40684step1 = (fun i j => raw40684step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40684step1 raw40684step0; decide +kernel
      have hl : raw40684step1Labels = raw40684step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40684step0 raw40684step0Labels permutation80 hz
    mixedMoment B raw40684step1 raw40684step1Labels = mixedMoment B raw40684step2 raw40684step2Labels := by
      have ha : raw40684step2 = (fun i j => raw40684step1 (permutation28 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40684step2 raw40684step1; decide +kernel
      have hl : raw40684step2Labels = raw40684step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40684step1 raw40684step1Labels permutation28 permutation6
    _ = mixedMoment B node3098 node3098Labels := by rfl

def raw40685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40685Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw40685step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40685step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![3, -3, 0]]
def raw40685step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40685step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw40685step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40685step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40685step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40685 raw40685Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw40685 raw40685Labels = mixedMoment B raw40685step0 raw40685step0Labels := by
      have hz : ∀ j, raw40685 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40685step0 = (fun i j => raw40685 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40685step0 raw40685; decide +kernel
      have hl : raw40685step0Labels = raw40685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40685 raw40685Labels permutation520 hz
    mixedMoment B raw40685step0 raw40685step0Labels = mixedMoment B raw40685step1 raw40685step1Labels := by
      have hz : ∀ j, raw40685step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40685step1 = (fun i j => raw40685step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40685step1 raw40685step0; decide +kernel
      have hl : raw40685step1Labels = raw40685step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40685step0 raw40685step0Labels permutation104 hz
    mixedMoment B raw40685step1 raw40685step1Labels = mixedMoment B raw40685step2 raw40685step2Labels := by
      have ha : raw40685step2 = (fun i j => raw40685step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40685step2 raw40685step1; decide +kernel
      have hl : raw40685step2Labels = raw40685step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40685step1 raw40685step1Labels permutation31 permutation3
    mixedMoment B raw40685step2 raw40685step2Labels = mixedMoment B raw40685step3 raw40685step3Labels := by
      have ha : raw40685step3 = -raw40685step2 := by apply Matrix.ext; change ∀ i j, raw40685step3 i j = -(raw40685step2 i j); unfold raw40685step3 raw40685step2; decide +kernel
      have hl : raw40685step3Labels = raw40685step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2278 node2278Labels := by rfl

def raw40686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40686Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![3, -2, -1]]
def raw40686step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw40686step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40686step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40686step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40686 raw40686Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw40686 raw40686Labels = mixedMoment B raw40686step0 raw40686step0Labels := by
      have hz : ∀ j, raw40686 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40686step0 = (fun i j => raw40686 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40686step0 raw40686; decide +kernel
      have hl : raw40686step0Labels = raw40686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40686 raw40686Labels permutation434 hz
    mixedMoment B raw40686step0 raw40686step0Labels = mixedMoment B raw40686step1 raw40686step1Labels := by
      have ha : raw40686step1 = (fun i j => raw40686step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40686step1 raw40686step0; decide +kernel
      have hl : raw40686step1Labels = raw40686step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40686step0 raw40686step0Labels permutation151 permutation3
    mixedMoment B raw40686step1 raw40686step1Labels = mixedMoment B raw40686step2 raw40686step2Labels := by
      have ha : raw40686step2 = -raw40686step1 := by apply Matrix.ext; change ∀ i j, raw40686step2 i j = -(raw40686step1 i j); unfold raw40686step2 raw40686step1; decide +kernel
      have hl : raw40686step2Labels = raw40686step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2731 node2731Labels := by rfl

def raw40687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40687Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![3, -1, -2]]
def raw40687step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw40687step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40687step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40687step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40687 raw40687Labels = mixedMoment B node3044 node3044Labels := by
  calc
    mixedMoment B raw40687 raw40687Labels = mixedMoment B raw40687step0 raw40687step0Labels := by
      have hz : ∀ j, raw40687 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40687step0 = (fun i j => raw40687 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40687step0 raw40687; decide +kernel
      have hl : raw40687step0Labels = raw40687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40687 raw40687Labels permutation434 hz
    mixedMoment B raw40687step0 raw40687step0Labels = mixedMoment B raw40687step1 raw40687step1Labels := by
      have ha : raw40687step1 = (fun i j => raw40687step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40687step1 raw40687step0; decide +kernel
      have hl : raw40687step1Labels = raw40687step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40687step0 raw40687step0Labels permutation151 permutation3
    mixedMoment B raw40687step1 raw40687step1Labels = mixedMoment B raw40687step2 raw40687step2Labels := by
      have ha : raw40687step2 = -raw40687step1 := by apply Matrix.ext; change ∀ i j, raw40687step2 i j = -(raw40687step1 i j); unfold raw40687step2 raw40687step1; decide +kernel
      have hl : raw40687step2Labels = raw40687step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3044 node3044Labels := by rfl

def raw40688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40688Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw40688step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw40688step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40688step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40688step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40688 raw40688Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw40688 raw40688Labels = mixedMoment B raw40688step0 raw40688step0Labels := by
      have hz : ∀ j, raw40688 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40688step0 = (fun i j => raw40688 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40688step0 raw40688; decide +kernel
      have hl : raw40688step0Labels = raw40688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40688 raw40688Labels permutation434 hz
    mixedMoment B raw40688step0 raw40688step0Labels = mixedMoment B raw40688step1 raw40688step1Labels := by
      have ha : raw40688step1 = (fun i j => raw40688step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40688step1 raw40688step0; decide +kernel
      have hl : raw40688step1Labels = raw40688step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40688step0 raw40688step0Labels permutation151 permutation3
    mixedMoment B raw40688step1 raw40688step1Labels = mixedMoment B raw40688step2 raw40688step2Labels := by
      have ha : raw40688step2 = -raw40688step1 := by apply Matrix.ext; change ∀ i j, raw40688step2 i j = -(raw40688step1 i j); unfold raw40688step2 raw40688step1; decide +kernel
      have hl : raw40688step2Labels = raw40688step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3813 node3813Labels := by rfl

def raw40689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40689Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw40689step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw40689step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40689 raw40689Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw40689 raw40689Labels = mixedMoment B raw40689step0 raw40689step0Labels := by
      have hz : ∀ j, raw40689 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40689step0 = (fun i j => raw40689 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40689step0 raw40689; decide +kernel
      have hl : raw40689step0Labels = raw40689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40689 raw40689Labels permutation434 hz
    mixedMoment B raw40689step0 raw40689step0Labels = mixedMoment B raw40689step1 raw40689step1Labels := by
      have ha : raw40689step1 = (fun i j => raw40689step0 (permutation98 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40689step1 raw40689step0; decide +kernel
      have hl : raw40689step1Labels = raw40689step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40689step0 raw40689step0Labels permutation98 permutation6
    _ = mixedMoment B node3884 node3884Labels := by rfl

def raw40690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40690Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw40690step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40690step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40690step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40690step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40690 raw40690Labels = mixedMoment B node3506 node3506Labels := by
  calc
    mixedMoment B raw40690 raw40690Labels = mixedMoment B raw40690step0 raw40690step0Labels := by
      have hz : ∀ j, raw40690 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40690step0 = (fun i j => raw40690 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40690step0 raw40690; decide +kernel
      have hl : raw40690step0Labels = raw40690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40690 raw40690Labels permutation434 hz
    mixedMoment B raw40690step0 raw40690step0Labels = mixedMoment B raw40690step1 raw40690step1Labels := by
      have ha : raw40690step1 = (fun i j => raw40690step0 (permutation111 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40690step1 raw40690step0; decide +kernel
      have hl : raw40690step1Labels = raw40690step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40690step0 raw40690step0Labels permutation111 permutation6
    mixedMoment B raw40690step1 raw40690step1Labels = mixedMoment B raw40690step2 raw40690step2Labels := by
      have ha : raw40690step2 = -raw40690step1 := by apply Matrix.ext; change ∀ i j, raw40690step2 i j = -(raw40690step1 i j); unfold raw40690step2 raw40690step1; decide +kernel
      have hl : raw40690step2Labels = raw40690step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3506 node3506Labels := by rfl

def raw40691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40691Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40691step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw40691step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40691step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40691step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40691 raw40691Labels = mixedMoment B node3068 node3068Labels := by
  calc
    mixedMoment B raw40691 raw40691Labels = mixedMoment B raw40691step0 raw40691step0Labels := by
      have ha : raw40691step0 = (fun i j => raw40691 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40691step0 raw40691; decide +kernel
      have hl : raw40691step0Labels = raw40691Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40691 raw40691Labels permutation664 permutation3
    mixedMoment B raw40691step0 raw40691step0Labels = mixedMoment B raw40691step1 raw40691step1Labels := by
      have ha : raw40691step1 = -raw40691step0 := by apply Matrix.ext; change ∀ i j, raw40691step1 i j = -(raw40691step0 i j); unfold raw40691step1 raw40691step0; decide +kernel
      have hl : raw40691step1Labels = raw40691step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3068 node3068Labels := by rfl

def raw40692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40692Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40692step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw40692step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40692step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40692step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40692 raw40692Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw40692 raw40692Labels = mixedMoment B raw40692step0 raw40692step0Labels := by
      have ha : raw40692step0 = (fun i j => raw40692 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40692step0 raw40692; decide +kernel
      have hl : raw40692step0Labels = raw40692Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40692 raw40692Labels permutation688 permutation3
    mixedMoment B raw40692step0 raw40692step0Labels = mixedMoment B raw40692step1 raw40692step1Labels := by
      have ha : raw40692step1 = -raw40692step0 := by apply Matrix.ext; change ∀ i j, raw40692step1 i j = -(raw40692step0 i j); unfold raw40692step1 raw40692step0; decide +kernel
      have hl : raw40692step1Labels = raw40692step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3840 node3840Labels := by rfl

def raw40693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40693Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40693step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw40693step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40693 raw40693Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw40693 raw40693Labels = mixedMoment B raw40693step0 raw40693step0Labels := by
      have ha : raw40693step0 = (fun i j => raw40693 (permutation428 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40693step0 raw40693; decide +kernel
      have hl : raw40693step0Labels = raw40693Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40693 raw40693Labels permutation428 permutation6
    _ = mixedMoment B node3880 node3880Labels := by rfl

def raw40694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40694Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40694step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40694step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40694 raw40694Labels = mixedMoment B node3730 node3730Labels := by
  calc
    mixedMoment B raw40694 raw40694Labels = mixedMoment B raw40694step0 raw40694step0Labels := by
      have ha : raw40694step0 = (fun i j => raw40694 (permutation414 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40694step0 raw40694; decide +kernel
      have hl : raw40694step0Labels = raw40694Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40694 raw40694Labels permutation414 permutation6
    _ = mixedMoment B node3730 node3730Labels := by rfl

def raw40695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40695Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40695step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40695step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40695 raw40695Labels = mixedMoment B node3826 node3826Labels := by
  calc
    mixedMoment B raw40695 raw40695Labels = mixedMoment B raw40695step0 raw40695step0Labels := by
      have ha : raw40695step0 = (fun i j => raw40695 (permutation409 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40695step0 raw40695; decide +kernel
      have hl : raw40695step0Labels = raw40695Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40695 raw40695Labels permutation409 permutation6
    _ = mixedMoment B node3826 node3826Labels := by rfl

def raw40696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40696Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40696step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40696 raw40696Labels = mixedMoment B node3723 node3723Labels := by
  calc
    mixedMoment B raw40696 raw40696Labels = mixedMoment B raw40696step0 raw40696step0Labels := by
      have ha : raw40696step0 = (fun i j => raw40696 (permutation428 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40696step0 raw40696; decide +kernel
      have hl : raw40696step0Labels = raw40696Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40696 raw40696Labels permutation428 permutation6
    _ = mixedMoment B node3723 node3723Labels := by rfl

def raw40697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40697Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40697step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw40697step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40697 raw40697Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw40697 raw40697Labels = mixedMoment B raw40697step0 raw40697step0Labels := by
      have ha : raw40697step0 = (fun i j => raw40697 (permutation389 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40697step0 raw40697; decide +kernel
      have hl : raw40697step0Labels = raw40697Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40697 raw40697Labels permutation389 permutation6
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw40698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw40698Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40698step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw40698step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40698 raw40698Labels = mixedMoment B node3909 node3909Labels := by
  calc
    mixedMoment B raw40698 raw40698Labels = mixedMoment B raw40698step0 raw40698step0Labels := by
      have ha : raw40698step0 = (fun i j => raw40698 (permutation393 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40698step0 raw40698; decide +kernel
      have hl : raw40698step0Labels = raw40698Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40698 raw40698Labels permutation393 permutation6
    _ = mixedMoment B node3909 node3909Labels := by rfl

def raw40699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw40699Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40699step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw40699step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40699step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40699 raw40699Labels = mixedMoment B node2709 node2709Labels := by
  calc
    mixedMoment B raw40699 raw40699Labels = mixedMoment B raw40699step0 raw40699step0Labels := by
      have ha : raw40699step0 = (fun i j => raw40699 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40699step0 raw40699; decide +kernel
      have hl : raw40699step0Labels = raw40699Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40699 raw40699Labels permutation682 permutation3
    mixedMoment B raw40699step0 raw40699step0Labels = mixedMoment B raw40699step1 raw40699step1Labels := by
      have ha : raw40699step1 = -raw40699step0 := by apply Matrix.ext; change ∀ i j, raw40699step1 i j = -(raw40699step0 i j); unfold raw40699step1 raw40699step0; decide +kernel
      have hl : raw40699step1Labels = raw40699step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2709 node2709Labels := by rfl

def raw40700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![3, -1, -2]]
def raw40700Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40700step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw40700step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40700step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40700step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40700 raw40700Labels = mixedMoment B node3029 node3029Labels := by
  calc
    mixedMoment B raw40700 raw40700Labels = mixedMoment B raw40700step0 raw40700step0Labels := by
      have ha : raw40700step0 = (fun i j => raw40700 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40700step0 raw40700; decide +kernel
      have hl : raw40700step0Labels = raw40700Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40700 raw40700Labels permutation682 permutation3
    mixedMoment B raw40700step0 raw40700step0Labels = mixedMoment B raw40700step1 raw40700step1Labels := by
      have ha : raw40700step1 = -raw40700step0 := by apply Matrix.ext; change ∀ i j, raw40700step1 i j = -(raw40700step0 i j); unfold raw40700step1 raw40700step0; decide +kernel
      have hl : raw40700step1Labels = raw40700step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3029 node3029Labels := by rfl

def raw40701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw40701Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40701step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw40701step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40701step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40701step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40701 raw40701Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw40701 raw40701Labels = mixedMoment B raw40701step0 raw40701step0Labels := by
      have ha : raw40701step0 = (fun i j => raw40701 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40701step0 raw40701; decide +kernel
      have hl : raw40701step0Labels = raw40701Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40701 raw40701Labels permutation682 permutation3
    mixedMoment B raw40701step0 raw40701step0Labels = mixedMoment B raw40701step1 raw40701step1Labels := by
      have ha : raw40701step1 = -raw40701step0 := by apply Matrix.ext; change ∀ i j, raw40701step1 i j = -(raw40701step0 i j); unfold raw40701step1 raw40701step0; decide +kernel
      have hl : raw40701step1Labels = raw40701step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3800 node3800Labels := by rfl

def raw40702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw40702Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40702step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw40702step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40702step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40702step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40702 raw40702Labels = mixedMoment B node3953 node3953Labels := by
  calc
    mixedMoment B raw40702 raw40702Labels = mixedMoment B raw40702step0 raw40702step0Labels := by
      have ha : raw40702step0 = (fun i j => raw40702 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40702step0 raw40702; decide +kernel
      have hl : raw40702step0Labels = raw40702Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40702 raw40702Labels permutation682 permutation3
    mixedMoment B raw40702step0 raw40702step0Labels = mixedMoment B raw40702step1 raw40702step1Labels := by
      have ha : raw40702step1 = -raw40702step0 := by apply Matrix.ext; change ∀ i j, raw40702step1 i j = -(raw40702step0 i j); unfold raw40702step1 raw40702step0; decide +kernel
      have hl : raw40702step1Labels = raw40702step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3953 node3953Labels := by rfl

def raw40703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw40703Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40703step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40703step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40703step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40703step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40703 raw40703Labels = mixedMoment B node3505 node3505Labels := by
  calc
    mixedMoment B raw40703 raw40703Labels = mixedMoment B raw40703step0 raw40703step0Labels := by
      have ha : raw40703step0 = (fun i j => raw40703 (permutation529 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40703step0 raw40703; decide +kernel
      have hl : raw40703step0Labels = raw40703Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40703 raw40703Labels permutation529 permutation6
    mixedMoment B raw40703step0 raw40703step0Labels = mixedMoment B raw40703step1 raw40703step1Labels := by
      have ha : raw40703step1 = -raw40703step0 := by apply Matrix.ext; change ∀ i j, raw40703step1 i j = -(raw40703step0 i j); unfold raw40703step1 raw40703step0; decide +kernel
      have hl : raw40703step1Labels = raw40703step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3505 node3505Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
