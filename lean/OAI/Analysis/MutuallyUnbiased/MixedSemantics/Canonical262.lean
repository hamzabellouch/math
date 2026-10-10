import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw33536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33536Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33536step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33536 raw33536Labels = mixedMoment B node736 node736Labels := by
  calc
    mixedMoment B raw33536 raw33536Labels = mixedMoment B raw33536step0 raw33536step0Labels := by
      have ha : raw33536step0 = (fun i j => raw33536 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33536step0 raw33536; decide +kernel
      have hl : raw33536step0Labels = raw33536Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33536 raw33536Labels permutation152 permutation3
    _ = mixedMoment B node736 node736Labels := by rfl

def raw33537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33537Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33537step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33537 raw33537Labels = mixedMoment B node1811 node1811Labels := by
  calc
    mixedMoment B raw33537 raw33537Labels = mixedMoment B raw33537step0 raw33537step0Labels := by
      have ha : raw33537step0 = (fun i j => raw33537 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33537step0 raw33537; decide +kernel
      have hl : raw33537step0Labels = raw33537Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33537 raw33537Labels permutation152 permutation3
    _ = mixedMoment B node1811 node1811Labels := by rfl

def raw33538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33538Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33538step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33538step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33538step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33538 raw33538Labels = mixedMoment B node2110 node2110Labels := by
  calc
    mixedMoment B raw33538 raw33538Labels = mixedMoment B raw33538step0 raw33538step0Labels := by
      have hz : ∀ j, raw33538 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33538step0 = (fun i j => raw33538 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33538step0 raw33538; decide +kernel
      have hl : raw33538step0Labels = raw33538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33538 raw33538Labels permutation520 hz
    mixedMoment B raw33538step0 raw33538step0Labels = mixedMoment B raw33538step1 raw33538step1Labels := by
      have ha : raw33538step1 = (fun i j => raw33538step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33538step1 raw33538step0; decide +kernel
      have hl : raw33538step1Labels = raw33538step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33538step0 raw33538step0Labels permutation32 permutation3
    _ = mixedMoment B node2110 node2110Labels := by rfl

def raw33539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33539Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw33539step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33539 raw33539Labels = mixedMoment B node2100 node2100Labels := by
  calc
    mixedMoment B raw33539 raw33539Labels = mixedMoment B raw33539step0 raw33539step0Labels := by
      have ha : raw33539step0 = (fun i j => raw33539 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33539step0 raw33539; decide +kernel
      have hl : raw33539step0Labels = raw33539Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33539 raw33539Labels permutation170 permutation3
    _ = mixedMoment B node2100 node2100Labels := by rfl

def raw33540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33540Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33540step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33540step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33540step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33540 raw33540Labels = mixedMoment B node738 node738Labels := by
  calc
    mixedMoment B raw33540 raw33540Labels = mixedMoment B raw33540step0 raw33540step0Labels := by
      have hz : ∀ j, raw33540 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33540step0 = (fun i j => raw33540 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33540step0 raw33540; decide +kernel
      have hl : raw33540step0Labels = raw33540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33540 raw33540Labels permutation346 hz
    mixedMoment B raw33540step0 raw33540step0Labels = mixedMoment B raw33540step1 raw33540step1Labels := by
      have ha : raw33540step1 = (fun i j => raw33540step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33540step1 raw33540step0; decide +kernel
      have hl : raw33540step1Labels = raw33540step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33540step0 raw33540step0Labels permutation35 permutation3
    _ = mixedMoment B node738 node738Labels := by rfl

def raw33541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33541Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33541step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33541step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33541 raw33541Labels = mixedMoment B node1814 node1814Labels := by
  calc
    mixedMoment B raw33541 raw33541Labels = mixedMoment B raw33541step0 raw33541step0Labels := by
      have hz : ∀ j, raw33541 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33541step0 = (fun i j => raw33541 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33541step0 raw33541; decide +kernel
      have hl : raw33541step0Labels = raw33541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33541 raw33541Labels permutation346 hz
    mixedMoment B raw33541step0 raw33541step0Labels = mixedMoment B raw33541step1 raw33541step1Labels := by
      have ha : raw33541step1 = (fun i j => raw33541step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33541step1 raw33541step0; decide +kernel
      have hl : raw33541step1Labels = raw33541step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33541step0 raw33541step0Labels permutation35 permutation3
    _ = mixedMoment B node1814 node1814Labels := by rfl

def raw33542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33542Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33542step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33542step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33542 raw33542Labels = mixedMoment B node1878 node1878Labels := by
  calc
    mixedMoment B raw33542 raw33542Labels = mixedMoment B raw33542step0 raw33542step0Labels := by
      have ha : raw33542step0 = (fun i j => raw33542 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33542step0 raw33542; decide +kernel
      have hl : raw33542step0Labels = raw33542Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33542 raw33542Labels permutation179 permutation3
    _ = mixedMoment B node1878 node1878Labels := by rfl

def raw33543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33543Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33543step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33543step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw33543step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33543step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33543step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33543 raw33543Labels = mixedMoment B node2115 node2115Labels := by
  calc
    mixedMoment B raw33543 raw33543Labels = mixedMoment B raw33543step0 raw33543step0Labels := by
      have hz : ∀ j, raw33543 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33543step0 = (fun i j => raw33543 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33543step0 raw33543; decide +kernel
      have hl : raw33543step0Labels = raw33543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33543 raw33543Labels permutation520 hz
    mixedMoment B raw33543step0 raw33543step0Labels = mixedMoment B raw33543step1 raw33543step1Labels := by
      have hz : ∀ j, raw33543step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33543step1 = (fun i j => raw33543step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33543step1 raw33543step0; decide +kernel
      have hl : raw33543step1Labels = raw33543step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33543step0 raw33543step0Labels permutation80 hz
    mixedMoment B raw33543step1 raw33543step1Labels = mixedMoment B raw33543step2 raw33543step2Labels := by
      have ha : raw33543step2 = (fun i j => raw33543step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33543step2 raw33543step1; decide +kernel
      have hl : raw33543step2Labels = raw33543step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33543step1 raw33543step1Labels permutation9 permutation3
    _ = mixedMoment B node2115 node2115Labels := by rfl

def raw33544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33544Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33544step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33544step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33544step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33544 raw33544Labels = mixedMoment B node2101 node2101Labels := by
  calc
    mixedMoment B raw33544 raw33544Labels = mixedMoment B raw33544step0 raw33544step0Labels := by
      have hz : ∀ j, raw33544 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33544step0 = (fun i j => raw33544 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33544step0 raw33544; decide +kernel
      have hl : raw33544step0Labels = raw33544Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33544 raw33544Labels permutation346 hz
    mixedMoment B raw33544step0 raw33544step0Labels = mixedMoment B raw33544step1 raw33544step1Labels := by
      have ha : raw33544step1 = (fun i j => raw33544step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33544step1 raw33544step0; decide +kernel
      have hl : raw33544step1Labels = raw33544step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33544step0 raw33544step0Labels permutation37 permutation3
    _ = mixedMoment B node2101 node2101Labels := by rfl

def raw33545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33545Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33545step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33545step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw33545step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33545step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33545step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33545 raw33545Labels = mixedMoment B node2115 node2115Labels := by
  calc
    mixedMoment B raw33545 raw33545Labels = mixedMoment B raw33545step0 raw33545step0Labels := by
      have hz : ∀ j, raw33545 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33545step0 = (fun i j => raw33545 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33545step0 raw33545; decide +kernel
      have hl : raw33545step0Labels = raw33545Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33545 raw33545Labels permutation434 hz
    mixedMoment B raw33545step0 raw33545step0Labels = mixedMoment B raw33545step1 raw33545step1Labels := by
      have hz : ∀ j, raw33545step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33545step1 = (fun i j => raw33545step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33545step1 raw33545step0; decide +kernel
      have hl : raw33545step1Labels = raw33545step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33545step0 raw33545step0Labels permutation80 hz
    mixedMoment B raw33545step1 raw33545step1Labels = mixedMoment B raw33545step2 raw33545step2Labels := by
      have ha : raw33545step2 = (fun i j => raw33545step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33545step2 raw33545step1; decide +kernel
      have hl : raw33545step2Labels = raw33545step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33545step1 raw33545step1Labels permutation9 permutation3
    _ = mixedMoment B node2115 node2115Labels := by rfl

def raw33546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33546Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33546step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33546step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33546step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33546 raw33546Labels = mixedMoment B node737 node737Labels := by
  calc
    mixedMoment B raw33546 raw33546Labels = mixedMoment B raw33546step0 raw33546step0Labels := by
      have hz : ∀ j, raw33546 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33546step0 = (fun i j => raw33546 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33546step0 raw33546; decide +kernel
      have hl : raw33546step0Labels = raw33546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33546 raw33546Labels permutation346 hz
    mixedMoment B raw33546step0 raw33546step0Labels = mixedMoment B raw33546step1 raw33546step1Labels := by
      have ha : raw33546step1 = (fun i j => raw33546step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33546step1 raw33546step0; decide +kernel
      have hl : raw33546step1Labels = raw33546step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33546step0 raw33546step0Labels permutation32 permutation3
    _ = mixedMoment B node737 node737Labels := by rfl

def raw33547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33547Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33547step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33547step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33547step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33547 raw33547Labels = mixedMoment B node1812 node1812Labels := by
  calc
    mixedMoment B raw33547 raw33547Labels = mixedMoment B raw33547step0 raw33547step0Labels := by
      have hz : ∀ j, raw33547 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33547step0 = (fun i j => raw33547 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33547step0 raw33547; decide +kernel
      have hl : raw33547step0Labels = raw33547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33547 raw33547Labels permutation346 hz
    mixedMoment B raw33547step0 raw33547step0Labels = mixedMoment B raw33547step1 raw33547step1Labels := by
      have ha : raw33547step1 = (fun i j => raw33547step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33547step1 raw33547step0; decide +kernel
      have hl : raw33547step1Labels = raw33547step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33547step0 raw33547step0Labels permutation32 permutation3
    _ = mixedMoment B node1812 node1812Labels := by rfl

def raw33548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33548Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33548step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33548 raw33548Labels = mixedMoment B node1877 node1877Labels := by
  calc
    mixedMoment B raw33548 raw33548Labels = mixedMoment B raw33548step0 raw33548step0Labels := by
      have ha : raw33548step0 = (fun i j => raw33548 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33548step0 raw33548; decide +kernel
      have hl : raw33548step0Labels = raw33548Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33548 raw33548Labels permutation176 permutation3
    _ = mixedMoment B node1877 node1877Labels := by rfl

def raw33549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw33549Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33549step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33549step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![3, -1, -2]]
def raw33549step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33549step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33549step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33549 raw33549Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw33549 raw33549Labels = mixedMoment B raw33549step0 raw33549step0Labels := by
      have hz : ∀ j, raw33549 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33549step0 = (fun i j => raw33549 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33549step0 raw33549; decide +kernel
      have hl : raw33549step0Labels = raw33549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33549 raw33549Labels permutation520 hz
    mixedMoment B raw33549step0 raw33549step0Labels = mixedMoment B raw33549step1 raw33549step1Labels := by
      have hz : ∀ j, raw33549step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33549step1 = (fun i j => raw33549step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33549step1 raw33549step0; decide +kernel
      have hl : raw33549step1Labels = raw33549step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33549step0 raw33549step0Labels permutation80 hz
    mixedMoment B raw33549step1 raw33549step1Labels = mixedMoment B raw33549step2 raw33549step2Labels := by
      have ha : raw33549step2 = (fun i j => raw33549step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33549step2 raw33549step1; decide +kernel
      have hl : raw33549step2Labels = raw33549step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33549step1 raw33549step1Labels permutation8 permutation3
    _ = mixedMoment B node2112 node2112Labels := by rfl

def raw33550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw33550Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw33550step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33550step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw33550step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33550step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw33550step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33550step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw33550step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33550 raw33550Labels = mixedMoment B node4477 node4477Labels := by
  calc
    mixedMoment B raw33550 raw33550Labels = mixedMoment B raw33550step0 raw33550step0Labels := by
      have hz : ∀ j, raw33550 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33550step0 = (fun i j => raw33550 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33550step0 raw33550; decide +kernel
      have hl : raw33550step0Labels = raw33550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33550 raw33550Labels permutation346 hz
    mixedMoment B raw33550step0 raw33550step0Labels = mixedMoment B raw33550step1 raw33550step1Labels := by
      have ha : raw33550step1 = (fun i j => raw33550step0 (permutation53 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33550step1 raw33550step0; decide +kernel
      have hl : raw33550step1Labels = raw33550step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33550step0 raw33550step0Labels permutation53 permutation4
    mixedMoment B raw33550step1 raw33550step1Labels = mixedMoment B raw33550step2 raw33550step2Labels := by
      have ha : raw33550step2 = -raw33550step1 := by apply Matrix.ext; change ∀ i j, raw33550step2 i j = -(raw33550step1 i j); unfold raw33550step2 raw33550step1; decide +kernel
      have hl : raw33550step2Labels = raw33550step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33550step2 raw33550step2Labels = mixedMoment B raw33550step3 raw33550step3Labels := by
      have ha : raw33550step3 = raw33550step2 := by apply Matrix.ext; unfold raw33550step3 raw33550step2; decide +kernel
      have hl : raw33550step2Labels = labelEmbedding7 ∘ raw33550step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33550step2 raw33550step2Labels raw33550step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4477 node4477Labels := by rfl

def raw33551 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw33551Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw33551step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33551step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw33551step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33551step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw33551step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33551 raw33551Labels = mixedMoment B node4818 node4818Labels := by
  calc
    mixedMoment B raw33551 raw33551Labels = mixedMoment B raw33551step0 raw33551step0Labels := by
      have ha : raw33551step0 = (fun i j => raw33551 (permutation197 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33551step0 raw33551; decide +kernel
      have hl : raw33551step0Labels = raw33551Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33551 raw33551Labels permutation197 permutation4
    mixedMoment B raw33551step0 raw33551step0Labels = mixedMoment B raw33551step1 raw33551step1Labels := by
      have ha : raw33551step1 = -raw33551step0 := by apply Matrix.ext; change ∀ i j, raw33551step1 i j = -(raw33551step0 i j); unfold raw33551step1 raw33551step0; decide +kernel
      have hl : raw33551step1Labels = raw33551step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33551step1 raw33551step1Labels = mixedMoment B raw33551step2 raw33551step2Labels := by
      have ha : raw33551step2 = raw33551step1 := by apply Matrix.ext; unfold raw33551step2 raw33551step1; decide +kernel
      have hl : raw33551step1Labels = labelEmbedding7 ∘ raw33551step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33551step1 raw33551step1Labels raw33551step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4818 node4818Labels := by rfl

def raw33552 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw33552Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw33552step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33552step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw33552step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33552step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw33552step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33552 raw33552Labels = mixedMoment B node4880 node4880Labels := by
  calc
    mixedMoment B raw33552 raw33552Labels = mixedMoment B raw33552step0 raw33552step0Labels := by
      have hz : ∀ j, raw33552 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33552step0 = (fun i j => raw33552 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33552step0 raw33552; decide +kernel
      have hl : raw33552step0Labels = raw33552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33552 raw33552Labels permutation346 hz
    mixedMoment B raw33552step0 raw33552step0Labels = mixedMoment B raw33552step1 raw33552step1Labels := by
      have ha : raw33552step1 = (fun i j => raw33552step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33552step1 raw33552step0; decide +kernel
      have hl : raw33552step1Labels = raw33552step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33552step0 raw33552step0Labels permutation32 permutation6
    mixedMoment B raw33552step1 raw33552step1Labels = mixedMoment B raw33552step2 raw33552step2Labels := by
      have ha : raw33552step2 = raw33552step1 := by apply Matrix.ext; unfold raw33552step2 raw33552step1; decide +kernel
      have hl : raw33552step1Labels = labelEmbedding9 ∘ raw33552step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33552step1 raw33552step1Labels raw33552step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4880 node4880Labels := by rfl

def raw33553 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33553Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33553step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw33553step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33553step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw33553step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33553 raw33553Labels = mixedMoment B node4880 node4880Labels := by
  calc
    mixedMoment B raw33553 raw33553Labels = mixedMoment B raw33553step0 raw33553step0Labels := by
      have hz : ∀ j, raw33553 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33553step0 = (fun i j => raw33553 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33553step0 raw33553; decide +kernel
      have hl : raw33553step0Labels = raw33553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33553 raw33553Labels permutation346 hz
    mixedMoment B raw33553step0 raw33553step0Labels = mixedMoment B raw33553step1 raw33553step1Labels := by
      have ha : raw33553step1 = (fun i j => raw33553step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33553step1 raw33553step0; decide +kernel
      have hl : raw33553step1Labels = raw33553step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33553step0 raw33553step0Labels permutation34 permutation6
    mixedMoment B raw33553step1 raw33553step1Labels = mixedMoment B raw33553step2 raw33553step2Labels := by
      have ha : raw33553step2 = raw33553step1 := by apply Matrix.ext; unfold raw33553step2 raw33553step1; decide +kernel
      have hl : raw33553step1Labels = labelEmbedding9 ∘ raw33553step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33553step1 raw33553step1Labels raw33553step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4880 node4880Labels := by rfl

def raw33554 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw33554Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw33554step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33554step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw33554step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33554step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw33554step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33554step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw33554step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33554 raw33554Labels = mixedMoment B node4882 node4882Labels := by
  calc
    mixedMoment B raw33554 raw33554Labels = mixedMoment B raw33554step0 raw33554step0Labels := by
      have hz : ∀ j, raw33554 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33554step0 = (fun i j => raw33554 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33554step0 raw33554; decide +kernel
      have hl : raw33554step0Labels = raw33554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33554 raw33554Labels permutation346 hz
    mixedMoment B raw33554step0 raw33554step0Labels = mixedMoment B raw33554step1 raw33554step1Labels := by
      have ha : raw33554step1 = (fun i j => raw33554step0 (permutation53 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33554step1 raw33554step0; decide +kernel
      have hl : raw33554step1Labels = raw33554step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33554step0 raw33554step0Labels permutation53 permutation4
    mixedMoment B raw33554step1 raw33554step1Labels = mixedMoment B raw33554step2 raw33554step2Labels := by
      have ha : raw33554step2 = -raw33554step1 := by apply Matrix.ext; change ∀ i j, raw33554step2 i j = -(raw33554step1 i j); unfold raw33554step2 raw33554step1; decide +kernel
      have hl : raw33554step2Labels = raw33554step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33554step2 raw33554step2Labels = mixedMoment B raw33554step3 raw33554step3Labels := by
      have ha : raw33554step3 = raw33554step2 := by apply Matrix.ext; unfold raw33554step3 raw33554step2; decide +kernel
      have hl : raw33554step2Labels = labelEmbedding7 ∘ raw33554step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33554step2 raw33554step2Labels raw33554step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4882 node4882Labels := by rfl

def raw33555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw33555Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33555step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33555step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33555step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33555step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33555step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33555 raw33555Labels = mixedMoment B node4469 node4469Labels := by
  calc
    mixedMoment B raw33555 raw33555Labels = mixedMoment B raw33555step0 raw33555step0Labels := by
      have ha : raw33555step0 = (fun i j => raw33555 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33555step0 raw33555; decide +kernel
      have hl : raw33555step0Labels = raw33555Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33555 raw33555Labels permutation246 permutation4
    mixedMoment B raw33555step0 raw33555step0Labels = mixedMoment B raw33555step1 raw33555step1Labels := by
      have ha : raw33555step1 = -raw33555step0 := by apply Matrix.ext; change ∀ i j, raw33555step1 i j = -(raw33555step0 i j); unfold raw33555step1 raw33555step0; decide +kernel
      have hl : raw33555step1Labels = raw33555step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33555step1 raw33555step1Labels = mixedMoment B raw33555step2 raw33555step2Labels := by
      have ha : raw33555step2 = raw33555step1 := by apply Matrix.ext; unfold raw33555step2 raw33555step1; decide +kernel
      have hl : raw33555step1Labels = labelEmbedding7 ∘ raw33555step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33555step1 raw33555step1Labels raw33555step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4469 node4469Labels := by rfl

def raw33556 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33556Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33556step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw33556step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33556step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw33556step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33556 raw33556Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw33556 raw33556Labels = mixedMoment B raw33556step0 raw33556step0Labels := by
      have ha : raw33556step0 = (fun i j => raw33556 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33556step0 raw33556; decide +kernel
      have hl : raw33556step0Labels = raw33556Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33556 raw33556Labels permutation154 permutation6
    mixedMoment B raw33556step0 raw33556step0Labels = mixedMoment B raw33556step1 raw33556step1Labels := by
      have ha : raw33556step1 = raw33556step0 := by apply Matrix.ext; unfold raw33556step1 raw33556step0; decide +kernel
      have hl : raw33556step0Labels = labelEmbedding9 ∘ raw33556step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33556step0 raw33556step0Labels raw33556step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4852 node4852Labels := by rfl

def raw33557 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw33557Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33557step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw33557step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33557step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw33557step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33557 raw33557Labels = mixedMoment B node4854 node4854Labels := by
  calc
    mixedMoment B raw33557 raw33557Labels = mixedMoment B raw33557step0 raw33557step0Labels := by
      have ha : raw33557step0 = (fun i j => raw33557 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33557step0 raw33557; decide +kernel
      have hl : raw33557step0Labels = raw33557Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33557 raw33557Labels permutation152 permutation6
    mixedMoment B raw33557step0 raw33557step0Labels = mixedMoment B raw33557step1 raw33557step1Labels := by
      have ha : raw33557step1 = raw33557step0 := by apply Matrix.ext; unfold raw33557step1 raw33557step0; decide +kernel
      have hl : raw33557step0Labels = labelEmbedding9 ∘ raw33557step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33557step0 raw33557step0Labels raw33557step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4854 node4854Labels := by rfl

def raw33558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw33558Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw33558step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33558step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw33558step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33558step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33558step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33558step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33558step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33558 raw33558Labels = mixedMoment B node4471 node4471Labels := by
  calc
    mixedMoment B raw33558 raw33558Labels = mixedMoment B raw33558step0 raw33558step0Labels := by
      have hz : ∀ j, raw33558 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33558step0 = (fun i j => raw33558 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33558step0 raw33558; decide +kernel
      have hl : raw33558step0Labels = raw33558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33558 raw33558Labels permutation346 hz
    mixedMoment B raw33558step0 raw33558step0Labels = mixedMoment B raw33558step1 raw33558step1Labels := by
      have ha : raw33558step1 = (fun i j => raw33558step0 (permutation51 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33558step1 raw33558step0; decide +kernel
      have hl : raw33558step1Labels = raw33558step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33558step0 raw33558step0Labels permutation51 permutation4
    mixedMoment B raw33558step1 raw33558step1Labels = mixedMoment B raw33558step2 raw33558step2Labels := by
      have ha : raw33558step2 = -raw33558step1 := by apply Matrix.ext; change ∀ i j, raw33558step2 i j = -(raw33558step1 i j); unfold raw33558step2 raw33558step1; decide +kernel
      have hl : raw33558step2Labels = raw33558step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33558step2 raw33558step2Labels = mixedMoment B raw33558step3 raw33558step3Labels := by
      have ha : raw33558step3 = raw33558step2 := by apply Matrix.ext; unfold raw33558step3 raw33558step2; decide +kernel
      have hl : raw33558step2Labels = labelEmbedding7 ∘ raw33558step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33558step2 raw33558step2Labels raw33558step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4471 node4471Labels := by rfl

def raw33559 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw33559Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33559step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw33559step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33559step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33559step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33559step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33559step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33559 raw33559Labels = mixedMoment B node4813 node4813Labels := by
  calc
    mixedMoment B raw33559 raw33559Labels = mixedMoment B raw33559step0 raw33559step0Labels := by
      have ha : raw33559step0 = (fun i j => raw33559 (permutation195 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33559step0 raw33559; decide +kernel
      have hl : raw33559step0Labels = raw33559Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33559 raw33559Labels permutation195 permutation4
    mixedMoment B raw33559step0 raw33559step0Labels = mixedMoment B raw33559step1 raw33559step1Labels := by
      have ha : raw33559step1 = -raw33559step0 := by apply Matrix.ext; change ∀ i j, raw33559step1 i j = -(raw33559step0 i j); unfold raw33559step1 raw33559step0; decide +kernel
      have hl : raw33559step1Labels = raw33559step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33559step1 raw33559step1Labels = mixedMoment B raw33559step2 raw33559step2Labels := by
      have ha : raw33559step2 = raw33559step1 := by apply Matrix.ext; unfold raw33559step2 raw33559step1; decide +kernel
      have hl : raw33559step1Labels = labelEmbedding7 ∘ raw33559step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33559step1 raw33559step1Labels raw33559step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4813 node4813Labels := by rfl

def raw33560 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33560step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33560step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw33560step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33560step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw33560step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33560 raw33560Labels = mixedMoment B node4867 node4867Labels := by
  calc
    mixedMoment B raw33560 raw33560Labels = mixedMoment B raw33560step0 raw33560step0Labels := by
      have hz : ∀ j, raw33560 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33560step0 = (fun i j => raw33560 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33560step0 raw33560; decide +kernel
      have hl : raw33560step0Labels = raw33560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33560 raw33560Labels permutation346 hz
    mixedMoment B raw33560step0 raw33560step0Labels = mixedMoment B raw33560step1 raw33560step1Labels := by
      have ha : raw33560step1 = (fun i j => raw33560step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33560step1 raw33560step0; decide +kernel
      have hl : raw33560step1Labels = raw33560step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33560step0 raw33560step0Labels permutation34 permutation6
    mixedMoment B raw33560step1 raw33560step1Labels = mixedMoment B raw33560step2 raw33560step2Labels := by
      have ha : raw33560step2 = raw33560step1 := by apply Matrix.ext; unfold raw33560step2 raw33560step1; decide +kernel
      have hl : raw33560step1Labels = labelEmbedding9 ∘ raw33560step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33560step1 raw33560step1Labels raw33560step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4867 node4867Labels := by rfl

def raw33561 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw33561Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw33561step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33561step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw33561step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33561step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw33561step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33561 raw33561Labels = mixedMoment B node4870 node4870Labels := by
  calc
    mixedMoment B raw33561 raw33561Labels = mixedMoment B raw33561step0 raw33561step0Labels := by
      have hz : ∀ j, raw33561 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33561step0 = (fun i j => raw33561 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33561step0 raw33561; decide +kernel
      have hl : raw33561step0Labels = raw33561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33561 raw33561Labels permutation346 hz
    mixedMoment B raw33561step0 raw33561step0Labels = mixedMoment B raw33561step1 raw33561step1Labels := by
      have ha : raw33561step1 = (fun i j => raw33561step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33561step1 raw33561step0; decide +kernel
      have hl : raw33561step1Labels = raw33561step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33561step0 raw33561step0Labels permutation34 permutation6
    mixedMoment B raw33561step1 raw33561step1Labels = mixedMoment B raw33561step2 raw33561step2Labels := by
      have ha : raw33561step2 = raw33561step1 := by apply Matrix.ext; unfold raw33561step2 raw33561step1; decide +kernel
      have hl : raw33561step1Labels = labelEmbedding9 ∘ raw33561step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33561step1 raw33561step1Labels raw33561step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4870 node4870Labels := by rfl

def raw33562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw33562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw33562step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33562step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw33562step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33562step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33562step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33562step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33562step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33562 raw33562Labels = mixedMoment B node4471 node4471Labels := by
  calc
    mixedMoment B raw33562 raw33562Labels = mixedMoment B raw33562step0 raw33562step0Labels := by
      have hz : ∀ j, raw33562 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33562step0 = (fun i j => raw33562 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33562step0 raw33562; decide +kernel
      have hl : raw33562step0Labels = raw33562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33562 raw33562Labels permutation346 hz
    mixedMoment B raw33562step0 raw33562step0Labels = mixedMoment B raw33562step1 raw33562step1Labels := by
      have ha : raw33562step1 = (fun i j => raw33562step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33562step1 raw33562step0; decide +kernel
      have hl : raw33562step1Labels = raw33562step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33562step0 raw33562step0Labels permutation50 permutation4
    mixedMoment B raw33562step1 raw33562step1Labels = mixedMoment B raw33562step2 raw33562step2Labels := by
      have ha : raw33562step2 = -raw33562step1 := by apply Matrix.ext; change ∀ i j, raw33562step2 i j = -(raw33562step1 i j); unfold raw33562step2 raw33562step1; decide +kernel
      have hl : raw33562step2Labels = raw33562step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33562step2 raw33562step2Labels = mixedMoment B raw33562step3 raw33562step3Labels := by
      have ha : raw33562step3 = raw33562step2 := by apply Matrix.ext; unfold raw33562step3 raw33562step2; decide +kernel
      have hl : raw33562step2Labels = labelEmbedding7 ∘ raw33562step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33562step2 raw33562step2Labels raw33562step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4471 node4471Labels := by rfl

def raw33563 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw33563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33563step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw33563step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33563step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33563step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33563step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33563step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33563 raw33563Labels = mixedMoment B node4813 node4813Labels := by
  calc
    mixedMoment B raw33563 raw33563Labels = mixedMoment B raw33563step0 raw33563step0Labels := by
      have ha : raw33563step0 = (fun i j => raw33563 (permutation194 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33563step0 raw33563; decide +kernel
      have hl : raw33563step0Labels = raw33563Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33563 raw33563Labels permutation194 permutation4
    mixedMoment B raw33563step0 raw33563step0Labels = mixedMoment B raw33563step1 raw33563step1Labels := by
      have ha : raw33563step1 = -raw33563step0 := by apply Matrix.ext; change ∀ i j, raw33563step1 i j = -(raw33563step0 i j); unfold raw33563step1 raw33563step0; decide +kernel
      have hl : raw33563step1Labels = raw33563step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33563step1 raw33563step1Labels = mixedMoment B raw33563step2 raw33563step2Labels := by
      have ha : raw33563step2 = raw33563step1 := by apply Matrix.ext; unfold raw33563step2 raw33563step1; decide +kernel
      have hl : raw33563step1Labels = labelEmbedding7 ∘ raw33563step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33563step1 raw33563step1Labels raw33563step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4813 node4813Labels := by rfl

def raw33564 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw33564Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw33564step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw33564step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33564step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw33564step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33564 raw33564Labels = mixedMoment B node4867 node4867Labels := by
  calc
    mixedMoment B raw33564 raw33564Labels = mixedMoment B raw33564step0 raw33564step0Labels := by
      have hz : ∀ j, raw33564 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33564step0 = (fun i j => raw33564 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33564step0 raw33564; decide +kernel
      have hl : raw33564step0Labels = raw33564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33564 raw33564Labels permutation346 hz
    mixedMoment B raw33564step0 raw33564step0Labels = mixedMoment B raw33564step1 raw33564step1Labels := by
      have ha : raw33564step1 = (fun i j => raw33564step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33564step1 raw33564step0; decide +kernel
      have hl : raw33564step1Labels = raw33564step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33564step0 raw33564step0Labels permutation32 permutation6
    mixedMoment B raw33564step1 raw33564step1Labels = mixedMoment B raw33564step2 raw33564step2Labels := by
      have ha : raw33564step2 = raw33564step1 := by apply Matrix.ext; unfold raw33564step2 raw33564step1; decide +kernel
      have hl : raw33564step1Labels = labelEmbedding9 ∘ raw33564step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33564step1 raw33564step1Labels raw33564step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4867 node4867Labels := by rfl

def raw33565 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw33565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw33565step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33565step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw33565step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33565step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw33565step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33565 raw33565Labels = mixedMoment B node4870 node4870Labels := by
  calc
    mixedMoment B raw33565 raw33565Labels = mixedMoment B raw33565step0 raw33565step0Labels := by
      have hz : ∀ j, raw33565 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33565step0 = (fun i j => raw33565 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33565step0 raw33565; decide +kernel
      have hl : raw33565step0Labels = raw33565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33565 raw33565Labels permutation346 hz
    mixedMoment B raw33565step0 raw33565step0Labels = mixedMoment B raw33565step1 raw33565step1Labels := by
      have ha : raw33565step1 = (fun i j => raw33565step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33565step1 raw33565step0; decide +kernel
      have hl : raw33565step1Labels = raw33565step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33565step0 raw33565step0Labels permutation32 permutation6
    mixedMoment B raw33565step1 raw33565step1Labels = mixedMoment B raw33565step2 raw33565step2Labels := by
      have ha : raw33565step2 = raw33565step1 := by apply Matrix.ext; unfold raw33565step2 raw33565step1; decide +kernel
      have hl : raw33565step1Labels = labelEmbedding9 ∘ raw33565step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33565step1 raw33565step1Labels raw33565step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4870 node4870Labels := by rfl

def raw33566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw33566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw33566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33566step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33566step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33566step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33566step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33566step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33566 raw33566Labels = mixedMoment B node4489 node4489Labels := by
  calc
    mixedMoment B raw33566 raw33566Labels = mixedMoment B raw33566step0 raw33566step0Labels := by
      have hz : ∀ j, raw33566 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33566step0 = (fun i j => raw33566 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33566step0 raw33566; decide +kernel
      have hl : raw33566step0Labels = raw33566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33566 raw33566Labels permutation346 hz
    mixedMoment B raw33566step0 raw33566step0Labels = mixedMoment B raw33566step1 raw33566step1Labels := by
      have ha : raw33566step1 = (fun i j => raw33566step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33566step1 raw33566step0; decide +kernel
      have hl : raw33566step1Labels = raw33566step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33566step0 raw33566step0Labels permutation32 permutation4
    mixedMoment B raw33566step1 raw33566step1Labels = mixedMoment B raw33566step2 raw33566step2Labels := by
      have ha : raw33566step2 = -raw33566step1 := by apply Matrix.ext; change ∀ i j, raw33566step2 i j = -(raw33566step1 i j); unfold raw33566step2 raw33566step1; decide +kernel
      have hl : raw33566step2Labels = raw33566step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33566step2 raw33566step2Labels = mixedMoment B raw33566step3 raw33566step3Labels := by
      have ha : raw33566step3 = raw33566step2 := by apply Matrix.ext; unfold raw33566step3 raw33566step2; decide +kernel
      have hl : raw33566step2Labels = labelEmbedding7 ∘ raw33566step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33566step2 raw33566step2Labels raw33566step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4489 node4489Labels := by rfl

def raw33567 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw33567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw33567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33567step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33567step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33567step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33567 raw33567Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw33567 raw33567Labels = mixedMoment B raw33567step0 raw33567step0Labels := by
      have hz : ∀ j, raw33567 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33567step0 = (fun i j => raw33567 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33567step0 raw33567; decide +kernel
      have hl : raw33567step0Labels = raw33567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33567 raw33567Labels permutation346 hz
    mixedMoment B raw33567step0 raw33567step0Labels = mixedMoment B raw33567step1 raw33567step1Labels := by
      have ha : raw33567step1 = (fun i j => raw33567step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33567step1 raw33567step0; decide +kernel
      have hl : raw33567step1Labels = raw33567step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33567step0 raw33567step0Labels permutation32 permutation6
    mixedMoment B raw33567step1 raw33567step1Labels = mixedMoment B raw33567step2 raw33567step2Labels := by
      have ha : raw33567step2 = raw33567step1 := by apply Matrix.ext; unfold raw33567step2 raw33567step1; decide +kernel
      have hl : raw33567step1Labels = labelEmbedding9 ∘ raw33567step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33567step1 raw33567step1Labels raw33567step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw33568 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33568step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33568step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33568step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33568step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33568 raw33568Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw33568 raw33568Labels = mixedMoment B raw33568step0 raw33568step0Labels := by
      have hz : ∀ j, raw33568 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33568step0 = (fun i j => raw33568 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33568step0 raw33568; decide +kernel
      have hl : raw33568step0Labels = raw33568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33568 raw33568Labels permutation346 hz
    mixedMoment B raw33568step0 raw33568step0Labels = mixedMoment B raw33568step1 raw33568step1Labels := by
      have ha : raw33568step1 = (fun i j => raw33568step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33568step1 raw33568step0; decide +kernel
      have hl : raw33568step1Labels = raw33568step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33568step0 raw33568step0Labels permutation34 permutation6
    mixedMoment B raw33568step1 raw33568step1Labels = mixedMoment B raw33568step2 raw33568step2Labels := by
      have ha : raw33568step2 = raw33568step1 := by apply Matrix.ext; unfold raw33568step2 raw33568step1; decide +kernel
      have hl : raw33568step1Labels = labelEmbedding9 ∘ raw33568step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33568step1 raw33568step1Labels raw33568step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw33569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33569step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33569step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw33569step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33569step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw33569step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33569step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw33569step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33569 raw33569Labels = mixedMoment B node5288 node5288Labels := by
  calc
    mixedMoment B raw33569 raw33569Labels = mixedMoment B raw33569step0 raw33569step0Labels := by
      have hz : ∀ j, raw33569 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33569step0 = (fun i j => raw33569 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33569step0 raw33569; decide +kernel
      have hl : raw33569step0Labels = raw33569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33569 raw33569Labels permutation346 hz
    mixedMoment B raw33569step0 raw33569step0Labels = mixedMoment B raw33569step1 raw33569step1Labels := by
      have ha : raw33569step1 = (fun i j => raw33569step0 (permutation62 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33569step1 raw33569step0; decide +kernel
      have hl : raw33569step1Labels = raw33569step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33569step0 raw33569step0Labels permutation62 permutation5
    mixedMoment B raw33569step1 raw33569step1Labels = mixedMoment B raw33569step2 raw33569step2Labels := by
      have ha : raw33569step2 = -raw33569step1 := by apply Matrix.ext; change ∀ i j, raw33569step2 i j = -(raw33569step1 i j); unfold raw33569step2 raw33569step1; decide +kernel
      have hl : raw33569step2Labels = raw33569step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33569step2 raw33569step2Labels = mixedMoment B raw33569step3 raw33569step3Labels := by
      have ha : raw33569step3 = raw33569step2 := by apply Matrix.ext; unfold raw33569step3 raw33569step2; decide +kernel
      have hl : raw33569step2Labels = labelEmbedding8 ∘ raw33569step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33569step2 raw33569step2Labels raw33569step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5288 node5288Labels := by rfl

def raw33570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33570step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33570step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33570step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33570step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33570step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33570 raw33570Labels = mixedMoment B node5255 node5255Labels := by
  calc
    mixedMoment B raw33570 raw33570Labels = mixedMoment B raw33570step0 raw33570step0Labels := by
      have ha : raw33570step0 = (fun i j => raw33570 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33570step0 raw33570; decide +kernel
      have hl : raw33570step0Labels = raw33570Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33570 raw33570Labels permutation188 permutation7
    mixedMoment B raw33570step0 raw33570step0Labels = mixedMoment B raw33570step1 raw33570step1Labels := by
      have ha : raw33570step1 = -raw33570step0 := by apply Matrix.ext; change ∀ i j, raw33570step1 i j = -(raw33570step0 i j); unfold raw33570step1 raw33570step0; decide +kernel
      have hl : raw33570step1Labels = raw33570step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33570step1 raw33570step1Labels = mixedMoment B raw33570step2 raw33570step2Labels := by
      have ha : raw33570step2 = raw33570step1 := by apply Matrix.ext; unfold raw33570step2 raw33570step1; decide +kernel
      have hl : raw33570step1Labels = labelEmbedding10 ∘ raw33570step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33570step1 raw33570step1Labels raw33570step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5255 node5255Labels := by rfl

def raw33571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33571step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw33571step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33571step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw33571step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33571step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw33571step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33571 raw33571Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw33571 raw33571Labels = mixedMoment B raw33571step0 raw33571step0Labels := by
      have hz : ∀ j, raw33571 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33571step0 = (fun i j => raw33571 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33571step0 raw33571; decide +kernel
      have hl : raw33571step0Labels = raw33571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33571 raw33571Labels permutation346 hz
    mixedMoment B raw33571step0 raw33571step0Labels = mixedMoment B raw33571step1 raw33571step1Labels := by
      have ha : raw33571step1 = (fun i j => raw33571step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33571step1 raw33571step0; decide +kernel
      have hl : raw33571step1Labels = raw33571step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33571step0 raw33571step0Labels permutation44 permutation7
    mixedMoment B raw33571step1 raw33571step1Labels = mixedMoment B raw33571step2 raw33571step2Labels := by
      have ha : raw33571step2 = -raw33571step1 := by apply Matrix.ext; change ∀ i j, raw33571step2 i j = -(raw33571step1 i j); unfold raw33571step2 raw33571step1; decide +kernel
      have hl : raw33571step2Labels = raw33571step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33571step2 raw33571step2Labels = mixedMoment B raw33571step3 raw33571step3Labels := by
      have ha : raw33571step3 = raw33571step2 := by apply Matrix.ext; unfold raw33571step3 raw33571step2; decide +kernel
      have hl : raw33571step2Labels = labelEmbedding10 ∘ raw33571step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33571step2 raw33571step2Labels raw33571step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw33572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33572step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33572step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33572step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33572step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33572step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33572step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33572step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33572step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33572step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33572 raw33572Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw33572 raw33572Labels = mixedMoment B raw33572step0 raw33572step0Labels := by
      have hz : ∀ j, raw33572 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33572step0 = (fun i j => raw33572 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33572step0 raw33572; decide +kernel
      have hl : raw33572step0Labels = raw33572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33572 raw33572Labels permutation520 hz
    mixedMoment B raw33572step0 raw33572step0Labels = mixedMoment B raw33572step1 raw33572step1Labels := by
      have hz : ∀ j, raw33572step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33572step1 = (fun i j => raw33572step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33572step1 raw33572step0; decide +kernel
      have hl : raw33572step1Labels = raw33572step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33572step0 raw33572step0Labels permutation80 hz
    mixedMoment B raw33572step1 raw33572step1Labels = mixedMoment B raw33572step2 raw33572step2Labels := by
      have ha : raw33572step2 = (fun i j => raw33572step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33572step2 raw33572step1; decide +kernel
      have hl : raw33572step2Labels = raw33572step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33572step1 raw33572step1Labels permutation8 permutation7
    mixedMoment B raw33572step2 raw33572step2Labels = mixedMoment B raw33572step3 raw33572step3Labels := by
      have ha : raw33572step3 = -raw33572step2 := by apply Matrix.ext; change ∀ i j, raw33572step3 i j = -(raw33572step2 i j); unfold raw33572step3 raw33572step2; decide +kernel
      have hl : raw33572step3Labels = raw33572step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33572step3 raw33572step3Labels = mixedMoment B raw33572step4 raw33572step4Labels := by
      have ha : raw33572step4 = raw33572step3 := by apply Matrix.ext; unfold raw33572step4 raw33572step3; decide +kernel
      have hl : raw33572step3Labels = labelEmbedding10 ∘ raw33572step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33572step3 raw33572step3Labels raw33572step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw33573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33573step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33573step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33573step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33573step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33573step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33573step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33573step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33573 raw33573Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw33573 raw33573Labels = mixedMoment B raw33573step0 raw33573step0Labels := by
      have hz : ∀ j, raw33573 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33573step0 = (fun i j => raw33573 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33573step0 raw33573; decide +kernel
      have hl : raw33573step0Labels = raw33573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33573 raw33573Labels permutation346 hz
    mixedMoment B raw33573step0 raw33573step0Labels = mixedMoment B raw33573step1 raw33573step1Labels := by
      have ha : raw33573step1 = (fun i j => raw33573step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33573step1 raw33573step0; decide +kernel
      have hl : raw33573step1Labels = raw33573step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33573step0 raw33573step0Labels permutation44 permutation7
    mixedMoment B raw33573step1 raw33573step1Labels = mixedMoment B raw33573step2 raw33573step2Labels := by
      have ha : raw33573step2 = -raw33573step1 := by apply Matrix.ext; change ∀ i j, raw33573step2 i j = -(raw33573step1 i j); unfold raw33573step2 raw33573step1; decide +kernel
      have hl : raw33573step2Labels = raw33573step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33573step2 raw33573step2Labels = mixedMoment B raw33573step3 raw33573step3Labels := by
      have ha : raw33573step3 = raw33573step2 := by apply Matrix.ext; unfold raw33573step3 raw33573step2; decide +kernel
      have hl : raw33573step2Labels = labelEmbedding10 ∘ raw33573step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33573step2 raw33573step2Labels raw33573step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw33574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33574step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33574step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33574 raw33574Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw33574 raw33574Labels = mixedMoment B raw33574step0 raw33574step0Labels := by
      have hz : ∀ j, raw33574 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33574step0 = (fun i j => raw33574 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33574step0 raw33574; decide +kernel
      have hl : raw33574step0Labels = raw33574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33574 raw33574Labels permutation346 hz
    mixedMoment B raw33574step0 raw33574step0Labels = mixedMoment B raw33574step1 raw33574step1Labels := by
      have ha : raw33574step1 = (fun i j => raw33574step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33574step1 raw33574step0; decide +kernel
      have hl : raw33574step1Labels = raw33574step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33574step0 raw33574step0Labels permutation34 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw33575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33575Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33575step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33575 raw33575Labels = mixedMoment B node4696 node4696Labels := by
  calc
    mixedMoment B raw33575 raw33575Labels = mixedMoment B raw33575step0 raw33575step0Labels := by
      have ha : raw33575step0 = (fun i j => raw33575 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33575step0 raw33575; decide +kernel
      have hl : raw33575step0Labels = raw33575Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33575 raw33575Labels permutation154 permutation2
    _ = mixedMoment B node4696 node4696Labels := by rfl

def raw33576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33576Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33576step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw33576step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33576 raw33576Labels = mixedMoment B node4851 node4851Labels := by
  calc
    mixedMoment B raw33576 raw33576Labels = mixedMoment B raw33576step0 raw33576step0Labels := by
      have ha : raw33576step0 = (fun i j => raw33576 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33576step0 raw33576; decide +kernel
      have hl : raw33576step0Labels = raw33576Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33576 raw33576Labels permutation158 permutation2
    _ = mixedMoment B node4851 node4851Labels := by rfl

def raw33577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33577Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33577step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33577 raw33577Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw33577 raw33577Labels = mixedMoment B raw33577step0 raw33577step0Labels := by
      have hz : ∀ j, raw33577 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33577step0 = (fun i j => raw33577 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33577step0 raw33577; decide +kernel
      have hl : raw33577step0Labels = raw33577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33577 raw33577Labels permutation520 hz
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw33578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33578Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33578step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33578step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33578 raw33578Labels = mixedMoment B node4864 node4864Labels := by
  calc
    mixedMoment B raw33578 raw33578Labels = mixedMoment B raw33578step0 raw33578step0Labels := by
      have ha : raw33578step0 = (fun i j => raw33578 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33578step0 raw33578; decide +kernel
      have hl : raw33578step0Labels = raw33578Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33578 raw33578Labels permutation154 permutation2
    _ = mixedMoment B node4864 node4864Labels := by rfl

def raw33579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33579Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33579step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33579step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw33579step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33579 raw33579Labels = mixedMoment B node4701 node4701Labels := by
  calc
    mixedMoment B raw33579 raw33579Labels = mixedMoment B raw33579step0 raw33579step0Labels := by
      have hz : ∀ j, raw33579 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33579step0 = (fun i j => raw33579 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33579step0 raw33579; decide +kernel
      have hl : raw33579step0Labels = raw33579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33579 raw33579Labels permutation346 hz
    mixedMoment B raw33579step0 raw33579step0Labels = mixedMoment B raw33579step1 raw33579step1Labels := by
      have ha : raw33579step1 = (fun i j => raw33579step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33579step1 raw33579step0; decide +kernel
      have hl : raw33579step1Labels = raw33579step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33579step0 raw33579step0Labels permutation34 permutation2
    _ = mixedMoment B node4701 node4701Labels := by rfl

def raw33580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33580step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw33580step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33580 raw33580Labels = mixedMoment B node4774 node4774Labels := by
  calc
    mixedMoment B raw33580 raw33580Labels = mixedMoment B raw33580step0 raw33580step0Labels := by
      have ha : raw33580step0 = (fun i j => raw33580 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33580step0 raw33580; decide +kernel
      have hl : raw33580step0Labels = raw33580Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33580 raw33580Labels permutation178 permutation2
    _ = mixedMoment B node4774 node4774Labels := by rfl

def raw33581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw33581step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33581step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33581step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33581 raw33581Labels = mixedMoment B node4875 node4875Labels := by
  calc
    mixedMoment B raw33581 raw33581Labels = mixedMoment B raw33581step0 raw33581step0Labels := by
      have hz : ∀ j, raw33581 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33581step0 = (fun i j => raw33581 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33581step0 raw33581; decide +kernel
      have hl : raw33581step0Labels = raw33581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33581 raw33581Labels permutation520 hz
    mixedMoment B raw33581step0 raw33581step0Labels = mixedMoment B raw33581step1 raw33581step1Labels := by
      have hz : ∀ j, raw33581step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33581step1 = (fun i j => raw33581step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33581step1 raw33581step0; decide +kernel
      have hl : raw33581step1Labels = raw33581step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33581step0 raw33581step0Labels permutation80 hz
    _ = mixedMoment B node4875 node4875Labels := by rfl

def raw33582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33582Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33582step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33582step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33582step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33582 raw33582Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw33582 raw33582Labels = mixedMoment B raw33582step0 raw33582step0Labels := by
      have hz : ∀ j, raw33582 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33582step0 = (fun i j => raw33582 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33582step0 raw33582; decide +kernel
      have hl : raw33582step0Labels = raw33582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33582 raw33582Labels permutation346 hz
    mixedMoment B raw33582step0 raw33582step0Labels = mixedMoment B raw33582step1 raw33582step1Labels := by
      have ha : raw33582step1 = (fun i j => raw33582step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33582step1 raw33582step0; decide +kernel
      have hl : raw33582step1Labels = raw33582step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33582step0 raw33582step0Labels permutation35 permutation2
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw33583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33583step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33583 raw33583Labels = mixedMoment B node4703 node4703Labels := by
  calc
    mixedMoment B raw33583 raw33583Labels = mixedMoment B raw33583step0 raw33583step0Labels := by
      have hz : ∀ j, raw33583 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33583step0 = (fun i j => raw33583 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33583step0 raw33583; decide +kernel
      have hl : raw33583step0Labels = raw33583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33583 raw33583Labels permutation346 hz
    _ = mixedMoment B node4703 node4703Labels := by rfl

def raw33584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33584step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33584 raw33584Labels = mixedMoment B node4775 node4775Labels := by
  calc
    mixedMoment B raw33584 raw33584Labels = mixedMoment B raw33584step0 raw33584step0Labels := by
      have ha : raw33584step0 = (fun i j => raw33584 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33584step0 raw33584; decide +kernel
      have hl : raw33584step0Labels = raw33584Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33584 raw33584Labels permutation176 permutation2
    _ = mixedMoment B node4775 node4775Labels := by rfl

def raw33585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33585Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33585step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33585 raw33585Labels = mixedMoment B node4856 node4856Labels := by
  calc
    mixedMoment B raw33585 raw33585Labels = mixedMoment B raw33585step0 raw33585step0Labels := by
      have hz : ∀ j, raw33585 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33585step0 = (fun i j => raw33585 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33585step0 raw33585; decide +kernel
      have hl : raw33585step0Labels = raw33585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33585 raw33585Labels permutation346 hz
    _ = mixedMoment B node4856 node4856Labels := by rfl

def raw33586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw33586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw33586step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33586step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33586 raw33586Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw33586 raw33586Labels = mixedMoment B raw33586step0 raw33586step0Labels := by
      have hz : ∀ j, raw33586 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33586step0 = (fun i j => raw33586 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33586step0 raw33586; decide +kernel
      have hl : raw33586step0Labels = raw33586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33586 raw33586Labels permutation346 hz
    mixedMoment B raw33586step0 raw33586step0Labels = mixedMoment B raw33586step1 raw33586step1Labels := by
      have ha : raw33586step1 = (fun i j => raw33586step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33586step1 raw33586step0; decide +kernel
      have hl : raw33586step1Labels = raw33586step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33586step0 raw33586step0Labels permutation33 permutation2
    _ = mixedMoment B node4869 node4869Labels := by rfl

def raw33587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33587step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33587step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33587 raw33587Labels = mixedMoment B node4699 node4699Labels := by
  calc
    mixedMoment B raw33587 raw33587Labels = mixedMoment B raw33587step0 raw33587step0Labels := by
      have hz : ∀ j, raw33587 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33587step0 = (fun i j => raw33587 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33587step0 raw33587; decide +kernel
      have hl : raw33587step0Labels = raw33587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33587 raw33587Labels permutation346 hz
    mixedMoment B raw33587step0 raw33587step0Labels = mixedMoment B raw33587step1 raw33587step1Labels := by
      have ha : raw33587step1 = (fun i j => raw33587step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33587step1 raw33587step0; decide +kernel
      have hl : raw33587step1Labels = raw33587step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33587step0 raw33587step0Labels permutation34 permutation2
    _ = mixedMoment B node4699 node4699Labels := by rfl

def raw33588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33588Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33588step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33588step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33588 raw33588Labels = mixedMoment B node4772 node4772Labels := by
  calc
    mixedMoment B raw33588 raw33588Labels = mixedMoment B raw33588step0 raw33588step0Labels := by
      have ha : raw33588step0 = (fun i j => raw33588 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33588step0 raw33588; decide +kernel
      have hl : raw33588step0Labels = raw33588Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33588 raw33588Labels permutation178 permutation2
    _ = mixedMoment B node4772 node4772Labels := by rfl

def raw33589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33589step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33589 raw33589Labels = mixedMoment B node4853 node4853Labels := by
  calc
    mixedMoment B raw33589 raw33589Labels = mixedMoment B raw33589step0 raw33589step0Labels := by
      have hz : ∀ j, raw33589 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33589step0 = (fun i j => raw33589 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33589step0 raw33589; decide +kernel
      have hl : raw33589step0Labels = raw33589Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33589 raw33589Labels permutation346 hz
    _ = mixedMoment B node4853 node4853Labels := by rfl

def raw33590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw33590Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33590step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33590step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33590step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33590 raw33590Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw33590 raw33590Labels = mixedMoment B raw33590step0 raw33590step0Labels := by
      have hz : ∀ j, raw33590 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33590step0 = (fun i j => raw33590 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33590step0 raw33590; decide +kernel
      have hl : raw33590step0Labels = raw33590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33590 raw33590Labels permutation520 hz
    mixedMoment B raw33590step0 raw33590step0Labels = mixedMoment B raw33590step1 raw33590step1Labels := by
      have hz : ∀ j, raw33590step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33590step1 = (fun i j => raw33590step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33590step1 raw33590step0; decide +kernel
      have hl : raw33590step1Labels = raw33590step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33590step0 raw33590step0Labels permutation80 hz
    _ = mixedMoment B node4871 node4871Labels := by rfl

def raw33591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33591Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33591step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw33591step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33591step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw33591step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33591step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw33591step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33591 raw33591Labels = mixedMoment B node2760 node2760Labels := by
  calc
    mixedMoment B raw33591 raw33591Labels = mixedMoment B raw33591step0 raw33591step0Labels := by
      have hz : ∀ j, raw33591 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33591step0 = (fun i j => raw33591 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33591step0 raw33591; decide +kernel
      have hl : raw33591step0Labels = raw33591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33591 raw33591Labels permutation346 hz
    mixedMoment B raw33591step0 raw33591step0Labels = mixedMoment B raw33591step1 raw33591step1Labels := by
      have ha : raw33591step1 = (fun i j => raw33591step0 (permutation62 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33591step1 raw33591step0; decide +kernel
      have hl : raw33591step1Labels = raw33591step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33591step0 raw33591step0Labels permutation62 permutation5
    mixedMoment B raw33591step1 raw33591step1Labels = mixedMoment B raw33591step2 raw33591step2Labels := by
      have ha : raw33591step2 = -raw33591step1 := by apply Matrix.ext; change ∀ i j, raw33591step2 i j = -(raw33591step1 i j); unfold raw33591step2 raw33591step1; decide +kernel
      have hl : raw33591step2Labels = raw33591step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33591step2 raw33591step2Labels = mixedMoment B raw33591step3 raw33591step3Labels := by
      have ha : raw33591step3 = raw33591step2 := by apply Matrix.ext; unfold raw33591step3 raw33591step2; decide +kernel
      have hl : raw33591step2Labels = labelEmbedding1 ∘ raw33591step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33591step2 raw33591step2Labels raw33591step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2760 node2760Labels := by rfl

def raw33592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33592Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33592step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33592step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33592step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33592step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33592step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33592step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33592 raw33592Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw33592 raw33592Labels = mixedMoment B raw33592step0 raw33592step0Labels := by
      have ha : raw33592step0 = (fun i j => raw33592 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33592step0 raw33592; decide +kernel
      have hl : raw33592step0Labels = raw33592Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33592 raw33592Labels permutation188 permutation7
    mixedMoment B raw33592step0 raw33592step0Labels = mixedMoment B raw33592step1 raw33592step1Labels := by
      have ha : raw33592step1 = -raw33592step0 := by apply Matrix.ext; change ∀ i j, raw33592step1 i j = -(raw33592step0 i j); unfold raw33592step1 raw33592step0; decide +kernel
      have hl : raw33592step1Labels = raw33592step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33592step1 raw33592step1Labels = mixedMoment B raw33592step2 raw33592step2Labels := by
      have ha : raw33592step2 = raw33592step1 := by apply Matrix.ext; unfold raw33592step2 raw33592step1; decide +kernel
      have hl : raw33592step1Labels = labelEmbedding1 ∘ raw33592step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33592step1 raw33592step1Labels raw33592step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2718 node2718Labels := by rfl

def raw33593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33593Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33593step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33593step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw33593step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33593step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw33593step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33593step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw33593step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33593 raw33593Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw33593 raw33593Labels = mixedMoment B raw33593step0 raw33593step0Labels := by
      have hz : ∀ j, raw33593 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33593step0 = (fun i j => raw33593 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33593step0 raw33593; decide +kernel
      have hl : raw33593step0Labels = raw33593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33593 raw33593Labels permutation346 hz
    mixedMoment B raw33593step0 raw33593step0Labels = mixedMoment B raw33593step1 raw33593step1Labels := by
      have ha : raw33593step1 = (fun i j => raw33593step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33593step1 raw33593step0; decide +kernel
      have hl : raw33593step1Labels = raw33593step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33593step0 raw33593step0Labels permutation44 permutation7
    mixedMoment B raw33593step1 raw33593step1Labels = mixedMoment B raw33593step2 raw33593step2Labels := by
      have ha : raw33593step2 = -raw33593step1 := by apply Matrix.ext; change ∀ i j, raw33593step2 i j = -(raw33593step1 i j); unfold raw33593step2 raw33593step1; decide +kernel
      have hl : raw33593step2Labels = raw33593step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33593step2 raw33593step2Labels = mixedMoment B raw33593step3 raw33593step3Labels := by
      have ha : raw33593step3 = raw33593step2 := by apply Matrix.ext; unfold raw33593step3 raw33593step2; decide +kernel
      have hl : raw33593step2Labels = labelEmbedding1 ∘ raw33593step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33593step2 raw33593step2Labels raw33593step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2763 node2763Labels := by rfl

def raw33594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33594Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33594step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33594step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33594step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33594step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33594step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33594step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33594step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33594step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33594step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33594 raw33594Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw33594 raw33594Labels = mixedMoment B raw33594step0 raw33594step0Labels := by
      have hz : ∀ j, raw33594 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33594step0 = (fun i j => raw33594 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33594step0 raw33594; decide +kernel
      have hl : raw33594step0Labels = raw33594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33594 raw33594Labels permutation520 hz
    mixedMoment B raw33594step0 raw33594step0Labels = mixedMoment B raw33594step1 raw33594step1Labels := by
      have hz : ∀ j, raw33594step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33594step1 = (fun i j => raw33594step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33594step1 raw33594step0; decide +kernel
      have hl : raw33594step1Labels = raw33594step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33594step0 raw33594step0Labels permutation80 hz
    mixedMoment B raw33594step1 raw33594step1Labels = mixedMoment B raw33594step2 raw33594step2Labels := by
      have ha : raw33594step2 = (fun i j => raw33594step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33594step2 raw33594step1; decide +kernel
      have hl : raw33594step2Labels = raw33594step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33594step1 raw33594step1Labels permutation8 permutation7
    mixedMoment B raw33594step2 raw33594step2Labels = mixedMoment B raw33594step3 raw33594step3Labels := by
      have ha : raw33594step3 = -raw33594step2 := by apply Matrix.ext; change ∀ i j, raw33594step3 i j = -(raw33594step2 i j); unfold raw33594step3 raw33594step2; decide +kernel
      have hl : raw33594step3Labels = raw33594step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33594step3 raw33594step3Labels = mixedMoment B raw33594step4 raw33594step4Labels := by
      have ha : raw33594step4 = raw33594step3 := by apply Matrix.ext; unfold raw33594step4 raw33594step3; decide +kernel
      have hl : raw33594step3Labels = labelEmbedding1 ∘ raw33594step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33594step3 raw33594step3Labels raw33594step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2782 node2782Labels := by rfl

def raw33595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33595Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33595step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33595step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33595step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33595step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33595step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33595step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33595step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33595 raw33595Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw33595 raw33595Labels = mixedMoment B raw33595step0 raw33595step0Labels := by
      have hz : ∀ j, raw33595 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33595step0 = (fun i j => raw33595 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33595step0 raw33595; decide +kernel
      have hl : raw33595step0Labels = raw33595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33595 raw33595Labels permutation346 hz
    mixedMoment B raw33595step0 raw33595step0Labels = mixedMoment B raw33595step1 raw33595step1Labels := by
      have ha : raw33595step1 = (fun i j => raw33595step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33595step1 raw33595step0; decide +kernel
      have hl : raw33595step1Labels = raw33595step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33595step0 raw33595step0Labels permutation44 permutation7
    mixedMoment B raw33595step1 raw33595step1Labels = mixedMoment B raw33595step2 raw33595step2Labels := by
      have ha : raw33595step2 = -raw33595step1 := by apply Matrix.ext; change ∀ i j, raw33595step2 i j = -(raw33595step1 i j); unfold raw33595step2 raw33595step1; decide +kernel
      have hl : raw33595step2Labels = raw33595step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33595step2 raw33595step2Labels = mixedMoment B raw33595step3 raw33595step3Labels := by
      have ha : raw33595step3 = raw33595step2 := by apply Matrix.ext; unfold raw33595step3 raw33595step2; decide +kernel
      have hl : raw33595step2Labels = labelEmbedding1 ∘ raw33595step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33595step2 raw33595step2Labels raw33595step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2764 node2764Labels := by rfl

def raw33596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33596Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33596step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33596step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33596step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33596step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33596step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33596step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33596 raw33596Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw33596 raw33596Labels = mixedMoment B raw33596step0 raw33596step0Labels := by
      have hz : ∀ j, raw33596 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33596step0 = (fun i j => raw33596 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33596step0 raw33596; decide +kernel
      have hl : raw33596step0Labels = raw33596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33596 raw33596Labels permutation346 hz
    mixedMoment B raw33596step0 raw33596step0Labels = mixedMoment B raw33596step1 raw33596step1Labels := by
      have ha : raw33596step1 = (fun i j => raw33596step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33596step1 raw33596step0; decide +kernel
      have hl : raw33596step1Labels = raw33596step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33596step0 raw33596step0Labels permutation44 permutation7
    mixedMoment B raw33596step1 raw33596step1Labels = mixedMoment B raw33596step2 raw33596step2Labels := by
      have ha : raw33596step2 = -raw33596step1 := by apply Matrix.ext; change ∀ i j, raw33596step2 i j = -(raw33596step1 i j); unfold raw33596step2 raw33596step1; decide +kernel
      have hl : raw33596step2Labels = raw33596step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33596step2 raw33596step2Labels = mixedMoment B raw33596step3 raw33596step3Labels := by
      have ha : raw33596step3 = raw33596step2 := by apply Matrix.ext; unfold raw33596step3 raw33596step2; decide +kernel
      have hl : raw33596step2Labels = labelEmbedding1 ∘ raw33596step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33596step2 raw33596step2Labels raw33596step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

def raw33597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33597Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw33597step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33597step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw33597step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33597step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw33597step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33597 raw33597Labels = mixedMoment B node2238 node2238Labels := by
  calc
    mixedMoment B raw33597 raw33597Labels = mixedMoment B raw33597step0 raw33597step0Labels := by
      have ha : raw33597step0 = (fun i j => raw33597 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33597step0 raw33597; decide +kernel
      have hl : raw33597step0Labels = raw33597Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33597 raw33597Labels permutation188 permutation7
    mixedMoment B raw33597step0 raw33597step0Labels = mixedMoment B raw33597step1 raw33597step1Labels := by
      have ha : raw33597step1 = -raw33597step0 := by apply Matrix.ext; change ∀ i j, raw33597step1 i j = -(raw33597step0 i j); unfold raw33597step1 raw33597step0; decide +kernel
      have hl : raw33597step1Labels = raw33597step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33597step1 raw33597step1Labels = mixedMoment B raw33597step2 raw33597step2Labels := by
      have ha : raw33597step2 = raw33597step1 := by apply Matrix.ext; unfold raw33597step2 raw33597step1; decide +kernel
      have hl : raw33597step1Labels = labelEmbedding1 ∘ raw33597step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33597step1 raw33597step1Labels raw33597step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2238 node2238Labels := by rfl

def raw33598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33598Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw33598step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33598step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw33598step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33598step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw33598step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33598 raw33598Labels = mixedMoment B node2240 node2240Labels := by
  calc
    mixedMoment B raw33598 raw33598Labels = mixedMoment B raw33598step0 raw33598step0Labels := by
      have ha : raw33598step0 = (fun i j => raw33598 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33598step0 raw33598; decide +kernel
      have hl : raw33598step0Labels = raw33598Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33598 raw33598Labels permutation188 permutation7
    mixedMoment B raw33598step0 raw33598step0Labels = mixedMoment B raw33598step1 raw33598step1Labels := by
      have ha : raw33598step1 = -raw33598step0 := by apply Matrix.ext; change ∀ i j, raw33598step1 i j = -(raw33598step0 i j); unfold raw33598step1 raw33598step0; decide +kernel
      have hl : raw33598step1Labels = raw33598step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33598step1 raw33598step1Labels = mixedMoment B raw33598step2 raw33598step2Labels := by
      have ha : raw33598step2 = raw33598step1 := by apply Matrix.ext; unfold raw33598step2 raw33598step1; decide +kernel
      have hl : raw33598step1Labels = labelEmbedding1 ∘ raw33598step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33598step1 raw33598step1Labels raw33598step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2240 node2240Labels := by rfl

def raw33599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33599Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33599step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33599step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33599step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33599step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33599step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33599step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33599 raw33599Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw33599 raw33599Labels = mixedMoment B raw33599step0 raw33599step0Labels := by
      have hz : ∀ j, raw33599 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33599step0 = (fun i j => raw33599 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33599step0 raw33599; decide +kernel
      have hl : raw33599step0Labels = raw33599Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33599 raw33599Labels permutation520 hz
    mixedMoment B raw33599step0 raw33599step0Labels = mixedMoment B raw33599step1 raw33599step1Labels := by
      have ha : raw33599step1 = (fun i j => raw33599step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33599step1 raw33599step0; decide +kernel
      have hl : raw33599step1Labels = raw33599step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33599step0 raw33599step0Labels permutation38 permutation7
    mixedMoment B raw33599step1 raw33599step1Labels = mixedMoment B raw33599step2 raw33599step2Labels := by
      have ha : raw33599step2 = -raw33599step1 := by apply Matrix.ext; change ∀ i j, raw33599step2 i j = -(raw33599step1 i j); unfold raw33599step2 raw33599step1; decide +kernel
      have hl : raw33599step2Labels = raw33599step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33599step2 raw33599step2Labels = mixedMoment B raw33599step3 raw33599step3Labels := by
      have ha : raw33599step3 = raw33599step2 := by apply Matrix.ext; unfold raw33599step3 raw33599step2; decide +kernel
      have hl : raw33599step2Labels = labelEmbedding1 ∘ raw33599step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33599step2 raw33599step2Labels raw33599step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

def raw33600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33600Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33600step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33600step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33600step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33600step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33600step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33600 raw33600Labels = mixedMoment B node2241 node2241Labels := by
  calc
    mixedMoment B raw33600 raw33600Labels = mixedMoment B raw33600step0 raw33600step0Labels := by
      have ha : raw33600step0 = (fun i j => raw33600 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33600step0 raw33600; decide +kernel
      have hl : raw33600step0Labels = raw33600Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33600 raw33600Labels permutation188 permutation7
    mixedMoment B raw33600step0 raw33600step0Labels = mixedMoment B raw33600step1 raw33600step1Labels := by
      have ha : raw33600step1 = -raw33600step0 := by apply Matrix.ext; change ∀ i j, raw33600step1 i j = -(raw33600step0 i j); unfold raw33600step1 raw33600step0; decide +kernel
      have hl : raw33600step1Labels = raw33600step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33600step1 raw33600step1Labels = mixedMoment B raw33600step2 raw33600step2Labels := by
      have ha : raw33600step2 = raw33600step1 := by apply Matrix.ext; unfold raw33600step2 raw33600step1; decide +kernel
      have hl : raw33600step1Labels = labelEmbedding1 ∘ raw33600step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33600step1 raw33600step1Labels raw33600step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2241 node2241Labels := by rfl

def raw33601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33601Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33601step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33601step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw33601step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33601step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw33601step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33601step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw33601step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33601 raw33601Labels = mixedMoment B node2257 node2257Labels := by
  calc
    mixedMoment B raw33601 raw33601Labels = mixedMoment B raw33601step0 raw33601step0Labels := by
      have hz : ∀ j, raw33601 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33601step0 = (fun i j => raw33601 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33601step0 raw33601; decide +kernel
      have hl : raw33601step0Labels = raw33601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33601 raw33601Labels permutation346 hz
    mixedMoment B raw33601step0 raw33601step0Labels = mixedMoment B raw33601step1 raw33601step1Labels := by
      have ha : raw33601step1 = (fun i j => raw33601step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33601step1 raw33601step0; decide +kernel
      have hl : raw33601step1Labels = raw33601step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33601step0 raw33601step0Labels permutation44 permutation7
    mixedMoment B raw33601step1 raw33601step1Labels = mixedMoment B raw33601step2 raw33601step2Labels := by
      have ha : raw33601step2 = -raw33601step1 := by apply Matrix.ext; change ∀ i j, raw33601step2 i j = -(raw33601step1 i j); unfold raw33601step2 raw33601step1; decide +kernel
      have hl : raw33601step2Labels = raw33601step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33601step2 raw33601step2Labels = mixedMoment B raw33601step3 raw33601step3Labels := by
      have ha : raw33601step3 = raw33601step2 := by apply Matrix.ext; unfold raw33601step3 raw33601step2; decide +kernel
      have hl : raw33601step2Labels = labelEmbedding1 ∘ raw33601step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33601step2 raw33601step2Labels raw33601step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2257 node2257Labels := by rfl

def raw33602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33602Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33602step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw33602step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33602step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw33602step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33602step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw33602step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33602 raw33602Labels = mixedMoment B node2199 node2199Labels := by
  calc
    mixedMoment B raw33602 raw33602Labels = mixedMoment B raw33602step0 raw33602step0Labels := by
      have ha : raw33602step0 = (fun i j => raw33602 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33602step0 raw33602; decide +kernel
      have hl : raw33602step0Labels = raw33602Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33602 raw33602Labels permutation188 permutation7
    mixedMoment B raw33602step0 raw33602step0Labels = mixedMoment B raw33602step1 raw33602step1Labels := by
      have ha : raw33602step1 = -raw33602step0 := by apply Matrix.ext; change ∀ i j, raw33602step1 i j = -(raw33602step0 i j); unfold raw33602step1 raw33602step0; decide +kernel
      have hl : raw33602step1Labels = raw33602step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33602step1 raw33602step1Labels = mixedMoment B raw33602step2 raw33602step2Labels := by
      have ha : raw33602step2 = raw33602step1 := by apply Matrix.ext; unfold raw33602step2 raw33602step1; decide +kernel
      have hl : raw33602step1Labels = labelEmbedding1 ∘ raw33602step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33602step1 raw33602step1Labels raw33602step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2199 node2199Labels := by rfl

def raw33603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw33603Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw33603step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33603step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw33603step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33603step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw33603step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33603step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw33603step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33603step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw33603step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33603 raw33603Labels = mixedMoment B node2288 node2288Labels := by
  calc
    mixedMoment B raw33603 raw33603Labels = mixedMoment B raw33603step0 raw33603step0Labels := by
      have hz : ∀ j, raw33603 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33603step0 = (fun i j => raw33603 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33603step0 raw33603; decide +kernel
      have hl : raw33603step0Labels = raw33603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33603 raw33603Labels permutation520 hz
    mixedMoment B raw33603step0 raw33603step0Labels = mixedMoment B raw33603step1 raw33603step1Labels := by
      have hz : ∀ j, raw33603step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33603step1 = (fun i j => raw33603step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33603step1 raw33603step0; decide +kernel
      have hl : raw33603step1Labels = raw33603step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33603step0 raw33603step0Labels permutation80 hz
    mixedMoment B raw33603step1 raw33603step1Labels = mixedMoment B raw33603step2 raw33603step2Labels := by
      have ha : raw33603step2 = (fun i j => raw33603step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33603step2 raw33603step1; decide +kernel
      have hl : raw33603step2Labels = raw33603step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33603step1 raw33603step1Labels permutation8 permutation7
    mixedMoment B raw33603step2 raw33603step2Labels = mixedMoment B raw33603step3 raw33603step3Labels := by
      have ha : raw33603step3 = -raw33603step2 := by apply Matrix.ext; change ∀ i j, raw33603step3 i j = -(raw33603step2 i j); unfold raw33603step3 raw33603step2; decide +kernel
      have hl : raw33603step3Labels = raw33603step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33603step3 raw33603step3Labels = mixedMoment B raw33603step4 raw33603step4Labels := by
      have ha : raw33603step4 = raw33603step3 := by apply Matrix.ext; unfold raw33603step4 raw33603step3; decide +kernel
      have hl : raw33603step3Labels = labelEmbedding1 ∘ raw33603step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33603step3 raw33603step3Labels raw33603step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2288 node2288Labels := by rfl

def raw33604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33604Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw33604step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33604step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33604step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33604step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33604step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33604step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33604 raw33604Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw33604 raw33604Labels = mixedMoment B raw33604step0 raw33604step0Labels := by
      have hz : ∀ j, raw33604 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33604step0 = (fun i j => raw33604 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33604step0 raw33604; decide +kernel
      have hl : raw33604step0Labels = raw33604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33604 raw33604Labels permutation346 hz
    mixedMoment B raw33604step0 raw33604step0Labels = mixedMoment B raw33604step1 raw33604step1Labels := by
      have ha : raw33604step1 = (fun i j => raw33604step0 (permutation45 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33604step1 raw33604step0; decide +kernel
      have hl : raw33604step1Labels = raw33604step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33604step0 raw33604step0Labels permutation45 permutation7
    mixedMoment B raw33604step1 raw33604step1Labels = mixedMoment B raw33604step2 raw33604step2Labels := by
      have ha : raw33604step2 = -raw33604step1 := by apply Matrix.ext; change ∀ i j, raw33604step2 i j = -(raw33604step1 i j); unfold raw33604step2 raw33604step1; decide +kernel
      have hl : raw33604step2Labels = raw33604step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33604step2 raw33604step2Labels = mixedMoment B raw33604step3 raw33604step3Labels := by
      have ha : raw33604step3 = raw33604step2 := by apply Matrix.ext; unfold raw33604step3 raw33604step2; decide +kernel
      have hl : raw33604step2Labels = labelEmbedding1 ∘ raw33604step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33604step2 raw33604step2Labels raw33604step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

def raw33605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33605Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33605step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33605step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw33605step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33605step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw33605step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33605step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw33605step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33605 raw33605Labels = mixedMoment B node2272 node2272Labels := by
  calc
    mixedMoment B raw33605 raw33605Labels = mixedMoment B raw33605step0 raw33605step0Labels := by
      have hz : ∀ j, raw33605 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33605step0 = (fun i j => raw33605 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33605step0 raw33605; decide +kernel
      have hl : raw33605step0Labels = raw33605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33605 raw33605Labels permutation346 hz
    mixedMoment B raw33605step0 raw33605step0Labels = mixedMoment B raw33605step1 raw33605step1Labels := by
      have ha : raw33605step1 = (fun i j => raw33605step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33605step1 raw33605step0; decide +kernel
      have hl : raw33605step1Labels = raw33605step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33605step0 raw33605step0Labels permutation44 permutation7
    mixedMoment B raw33605step1 raw33605step1Labels = mixedMoment B raw33605step2 raw33605step2Labels := by
      have ha : raw33605step2 = -raw33605step1 := by apply Matrix.ext; change ∀ i j, raw33605step2 i j = -(raw33605step1 i j); unfold raw33605step2 raw33605step1; decide +kernel
      have hl : raw33605step2Labels = raw33605step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33605step2 raw33605step2Labels = mixedMoment B raw33605step3 raw33605step3Labels := by
      have ha : raw33605step3 = raw33605step2 := by apply Matrix.ext; unfold raw33605step3 raw33605step2; decide +kernel
      have hl : raw33605step2Labels = labelEmbedding1 ∘ raw33605step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33605step2 raw33605step2Labels raw33605step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2272 node2272Labels := by rfl

def raw33606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33606Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33606step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33606step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33606step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33606step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33606step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33606step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33606 raw33606Labels = mixedMoment B node2211 node2211Labels := by
  calc
    mixedMoment B raw33606 raw33606Labels = mixedMoment B raw33606step0 raw33606step0Labels := by
      have ha : raw33606step0 = (fun i j => raw33606 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33606step0 raw33606; decide +kernel
      have hl : raw33606step0Labels = raw33606Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33606 raw33606Labels permutation188 permutation7
    mixedMoment B raw33606step0 raw33606step0Labels = mixedMoment B raw33606step1 raw33606step1Labels := by
      have ha : raw33606step1 = -raw33606step0 := by apply Matrix.ext; change ∀ i j, raw33606step1 i j = -(raw33606step0 i j); unfold raw33606step1 raw33606step0; decide +kernel
      have hl : raw33606step1Labels = raw33606step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33606step1 raw33606step1Labels = mixedMoment B raw33606step2 raw33606step2Labels := by
      have ha : raw33606step2 = raw33606step1 := by apply Matrix.ext; unfold raw33606step2 raw33606step1; decide +kernel
      have hl : raw33606step1Labels = labelEmbedding1 ∘ raw33606step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33606step1 raw33606step1Labels raw33606step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2211 node2211Labels := by rfl

def raw33607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33607Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33607step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33607step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw33607step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33607step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw33607step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33607step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw33607step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33607 raw33607Labels = mixedMoment B node2274 node2274Labels := by
  calc
    mixedMoment B raw33607 raw33607Labels = mixedMoment B raw33607step0 raw33607step0Labels := by
      have hz : ∀ j, raw33607 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33607step0 = (fun i j => raw33607 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33607step0 raw33607; decide +kernel
      have hl : raw33607step0Labels = raw33607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33607 raw33607Labels permutation346 hz
    mixedMoment B raw33607step0 raw33607step0Labels = mixedMoment B raw33607step1 raw33607step1Labels := by
      have ha : raw33607step1 = (fun i j => raw33607step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33607step1 raw33607step0; decide +kernel
      have hl : raw33607step1Labels = raw33607step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33607step0 raw33607step0Labels permutation44 permutation7
    mixedMoment B raw33607step1 raw33607step1Labels = mixedMoment B raw33607step2 raw33607step2Labels := by
      have ha : raw33607step2 = -raw33607step1 := by apply Matrix.ext; change ∀ i j, raw33607step2 i j = -(raw33607step1 i j); unfold raw33607step2 raw33607step1; decide +kernel
      have hl : raw33607step2Labels = raw33607step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33607step2 raw33607step2Labels = mixedMoment B raw33607step3 raw33607step3Labels := by
      have ha : raw33607step3 = raw33607step2 := by apply Matrix.ext; unfold raw33607step3 raw33607step2; decide +kernel
      have hl : raw33607step2Labels = labelEmbedding1 ∘ raw33607step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33607step2 raw33607step2Labels raw33607step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2274 node2274Labels := by rfl

def raw33608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw33608Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw33608step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33608step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33608step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33608step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33608step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33608step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33608 raw33608Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw33608 raw33608Labels = mixedMoment B raw33608step0 raw33608step0Labels := by
      have hz : ∀ j, raw33608 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33608step0 = (fun i j => raw33608 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33608step0 raw33608; decide +kernel
      have hl : raw33608step0Labels = raw33608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33608 raw33608Labels permutation346 hz
    mixedMoment B raw33608step0 raw33608step0Labels = mixedMoment B raw33608step1 raw33608step1Labels := by
      have ha : raw33608step1 = (fun i j => raw33608step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33608step1 raw33608step0; decide +kernel
      have hl : raw33608step1Labels = raw33608step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33608step0 raw33608step0Labels permutation44 permutation7
    mixedMoment B raw33608step1 raw33608step1Labels = mixedMoment B raw33608step2 raw33608step2Labels := by
      have ha : raw33608step2 = -raw33608step1 := by apply Matrix.ext; change ∀ i j, raw33608step2 i j = -(raw33608step1 i j); unfold raw33608step2 raw33608step1; decide +kernel
      have hl : raw33608step2Labels = raw33608step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33608step2 raw33608step2Labels = mixedMoment B raw33608step3 raw33608step3Labels := by
      have ha : raw33608step3 = raw33608step2 := by apply Matrix.ext; unfold raw33608step3 raw33608step2; decide +kernel
      have hl : raw33608step2Labels = labelEmbedding1 ∘ raw33608step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33608step2 raw33608step2Labels raw33608step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2275 node2275Labels := by rfl

def raw33609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33609Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33609step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33609step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, -2, 3]]
def raw33609step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33609step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]
def raw33609step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33609step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]
def raw33609step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33609 raw33609Labels = mixedMoment B node2256 node2256Labels := by
  calc
    mixedMoment B raw33609 raw33609Labels = mixedMoment B raw33609step0 raw33609step0Labels := by
      have hz : ∀ j, raw33609 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33609step0 = (fun i j => raw33609 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33609step0 raw33609; decide +kernel
      have hl : raw33609step0Labels = raw33609Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33609 raw33609Labels permutation346 hz
    mixedMoment B raw33609step0 raw33609step0Labels = mixedMoment B raw33609step1 raw33609step1Labels := by
      have ha : raw33609step1 = (fun i j => raw33609step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33609step1 raw33609step0; decide +kernel
      have hl : raw33609step1Labels = raw33609step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33609step0 raw33609step0Labels permutation44 permutation7
    mixedMoment B raw33609step1 raw33609step1Labels = mixedMoment B raw33609step2 raw33609step2Labels := by
      have ha : raw33609step2 = -raw33609step1 := by apply Matrix.ext; change ∀ i j, raw33609step2 i j = -(raw33609step1 i j); unfold raw33609step2 raw33609step1; decide +kernel
      have hl : raw33609step2Labels = raw33609step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33609step2 raw33609step2Labels = mixedMoment B raw33609step3 raw33609step3Labels := by
      have ha : raw33609step3 = raw33609step2 := by apply Matrix.ext; unfold raw33609step3 raw33609step2; decide +kernel
      have hl : raw33609step2Labels = labelEmbedding1 ∘ raw33609step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33609step2 raw33609step2Labels raw33609step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2256 node2256Labels := by rfl

def raw33610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33610Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33610step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw33610step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33610step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw33610step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33610step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw33610step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33610 raw33610Labels = mixedMoment B node2198 node2198Labels := by
  calc
    mixedMoment B raw33610 raw33610Labels = mixedMoment B raw33610step0 raw33610step0Labels := by
      have ha : raw33610step0 = (fun i j => raw33610 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33610step0 raw33610; decide +kernel
      have hl : raw33610step0Labels = raw33610Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33610 raw33610Labels permutation188 permutation7
    mixedMoment B raw33610step0 raw33610step0Labels = mixedMoment B raw33610step1 raw33610step1Labels := by
      have ha : raw33610step1 = -raw33610step0 := by apply Matrix.ext; change ∀ i j, raw33610step1 i j = -(raw33610step0 i j); unfold raw33610step1 raw33610step0; decide +kernel
      have hl : raw33610step1Labels = raw33610step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33610step1 raw33610step1Labels = mixedMoment B raw33610step2 raw33610step2Labels := by
      have ha : raw33610step2 = raw33610step1 := by apply Matrix.ext; unfold raw33610step2 raw33610step1; decide +kernel
      have hl : raw33610step1Labels = labelEmbedding1 ∘ raw33610step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33610step1 raw33610step1Labels raw33610step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2198 node2198Labels := by rfl

def raw33611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33611Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw33611step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3]]
def raw33611step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33611step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw33611step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33611step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw33611step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33611 raw33611Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw33611 raw33611Labels = mixedMoment B raw33611step0 raw33611step0Labels := by
      have hz : ∀ j, raw33611 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33611step0 = (fun i j => raw33611 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33611step0 raw33611; decide +kernel
      have hl : raw33611step0Labels = raw33611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33611 raw33611Labels permutation346 hz
    mixedMoment B raw33611step0 raw33611step0Labels = mixedMoment B raw33611step1 raw33611step1Labels := by
      have ha : raw33611step1 = (fun i j => raw33611step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33611step1 raw33611step0; decide +kernel
      have hl : raw33611step1Labels = raw33611step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33611step0 raw33611step0Labels permutation44 permutation7
    mixedMoment B raw33611step1 raw33611step1Labels = mixedMoment B raw33611step2 raw33611step2Labels := by
      have ha : raw33611step2 = -raw33611step1 := by apply Matrix.ext; change ∀ i j, raw33611step2 i j = -(raw33611step1 i j); unfold raw33611step2 raw33611step1; decide +kernel
      have hl : raw33611step2Labels = raw33611step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33611step2 raw33611step2Labels = mixedMoment B raw33611step3 raw33611step3Labels := by
      have ha : raw33611step3 = raw33611step2 := by apply Matrix.ext; unfold raw33611step3 raw33611step2; decide +kernel
      have hl : raw33611step2Labels = labelEmbedding1 ∘ raw33611step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33611step2 raw33611step2Labels raw33611step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2259 node2259Labels := by rfl

def raw33612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw33612Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33612step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33612step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33612step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33612step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw33612step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33612step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw33612step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33612step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw33612step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33612 raw33612Labels = mixedMoment B node2287 node2287Labels := by
  calc
    mixedMoment B raw33612 raw33612Labels = mixedMoment B raw33612step0 raw33612step0Labels := by
      have hz : ∀ j, raw33612 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33612step0 = (fun i j => raw33612 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33612step0 raw33612; decide +kernel
      have hl : raw33612step0Labels = raw33612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33612 raw33612Labels permutation520 hz
    mixedMoment B raw33612step0 raw33612step0Labels = mixedMoment B raw33612step1 raw33612step1Labels := by
      have hz : ∀ j, raw33612step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33612step1 = (fun i j => raw33612step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33612step1 raw33612step0; decide +kernel
      have hl : raw33612step1Labels = raw33612step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33612step0 raw33612step0Labels permutation80 hz
    mixedMoment B raw33612step1 raw33612step1Labels = mixedMoment B raw33612step2 raw33612step2Labels := by
      have ha : raw33612step2 = (fun i j => raw33612step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33612step2 raw33612step1; decide +kernel
      have hl : raw33612step2Labels = raw33612step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33612step1 raw33612step1Labels permutation8 permutation7
    mixedMoment B raw33612step2 raw33612step2Labels = mixedMoment B raw33612step3 raw33612step3Labels := by
      have ha : raw33612step3 = -raw33612step2 := by apply Matrix.ext; change ∀ i j, raw33612step3 i j = -(raw33612step2 i j); unfold raw33612step3 raw33612step2; decide +kernel
      have hl : raw33612step3Labels = raw33612step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33612step3 raw33612step3Labels = mixedMoment B raw33612step4 raw33612step4Labels := by
      have ha : raw33612step4 = raw33612step3 := by apply Matrix.ext; unfold raw33612step4 raw33612step3; decide +kernel
      have hl : raw33612step3Labels = labelEmbedding1 ∘ raw33612step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33612step3 raw33612step3Labels raw33612step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2287 node2287Labels := by rfl

def raw33613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33613Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33613step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3]]
def raw33613step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33613step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw33613step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33613 raw33613Labels = mixedMoment B node3096 node3096Labels := by
  calc
    mixedMoment B raw33613 raw33613Labels = mixedMoment B raw33613step0 raw33613step0Labels := by
      have hz : ∀ j, raw33613 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33613step0 = (fun i j => raw33613 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33613step0 raw33613; decide +kernel
      have hl : raw33613step0Labels = raw33613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33613 raw33613Labels permutation346 hz
    mixedMoment B raw33613step0 raw33613step0Labels = mixedMoment B raw33613step1 raw33613step1Labels := by
      have ha : raw33613step1 = (fun i j => raw33613step0 (permutation67 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33613step1 raw33613step0; decide +kernel
      have hl : raw33613step1Labels = raw33613step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33613step0 raw33613step0Labels permutation67 permutation4
    mixedMoment B raw33613step1 raw33613step1Labels = mixedMoment B raw33613step2 raw33613step2Labels := by
      have ha : raw33613step2 = -raw33613step1 := by apply Matrix.ext; change ∀ i j, raw33613step2 i j = -(raw33613step1 i j); unfold raw33613step2 raw33613step1; decide +kernel
      have hl : raw33613step2Labels = raw33613step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3096 node3096Labels := by rfl

def raw33614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33614Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33614step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33614step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33614 raw33614Labels = mixedMoment B node1822 node1822Labels := by
  calc
    mixedMoment B raw33614 raw33614Labels = mixedMoment B raw33614step0 raw33614step0Labels := by
      have ha : raw33614step0 = (fun i j => raw33614 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33614step0 raw33614; decide +kernel
      have hl : raw33614step0Labels = raw33614Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33614 raw33614Labels permutation154 permutation2
    _ = mixedMoment B node1822 node1822Labels := by rfl

def raw33615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33615Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw33615step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33615step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw33615step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33615 raw33615Labels = mixedMoment B node1827 node1827Labels := by
  calc
    mixedMoment B raw33615 raw33615Labels = mixedMoment B raw33615step0 raw33615step0Labels := by
      have hz : ∀ j, raw33615 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33615step0 = (fun i j => raw33615 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33615step0 raw33615; decide +kernel
      have hl : raw33615step0Labels = raw33615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33615 raw33615Labels permutation346 hz
    mixedMoment B raw33615step0 raw33615step0Labels = mixedMoment B raw33615step1 raw33615step1Labels := by
      have ha : raw33615step1 = (fun i j => raw33615step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33615step1 raw33615step0; decide +kernel
      have hl : raw33615step1Labels = raw33615step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33615step0 raw33615step0Labels permutation34 permutation2
    _ = mixedMoment B node1827 node1827Labels := by rfl

def raw33616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33616step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33616step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33616step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33616step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33616 raw33616Labels = mixedMoment B node4232 node4232Labels := by
  calc
    mixedMoment B raw33616 raw33616Labels = mixedMoment B raw33616step0 raw33616step0Labels := by
      have ha : raw33616step0 = (fun i j => raw33616 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33616step0 raw33616; decide +kernel
      have hl : raw33616step0Labels = raw33616Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33616 raw33616Labels permutation164 permutation3
    mixedMoment B raw33616step0 raw33616step0Labels = mixedMoment B raw33616step1 raw33616step1Labels := by
      have ha : raw33616step1 = raw33616step0 := by apply Matrix.ext; unfold raw33616step1 raw33616step0; decide +kernel
      have hl : raw33616step0Labels = labelEmbedding6 ∘ raw33616step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33616step0 raw33616step0Labels raw33616step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4232 node4232Labels := by rfl

def raw33617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33617step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33617step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33617step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33617step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33617 raw33617Labels = mixedMoment B node4679 node4679Labels := by
  calc
    mixedMoment B raw33617 raw33617Labels = mixedMoment B raw33617step0 raw33617step0Labels := by
      have ha : raw33617step0 = (fun i j => raw33617 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33617step0 raw33617; decide +kernel
      have hl : raw33617step0Labels = raw33617Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33617 raw33617Labels permutation164 permutation3
    mixedMoment B raw33617step0 raw33617step0Labels = mixedMoment B raw33617step1 raw33617step1Labels := by
      have ha : raw33617step1 = raw33617step0 := by apply Matrix.ext; unfold raw33617step1 raw33617step0; decide +kernel
      have hl : raw33617step0Labels = labelEmbedding6 ∘ raw33617step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33617step0 raw33617step0Labels raw33617step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4679 node4679Labels := by rfl

def raw33618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw33618Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33618step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33618step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33618step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33618step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33618step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33618 raw33618Labels = mixedMoment B node4826 node4826Labels := by
  calc
    mixedMoment B raw33618 raw33618Labels = mixedMoment B raw33618step0 raw33618step0Labels := by
      have ha : raw33618step0 = (fun i j => raw33618 (permutation224 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33618step0 raw33618; decide +kernel
      have hl : raw33618step0Labels = raw33618Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33618 raw33618Labels permutation224 permutation5
    mixedMoment B raw33618step0 raw33618step0Labels = mixedMoment B raw33618step1 raw33618step1Labels := by
      have ha : raw33618step1 = -raw33618step0 := by apply Matrix.ext; change ∀ i j, raw33618step1 i j = -(raw33618step0 i j); unfold raw33618step1 raw33618step0; decide +kernel
      have hl : raw33618step1Labels = raw33618step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33618step1 raw33618step1Labels = mixedMoment B raw33618step2 raw33618step2Labels := by
      have ha : raw33618step2 = raw33618step1 := by apply Matrix.ext; unfold raw33618step2 raw33618step1; decide +kernel
      have hl : raw33618step1Labels = labelEmbedding8 ∘ raw33618step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33618step1 raw33618step1Labels raw33618step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4826 node4826Labels := by rfl

def raw33619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33619step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33619step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33619step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33619step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33619 raw33619Labels = mixedMoment B node4864 node4864Labels := by
  calc
    mixedMoment B raw33619 raw33619Labels = mixedMoment B raw33619step0 raw33619step0Labels := by
      have ha : raw33619step0 = (fun i j => raw33619 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33619step0 raw33619; decide +kernel
      have hl : raw33619step0Labels = raw33619Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33619 raw33619Labels permutation168 permutation3
    mixedMoment B raw33619step0 raw33619step0Labels = mixedMoment B raw33619step1 raw33619step1Labels := by
      have ha : raw33619step1 = raw33619step0 := by apply Matrix.ext; unfold raw33619step1 raw33619step0; decide +kernel
      have hl : raw33619step0Labels = labelEmbedding6 ∘ raw33619step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33619step0 raw33619step0Labels raw33619step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4864 node4864Labels := by rfl

def raw33620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33620Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33620step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33620step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33620step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33620step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33620 raw33620Labels = mixedMoment B node4234 node4234Labels := by
  calc
    mixedMoment B raw33620 raw33620Labels = mixedMoment B raw33620step0 raw33620step0Labels := by
      have hz : ∀ j, raw33620 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33620step0 = (fun i j => raw33620 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33620step0 raw33620; decide +kernel
      have hl : raw33620step0Labels = raw33620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33620 raw33620Labels permutation346 hz
    mixedMoment B raw33620step0 raw33620step0Labels = mixedMoment B raw33620step1 raw33620step1Labels := by
      have ha : raw33620step1 = (fun i j => raw33620step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33620step1 raw33620step0; decide +kernel
      have hl : raw33620step1Labels = raw33620step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33620step0 raw33620step0Labels permutation35 permutation3
    mixedMoment B raw33620step1 raw33620step1Labels = mixedMoment B raw33620step2 raw33620step2Labels := by
      have ha : raw33620step2 = raw33620step1 := by apply Matrix.ext; unfold raw33620step2 raw33620step1; decide +kernel
      have hl : raw33620step1Labels = labelEmbedding6 ∘ raw33620step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33620step1 raw33620step1Labels raw33620step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4234 node4234Labels := by rfl

def raw33621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33621Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33621step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33621step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33621step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33621 raw33621Labels = mixedMoment B node4684 node4684Labels := by
  calc
    mixedMoment B raw33621 raw33621Labels = mixedMoment B raw33621step0 raw33621step0Labels := by
      have hz : ∀ j, raw33621 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33621step0 = (fun i j => raw33621 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33621step0 raw33621; decide +kernel
      have hl : raw33621step0Labels = raw33621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33621 raw33621Labels permutation346 hz
    mixedMoment B raw33621step0 raw33621step0Labels = mixedMoment B raw33621step1 raw33621step1Labels := by
      have ha : raw33621step1 = (fun i j => raw33621step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33621step1 raw33621step0; decide +kernel
      have hl : raw33621step1Labels = raw33621step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33621step0 raw33621step0Labels permutation35 permutation3
    mixedMoment B raw33621step1 raw33621step1Labels = mixedMoment B raw33621step2 raw33621step2Labels := by
      have ha : raw33621step2 = raw33621step1 := by apply Matrix.ext; unfold raw33621step2 raw33621step1; decide +kernel
      have hl : raw33621step1Labels = labelEmbedding6 ∘ raw33621step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33621step1 raw33621step1Labels raw33621step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4684 node4684Labels := by rfl

def raw33622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33622Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33622step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33622step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33622step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33622step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33622 raw33622Labels = mixedMoment B node4722 node4722Labels := by
  calc
    mixedMoment B raw33622 raw33622Labels = mixedMoment B raw33622step0 raw33622step0Labels := by
      have ha : raw33622step0 = (fun i j => raw33622 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33622step0 raw33622; decide +kernel
      have hl : raw33622step0Labels = raw33622Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33622 raw33622Labels permutation179 permutation3
    mixedMoment B raw33622step0 raw33622step0Labels = mixedMoment B raw33622step1 raw33622step1Labels := by
      have ha : raw33622step1 = raw33622step0 := by apply Matrix.ext; unfold raw33622step1 raw33622step0; decide +kernel
      have hl : raw33622step0Labels = labelEmbedding6 ∘ raw33622step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33622step0 raw33622step0Labels raw33622step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4722 node4722Labels := by rfl

def raw33623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw33623Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw33623step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33623step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw33623step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33623step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw33623step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33623step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw33623step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33623 raw33623Labels = mixedMoment B node4828 node4828Labels := by
  calc
    mixedMoment B raw33623 raw33623Labels = mixedMoment B raw33623step0 raw33623step0Labels := by
      have hz : ∀ j, raw33623 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33623step0 = (fun i j => raw33623 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33623step0 raw33623; decide +kernel
      have hl : raw33623step0Labels = raw33623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33623 raw33623Labels permutation346 hz
    mixedMoment B raw33623step0 raw33623step0Labels = mixedMoment B raw33623step1 raw33623step1Labels := by
      have ha : raw33623step1 = (fun i j => raw33623step0 (permutation45 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33623step1 raw33623step0; decide +kernel
      have hl : raw33623step1Labels = raw33623step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33623step0 raw33623step0Labels permutation45 permutation5
    mixedMoment B raw33623step1 raw33623step1Labels = mixedMoment B raw33623step2 raw33623step2Labels := by
      have ha : raw33623step2 = -raw33623step1 := by apply Matrix.ext; change ∀ i j, raw33623step2 i j = -(raw33623step1 i j); unfold raw33623step2 raw33623step1; decide +kernel
      have hl : raw33623step2Labels = raw33623step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33623step2 raw33623step2Labels = mixedMoment B raw33623step3 raw33623step3Labels := by
      have ha : raw33623step3 = raw33623step2 := by apply Matrix.ext; unfold raw33623step3 raw33623step2; decide +kernel
      have hl : raw33623step2Labels = labelEmbedding8 ∘ raw33623step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33623step2 raw33623step2Labels raw33623step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4828 node4828Labels := by rfl

def raw33624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33624Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33624step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33624step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33624step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33624step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33624 raw33624Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw33624 raw33624Labels = mixedMoment B raw33624step0 raw33624step0Labels := by
      have hz : ∀ j, raw33624 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33624step0 = (fun i j => raw33624 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33624step0 raw33624; decide +kernel
      have hl : raw33624step0Labels = raw33624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33624 raw33624Labels permutation346 hz
    mixedMoment B raw33624step0 raw33624step0Labels = mixedMoment B raw33624step1 raw33624step1Labels := by
      have ha : raw33624step1 = (fun i j => raw33624step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33624step1 raw33624step0; decide +kernel
      have hl : raw33624step1Labels = raw33624step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33624step0 raw33624step0Labels permutation35 permutation3
    mixedMoment B raw33624step1 raw33624step1Labels = mixedMoment B raw33624step2 raw33624step2Labels := by
      have ha : raw33624step2 = raw33624step1 := by apply Matrix.ext; unfold raw33624step2 raw33624step1; decide +kernel
      have hl : raw33624step1Labels = labelEmbedding6 ∘ raw33624step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33624step1 raw33624step1Labels raw33624step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4865 node4865Labels := by rfl

def raw33625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33625Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33625step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33625step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33625step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33625 raw33625Labels = mixedMoment B node4233 node4233Labels := by
  calc
    mixedMoment B raw33625 raw33625Labels = mixedMoment B raw33625step0 raw33625step0Labels := by
      have hz : ∀ j, raw33625 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33625step0 = (fun i j => raw33625 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33625step0 raw33625; decide +kernel
      have hl : raw33625step0Labels = raw33625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33625 raw33625Labels permutation346 hz
    mixedMoment B raw33625step0 raw33625step0Labels = mixedMoment B raw33625step1 raw33625step1Labels := by
      have ha : raw33625step1 = (fun i j => raw33625step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33625step1 raw33625step0; decide +kernel
      have hl : raw33625step1Labels = raw33625step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33625step0 raw33625step0Labels permutation34 permutation3
    mixedMoment B raw33625step1 raw33625step1Labels = mixedMoment B raw33625step2 raw33625step2Labels := by
      have ha : raw33625step2 = raw33625step1 := by apply Matrix.ext; unfold raw33625step2 raw33625step1; decide +kernel
      have hl : raw33625step1Labels = labelEmbedding6 ∘ raw33625step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33625step1 raw33625step1Labels raw33625step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4233 node4233Labels := by rfl

def raw33626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33626Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33626step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33626step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33626step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33626step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33626 raw33626Labels = mixedMoment B node4681 node4681Labels := by
  calc
    mixedMoment B raw33626 raw33626Labels = mixedMoment B raw33626step0 raw33626step0Labels := by
      have hz : ∀ j, raw33626 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33626step0 = (fun i j => raw33626 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33626step0 raw33626; decide +kernel
      have hl : raw33626step0Labels = raw33626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33626 raw33626Labels permutation346 hz
    mixedMoment B raw33626step0 raw33626step0Labels = mixedMoment B raw33626step1 raw33626step1Labels := by
      have ha : raw33626step1 = (fun i j => raw33626step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33626step1 raw33626step0; decide +kernel
      have hl : raw33626step1Labels = raw33626step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33626step0 raw33626step0Labels permutation34 permutation3
    mixedMoment B raw33626step1 raw33626step1Labels = mixedMoment B raw33626step2 raw33626step2Labels := by
      have ha : raw33626step2 = raw33626step1 := by apply Matrix.ext; unfold raw33626step2 raw33626step1; decide +kernel
      have hl : raw33626step1Labels = labelEmbedding6 ∘ raw33626step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33626step1 raw33626step1Labels raw33626step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4681 node4681Labels := by rfl

def raw33627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33627Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33627step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33627step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33627step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33627step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33627 raw33627Labels = mixedMoment B node4721 node4721Labels := by
  calc
    mixedMoment B raw33627 raw33627Labels = mixedMoment B raw33627step0 raw33627step0Labels := by
      have ha : raw33627step0 = (fun i j => raw33627 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33627step0 raw33627; decide +kernel
      have hl : raw33627step0Labels = raw33627Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33627 raw33627Labels permutation178 permutation3
    mixedMoment B raw33627step0 raw33627step0Labels = mixedMoment B raw33627step1 raw33627step1Labels := by
      have ha : raw33627step1 = raw33627step0 := by apply Matrix.ext; unfold raw33627step1 raw33627step0; decide +kernel
      have hl : raw33627step0Labels = labelEmbedding6 ∘ raw33627step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33627step0 raw33627step0Labels raw33627step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4721 node4721Labels := by rfl

def raw33628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw33628Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw33628step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33628step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw33628step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33628step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw33628step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33628step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw33628step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33628 raw33628Labels = mixedMoment B node4827 node4827Labels := by
  calc
    mixedMoment B raw33628 raw33628Labels = mixedMoment B raw33628step0 raw33628step0Labels := by
      have hz : ∀ j, raw33628 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33628step0 = (fun i j => raw33628 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33628step0 raw33628; decide +kernel
      have hl : raw33628step0Labels = raw33628Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33628 raw33628Labels permutation346 hz
    mixedMoment B raw33628step0 raw33628step0Labels = mixedMoment B raw33628step1 raw33628step1Labels := by
      have ha : raw33628step1 = (fun i j => raw33628step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33628step1 raw33628step0; decide +kernel
      have hl : raw33628step1Labels = raw33628step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33628step0 raw33628step0Labels permutation44 permutation5
    mixedMoment B raw33628step1 raw33628step1Labels = mixedMoment B raw33628step2 raw33628step2Labels := by
      have ha : raw33628step2 = -raw33628step1 := by apply Matrix.ext; change ∀ i j, raw33628step2 i j = -(raw33628step1 i j); unfold raw33628step2 raw33628step1; decide +kernel
      have hl : raw33628step2Labels = raw33628step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33628step2 raw33628step2Labels = mixedMoment B raw33628step3 raw33628step3Labels := by
      have ha : raw33628step3 = raw33628step2 := by apply Matrix.ext; unfold raw33628step3 raw33628step2; decide +kernel
      have hl : raw33628step2Labels = labelEmbedding8 ∘ raw33628step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33628step2 raw33628step2Labels raw33628step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4827 node4827Labels := by rfl

def raw33629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33629Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33629step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33629 raw33629Labels = mixedMoment B node732 node732Labels := by
  calc
    mixedMoment B raw33629 raw33629Labels = mixedMoment B raw33629step0 raw33629step0Labels := by
      have ha : raw33629step0 = (fun i j => raw33629 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33629step0 raw33629; decide +kernel
      have hl : raw33629step0Labels = raw33629Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33629 raw33629Labels permutation164 permutation3
    _ = mixedMoment B node732 node732Labels := by rfl

def raw33630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33630Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33630step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33630 raw33630Labels = mixedMoment B node1805 node1805Labels := by
  calc
    mixedMoment B raw33630 raw33630Labels = mixedMoment B raw33630step0 raw33630step0Labels := by
      have ha : raw33630step0 = (fun i j => raw33630 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33630step0 raw33630; decide +kernel
      have hl : raw33630step0Labels = raw33630Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33630 raw33630Labels permutation164 permutation3
    _ = mixedMoment B node1805 node1805Labels := by rfl

def raw33631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw33631Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33631step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33631 raw33631Labels = mixedMoment B node2077 node2077Labels := by
  calc
    mixedMoment B raw33631 raw33631Labels = mixedMoment B raw33631step0 raw33631step0Labels := by
      have ha : raw33631step0 = (fun i j => raw33631 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33631step0 raw33631; decide +kernel
      have hl : raw33631step0Labels = raw33631Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33631 raw33631Labels permutation164 permutation3
    _ = mixedMoment B node2077 node2077Labels := by rfl

def raw33632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33632Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33632step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33632 raw33632Labels = mixedMoment B node2105 node2105Labels := by
  calc
    mixedMoment B raw33632 raw33632Labels = mixedMoment B raw33632step0 raw33632step0Labels := by
      have ha : raw33632step0 = (fun i j => raw33632 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33632step0 raw33632; decide +kernel
      have hl : raw33632step0Labels = raw33632Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33632 raw33632Labels permutation168 permutation3
    _ = mixedMoment B node2105 node2105Labels := by rfl

def raw33633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33633Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33633step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33633step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33633 raw33633Labels = mixedMoment B node734 node734Labels := by
  calc
    mixedMoment B raw33633 raw33633Labels = mixedMoment B raw33633step0 raw33633step0Labels := by
      have hz : ∀ j, raw33633 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33633step0 = (fun i j => raw33633 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33633step0 raw33633; decide +kernel
      have hl : raw33633step0Labels = raw33633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33633 raw33633Labels permutation346 hz
    mixedMoment B raw33633step0 raw33633step0Labels = mixedMoment B raw33633step1 raw33633step1Labels := by
      have ha : raw33633step1 = (fun i j => raw33633step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33633step1 raw33633step0; decide +kernel
      have hl : raw33633step1Labels = raw33633step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33633step0 raw33633step0Labels permutation35 permutation3
    _ = mixedMoment B node734 node734Labels := by rfl

def raw33634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33634Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33634step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33634 raw33634Labels = mixedMoment B node1810 node1810Labels := by
  calc
    mixedMoment B raw33634 raw33634Labels = mixedMoment B raw33634step0 raw33634step0Labels := by
      have hz : ∀ j, raw33634 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33634step0 = (fun i j => raw33634 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33634step0 raw33634; decide +kernel
      have hl : raw33634step0Labels = raw33634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33634 raw33634Labels permutation346 hz
    mixedMoment B raw33634step0 raw33634step0Labels = mixedMoment B raw33634step1 raw33634step1Labels := by
      have ha : raw33634step1 = (fun i j => raw33634step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33634step1 raw33634step0; decide +kernel
      have hl : raw33634step1Labels = raw33634step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33634step0 raw33634step0Labels permutation35 permutation3
    _ = mixedMoment B node1810 node1810Labels := by rfl

def raw33635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw33635Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33635step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33635step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33635 raw33635Labels = mixedMoment B node1876 node1876Labels := by
  calc
    mixedMoment B raw33635 raw33635Labels = mixedMoment B raw33635step0 raw33635step0Labels := by
      have ha : raw33635step0 = (fun i j => raw33635 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33635step0 raw33635; decide +kernel
      have hl : raw33635step0Labels = raw33635Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33635 raw33635Labels permutation179 permutation3
    _ = mixedMoment B node1876 node1876Labels := by rfl

def raw33636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw33636Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw33636step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33636step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw33636step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33636 raw33636Labels = mixedMoment B node2082 node2082Labels := by
  calc
    mixedMoment B raw33636 raw33636Labels = mixedMoment B raw33636step0 raw33636step0Labels := by
      have hz : ∀ j, raw33636 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33636step0 = (fun i j => raw33636 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33636step0 raw33636; decide +kernel
      have hl : raw33636step0Labels = raw33636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33636 raw33636Labels permutation346 hz
    mixedMoment B raw33636step0 raw33636step0Labels = mixedMoment B raw33636step1 raw33636step1Labels := by
      have ha : raw33636step1 = (fun i j => raw33636step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33636step1 raw33636step0; decide +kernel
      have hl : raw33636step1Labels = raw33636step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33636step0 raw33636step0Labels permutation35 permutation3
    _ = mixedMoment B node2082 node2082Labels := by rfl

def raw33637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33637Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33637step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33637step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33637 raw33637Labels = mixedMoment B node2106 node2106Labels := by
  calc
    mixedMoment B raw33637 raw33637Labels = mixedMoment B raw33637step0 raw33637step0Labels := by
      have hz : ∀ j, raw33637 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33637step0 = (fun i j => raw33637 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33637step0 raw33637; decide +kernel
      have hl : raw33637step0Labels = raw33637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33637 raw33637Labels permutation346 hz
    mixedMoment B raw33637step0 raw33637step0Labels = mixedMoment B raw33637step1 raw33637step1Labels := by
      have ha : raw33637step1 = (fun i j => raw33637step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33637step1 raw33637step0; decide +kernel
      have hl : raw33637step1Labels = raw33637step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33637step0 raw33637step0Labels permutation35 permutation3
    _ = mixedMoment B node2106 node2106Labels := by rfl

def raw33638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33638Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33638step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33638 raw33638Labels = mixedMoment B node733 node733Labels := by
  calc
    mixedMoment B raw33638 raw33638Labels = mixedMoment B raw33638step0 raw33638step0Labels := by
      have hz : ∀ j, raw33638 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33638step0 = (fun i j => raw33638 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33638step0 raw33638; decide +kernel
      have hl : raw33638step0Labels = raw33638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33638 raw33638Labels permutation346 hz
    mixedMoment B raw33638step0 raw33638step0Labels = mixedMoment B raw33638step1 raw33638step1Labels := by
      have ha : raw33638step1 = (fun i j => raw33638step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33638step1 raw33638step0; decide +kernel
      have hl : raw33638step1Labels = raw33638step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33638step0 raw33638step0Labels permutation34 permutation3
    _ = mixedMoment B node733 node733Labels := by rfl

def raw33639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33639Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33639step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33639step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33639 raw33639Labels = mixedMoment B node1807 node1807Labels := by
  calc
    mixedMoment B raw33639 raw33639Labels = mixedMoment B raw33639step0 raw33639step0Labels := by
      have hz : ∀ j, raw33639 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33639step0 = (fun i j => raw33639 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33639step0 raw33639; decide +kernel
      have hl : raw33639step0Labels = raw33639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33639 raw33639Labels permutation346 hz
    mixedMoment B raw33639step0 raw33639step0Labels = mixedMoment B raw33639step1 raw33639step1Labels := by
      have ha : raw33639step1 = (fun i j => raw33639step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33639step1 raw33639step0; decide +kernel
      have hl : raw33639step1Labels = raw33639step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33639step0 raw33639step0Labels permutation34 permutation3
    _ = mixedMoment B node1807 node1807Labels := by rfl

def raw33640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw33640Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33640step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33640step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33640 raw33640Labels = mixedMoment B node1875 node1875Labels := by
  calc
    mixedMoment B raw33640 raw33640Labels = mixedMoment B raw33640step0 raw33640step0Labels := by
      have ha : raw33640step0 = (fun i j => raw33640 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33640step0 raw33640; decide +kernel
      have hl : raw33640step0Labels = raw33640Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33640 raw33640Labels permutation178 permutation3
    _ = mixedMoment B node1875 node1875Labels := by rfl

def raw33641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw33641Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw33641step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33641step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw33641step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33641 raw33641Labels = mixedMoment B node2079 node2079Labels := by
  calc
    mixedMoment B raw33641 raw33641Labels = mixedMoment B raw33641step0 raw33641step0Labels := by
      have hz : ∀ j, raw33641 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33641step0 = (fun i j => raw33641 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33641step0 raw33641; decide +kernel
      have hl : raw33641step0Labels = raw33641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33641 raw33641Labels permutation346 hz
    mixedMoment B raw33641step0 raw33641step0Labels = mixedMoment B raw33641step1 raw33641step1Labels := by
      have ha : raw33641step1 = (fun i j => raw33641step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33641step1 raw33641step0; decide +kernel
      have hl : raw33641step1Labels = raw33641step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33641step0 raw33641step0Labels permutation34 permutation3
    _ = mixedMoment B node2079 node2079Labels := by rfl

def raw33642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33642Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33642step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw33642step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33642step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw33642step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33642step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw33642step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33642 raw33642Labels = mixedMoment B node4462 node4462Labels := by
  calc
    mixedMoment B raw33642 raw33642Labels = mixedMoment B raw33642step0 raw33642step0Labels := by
      have hz : ∀ j, raw33642 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33642step0 = (fun i j => raw33642 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33642step0 raw33642; decide +kernel
      have hl : raw33642step0Labels = raw33642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33642 raw33642Labels permutation346 hz
    mixedMoment B raw33642step0 raw33642step0Labels = mixedMoment B raw33642step1 raw33642step1Labels := by
      have ha : raw33642step1 = (fun i j => raw33642step0 (permutation47 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33642step1 raw33642step0; decide +kernel
      have hl : raw33642step1Labels = raw33642step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33642step0 raw33642step0Labels permutation47 permutation4
    mixedMoment B raw33642step1 raw33642step1Labels = mixedMoment B raw33642step2 raw33642step2Labels := by
      have ha : raw33642step2 = -raw33642step1 := by apply Matrix.ext; change ∀ i j, raw33642step2 i j = -(raw33642step1 i j); unfold raw33642step2 raw33642step1; decide +kernel
      have hl : raw33642step2Labels = raw33642step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33642step2 raw33642step2Labels = mixedMoment B raw33642step3 raw33642step3Labels := by
      have ha : raw33642step3 = raw33642step2 := by apply Matrix.ext; unfold raw33642step3 raw33642step2; decide +kernel
      have hl : raw33642step2Labels = labelEmbedding7 ∘ raw33642step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33642step2 raw33642step2Labels raw33642step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4462 node4462Labels := by rfl

def raw33643 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33643Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33643step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw33643step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33643step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw33643step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33643step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw33643step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33643 raw33643Labels = mixedMoment B node4806 node4806Labels := by
  calc
    mixedMoment B raw33643 raw33643Labels = mixedMoment B raw33643step0 raw33643step0Labels := by
      have ha : raw33643step0 = (fun i j => raw33643 (permutation191 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33643step0 raw33643; decide +kernel
      have hl : raw33643step0Labels = raw33643Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33643 raw33643Labels permutation191 permutation4
    mixedMoment B raw33643step0 raw33643step0Labels = mixedMoment B raw33643step1 raw33643step1Labels := by
      have ha : raw33643step1 = -raw33643step0 := by apply Matrix.ext; change ∀ i j, raw33643step1 i j = -(raw33643step0 i j); unfold raw33643step1 raw33643step0; decide +kernel
      have hl : raw33643step1Labels = raw33643step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33643step1 raw33643step1Labels = mixedMoment B raw33643step2 raw33643step2Labels := by
      have ha : raw33643step2 = raw33643step1 := by apply Matrix.ext; unfold raw33643step2 raw33643step1; decide +kernel
      have hl : raw33643step1Labels = labelEmbedding7 ∘ raw33643step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33643step1 raw33643step1Labels raw33643step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4806 node4806Labels := by rfl

def raw33644 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33644Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33644step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33644step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw33644step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33644step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw33644step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33644 raw33644Labels = mixedMoment B node4879 node4879Labels := by
  calc
    mixedMoment B raw33644 raw33644Labels = mixedMoment B raw33644step0 raw33644step0Labels := by
      have hz : ∀ j, raw33644 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33644step0 = (fun i j => raw33644 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33644step0 raw33644; decide +kernel
      have hl : raw33644step0Labels = raw33644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33644 raw33644Labels permutation346 hz
    mixedMoment B raw33644step0 raw33644step0Labels = mixedMoment B raw33644step1 raw33644step1Labels := by
      have ha : raw33644step1 = (fun i j => raw33644step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33644step1 raw33644step0; decide +kernel
      have hl : raw33644step1Labels = raw33644step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33644step0 raw33644step0Labels permutation32 permutation6
    mixedMoment B raw33644step1 raw33644step1Labels = mixedMoment B raw33644step2 raw33644step2Labels := by
      have ha : raw33644step2 = raw33644step1 := by apply Matrix.ext; unfold raw33644step2 raw33644step1; decide +kernel
      have hl : raw33644step1Labels = labelEmbedding9 ∘ raw33644step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33644step1 raw33644step1Labels raw33644step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4879 node4879Labels := by rfl

def raw33645 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw33645Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw33645step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw33645step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33645step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw33645step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33645step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw33645step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33645 raw33645Labels = mixedMoment B node4870 node4870Labels := by
  calc
    mixedMoment B raw33645 raw33645Labels = mixedMoment B raw33645step0 raw33645step0Labels := by
      have hz : ∀ j, raw33645 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33645step0 = (fun i j => raw33645 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33645step0 raw33645; decide +kernel
      have hl : raw33645step0Labels = raw33645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33645 raw33645Labels permutation346 hz
    mixedMoment B raw33645step0 raw33645step0Labels = mixedMoment B raw33645step1 raw33645step1Labels := by
      have ha : raw33645step1 = (fun i j => raw33645step0 (permutation47 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33645step1 raw33645step0; decide +kernel
      have hl : raw33645step1Labels = raw33645step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33645step0 raw33645step0Labels permutation47 permutation4
    mixedMoment B raw33645step1 raw33645step1Labels = mixedMoment B raw33645step2 raw33645step2Labels := by
      have ha : raw33645step2 = -raw33645step1 := by apply Matrix.ext; change ∀ i j, raw33645step2 i j = -(raw33645step1 i j); unfold raw33645step2 raw33645step1; decide +kernel
      have hl : raw33645step2Labels = raw33645step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33645step2 raw33645step2Labels = mixedMoment B raw33645step3 raw33645step3Labels := by
      have ha : raw33645step3 = raw33645step2 := by apply Matrix.ext; unfold raw33645step3 raw33645step2; decide +kernel
      have hl : raw33645step2Labels = labelEmbedding7 ∘ raw33645step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33645step2 raw33645step2Labels raw33645step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4870 node4870Labels := by rfl

def raw33646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33646Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw33646step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33646step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33646step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33646step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33646step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33646 raw33646Labels = mixedMoment B node4449 node4449Labels := by
  calc
    mixedMoment B raw33646 raw33646Labels = mixedMoment B raw33646step0 raw33646step0Labels := by
      have ha : raw33646step0 = (fun i j => raw33646 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33646step0 raw33646; decide +kernel
      have hl : raw33646step0Labels = raw33646Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33646 raw33646Labels permutation224 permutation4
    mixedMoment B raw33646step0 raw33646step0Labels = mixedMoment B raw33646step1 raw33646step1Labels := by
      have ha : raw33646step1 = -raw33646step0 := by apply Matrix.ext; change ∀ i j, raw33646step1 i j = -(raw33646step0 i j); unfold raw33646step1 raw33646step0; decide +kernel
      have hl : raw33646step1Labels = raw33646step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33646step1 raw33646step1Labels = mixedMoment B raw33646step2 raw33646step2Labels := by
      have ha : raw33646step2 = raw33646step1 := by apply Matrix.ext; unfold raw33646step2 raw33646step1; decide +kernel
      have hl : raw33646step1Labels = labelEmbedding7 ∘ raw33646step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33646step1 raw33646step1Labels raw33646step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4449 node4449Labels := by rfl

def raw33647 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw33647Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33647step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33647step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33647step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33647step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33647 raw33647Labels = mixedMoment B node4849 node4849Labels := by
  calc
    mixedMoment B raw33647 raw33647Labels = mixedMoment B raw33647step0 raw33647step0Labels := by
      have ha : raw33647step0 = (fun i j => raw33647 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33647step0 raw33647; decide +kernel
      have hl : raw33647step0Labels = raw33647Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33647 raw33647Labels permutation154 permutation6
    mixedMoment B raw33647step0 raw33647step0Labels = mixedMoment B raw33647step1 raw33647step1Labels := by
      have ha : raw33647step1 = raw33647step0 := by apply Matrix.ext; unfold raw33647step1 raw33647step0; decide +kernel
      have hl : raw33647step0Labels = labelEmbedding9 ∘ raw33647step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33647step0 raw33647step0Labels raw33647step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4849 node4849Labels := by rfl

def raw33648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33648Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33648step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33648step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw33648step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33648step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw33648step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33648step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw33648step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33648 raw33648Labels = mixedMoment B node4453 node4453Labels := by
  calc
    mixedMoment B raw33648 raw33648Labels = mixedMoment B raw33648step0 raw33648step0Labels := by
      have hz : ∀ j, raw33648 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33648step0 = (fun i j => raw33648 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33648step0 raw33648; decide +kernel
      have hl : raw33648step0Labels = raw33648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33648 raw33648Labels permutation346 hz
    mixedMoment B raw33648step0 raw33648step0Labels = mixedMoment B raw33648step1 raw33648step1Labels := by
      have ha : raw33648step1 = (fun i j => raw33648step0 (permutation45 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33648step1 raw33648step0; decide +kernel
      have hl : raw33648step1Labels = raw33648step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33648step0 raw33648step0Labels permutation45 permutation4
    mixedMoment B raw33648step1 raw33648step1Labels = mixedMoment B raw33648step2 raw33648step2Labels := by
      have ha : raw33648step2 = -raw33648step1 := by apply Matrix.ext; change ∀ i j, raw33648step2 i j = -(raw33648step1 i j); unfold raw33648step2 raw33648step1; decide +kernel
      have hl : raw33648step2Labels = raw33648step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33648step2 raw33648step2Labels = mixedMoment B raw33648step3 raw33648step3Labels := by
      have ha : raw33648step3 = raw33648step2 := by apply Matrix.ext; unfold raw33648step3 raw33648step2; decide +kernel
      have hl : raw33648step2Labels = labelEmbedding7 ∘ raw33648step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33648step2 raw33648step2Labels raw33648step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4453 node4453Labels := by rfl

def raw33649 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33649Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33649step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw33649step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33649step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw33649step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33649 raw33649Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw33649 raw33649Labels = mixedMoment B raw33649step0 raw33649step0Labels := by
      have hz : ∀ j, raw33649 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33649step0 = (fun i j => raw33649 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33649step0 raw33649; decide +kernel
      have hl : raw33649step0Labels = raw33649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33649 raw33649Labels permutation346 hz
    mixedMoment B raw33649step0 raw33649step0Labels = mixedMoment B raw33649step1 raw33649step1Labels := by
      have ha : raw33649step1 = (fun i j => raw33649step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33649step1 raw33649step0; decide +kernel
      have hl : raw33649step1Labels = raw33649step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33649step0 raw33649step0Labels permutation34 permutation6
    mixedMoment B raw33649step1 raw33649step1Labels = mixedMoment B raw33649step2 raw33649step2Labels := by
      have ha : raw33649step2 = raw33649step1 := by apply Matrix.ext; unfold raw33649step2 raw33649step1; decide +kernel
      have hl : raw33649step1Labels = labelEmbedding9 ∘ raw33649step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33649step1 raw33649step1Labels raw33649step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw33650 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33650Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw33650step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33650step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw33650step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33650step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw33650step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33650 raw33650Labels = mixedMoment B node4799 node4799Labels := by
  calc
    mixedMoment B raw33650 raw33650Labels = mixedMoment B raw33650step0 raw33650step0Labels := by
      have ha : raw33650step0 = (fun i j => raw33650 (permutation189 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33650step0 raw33650; decide +kernel
      have hl : raw33650step0Labels = raw33650Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33650 raw33650Labels permutation189 permutation4
    mixedMoment B raw33650step0 raw33650step0Labels = mixedMoment B raw33650step1 raw33650step1Labels := by
      have ha : raw33650step1 = -raw33650step0 := by apply Matrix.ext; change ∀ i j, raw33650step1 i j = -(raw33650step0 i j); unfold raw33650step1 raw33650step0; decide +kernel
      have hl : raw33650step1Labels = raw33650step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33650step1 raw33650step1Labels = mixedMoment B raw33650step2 raw33650step2Labels := by
      have ha : raw33650step2 = raw33650step1 := by apply Matrix.ext; unfold raw33650step2 raw33650step1; decide +kernel
      have hl : raw33650step1Labels = labelEmbedding7 ∘ raw33650step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33650step1 raw33650step1Labels raw33650step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4799 node4799Labels := by rfl

def raw33651 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw33651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw33651step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw33651step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33651step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw33651step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33651step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw33651step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33651 raw33651Labels = mixedMoment B node4861 node4861Labels := by
  calc
    mixedMoment B raw33651 raw33651Labels = mixedMoment B raw33651step0 raw33651step0Labels := by
      have hz : ∀ j, raw33651 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33651step0 = (fun i j => raw33651 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33651step0 raw33651; decide +kernel
      have hl : raw33651step0Labels = raw33651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33651 raw33651Labels permutation346 hz
    mixedMoment B raw33651step0 raw33651step0Labels = mixedMoment B raw33651step1 raw33651step1Labels := by
      have ha : raw33651step1 = (fun i j => raw33651step0 (permutation45 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33651step1 raw33651step0; decide +kernel
      have hl : raw33651step1Labels = raw33651step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33651step0 raw33651step0Labels permutation45 permutation4
    mixedMoment B raw33651step1 raw33651step1Labels = mixedMoment B raw33651step2 raw33651step2Labels := by
      have ha : raw33651step2 = -raw33651step1 := by apply Matrix.ext; change ∀ i j, raw33651step2 i j = -(raw33651step1 i j); unfold raw33651step2 raw33651step1; decide +kernel
      have hl : raw33651step2Labels = raw33651step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33651step2 raw33651step2Labels = mixedMoment B raw33651step3 raw33651step3Labels := by
      have ha : raw33651step3 = raw33651step2 := by apply Matrix.ext; unfold raw33651step3 raw33651step2; decide +kernel
      have hl : raw33651step2Labels = labelEmbedding7 ∘ raw33651step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33651step2 raw33651step2Labels raw33651step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4861 node4861Labels := by rfl

def raw33652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33652step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33652step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33652step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33652step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33652step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33652step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33652 raw33652Labels = mixedMoment B node4452 node4452Labels := by
  calc
    mixedMoment B raw33652 raw33652Labels = mixedMoment B raw33652step0 raw33652step0Labels := by
      have hz : ∀ j, raw33652 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33652step0 = (fun i j => raw33652 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33652step0 raw33652; decide +kernel
      have hl : raw33652step0Labels = raw33652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33652 raw33652Labels permutation346 hz
    mixedMoment B raw33652step0 raw33652step0Labels = mixedMoment B raw33652step1 raw33652step1Labels := by
      have ha : raw33652step1 = (fun i j => raw33652step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33652step1 raw33652step0; decide +kernel
      have hl : raw33652step1Labels = raw33652step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33652step0 raw33652step0Labels permutation44 permutation4
    mixedMoment B raw33652step1 raw33652step1Labels = mixedMoment B raw33652step2 raw33652step2Labels := by
      have ha : raw33652step2 = -raw33652step1 := by apply Matrix.ext; change ∀ i j, raw33652step2 i j = -(raw33652step1 i j); unfold raw33652step2 raw33652step1; decide +kernel
      have hl : raw33652step2Labels = raw33652step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33652step2 raw33652step2Labels = mixedMoment B raw33652step3 raw33652step3Labels := by
      have ha : raw33652step3 = raw33652step2 := by apply Matrix.ext; unfold raw33652step3 raw33652step2; decide +kernel
      have hl : raw33652step2Labels = labelEmbedding7 ∘ raw33652step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33652step2 raw33652step2Labels raw33652step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4452 node4452Labels := by rfl

def raw33653 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33653step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33653step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33653step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33653step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33653step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33653 raw33653Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw33653 raw33653Labels = mixedMoment B raw33653step0 raw33653step0Labels := by
      have hz : ∀ j, raw33653 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33653step0 = (fun i j => raw33653 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33653step0 raw33653; decide +kernel
      have hl : raw33653step0Labels = raw33653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33653 raw33653Labels permutation346 hz
    mixedMoment B raw33653step0 raw33653step0Labels = mixedMoment B raw33653step1 raw33653step1Labels := by
      have ha : raw33653step1 = (fun i j => raw33653step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33653step1 raw33653step0; decide +kernel
      have hl : raw33653step1Labels = raw33653step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33653step0 raw33653step0Labels permutation32 permutation6
    mixedMoment B raw33653step1 raw33653step1Labels = mixedMoment B raw33653step2 raw33653step2Labels := by
      have ha : raw33653step2 = raw33653step1 := by apply Matrix.ext; unfold raw33653step2 raw33653step1; decide +kernel
      have hl : raw33653step1Labels = labelEmbedding9 ∘ raw33653step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33653step1 raw33653step1Labels raw33653step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4865 node4865Labels := by rfl

def raw33654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33654step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-2, 0, 2]]
def raw33654step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33654step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw33654step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33654step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw33654step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33654 raw33654Labels = mixedMoment B node5279 node5279Labels := by
  calc
    mixedMoment B raw33654 raw33654Labels = mixedMoment B raw33654step0 raw33654step0Labels := by
      have hz : ∀ j, raw33654 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33654step0 = (fun i j => raw33654 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33654step0 raw33654; decide +kernel
      have hl : raw33654step0Labels = raw33654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33654 raw33654Labels permutation346 hz
    mixedMoment B raw33654step0 raw33654step0Labels = mixedMoment B raw33654step1 raw33654step1Labels := by
      have ha : raw33654step1 = (fun i j => raw33654step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33654step1 raw33654step0; decide +kernel
      have hl : raw33654step1Labels = raw33654step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33654step0 raw33654step0Labels permutation40 permutation7
    mixedMoment B raw33654step1 raw33654step1Labels = mixedMoment B raw33654step2 raw33654step2Labels := by
      have ha : raw33654step2 = -raw33654step1 := by apply Matrix.ext; change ∀ i j, raw33654step2 i j = -(raw33654step1 i j); unfold raw33654step2 raw33654step1; decide +kernel
      have hl : raw33654step2Labels = raw33654step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33654step2 raw33654step2Labels = mixedMoment B raw33654step3 raw33654step3Labels := by
      have ha : raw33654step3 = raw33654step2 := by apply Matrix.ext; unfold raw33654step3 raw33654step2; decide +kernel
      have hl : raw33654step2Labels = labelEmbedding10 ∘ raw33654step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33654step2 raw33654step2Labels raw33654step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5279 node5279Labels := by rfl

def raw33655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw33655step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33655step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33655step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33655step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33655step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33655 raw33655Labels = mixedMoment B node5249 node5249Labels := by
  calc
    mixedMoment B raw33655 raw33655Labels = mixedMoment B raw33655step0 raw33655step0Labels := by
      have ha : raw33655step0 = (fun i j => raw33655 (permutation184 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33655step0 raw33655; decide +kernel
      have hl : raw33655step0Labels = raw33655Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33655 raw33655Labels permutation184 permutation7
    mixedMoment B raw33655step0 raw33655step0Labels = mixedMoment B raw33655step1 raw33655step1Labels := by
      have ha : raw33655step1 = -raw33655step0 := by apply Matrix.ext; change ∀ i j, raw33655step1 i j = -(raw33655step0 i j); unfold raw33655step1 raw33655step0; decide +kernel
      have hl : raw33655step1Labels = raw33655step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33655step1 raw33655step1Labels = mixedMoment B raw33655step2 raw33655step2Labels := by
      have ha : raw33655step2 = raw33655step1 := by apply Matrix.ext; unfold raw33655step2 raw33655step1; decide +kernel
      have hl : raw33655step1Labels = labelEmbedding10 ∘ raw33655step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33655step1 raw33655step1Labels raw33655step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5249 node5249Labels := by rfl

def raw33656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33656step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33656step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33656step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33656step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw33656step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33656step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33656step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33656step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw33656step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33656 raw33656Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw33656 raw33656Labels = mixedMoment B raw33656step0 raw33656step0Labels := by
      have hz : ∀ j, raw33656 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33656step0 = (fun i j => raw33656 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33656step0 raw33656; decide +kernel
      have hl : raw33656step0Labels = raw33656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33656 raw33656Labels permutation520 hz
    mixedMoment B raw33656step0 raw33656step0Labels = mixedMoment B raw33656step1 raw33656step1Labels := by
      have hz : ∀ j, raw33656step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33656step1 = (fun i j => raw33656step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33656step1 raw33656step0; decide +kernel
      have hl : raw33656step1Labels = raw33656step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33656step0 raw33656step0Labels permutation80 hz
    mixedMoment B raw33656step1 raw33656step1Labels = mixedMoment B raw33656step2 raw33656step2Labels := by
      have ha : raw33656step2 = (fun i j => raw33656step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33656step2 raw33656step1; decide +kernel
      have hl : raw33656step2Labels = raw33656step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33656step1 raw33656step1Labels permutation10 permutation7
    mixedMoment B raw33656step2 raw33656step2Labels = mixedMoment B raw33656step3 raw33656step3Labels := by
      have ha : raw33656step3 = -raw33656step2 := by apply Matrix.ext; change ∀ i j, raw33656step3 i j = -(raw33656step2 i j); unfold raw33656step3 raw33656step2; decide +kernel
      have hl : raw33656step3Labels = raw33656step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33656step3 raw33656step3Labels = mixedMoment B raw33656step4 raw33656step4Labels := by
      have ha : raw33656step4 = raw33656step3 := by apply Matrix.ext; unfold raw33656step4 raw33656step3; decide +kernel
      have hl : raw33656step3Labels = labelEmbedding10 ∘ raw33656step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33656step3 raw33656step3Labels raw33656step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw33657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33657step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw33657step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33657step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw33657step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33657step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw33657step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33657 raw33657Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw33657 raw33657Labels = mixedMoment B raw33657step0 raw33657step0Labels := by
      have hz : ∀ j, raw33657 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33657step0 = (fun i j => raw33657 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33657step0 raw33657; decide +kernel
      have hl : raw33657step0Labels = raw33657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33657 raw33657Labels permutation346 hz
    mixedMoment B raw33657step0 raw33657step0Labels = mixedMoment B raw33657step1 raw33657step1Labels := by
      have ha : raw33657step1 = (fun i j => raw33657step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33657step1 raw33657step0; decide +kernel
      have hl : raw33657step1Labels = raw33657step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33657step0 raw33657step0Labels permutation40 permutation7
    mixedMoment B raw33657step1 raw33657step1Labels = mixedMoment B raw33657step2 raw33657step2Labels := by
      have ha : raw33657step2 = -raw33657step1 := by apply Matrix.ext; change ∀ i j, raw33657step2 i j = -(raw33657step1 i j); unfold raw33657step2 raw33657step1; decide +kernel
      have hl : raw33657step2Labels = raw33657step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33657step2 raw33657step2Labels = mixedMoment B raw33657step3 raw33657step3Labels := by
      have ha : raw33657step3 = raw33657step2 := by apply Matrix.ext; unfold raw33657step3 raw33657step2; decide +kernel
      have hl : raw33657step2Labels = labelEmbedding10 ∘ raw33657step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33657step2 raw33657step2Labels raw33657step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5282 node5282Labels := by rfl

def raw33658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33658 raw33658Labels = mixedMoment B node4695 node4695Labels := by
  calc
    _ = mixedMoment B node4695 node4695Labels := by rfl

def raw33659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33659 raw33659Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw33659 raw33659Labels = mixedMoment B raw33659step0 raw33659step0Labels := by
      have hz : ∀ j, raw33659 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33659step0 = (fun i j => raw33659 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33659step0 raw33659; decide +kernel
      have hl : raw33659step0Labels = raw33659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33659 raw33659Labels permutation520 hz
    _ = mixedMoment B node4865 node4865Labels := by rfl

def raw33660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33660 raw33660Labels = mixedMoment B node4863 node4863Labels := by
  calc
    _ = mixedMoment B node4863 node4863Labels := by rfl

def raw33661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33661Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33661step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33661step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33661 raw33661Labels = mixedMoment B node4700 node4700Labels := by
  calc
    mixedMoment B raw33661 raw33661Labels = mixedMoment B raw33661step0 raw33661step0Labels := by
      have hz : ∀ j, raw33661 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33661step0 = (fun i j => raw33661 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33661step0 raw33661; decide +kernel
      have hl : raw33661step0Labels = raw33661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33661 raw33661Labels permutation346 hz
    mixedMoment B raw33661step0 raw33661step0Labels = mixedMoment B raw33661step1 raw33661step1Labels := by
      have ha : raw33661step1 = (fun i j => raw33661step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33661step1 raw33661step0; decide +kernel
      have hl : raw33661step1Labels = raw33661step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33661step0 raw33661step0Labels permutation34 permutation2
    _ = mixedMoment B node4700 node4700Labels := by rfl

def raw33662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33662step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33662step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33662 raw33662Labels = mixedMoment B node4773 node4773Labels := by
  calc
    mixedMoment B raw33662 raw33662Labels = mixedMoment B raw33662step0 raw33662step0Labels := by
      have ha : raw33662step0 = (fun i j => raw33662 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33662step0 raw33662; decide +kernel
      have hl : raw33662step0Labels = raw33662Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33662 raw33662Labels permutation178 permutation2
    _ = mixedMoment B node4773 node4773Labels := by rfl

def raw33663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33663step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33663step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33663step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33663 raw33663Labels = mixedMoment B node4874 node4874Labels := by
  calc
    mixedMoment B raw33663 raw33663Labels = mixedMoment B raw33663step0 raw33663step0Labels := by
      have hz : ∀ j, raw33663 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33663step0 = (fun i j => raw33663 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33663step0 raw33663; decide +kernel
      have hl : raw33663step0Labels = raw33663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33663 raw33663Labels permutation520 hz
    mixedMoment B raw33663step0 raw33663step0Labels = mixedMoment B raw33663step1 raw33663step1Labels := by
      have hz : ∀ j, raw33663step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33663step1 = (fun i j => raw33663step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33663step1 raw33663step0; decide +kernel
      have hl : raw33663step1Labels = raw33663step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33663step0 raw33663step0Labels permutation80 hz
    _ = mixedMoment B node4874 node4874Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
