import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw12160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12160Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12160step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12160step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12160 raw12160Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw12160 raw12160Labels = mixedMoment B raw12160step0 raw12160step0Labels := by
      have hz : ∀ j, raw12160 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12160step0 = (fun i j => raw12160 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12160step0 raw12160; decide +kernel
      have hl : raw12160step0Labels = raw12160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12160 raw12160Labels permutation346 hz
    mixedMoment B raw12160step0 raw12160step0Labels = mixedMoment B raw12160step1 raw12160step1Labels := by
      have ha : raw12160step1 = (fun i j => raw12160step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12160step1 raw12160step0; decide +kernel
      have hl : raw12160step1Labels = raw12160step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12160step0 raw12160step0Labels permutation40 permutation3
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw12161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12161Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12161step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12161step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12161step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12161 raw12161Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw12161 raw12161Labels = mixedMoment B raw12161step0 raw12161step0Labels := by
      have hz : ∀ j, raw12161 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12161step0 = (fun i j => raw12161 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12161step0 raw12161; decide +kernel
      have hl : raw12161step0Labels = raw12161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12161 raw12161Labels permutation346 hz
    mixedMoment B raw12161step0 raw12161step0Labels = mixedMoment B raw12161step1 raw12161step1Labels := by
      have ha : raw12161step1 = (fun i j => raw12161step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12161step1 raw12161step0; decide +kernel
      have hl : raw12161step1Labels = raw12161step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12161step0 raw12161step0Labels permutation46 permutation3
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw12162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12162Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12162step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12162step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12162 raw12162Labels = mixedMoment B node2766 node2766Labels := by
  calc
    mixedMoment B raw12162 raw12162Labels = mixedMoment B raw12162step0 raw12162step0Labels := by
      have hz : ∀ j, raw12162 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12162step0 = (fun i j => raw12162 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12162step0 raw12162; decide +kernel
      have hl : raw12162step0Labels = raw12162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12162 raw12162Labels permutation346 hz
    mixedMoment B raw12162step0 raw12162step0Labels = mixedMoment B raw12162step1 raw12162step1Labels := by
      have ha : raw12162step1 = (fun i j => raw12162step0 (permutation53 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12162step1 raw12162step0; decide +kernel
      have hl : raw12162step1Labels = raw12162step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12162step0 raw12162step0Labels permutation53 permutation3
    _ = mixedMoment B node2766 node2766Labels := by rfl

def raw12163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12163Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12163step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12163step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12163 raw12163Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw12163 raw12163Labels = mixedMoment B raw12163step0 raw12163step0Labels := by
      have hz : ∀ j, raw12163 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12163step0 = (fun i j => raw12163 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12163step0 raw12163; decide +kernel
      have hl : raw12163step0Labels = raw12163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12163 raw12163Labels permutation265 hz
    mixedMoment B raw12163step0 raw12163step0Labels = mixedMoment B raw12163step1 raw12163step1Labels := by
      have ha : raw12163step1 = (fun i j => raw12163step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12163step1 raw12163step0; decide +kernel
      have hl : raw12163step1Labels = raw12163step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12163step0 raw12163step0Labels permutation40 permutation3
    _ = mixedMoment B node1079 node1079Labels := by rfl

def raw12164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12164Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12164step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12164step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12164 raw12164Labels = mixedMoment B node2508 node2508Labels := by
  calc
    mixedMoment B raw12164 raw12164Labels = mixedMoment B raw12164step0 raw12164step0Labels := by
      have ha : raw12164step0 = (fun i j => raw12164 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12164step0 raw12164; decide +kernel
      have hl : raw12164step0Labels = raw12164Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12164 raw12164Labels permutation160 permutation3
    _ = mixedMoment B node2508 node2508Labels := by rfl

def raw12165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12165Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12165step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12165step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12165 raw12165Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw12165 raw12165Labels = mixedMoment B raw12165step0 raw12165step0Labels := by
      have hz : ∀ j, raw12165 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12165step0 = (fun i j => raw12165 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12165step0 raw12165; decide +kernel
      have hl : raw12165step0Labels = raw12165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12165 raw12165Labels permutation265 hz
    mixedMoment B raw12165step0 raw12165step0Labels = mixedMoment B raw12165step1 raw12165step1Labels := by
      have ha : raw12165step1 = (fun i j => raw12165step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12165step1 raw12165step0; decide +kernel
      have hl : raw12165step1Labels = raw12165step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12165step0 raw12165step0Labels permutation40 permutation3
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw12166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12166Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12166step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12166step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12166step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12166 raw12166Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw12166 raw12166Labels = mixedMoment B raw12166step0 raw12166step0Labels := by
      have hz : ∀ j, raw12166 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12166step0 = (fun i j => raw12166 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12166step0 raw12166; decide +kernel
      have hl : raw12166step0Labels = raw12166Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12166 raw12166Labels permutation265 hz
    mixedMoment B raw12166step0 raw12166step0Labels = mixedMoment B raw12166step1 raw12166step1Labels := by
      have ha : raw12166step1 = (fun i j => raw12166step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12166step1 raw12166step0; decide +kernel
      have hl : raw12166step1Labels = raw12166step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12166step0 raw12166step0Labels permutation46 permutation3
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw12167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12167Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12167step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12167step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12167 raw12167Labels = mixedMoment B node2766 node2766Labels := by
  calc
    mixedMoment B raw12167 raw12167Labels = mixedMoment B raw12167step0 raw12167step0Labels := by
      have hz : ∀ j, raw12167 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12167step0 = (fun i j => raw12167 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12167step0 raw12167; decide +kernel
      have hl : raw12167step0Labels = raw12167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12167 raw12167Labels permutation265 hz
    mixedMoment B raw12167step0 raw12167step0Labels = mixedMoment B raw12167step1 raw12167step1Labels := by
      have ha : raw12167step1 = (fun i j => raw12167step0 (permutation53 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12167step1 raw12167step0; decide +kernel
      have hl : raw12167step1Labels = raw12167step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12167step0 raw12167step0Labels permutation53 permutation3
    _ = mixedMoment B node2766 node2766Labels := by rfl

def raw12168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12168Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12168step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12168step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12168step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12168step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12168step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12168 raw12168Labels = mixedMoment B node1083 node1083Labels := by
  calc
    mixedMoment B raw12168 raw12168Labels = mixedMoment B raw12168step0 raw12168step0Labels := by
      have hz : ∀ j, raw12168 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12168step0 = (fun i j => raw12168 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12168step0 raw12168; decide +kernel
      have hl : raw12168step0Labels = raw12168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12168 raw12168Labels permutation346 hz
    mixedMoment B raw12168step0 raw12168step0Labels = mixedMoment B raw12168step1 raw12168step1Labels := by
      have hz : ∀ j, raw12168step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12168step1 = (fun i j => raw12168step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12168step1 raw12168step0; decide +kernel
      have hl : raw12168step1Labels = raw12168step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12168step0 raw12168step0Labels permutation56 hz
    mixedMoment B raw12168step1 raw12168step1Labels = mixedMoment B raw12168step2 raw12168step2Labels := by
      have ha : raw12168step2 = (fun i j => raw12168step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12168step2 raw12168step1; decide +kernel
      have hl : raw12168step2Labels = raw12168step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12168step1 raw12168step1Labels permutation11 permutation3
    _ = mixedMoment B node1083 node1083Labels := by rfl

def raw12169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12169Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12169step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12169step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12169 raw12169Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw12169 raw12169Labels = mixedMoment B raw12169step0 raw12169step0Labels := by
      have hz : ∀ j, raw12169 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12169step0 = (fun i j => raw12169 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12169step0 raw12169; decide +kernel
      have hl : raw12169step0Labels = raw12169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12169 raw12169Labels permutation346 hz
    mixedMoment B raw12169step0 raw12169step0Labels = mixedMoment B raw12169step1 raw12169step1Labels := by
      have ha : raw12169step1 = (fun i j => raw12169step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12169step1 raw12169step0; decide +kernel
      have hl : raw12169step1Labels = raw12169step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12169step0 raw12169step0Labels permutation35 permutation3
    _ = mixedMoment B node2512 node2512Labels := by rfl

def raw12170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12170Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw12170step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12170step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12170 raw12170Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw12170 raw12170Labels = mixedMoment B raw12170step0 raw12170step0Labels := by
      have hz : ∀ j, raw12170 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12170step0 = (fun i j => raw12170 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12170step0 raw12170; decide +kernel
      have hl : raw12170step0Labels = raw12170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12170 raw12170Labels permutation265 hz
    mixedMoment B raw12170step0 raw12170step0Labels = mixedMoment B raw12170step1 raw12170step1Labels := by
      have ha : raw12170step1 = (fun i j => raw12170step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12170step1 raw12170step0; decide +kernel
      have hl : raw12170step1Labels = raw12170step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12170step0 raw12170step0Labels permutation35 permutation3
    _ = mixedMoment B node2512 node2512Labels := by rfl

def raw12171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12171Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12171step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12171step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw12171step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12171step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12171step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12171 raw12171Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw12171 raw12171Labels = mixedMoment B raw12171step0 raw12171step0Labels := by
      have hz : ∀ j, raw12171 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12171step0 = (fun i j => raw12171 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12171step0 raw12171; decide +kernel
      have hl : raw12171step0Labels = raw12171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12171 raw12171Labels permutation346 hz
    mixedMoment B raw12171step0 raw12171step0Labels = mixedMoment B raw12171step1 raw12171step1Labels := by
      have hz : ∀ j, raw12171step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12171step1 = (fun i j => raw12171step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12171step1 raw12171step0; decide +kernel
      have hl : raw12171step1Labels = raw12171step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12171step0 raw12171step0Labels permutation56 hz
    mixedMoment B raw12171step1 raw12171step1Labels = mixedMoment B raw12171step2 raw12171step2Labels := by
      have ha : raw12171step2 = (fun i j => raw12171step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12171step2 raw12171step1; decide +kernel
      have hl : raw12171step2Labels = raw12171step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12171step1 raw12171step1Labels permutation11 permutation3
    _ = mixedMoment B node2743 node2743Labels := by rfl

def raw12172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12172Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12172step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12172step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw12172step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12172step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12172step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12172 raw12172Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw12172 raw12172Labels = mixedMoment B raw12172step0 raw12172step0Labels := by
      have hz : ∀ j, raw12172 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12172step0 = (fun i j => raw12172 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12172step0 raw12172; decide +kernel
      have hl : raw12172step0Labels = raw12172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12172 raw12172Labels permutation346 hz
    mixedMoment B raw12172step0 raw12172step0Labels = mixedMoment B raw12172step1 raw12172step1Labels := by
      have hz : ∀ j, raw12172step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12172step1 = (fun i j => raw12172step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12172step1 raw12172step0; decide +kernel
      have hl : raw12172step1Labels = raw12172step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12172step0 raw12172step0Labels permutation56 hz
    mixedMoment B raw12172step1 raw12172step1Labels = mixedMoment B raw12172step2 raw12172step2Labels := by
      have ha : raw12172step2 = (fun i j => raw12172step1 (permutation13 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12172step2 raw12172step1; decide +kernel
      have hl : raw12172step2Labels = raw12172step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12172step1 raw12172step1Labels permutation13 permutation3
    _ = mixedMoment B node2767 node2767Labels := by rfl

def raw12173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12173Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12173step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12173step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12173step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12173step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12173step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12173 raw12173Labels = mixedMoment B node1083 node1083Labels := by
  calc
    mixedMoment B raw12173 raw12173Labels = mixedMoment B raw12173step0 raw12173step0Labels := by
      have hz : ∀ j, raw12173 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12173step0 = (fun i j => raw12173 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12173step0 raw12173; decide +kernel
      have hl : raw12173step0Labels = raw12173Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12173 raw12173Labels permutation346 hz
    mixedMoment B raw12173step0 raw12173step0Labels = mixedMoment B raw12173step1 raw12173step1Labels := by
      have hz : ∀ j, raw12173step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12173step1 = (fun i j => raw12173step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12173step1 raw12173step0; decide +kernel
      have hl : raw12173step1Labels = raw12173step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12173step0 raw12173step0Labels permutation56 hz
    mixedMoment B raw12173step1 raw12173step1Labels = mixedMoment B raw12173step2 raw12173step2Labels := by
      have ha : raw12173step2 = (fun i j => raw12173step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12173step2 raw12173step1; decide +kernel
      have hl : raw12173step2Labels = raw12173step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12173step1 raw12173step1Labels permutation9 permutation3
    _ = mixedMoment B node1083 node1083Labels := by rfl

def raw12174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12174Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12174step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12174step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12174 raw12174Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw12174 raw12174Labels = mixedMoment B raw12174step0 raw12174step0Labels := by
      have hz : ∀ j, raw12174 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12174step0 = (fun i j => raw12174 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12174step0 raw12174; decide +kernel
      have hl : raw12174step0Labels = raw12174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12174 raw12174Labels permutation346 hz
    mixedMoment B raw12174step0 raw12174step0Labels = mixedMoment B raw12174step1 raw12174step1Labels := by
      have ha : raw12174step1 = (fun i j => raw12174step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12174step1 raw12174step0; decide +kernel
      have hl : raw12174step1Labels = raw12174step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12174step0 raw12174step0Labels permutation33 permutation3
    _ = mixedMoment B node2512 node2512Labels := by rfl

def raw12175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12175Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12175step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw12175step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12175 raw12175Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw12175 raw12175Labels = mixedMoment B raw12175step0 raw12175step0Labels := by
      have hz : ∀ j, raw12175 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12175step0 = (fun i j => raw12175 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12175step0 raw12175; decide +kernel
      have hl : raw12175step0Labels = raw12175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12175 raw12175Labels permutation265 hz
    mixedMoment B raw12175step0 raw12175step0Labels = mixedMoment B raw12175step1 raw12175step1Labels := by
      have ha : raw12175step1 = (fun i j => raw12175step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12175step1 raw12175step0; decide +kernel
      have hl : raw12175step1Labels = raw12175step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12175step0 raw12175step0Labels permutation33 permutation3
    _ = mixedMoment B node2512 node2512Labels := by rfl

def raw12176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12176Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12176step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12176step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw12176step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12176step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12176step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12176 raw12176Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw12176 raw12176Labels = mixedMoment B raw12176step0 raw12176step0Labels := by
      have hz : ∀ j, raw12176 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12176step0 = (fun i j => raw12176 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12176step0 raw12176; decide +kernel
      have hl : raw12176step0Labels = raw12176Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12176 raw12176Labels permutation346 hz
    mixedMoment B raw12176step0 raw12176step0Labels = mixedMoment B raw12176step1 raw12176step1Labels := by
      have hz : ∀ j, raw12176step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12176step1 = (fun i j => raw12176step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12176step1 raw12176step0; decide +kernel
      have hl : raw12176step1Labels = raw12176step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12176step0 raw12176step0Labels permutation56 hz
    mixedMoment B raw12176step1 raw12176step1Labels = mixedMoment B raw12176step2 raw12176step2Labels := by
      have ha : raw12176step2 = (fun i j => raw12176step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12176step2 raw12176step1; decide +kernel
      have hl : raw12176step2Labels = raw12176step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12176step1 raw12176step1Labels permutation9 permutation3
    _ = mixedMoment B node2743 node2743Labels := by rfl

def raw12177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw12177Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw12177step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12177step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw12177step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12177step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12177step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12177 raw12177Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw12177 raw12177Labels = mixedMoment B raw12177step0 raw12177step0Labels := by
      have hz : ∀ j, raw12177 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12177step0 = (fun i j => raw12177 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12177step0 raw12177; decide +kernel
      have hl : raw12177step0Labels = raw12177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12177 raw12177Labels permutation346 hz
    mixedMoment B raw12177step0 raw12177step0Labels = mixedMoment B raw12177step1 raw12177step1Labels := by
      have hz : ∀ j, raw12177step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12177step1 = (fun i j => raw12177step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12177step1 raw12177step0; decide +kernel
      have hl : raw12177step1Labels = raw12177step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12177step0 raw12177step0Labels permutation56 hz
    mixedMoment B raw12177step1 raw12177step1Labels = mixedMoment B raw12177step2 raw12177step2Labels := by
      have ha : raw12177step2 = (fun i j => raw12177step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12177step2 raw12177step1; decide +kernel
      have hl : raw12177step2Labels = raw12177step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12177step1 raw12177step1Labels permutation12 permutation3
    _ = mixedMoment B node2767 node2767Labels := by rfl

def raw12178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12178Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12178step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12178step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12178step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12178step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw12178step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12178 raw12178Labels = mixedMoment B node1080 node1080Labels := by
  calc
    mixedMoment B raw12178 raw12178Labels = mixedMoment B raw12178step0 raw12178step0Labels := by
      have hz : ∀ j, raw12178 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12178step0 = (fun i j => raw12178 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12178step0 raw12178; decide +kernel
      have hl : raw12178step0Labels = raw12178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12178 raw12178Labels permutation346 hz
    mixedMoment B raw12178step0 raw12178step0Labels = mixedMoment B raw12178step1 raw12178step1Labels := by
      have hz : ∀ j, raw12178step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12178step1 = (fun i j => raw12178step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12178step1 raw12178step0; decide +kernel
      have hl : raw12178step1Labels = raw12178step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12178step0 raw12178step0Labels permutation56 hz
    mixedMoment B raw12178step1 raw12178step1Labels = mixedMoment B raw12178step2 raw12178step2Labels := by
      have ha : raw12178step2 = (fun i j => raw12178step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12178step2 raw12178step1; decide +kernel
      have hl : raw12178step2Labels = raw12178step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12178step1 raw12178step1Labels permutation8 permutation3
    _ = mixedMoment B node1080 node1080Labels := by rfl

def raw12179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12179Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12179step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12179step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw12179step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12179 raw12179Labels = mixedMoment B node2509 node2509Labels := by
  calc
    mixedMoment B raw12179 raw12179Labels = mixedMoment B raw12179step0 raw12179step0Labels := by
      have hz : ∀ j, raw12179 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12179step0 = (fun i j => raw12179 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12179step0 raw12179; decide +kernel
      have hl : raw12179step0Labels = raw12179Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12179 raw12179Labels permutation346 hz
    mixedMoment B raw12179step0 raw12179step0Labels = mixedMoment B raw12179step1 raw12179step1Labels := by
      have ha : raw12179step1 = (fun i j => raw12179step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12179step1 raw12179step0; decide +kernel
      have hl : raw12179step1Labels = raw12179step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12179step0 raw12179step0Labels permutation32 permutation3
    _ = mixedMoment B node2509 node2509Labels := by rfl

def raw12180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12180Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12180step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw12180step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12180 raw12180Labels = mixedMoment B node2509 node2509Labels := by
  calc
    mixedMoment B raw12180 raw12180Labels = mixedMoment B raw12180step0 raw12180step0Labels := by
      have hz : ∀ j, raw12180 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12180step0 = (fun i j => raw12180 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12180step0 raw12180; decide +kernel
      have hl : raw12180step0Labels = raw12180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12180 raw12180Labels permutation265 hz
    mixedMoment B raw12180step0 raw12180step0Labels = mixedMoment B raw12180step1 raw12180step1Labels := by
      have ha : raw12180step1 = (fun i j => raw12180step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12180step1 raw12180step0; decide +kernel
      have hl : raw12180step1Labels = raw12180step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12180step0 raw12180step0Labels permutation32 permutation3
    _ = mixedMoment B node2509 node2509Labels := by rfl

def raw12181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12181Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12181step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12181step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12181step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12181step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12181step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12181 raw12181Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw12181 raw12181Labels = mixedMoment B raw12181step0 raw12181step0Labels := by
      have hz : ∀ j, raw12181 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12181step0 = (fun i j => raw12181 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12181step0 raw12181; decide +kernel
      have hl : raw12181step0Labels = raw12181Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12181 raw12181Labels permutation346 hz
    mixedMoment B raw12181step0 raw12181step0Labels = mixedMoment B raw12181step1 raw12181step1Labels := by
      have hz : ∀ j, raw12181step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12181step1 = (fun i j => raw12181step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12181step1 raw12181step0; decide +kernel
      have hl : raw12181step1Labels = raw12181step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12181step0 raw12181step0Labels permutation56 hz
    mixedMoment B raw12181step1 raw12181step1Labels = mixedMoment B raw12181step2 raw12181step2Labels := by
      have ha : raw12181step2 = (fun i j => raw12181step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12181step2 raw12181step1; decide +kernel
      have hl : raw12181step2Labels = raw12181step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12181step1 raw12181step1Labels permutation8 permutation3
    _ = mixedMoment B node2740 node2740Labels := by rfl

def raw12182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw12182Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw12182step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12182step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw12182step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12182step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12182step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12182 raw12182Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw12182 raw12182Labels = mixedMoment B raw12182step0 raw12182step0Labels := by
      have hz : ∀ j, raw12182 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12182step0 = (fun i j => raw12182 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12182step0 raw12182; decide +kernel
      have hl : raw12182step0Labels = raw12182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12182 raw12182Labels permutation346 hz
    mixedMoment B raw12182step0 raw12182step0Labels = mixedMoment B raw12182step1 raw12182step1Labels := by
      have hz : ∀ j, raw12182step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12182step1 = (fun i j => raw12182step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12182step1 raw12182step0; decide +kernel
      have hl : raw12182step1Labels = raw12182step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12182step0 raw12182step0Labels permutation56 hz
    mixedMoment B raw12182step1 raw12182step1Labels = mixedMoment B raw12182step2 raw12182step2Labels := by
      have ha : raw12182step2 = (fun i j => raw12182step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12182step2 raw12182step1; decide +kernel
      have hl : raw12182step2Labels = raw12182step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12182step1 raw12182step1Labels permutation10 permutation3
    _ = mixedMoment B node2740 node2740Labels := by rfl

def raw12183 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12183Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12183step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12183step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12183step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12183step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12183 raw12183Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw12183 raw12183Labels = mixedMoment B raw12183step0 raw12183step0Labels := by
      have hz : ∀ j, raw12183 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12183step0 = (fun i j => raw12183 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12183step0 raw12183; decide +kernel
      have hl : raw12183step0Labels = raw12183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12183 raw12183Labels permutation265 hz
    mixedMoment B raw12183step0 raw12183step0Labels = mixedMoment B raw12183step1 raw12183step1Labels := by
      have ha : raw12183step1 = (fun i j => raw12183step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12183step1 raw12183step0; decide +kernel
      have hl : raw12183step1Labels = raw12183step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12183step0 raw12183step0Labels permutation36 permutation7
    mixedMoment B raw12183step1 raw12183step1Labels = mixedMoment B raw12183step2 raw12183step2Labels := by
      have ha : raw12183step2 = raw12183step1 := by apply Matrix.ext; unfold raw12183step2 raw12183step1; decide +kernel
      have hl : raw12183step1Labels = labelEmbedding10 ∘ raw12183step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12183step1 raw12183step1Labels raw12183step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw12184 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12184Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12184step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12184step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12184step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12184step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12184step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12184step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12184step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12184 raw12184Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw12184 raw12184Labels = mixedMoment B raw12184step0 raw12184step0Labels := by
      have hz : ∀ j, raw12184 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12184step0 = (fun i j => raw12184 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12184step0 raw12184; decide +kernel
      have hl : raw12184step0Labels = raw12184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12184 raw12184Labels permutation346 hz
    mixedMoment B raw12184step0 raw12184step0Labels = mixedMoment B raw12184step1 raw12184step1Labels := by
      have hz : ∀ j, raw12184step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12184step1 = (fun i j => raw12184step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12184step1 raw12184step0; decide +kernel
      have hl : raw12184step1Labels = raw12184step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12184step0 raw12184step0Labels permutation56 hz
    mixedMoment B raw12184step1 raw12184step1Labels = mixedMoment B raw12184step2 raw12184step2Labels := by
      have ha : raw12184step2 = (fun i j => raw12184step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12184step2 raw12184step1; decide +kernel
      have hl : raw12184step2Labels = raw12184step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12184step1 raw12184step1Labels permutation13 permutation7
    mixedMoment B raw12184step2 raw12184step2Labels = mixedMoment B raw12184step3 raw12184step3Labels := by
      have ha : raw12184step3 = raw12184step2 := by apply Matrix.ext; unfold raw12184step3 raw12184step2; decide +kernel
      have hl : raw12184step2Labels = labelEmbedding10 ∘ raw12184step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12184step2 raw12184step2Labels raw12184step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw12185 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12185Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12185step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12185step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12185step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12185step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12185step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12185step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12185step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12185 raw12185Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw12185 raw12185Labels = mixedMoment B raw12185step0 raw12185step0Labels := by
      have hz : ∀ j, raw12185 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12185step0 = (fun i j => raw12185 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12185step0 raw12185; decide +kernel
      have hl : raw12185step0Labels = raw12185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12185 raw12185Labels permutation346 hz
    mixedMoment B raw12185step0 raw12185step0Labels = mixedMoment B raw12185step1 raw12185step1Labels := by
      have hz : ∀ j, raw12185step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12185step1 = (fun i j => raw12185step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12185step1 raw12185step0; decide +kernel
      have hl : raw12185step1Labels = raw12185step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12185step0 raw12185step0Labels permutation56 hz
    mixedMoment B raw12185step1 raw12185step1Labels = mixedMoment B raw12185step2 raw12185step2Labels := by
      have ha : raw12185step2 = (fun i j => raw12185step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12185step2 raw12185step1; decide +kernel
      have hl : raw12185step2Labels = raw12185step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12185step1 raw12185step1Labels permutation12 permutation7
    mixedMoment B raw12185step2 raw12185step2Labels = mixedMoment B raw12185step3 raw12185step3Labels := by
      have ha : raw12185step3 = raw12185step2 := by apply Matrix.ext; unfold raw12185step3 raw12185step2; decide +kernel
      have hl : raw12185step2Labels = labelEmbedding10 ∘ raw12185step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12185step2 raw12185step2Labels raw12185step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw12186 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12186Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12186step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12186step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12186step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12186step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12186step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12186step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12186step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12186 raw12186Labels = mixedMoment B node5307 node5307Labels := by
  calc
    mixedMoment B raw12186 raw12186Labels = mixedMoment B raw12186step0 raw12186step0Labels := by
      have hz : ∀ j, raw12186 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12186step0 = (fun i j => raw12186 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12186step0 raw12186; decide +kernel
      have hl : raw12186step0Labels = raw12186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12186 raw12186Labels permutation346 hz
    mixedMoment B raw12186step0 raw12186step0Labels = mixedMoment B raw12186step1 raw12186step1Labels := by
      have hz : ∀ j, raw12186step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12186step1 = (fun i j => raw12186step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12186step1 raw12186step0; decide +kernel
      have hl : raw12186step1Labels = raw12186step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12186step0 raw12186step0Labels permutation56 hz
    mixedMoment B raw12186step1 raw12186step1Labels = mixedMoment B raw12186step2 raw12186step2Labels := by
      have ha : raw12186step2 = (fun i j => raw12186step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12186step2 raw12186step1; decide +kernel
      have hl : raw12186step2Labels = raw12186step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12186step1 raw12186step1Labels permutation12 permutation7
    mixedMoment B raw12186step2 raw12186step2Labels = mixedMoment B raw12186step3 raw12186step3Labels := by
      have ha : raw12186step3 = raw12186step2 := by apply Matrix.ext; unfold raw12186step3 raw12186step2; decide +kernel
      have hl : raw12186step2Labels = labelEmbedding10 ∘ raw12186step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12186step2 raw12186step2Labels raw12186step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5307 node5307Labels := by rfl

def raw12187 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12187Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12187step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12187step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw12187step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12187step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12187step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12187step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12187step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12187 raw12187Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw12187 raw12187Labels = mixedMoment B raw12187step0 raw12187step0Labels := by
      have hz : ∀ j, raw12187 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12187step0 = (fun i j => raw12187 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12187step0 raw12187; decide +kernel
      have hl : raw12187step0Labels = raw12187Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12187 raw12187Labels permutation346 hz
    mixedMoment B raw12187step0 raw12187step0Labels = mixedMoment B raw12187step1 raw12187step1Labels := by
      have ha : raw12187step1 = (fun i j => raw12187step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12187step1 raw12187step0; decide +kernel
      have hl : raw12187step1Labels = raw12187step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12187step0 raw12187step0Labels permutation40 permutation4
    mixedMoment B raw12187step1 raw12187step1Labels = mixedMoment B raw12187step2 raw12187step2Labels := by
      have ha : raw12187step2 = -raw12187step1 := by apply Matrix.ext; change ∀ i j, raw12187step2 i j = -(raw12187step1 i j); unfold raw12187step2 raw12187step1; decide +kernel
      have hl : raw12187step2Labels = raw12187step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12187step2 raw12187step2Labels = mixedMoment B raw12187step3 raw12187step3Labels := by
      have ha : raw12187step3 = raw12187step2 := by apply Matrix.ext; unfold raw12187step3 raw12187step2; decide +kernel
      have hl : raw12187step2Labels = labelEmbedding7 ∘ raw12187step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12187step2 raw12187step2Labels raw12187step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw12188 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12188Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12188step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12188step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12188step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12188step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12188 raw12188Labels = mixedMoment B node5256 node5256Labels := by
  calc
    mixedMoment B raw12188 raw12188Labels = mixedMoment B raw12188step0 raw12188step0Labels := by
      have ha : raw12188step0 = (fun i j => raw12188 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12188step0 raw12188; decide +kernel
      have hl : raw12188step0Labels = raw12188Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12188 raw12188Labels permutation176 permutation6
    mixedMoment B raw12188step0 raw12188step0Labels = mixedMoment B raw12188step1 raw12188step1Labels := by
      have ha : raw12188step1 = raw12188step0 := by apply Matrix.ext; unfold raw12188step1 raw12188step0; decide +kernel
      have hl : raw12188step0Labels = labelEmbedding9 ∘ raw12188step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12188step0 raw12188step0Labels raw12188step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5256 node5256Labels := by rfl

def raw12189 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12189Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12189step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12189step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12189step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12189 raw12189Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw12189 raw12189Labels = mixedMoment B raw12189step0 raw12189step0Labels := by
      have hz : ∀ j, raw12189 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12189step0 = (fun i j => raw12189 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12189step0 raw12189; decide +kernel
      have hl : raw12189step0Labels = raw12189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12189 raw12189Labels permutation346 hz
    mixedMoment B raw12189step0 raw12189step0Labels = mixedMoment B raw12189step1 raw12189step1Labels := by
      have ha : raw12189step1 = (fun i j => raw12189step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12189step1 raw12189step0; decide +kernel
      have hl : raw12189step1Labels = raw12189step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12189step0 raw12189step0Labels permutation32 permutation6
    mixedMoment B raw12189step1 raw12189step1Labels = mixedMoment B raw12189step2 raw12189step2Labels := by
      have ha : raw12189step2 = raw12189step1 := by apply Matrix.ext; unfold raw12189step2 raw12189step1; decide +kernel
      have hl : raw12189step1Labels = labelEmbedding9 ∘ raw12189step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12189step1 raw12189step1Labels raw12189step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw12190 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12190Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12190step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12190step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12190step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12190step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12190 raw12190Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw12190 raw12190Labels = mixedMoment B raw12190step0 raw12190step0Labels := by
      have hz : ∀ j, raw12190 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12190step0 = (fun i j => raw12190 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12190step0 raw12190; decide +kernel
      have hl : raw12190step0Labels = raw12190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12190 raw12190Labels permutation346 hz
    mixedMoment B raw12190step0 raw12190step0Labels = mixedMoment B raw12190step1 raw12190step1Labels := by
      have ha : raw12190step1 = (fun i j => raw12190step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12190step1 raw12190step0; decide +kernel
      have hl : raw12190step1Labels = raw12190step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12190step0 raw12190step0Labels permutation34 permutation6
    mixedMoment B raw12190step1 raw12190step1Labels = mixedMoment B raw12190step2 raw12190step2Labels := by
      have ha : raw12190step2 = raw12190step1 := by apply Matrix.ext; unfold raw12190step2 raw12190step1; decide +kernel
      have hl : raw12190step1Labels = labelEmbedding9 ∘ raw12190step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12190step1 raw12190step1Labels raw12190step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw12191 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12191Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12191step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12191step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12191step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12191step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12191 raw12191Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw12191 raw12191Labels = mixedMoment B raw12191step0 raw12191step0Labels := by
      have hz : ∀ j, raw12191 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12191step0 = (fun i j => raw12191 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12191step0 raw12191; decide +kernel
      have hl : raw12191step0Labels = raw12191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12191 raw12191Labels permutation346 hz
    mixedMoment B raw12191step0 raw12191step0Labels = mixedMoment B raw12191step1 raw12191step1Labels := by
      have ha : raw12191step1 = (fun i j => raw12191step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12191step1 raw12191step0; decide +kernel
      have hl : raw12191step1Labels = raw12191step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12191step0 raw12191step0Labels permutation32 permutation6
    mixedMoment B raw12191step1 raw12191step1Labels = mixedMoment B raw12191step2 raw12191step2Labels := by
      have ha : raw12191step2 = raw12191step1 := by apply Matrix.ext; unfold raw12191step2 raw12191step1; decide +kernel
      have hl : raw12191step1Labels = labelEmbedding9 ∘ raw12191step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12191step1 raw12191step1Labels raw12191step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw12192 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12192Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12192step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12192step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12192step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12192step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12192step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12192step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12192step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12192step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12192step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12192 raw12192Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw12192 raw12192Labels = mixedMoment B raw12192step0 raw12192step0Labels := by
      have hz : ∀ j, raw12192 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12192step0 = (fun i j => raw12192 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12192step0 raw12192; decide +kernel
      have hl : raw12192step0Labels = raw12192Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12192 raw12192Labels permutation346 hz
    mixedMoment B raw12192step0 raw12192step0Labels = mixedMoment B raw12192step1 raw12192step1Labels := by
      have hz : ∀ j, raw12192step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12192step1 = (fun i j => raw12192step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12192step1 raw12192step0; decide +kernel
      have hl : raw12192step1Labels = raw12192step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12192step0 raw12192step0Labels permutation56 hz
    mixedMoment B raw12192step1 raw12192step1Labels = mixedMoment B raw12192step2 raw12192step2Labels := by
      have ha : raw12192step2 = (fun i j => raw12192step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12192step2 raw12192step1; decide +kernel
      have hl : raw12192step2Labels = raw12192step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12192step1 raw12192step1Labels permutation10 permutation4
    mixedMoment B raw12192step2 raw12192step2Labels = mixedMoment B raw12192step3 raw12192step3Labels := by
      have ha : raw12192step3 = -raw12192step2 := by apply Matrix.ext; change ∀ i j, raw12192step3 i j = -(raw12192step2 i j); unfold raw12192step3 raw12192step2; decide +kernel
      have hl : raw12192step3Labels = raw12192step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12192step3 raw12192step3Labels = mixedMoment B raw12192step4 raw12192step4Labels := by
      have ha : raw12192step4 = raw12192step3 := by apply Matrix.ext; unfold raw12192step4 raw12192step3; decide +kernel
      have hl : raw12192step3Labels = labelEmbedding7 ∘ raw12192step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12192step3 raw12192step3Labels raw12192step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw12193 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12193Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12193step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12193step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12193step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12193step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12193 raw12193Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw12193 raw12193Labels = mixedMoment B raw12193step0 raw12193step0Labels := by
      have hz : ∀ j, raw12193 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12193step0 = (fun i j => raw12193 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12193step0 raw12193; decide +kernel
      have hl : raw12193step0Labels = raw12193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12193 raw12193Labels permutation265 hz
    mixedMoment B raw12193step0 raw12193step0Labels = mixedMoment B raw12193step1 raw12193step1Labels := by
      have ha : raw12193step1 = (fun i j => raw12193step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12193step1 raw12193step0; decide +kernel
      have hl : raw12193step1Labels = raw12193step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12193step0 raw12193step0Labels permutation34 permutation6
    mixedMoment B raw12193step1 raw12193step1Labels = mixedMoment B raw12193step2 raw12193step2Labels := by
      have ha : raw12193step2 = raw12193step1 := by apply Matrix.ext; unfold raw12193step2 raw12193step1; decide +kernel
      have hl : raw12193step1Labels = labelEmbedding9 ∘ raw12193step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12193step1 raw12193step1Labels raw12193step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw12194 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12194Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12194step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12194step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12194step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12194step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12194step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12194step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12194step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12194 raw12194Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw12194 raw12194Labels = mixedMoment B raw12194step0 raw12194step0Labels := by
      have hz : ∀ j, raw12194 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12194step0 = (fun i j => raw12194 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12194step0 raw12194; decide +kernel
      have hl : raw12194step0Labels = raw12194Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12194 raw12194Labels permutation346 hz
    mixedMoment B raw12194step0 raw12194step0Labels = mixedMoment B raw12194step1 raw12194step1Labels := by
      have hz : ∀ j, raw12194step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12194step1 = (fun i j => raw12194step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12194step1 raw12194step0; decide +kernel
      have hl : raw12194step1Labels = raw12194step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12194step0 raw12194step0Labels permutation56 hz
    mixedMoment B raw12194step1 raw12194step1Labels = mixedMoment B raw12194step2 raw12194step2Labels := by
      have ha : raw12194step2 = (fun i j => raw12194step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12194step2 raw12194step1; decide +kernel
      have hl : raw12194step2Labels = raw12194step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12194step1 raw12194step1Labels permutation10 permutation6
    mixedMoment B raw12194step2 raw12194step2Labels = mixedMoment B raw12194step3 raw12194step3Labels := by
      have ha : raw12194step3 = raw12194step2 := by apply Matrix.ext; unfold raw12194step3 raw12194step2; decide +kernel
      have hl : raw12194step2Labels = labelEmbedding9 ∘ raw12194step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12194step2 raw12194step2Labels raw12194step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw12195 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12195Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12195step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12195step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12195step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12195step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12195step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12195step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12195step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12195 raw12195Labels = mixedMoment B node5307 node5307Labels := by
  calc
    mixedMoment B raw12195 raw12195Labels = mixedMoment B raw12195step0 raw12195step0Labels := by
      have hz : ∀ j, raw12195 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12195step0 = (fun i j => raw12195 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12195step0 raw12195; decide +kernel
      have hl : raw12195step0Labels = raw12195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12195 raw12195Labels permutation346 hz
    mixedMoment B raw12195step0 raw12195step0Labels = mixedMoment B raw12195step1 raw12195step1Labels := by
      have hz : ∀ j, raw12195step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12195step1 = (fun i j => raw12195step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12195step1 raw12195step0; decide +kernel
      have hl : raw12195step1Labels = raw12195step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12195step0 raw12195step0Labels permutation56 hz
    mixedMoment B raw12195step1 raw12195step1Labels = mixedMoment B raw12195step2 raw12195step2Labels := by
      have ha : raw12195step2 = (fun i j => raw12195step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12195step2 raw12195step1; decide +kernel
      have hl : raw12195step2Labels = raw12195step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12195step1 raw12195step1Labels permutation10 permutation6
    mixedMoment B raw12195step2 raw12195step2Labels = mixedMoment B raw12195step3 raw12195step3Labels := by
      have ha : raw12195step3 = raw12195step2 := by apply Matrix.ext; unfold raw12195step3 raw12195step2; decide +kernel
      have hl : raw12195step2Labels = labelEmbedding9 ∘ raw12195step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12195step2 raw12195step2Labels raw12195step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5307 node5307Labels := by rfl

def raw12196 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12196Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12196step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12196step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12196step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12196step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12196step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12196step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12196step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12196step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12196step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12196 raw12196Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw12196 raw12196Labels = mixedMoment B raw12196step0 raw12196step0Labels := by
      have hz : ∀ j, raw12196 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12196step0 = (fun i j => raw12196 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12196step0 raw12196; decide +kernel
      have hl : raw12196step0Labels = raw12196Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12196 raw12196Labels permutation346 hz
    mixedMoment B raw12196step0 raw12196step0Labels = mixedMoment B raw12196step1 raw12196step1Labels := by
      have hz : ∀ j, raw12196step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12196step1 = (fun i j => raw12196step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12196step1 raw12196step0; decide +kernel
      have hl : raw12196step1Labels = raw12196step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12196step0 raw12196step0Labels permutation56 hz
    mixedMoment B raw12196step1 raw12196step1Labels = mixedMoment B raw12196step2 raw12196step2Labels := by
      have ha : raw12196step2 = (fun i j => raw12196step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12196step2 raw12196step1; decide +kernel
      have hl : raw12196step2Labels = raw12196step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12196step1 raw12196step1Labels permutation8 permutation4
    mixedMoment B raw12196step2 raw12196step2Labels = mixedMoment B raw12196step3 raw12196step3Labels := by
      have ha : raw12196step3 = -raw12196step2 := by apply Matrix.ext; change ∀ i j, raw12196step3 i j = -(raw12196step2 i j); unfold raw12196step3 raw12196step2; decide +kernel
      have hl : raw12196step3Labels = raw12196step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12196step3 raw12196step3Labels = mixedMoment B raw12196step4 raw12196step4Labels := by
      have ha : raw12196step4 = raw12196step3 := by apply Matrix.ext; unfold raw12196step4 raw12196step3; decide +kernel
      have hl : raw12196step3Labels = labelEmbedding7 ∘ raw12196step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12196step3 raw12196step3Labels raw12196step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw12197 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12197Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12197step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12197step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12197step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12197step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12197step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12197 raw12197Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw12197 raw12197Labels = mixedMoment B raw12197step0 raw12197step0Labels := by
      have hz : ∀ j, raw12197 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12197step0 = (fun i j => raw12197 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12197step0 raw12197; decide +kernel
      have hl : raw12197step0Labels = raw12197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12197 raw12197Labels permutation265 hz
    mixedMoment B raw12197step0 raw12197step0Labels = mixedMoment B raw12197step1 raw12197step1Labels := by
      have ha : raw12197step1 = (fun i j => raw12197step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12197step1 raw12197step0; decide +kernel
      have hl : raw12197step1Labels = raw12197step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12197step0 raw12197step0Labels permutation32 permutation6
    mixedMoment B raw12197step1 raw12197step1Labels = mixedMoment B raw12197step2 raw12197step2Labels := by
      have ha : raw12197step2 = raw12197step1 := by apply Matrix.ext; unfold raw12197step2 raw12197step1; decide +kernel
      have hl : raw12197step1Labels = labelEmbedding9 ∘ raw12197step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12197step1 raw12197step1Labels raw12197step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw12198 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12198Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12198step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12198step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12198step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12198step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12198step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12198step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12198step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12198 raw12198Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw12198 raw12198Labels = mixedMoment B raw12198step0 raw12198step0Labels := by
      have hz : ∀ j, raw12198 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12198step0 = (fun i j => raw12198 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12198step0 raw12198; decide +kernel
      have hl : raw12198step0Labels = raw12198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12198 raw12198Labels permutation346 hz
    mixedMoment B raw12198step0 raw12198step0Labels = mixedMoment B raw12198step1 raw12198step1Labels := by
      have hz : ∀ j, raw12198step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12198step1 = (fun i j => raw12198step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12198step1 raw12198step0; decide +kernel
      have hl : raw12198step1Labels = raw12198step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12198step0 raw12198step0Labels permutation56 hz
    mixedMoment B raw12198step1 raw12198step1Labels = mixedMoment B raw12198step2 raw12198step2Labels := by
      have ha : raw12198step2 = (fun i j => raw12198step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12198step2 raw12198step1; decide +kernel
      have hl : raw12198step2Labels = raw12198step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12198step1 raw12198step1Labels permutation8 permutation6
    mixedMoment B raw12198step2 raw12198step2Labels = mixedMoment B raw12198step3 raw12198step3Labels := by
      have ha : raw12198step3 = raw12198step2 := by apply Matrix.ext; unfold raw12198step3 raw12198step2; decide +kernel
      have hl : raw12198step2Labels = labelEmbedding9 ∘ raw12198step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12198step2 raw12198step2Labels raw12198step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw12199 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12199Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12199step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12199step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12199step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12199step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12199step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12199step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12199step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12199 raw12199Labels = mixedMoment B node5307 node5307Labels := by
  calc
    mixedMoment B raw12199 raw12199Labels = mixedMoment B raw12199step0 raw12199step0Labels := by
      have hz : ∀ j, raw12199 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12199step0 = (fun i j => raw12199 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12199step0 raw12199; decide +kernel
      have hl : raw12199step0Labels = raw12199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12199 raw12199Labels permutation346 hz
    mixedMoment B raw12199step0 raw12199step0Labels = mixedMoment B raw12199step1 raw12199step1Labels := by
      have hz : ∀ j, raw12199step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12199step1 = (fun i j => raw12199step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12199step1 raw12199step0; decide +kernel
      have hl : raw12199step1Labels = raw12199step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12199step0 raw12199step0Labels permutation56 hz
    mixedMoment B raw12199step1 raw12199step1Labels = mixedMoment B raw12199step2 raw12199step2Labels := by
      have ha : raw12199step2 = (fun i j => raw12199step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12199step2 raw12199step1; decide +kernel
      have hl : raw12199step2Labels = raw12199step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12199step1 raw12199step1Labels permutation8 permutation6
    mixedMoment B raw12199step2 raw12199step2Labels = mixedMoment B raw12199step3 raw12199step3Labels := by
      have ha : raw12199step3 = raw12199step2 := by apply Matrix.ext; unfold raw12199step3 raw12199step2; decide +kernel
      have hl : raw12199step2Labels = labelEmbedding9 ∘ raw12199step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12199step2 raw12199step2Labels raw12199step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5307 node5307Labels := by rfl

def raw12200 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12200step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12200step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12200step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12200step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw12200step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12200step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw12200step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12200step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw12200step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12200 raw12200Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw12200 raw12200Labels = mixedMoment B raw12200step0 raw12200step0Labels := by
      have hz : ∀ j, raw12200 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12200step0 = (fun i j => raw12200 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12200step0 raw12200; decide +kernel
      have hl : raw12200step0Labels = raw12200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12200 raw12200Labels permutation346 hz
    mixedMoment B raw12200step0 raw12200step0Labels = mixedMoment B raw12200step1 raw12200step1Labels := by
      have hz : ∀ j, raw12200step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12200step1 = (fun i j => raw12200step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12200step1 raw12200step0; decide +kernel
      have hl : raw12200step1Labels = raw12200step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12200step0 raw12200step0Labels permutation56 hz
    mixedMoment B raw12200step1 raw12200step1Labels = mixedMoment B raw12200step2 raw12200step2Labels := by
      have ha : raw12200step2 = (fun i j => raw12200step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12200step2 raw12200step1; decide +kernel
      have hl : raw12200step2Labels = raw12200step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12200step1 raw12200step1Labels permutation8 permutation4
    mixedMoment B raw12200step2 raw12200step2Labels = mixedMoment B raw12200step3 raw12200step3Labels := by
      have ha : raw12200step3 = -raw12200step2 := by apply Matrix.ext; change ∀ i j, raw12200step3 i j = -(raw12200step2 i j); unfold raw12200step3 raw12200step2; decide +kernel
      have hl : raw12200step3Labels = raw12200step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12200step3 raw12200step3Labels = mixedMoment B raw12200step4 raw12200step4Labels := by
      have ha : raw12200step4 = raw12200step3 := by apply Matrix.ext; unfold raw12200step4 raw12200step3; decide +kernel
      have hl : raw12200step3Labels = labelEmbedding7 ∘ raw12200step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12200step3 raw12200step3Labels raw12200step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

def raw12201 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12201Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12201step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12201step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw12201step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12201step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw12201step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12201 raw12201Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw12201 raw12201Labels = mixedMoment B raw12201step0 raw12201step0Labels := by
      have hz : ∀ j, raw12201 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12201step0 = (fun i j => raw12201 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12201step0 raw12201; decide +kernel
      have hl : raw12201step0Labels = raw12201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12201 raw12201Labels permutation265 hz
    mixedMoment B raw12201step0 raw12201step0Labels = mixedMoment B raw12201step1 raw12201step1Labels := by
      have ha : raw12201step1 = (fun i j => raw12201step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12201step1 raw12201step0; decide +kernel
      have hl : raw12201step1Labels = raw12201step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12201step0 raw12201step0Labels permutation32 permutation6
    mixedMoment B raw12201step1 raw12201step1Labels = mixedMoment B raw12201step2 raw12201step2Labels := by
      have ha : raw12201step2 = raw12201step1 := by apply Matrix.ext; unfold raw12201step2 raw12201step1; decide +kernel
      have hl : raw12201step1Labels = labelEmbedding9 ∘ raw12201step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12201step1 raw12201step1Labels raw12201step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw12202 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12202step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12202step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12202step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12202step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12202step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw12202step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12202step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12202 raw12202Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw12202 raw12202Labels = mixedMoment B raw12202step0 raw12202step0Labels := by
      have hz : ∀ j, raw12202 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12202step0 = (fun i j => raw12202 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12202step0 raw12202; decide +kernel
      have hl : raw12202step0Labels = raw12202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12202 raw12202Labels permutation346 hz
    mixedMoment B raw12202step0 raw12202step0Labels = mixedMoment B raw12202step1 raw12202step1Labels := by
      have hz : ∀ j, raw12202step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12202step1 = (fun i j => raw12202step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12202step1 raw12202step0; decide +kernel
      have hl : raw12202step1Labels = raw12202step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12202step0 raw12202step0Labels permutation56 hz
    mixedMoment B raw12202step1 raw12202step1Labels = mixedMoment B raw12202step2 raw12202step2Labels := by
      have ha : raw12202step2 = (fun i j => raw12202step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12202step2 raw12202step1; decide +kernel
      have hl : raw12202step2Labels = raw12202step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12202step1 raw12202step1Labels permutation31 permutation5
    mixedMoment B raw12202step2 raw12202step2Labels = mixedMoment B raw12202step3 raw12202step3Labels := by
      have ha : raw12202step3 = raw12202step2 := by apply Matrix.ext; unfold raw12202step3 raw12202step2; decide +kernel
      have hl : raw12202step2Labels = labelEmbedding8 ∘ raw12202step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12202step2 raw12202step2Labels raw12202step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw12203 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw12203Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw12203step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12203step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 0, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw12203step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12203step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12203step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw12203step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12203step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12203 raw12203Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw12203 raw12203Labels = mixedMoment B raw12203step0 raw12203step0Labels := by
      have hz : ∀ j, raw12203 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12203step0 = (fun i j => raw12203 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12203step0 raw12203; decide +kernel
      have hl : raw12203step0Labels = raw12203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12203 raw12203Labels permutation346 hz
    mixedMoment B raw12203step0 raw12203step0Labels = mixedMoment B raw12203step1 raw12203step1Labels := by
      have hz : ∀ j, raw12203step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12203step1 = (fun i j => raw12203step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12203step1 raw12203step0; decide +kernel
      have hl : raw12203step1Labels = raw12203step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12203step0 raw12203step0Labels permutation56 hz
    mixedMoment B raw12203step1 raw12203step1Labels = mixedMoment B raw12203step2 raw12203step2Labels := by
      have ha : raw12203step2 = (fun i j => raw12203step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12203step2 raw12203step1; decide +kernel
      have hl : raw12203step2Labels = raw12203step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12203step1 raw12203step1Labels permutation29 permutation5
    mixedMoment B raw12203step2 raw12203step2Labels = mixedMoment B raw12203step3 raw12203step3Labels := by
      have ha : raw12203step3 = raw12203step2 := by apply Matrix.ext; unfold raw12203step3 raw12203step2; decide +kernel
      have hl : raw12203step2Labels = labelEmbedding8 ∘ raw12203step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12203step2 raw12203step2Labels raw12203step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw12204 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12204Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12204step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12204step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12204step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12204step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12204step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12204 raw12204Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw12204 raw12204Labels = mixedMoment B raw12204step0 raw12204step0Labels := by
      have hz : ∀ j, raw12204 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12204step0 = (fun i j => raw12204 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12204step0 raw12204; decide +kernel
      have hl : raw12204step0Labels = raw12204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12204 raw12204Labels permutation265 hz
    mixedMoment B raw12204step0 raw12204step0Labels = mixedMoment B raw12204step1 raw12204step1Labels := by
      have ha : raw12204step1 = (fun i j => raw12204step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12204step1 raw12204step0; decide +kernel
      have hl : raw12204step1Labels = raw12204step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12204step0 raw12204step0Labels permutation36 permutation7
    mixedMoment B raw12204step1 raw12204step1Labels = mixedMoment B raw12204step2 raw12204step2Labels := by
      have ha : raw12204step2 = raw12204step1 := by apply Matrix.ext; unfold raw12204step2 raw12204step1; decide +kernel
      have hl : raw12204step1Labels = labelEmbedding1 ∘ raw12204step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12204step1 raw12204step1Labels raw12204step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2764 node2764Labels := by rfl

def raw12205 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12205Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12205step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12205step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12205step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12205step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12205step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12205step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12205step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12205 raw12205Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw12205 raw12205Labels = mixedMoment B raw12205step0 raw12205step0Labels := by
      have hz : ∀ j, raw12205 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12205step0 = (fun i j => raw12205 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12205step0 raw12205; decide +kernel
      have hl : raw12205step0Labels = raw12205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12205 raw12205Labels permutation346 hz
    mixedMoment B raw12205step0 raw12205step0Labels = mixedMoment B raw12205step1 raw12205step1Labels := by
      have hz : ∀ j, raw12205step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12205step1 = (fun i j => raw12205step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12205step1 raw12205step0; decide +kernel
      have hl : raw12205step1Labels = raw12205step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12205step0 raw12205step0Labels permutation56 hz
    mixedMoment B raw12205step1 raw12205step1Labels = mixedMoment B raw12205step2 raw12205step2Labels := by
      have ha : raw12205step2 = (fun i j => raw12205step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12205step2 raw12205step1; decide +kernel
      have hl : raw12205step2Labels = raw12205step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12205step1 raw12205step1Labels permutation13 permutation7
    mixedMoment B raw12205step2 raw12205step2Labels = mixedMoment B raw12205step3 raw12205step3Labels := by
      have ha : raw12205step3 = raw12205step2 := by apply Matrix.ext; unfold raw12205step3 raw12205step2; decide +kernel
      have hl : raw12205step2Labels = labelEmbedding1 ∘ raw12205step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12205step2 raw12205step2Labels raw12205step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2782 node2782Labels := by rfl

def raw12206 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12206Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12206step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12206step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12206step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12206step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12206step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12206step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12206step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12206 raw12206Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw12206 raw12206Labels = mixedMoment B raw12206step0 raw12206step0Labels := by
      have hz : ∀ j, raw12206 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12206step0 = (fun i j => raw12206 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12206step0 raw12206; decide +kernel
      have hl : raw12206step0Labels = raw12206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12206 raw12206Labels permutation346 hz
    mixedMoment B raw12206step0 raw12206step0Labels = mixedMoment B raw12206step1 raw12206step1Labels := by
      have hz : ∀ j, raw12206step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12206step1 = (fun i j => raw12206step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12206step1 raw12206step0; decide +kernel
      have hl : raw12206step1Labels = raw12206step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12206step0 raw12206step0Labels permutation56 hz
    mixedMoment B raw12206step1 raw12206step1Labels = mixedMoment B raw12206step2 raw12206step2Labels := by
      have ha : raw12206step2 = (fun i j => raw12206step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12206step2 raw12206step1; decide +kernel
      have hl : raw12206step2Labels = raw12206step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12206step1 raw12206step1Labels permutation12 permutation7
    mixedMoment B raw12206step2 raw12206step2Labels = mixedMoment B raw12206step3 raw12206step3Labels := by
      have ha : raw12206step3 = raw12206step2 := by apply Matrix.ext; unfold raw12206step3 raw12206step2; decide +kernel
      have hl : raw12206step2Labels = labelEmbedding1 ∘ raw12206step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12206step2 raw12206step2Labels raw12206step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2782 node2782Labels := by rfl

def raw12207 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12207Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12207step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12207step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12207step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12207step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12207step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12207step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12207step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12207 raw12207Labels = mixedMoment B node2785 node2785Labels := by
  calc
    mixedMoment B raw12207 raw12207Labels = mixedMoment B raw12207step0 raw12207step0Labels := by
      have hz : ∀ j, raw12207 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12207step0 = (fun i j => raw12207 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12207step0 raw12207; decide +kernel
      have hl : raw12207step0Labels = raw12207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12207 raw12207Labels permutation346 hz
    mixedMoment B raw12207step0 raw12207step0Labels = mixedMoment B raw12207step1 raw12207step1Labels := by
      have hz : ∀ j, raw12207step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12207step1 = (fun i j => raw12207step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12207step1 raw12207step0; decide +kernel
      have hl : raw12207step1Labels = raw12207step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12207step0 raw12207step0Labels permutation56 hz
    mixedMoment B raw12207step1 raw12207step1Labels = mixedMoment B raw12207step2 raw12207step2Labels := by
      have ha : raw12207step2 = (fun i j => raw12207step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12207step2 raw12207step1; decide +kernel
      have hl : raw12207step2Labels = raw12207step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12207step1 raw12207step1Labels permutation12 permutation7
    mixedMoment B raw12207step2 raw12207step2Labels = mixedMoment B raw12207step3 raw12207step3Labels := by
      have ha : raw12207step3 = raw12207step2 := by apply Matrix.ext; unfold raw12207step3 raw12207step2; decide +kernel
      have hl : raw12207step2Labels = labelEmbedding1 ∘ raw12207step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12207step2 raw12207step2Labels raw12207step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2785 node2785Labels := by rfl

def raw12208 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12208Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12208step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12208step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12208step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12208step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12208step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12208step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12208 raw12208Labels = mixedMoment B node3227 node3227Labels := by
  calc
    mixedMoment B raw12208 raw12208Labels = mixedMoment B raw12208step0 raw12208step0Labels := by
      have hz : ∀ j, raw12208 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12208step0 = (fun i j => raw12208 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12208step0 raw12208; decide +kernel
      have hl : raw12208step0Labels = raw12208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12208 raw12208Labels permutation346 hz
    mixedMoment B raw12208step0 raw12208step0Labels = mixedMoment B raw12208step1 raw12208step1Labels := by
      have ha : raw12208step1 = (fun i j => raw12208step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12208step1 raw12208step0; decide +kernel
      have hl : raw12208step1Labels = raw12208step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12208step0 raw12208step0Labels permutation40 permutation5
    mixedMoment B raw12208step1 raw12208step1Labels = mixedMoment B raw12208step2 raw12208step2Labels := by
      have ha : raw12208step2 = -raw12208step1 := by apply Matrix.ext; change ∀ i j, raw12208step2 i j = -(raw12208step1 i j); unfold raw12208step2 raw12208step1; decide +kernel
      have hl : raw12208step2Labels = raw12208step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12208step2 raw12208step2Labels = mixedMoment B raw12208step3 raw12208step3Labels := by
      have ha : raw12208step3 = raw12208step2 := by apply Matrix.ext; unfold raw12208step3 raw12208step2; decide +kernel
      have hl : raw12208step2Labels = labelEmbedding1 ∘ raw12208step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12208step2 raw12208step2Labels raw12208step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3227 node3227Labels := by rfl

def raw12209 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12209Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12209step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12209step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12209step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12209 raw12209Labels = mixedMoment B node3085 node3085Labels := by
  calc
    mixedMoment B raw12209 raw12209Labels = mixedMoment B raw12209step0 raw12209step0Labels := by
      have ha : raw12209step0 = (fun i j => raw12209 (permutation156 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12209step0 raw12209; decide +kernel
      have hl : raw12209step0Labels = raw12209Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12209 raw12209Labels permutation156 permutation7
    mixedMoment B raw12209step0 raw12209step0Labels = mixedMoment B raw12209step1 raw12209step1Labels := by
      have ha : raw12209step1 = raw12209step0 := by apply Matrix.ext; unfold raw12209step1 raw12209step0; decide +kernel
      have hl : raw12209step0Labels = labelEmbedding1 ∘ raw12209step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12209step0 raw12209step0Labels raw12209step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3085 node3085Labels := by rfl

def raw12210 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12210Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12210step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12210step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12210step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12210step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12210step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12210 raw12210Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw12210 raw12210Labels = mixedMoment B raw12210step0 raw12210step0Labels := by
      have hz : ∀ j, raw12210 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12210step0 = (fun i j => raw12210 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12210step0 raw12210; decide +kernel
      have hl : raw12210step0Labels = raw12210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12210 raw12210Labels permutation346 hz
    mixedMoment B raw12210step0 raw12210step0Labels = mixedMoment B raw12210step1 raw12210step1Labels := by
      have ha : raw12210step1 = (fun i j => raw12210step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12210step1 raw12210step0; decide +kernel
      have hl : raw12210step1Labels = raw12210step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12210step0 raw12210step0Labels permutation37 permutation7
    mixedMoment B raw12210step1 raw12210step1Labels = mixedMoment B raw12210step2 raw12210step2Labels := by
      have ha : raw12210step2 = raw12210step1 := by apply Matrix.ext; unfold raw12210step2 raw12210step1; decide +kernel
      have hl : raw12210step1Labels = labelEmbedding1 ∘ raw12210step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12210step1 raw12210step1Labels raw12210step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3097 node3097Labels := by rfl

def raw12211 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12211Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12211step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12211step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12211step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12211step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12211step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12211 raw12211Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw12211 raw12211Labels = mixedMoment B raw12211step0 raw12211step0Labels := by
      have hz : ∀ j, raw12211 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12211step0 = (fun i j => raw12211 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12211step0 raw12211; decide +kernel
      have hl : raw12211step0Labels = raw12211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12211 raw12211Labels permutation346 hz
    mixedMoment B raw12211step0 raw12211step0Labels = mixedMoment B raw12211step1 raw12211step1Labels := by
      have ha : raw12211step1 = (fun i j => raw12211step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12211step1 raw12211step0; decide +kernel
      have hl : raw12211step1Labels = raw12211step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12211step0 raw12211step0Labels permutation36 permutation7
    mixedMoment B raw12211step1 raw12211step1Labels = mixedMoment B raw12211step2 raw12211step2Labels := by
      have ha : raw12211step2 = raw12211step1 := by apply Matrix.ext; unfold raw12211step2 raw12211step1; decide +kernel
      have hl : raw12211step1Labels = labelEmbedding1 ∘ raw12211step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12211step1 raw12211step1Labels raw12211step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3097 node3097Labels := by rfl

def raw12212 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12212Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12212step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12212step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12212step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12212step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12212step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12212 raw12212Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw12212 raw12212Labels = mixedMoment B raw12212step0 raw12212step0Labels := by
      have hz : ∀ j, raw12212 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12212step0 = (fun i j => raw12212 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12212step0 raw12212; decide +kernel
      have hl : raw12212step0Labels = raw12212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12212 raw12212Labels permutation346 hz
    mixedMoment B raw12212step0 raw12212step0Labels = mixedMoment B raw12212step1 raw12212step1Labels := by
      have ha : raw12212step1 = (fun i j => raw12212step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12212step1 raw12212step0; decide +kernel
      have hl : raw12212step1Labels = raw12212step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12212step0 raw12212step0Labels permutation36 permutation7
    mixedMoment B raw12212step1 raw12212step1Labels = mixedMoment B raw12212step2 raw12212step2Labels := by
      have ha : raw12212step2 = raw12212step1 := by apply Matrix.ext; unfold raw12212step2 raw12212step1; decide +kernel
      have hl : raw12212step1Labels = labelEmbedding1 ∘ raw12212step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12212step1 raw12212step1Labels raw12212step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3100 node3100Labels := by rfl

def raw12213 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12213Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12213step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12213step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12213step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12213step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![-1, 1, 0], ![-2, 1, 1]]
def raw12213step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12213step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12213step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12213step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12213step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12213 raw12213Labels = mixedMoment B node3229 node3229Labels := by
  calc
    mixedMoment B raw12213 raw12213Labels = mixedMoment B raw12213step0 raw12213step0Labels := by
      have hz : ∀ j, raw12213 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12213step0 = (fun i j => raw12213 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12213step0 raw12213; decide +kernel
      have hl : raw12213step0Labels = raw12213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12213 raw12213Labels permutation346 hz
    mixedMoment B raw12213step0 raw12213step0Labels = mixedMoment B raw12213step1 raw12213step1Labels := by
      have hz : ∀ j, raw12213step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12213step1 = (fun i j => raw12213step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12213step1 raw12213step0; decide +kernel
      have hl : raw12213step1Labels = raw12213step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12213step0 raw12213step0Labels permutation56 hz
    mixedMoment B raw12213step1 raw12213step1Labels = mixedMoment B raw12213step2 raw12213step2Labels := by
      have ha : raw12213step2 = (fun i j => raw12213step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12213step2 raw12213step1; decide +kernel
      have hl : raw12213step2Labels = raw12213step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12213step1 raw12213step1Labels permutation10 permutation5
    mixedMoment B raw12213step2 raw12213step2Labels = mixedMoment B raw12213step3 raw12213step3Labels := by
      have ha : raw12213step3 = -raw12213step2 := by apply Matrix.ext; change ∀ i j, raw12213step3 i j = -(raw12213step2 i j); unfold raw12213step3 raw12213step2; decide +kernel
      have hl : raw12213step3Labels = raw12213step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12213step3 raw12213step3Labels = mixedMoment B raw12213step4 raw12213step4Labels := by
      have ha : raw12213step4 = raw12213step3 := by apply Matrix.ext; unfold raw12213step4 raw12213step3; decide +kernel
      have hl : raw12213step3Labels = labelEmbedding1 ∘ raw12213step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12213step3 raw12213step3Labels raw12213step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3229 node3229Labels := by rfl

def raw12214 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12214Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12214step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12214step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12214step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12214step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12214 raw12214Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw12214 raw12214Labels = mixedMoment B raw12214step0 raw12214step0Labels := by
      have hz : ∀ j, raw12214 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12214step0 = (fun i j => raw12214 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12214step0 raw12214; decide +kernel
      have hl : raw12214step0Labels = raw12214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12214 raw12214Labels permutation265 hz
    mixedMoment B raw12214step0 raw12214step0Labels = mixedMoment B raw12214step1 raw12214step1Labels := by
      have ha : raw12214step1 = (fun i j => raw12214step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12214step1 raw12214step0; decide +kernel
      have hl : raw12214step1Labels = raw12214step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12214step0 raw12214step0Labels permutation36 permutation7
    mixedMoment B raw12214step1 raw12214step1Labels = mixedMoment B raw12214step2 raw12214step2Labels := by
      have ha : raw12214step2 = raw12214step1 := by apply Matrix.ext; unfold raw12214step2 raw12214step1; decide +kernel
      have hl : raw12214step1Labels = labelEmbedding1 ∘ raw12214step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12214step1 raw12214step1Labels raw12214step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw12215 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12215Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12215step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12215step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12215step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12215step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12215step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12215step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12215step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12215 raw12215Labels = mixedMoment B node3119 node3119Labels := by
  calc
    mixedMoment B raw12215 raw12215Labels = mixedMoment B raw12215step0 raw12215step0Labels := by
      have hz : ∀ j, raw12215 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12215step0 = (fun i j => raw12215 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12215step0 raw12215; decide +kernel
      have hl : raw12215step0Labels = raw12215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12215 raw12215Labels permutation346 hz
    mixedMoment B raw12215step0 raw12215step0Labels = mixedMoment B raw12215step1 raw12215step1Labels := by
      have hz : ∀ j, raw12215step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12215step1 = (fun i j => raw12215step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12215step1 raw12215step0; decide +kernel
      have hl : raw12215step1Labels = raw12215step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12215step0 raw12215step0Labels permutation56 hz
    mixedMoment B raw12215step1 raw12215step1Labels = mixedMoment B raw12215step2 raw12215step2Labels := by
      have ha : raw12215step2 = (fun i j => raw12215step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12215step2 raw12215step1; decide +kernel
      have hl : raw12215step2Labels = raw12215step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12215step1 raw12215step1Labels permutation12 permutation7
    mixedMoment B raw12215step2 raw12215step2Labels = mixedMoment B raw12215step3 raw12215step3Labels := by
      have ha : raw12215step3 = raw12215step2 := by apply Matrix.ext; unfold raw12215step3 raw12215step2; decide +kernel
      have hl : raw12215step2Labels = labelEmbedding1 ∘ raw12215step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12215step2 raw12215step2Labels raw12215step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3119 node3119Labels := by rfl

def raw12216 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12216Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12216step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12216step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12216step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12216step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12216step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12216step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12216step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12216 raw12216Labels = mixedMoment B node3122 node3122Labels := by
  calc
    mixedMoment B raw12216 raw12216Labels = mixedMoment B raw12216step0 raw12216step0Labels := by
      have hz : ∀ j, raw12216 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12216step0 = (fun i j => raw12216 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12216step0 raw12216; decide +kernel
      have hl : raw12216step0Labels = raw12216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12216 raw12216Labels permutation346 hz
    mixedMoment B raw12216step0 raw12216step0Labels = mixedMoment B raw12216step1 raw12216step1Labels := by
      have hz : ∀ j, raw12216step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12216step1 = (fun i j => raw12216step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12216step1 raw12216step0; decide +kernel
      have hl : raw12216step1Labels = raw12216step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12216step0 raw12216step0Labels permutation56 hz
    mixedMoment B raw12216step1 raw12216step1Labels = mixedMoment B raw12216step2 raw12216step2Labels := by
      have ha : raw12216step2 = (fun i j => raw12216step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12216step2 raw12216step1; decide +kernel
      have hl : raw12216step2Labels = raw12216step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12216step1 raw12216step1Labels permutation9 permutation7
    mixedMoment B raw12216step2 raw12216step2Labels = mixedMoment B raw12216step3 raw12216step3Labels := by
      have ha : raw12216step3 = raw12216step2 := by apply Matrix.ext; unfold raw12216step3 raw12216step2; decide +kernel
      have hl : raw12216step2Labels = labelEmbedding1 ∘ raw12216step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12216step2 raw12216step2Labels raw12216step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3122 node3122Labels := by rfl

def raw12217 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12217Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12217step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12217step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12217step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12217step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![-1, 1, 0], ![-2, 1, 1]]
def raw12217step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12217step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12217step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12217step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12217step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12217 raw12217Labels = mixedMoment B node3229 node3229Labels := by
  calc
    mixedMoment B raw12217 raw12217Labels = mixedMoment B raw12217step0 raw12217step0Labels := by
      have hz : ∀ j, raw12217 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12217step0 = (fun i j => raw12217 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12217step0 raw12217; decide +kernel
      have hl : raw12217step0Labels = raw12217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12217 raw12217Labels permutation346 hz
    mixedMoment B raw12217step0 raw12217step0Labels = mixedMoment B raw12217step1 raw12217step1Labels := by
      have hz : ∀ j, raw12217step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12217step1 = (fun i j => raw12217step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12217step1 raw12217step0; decide +kernel
      have hl : raw12217step1Labels = raw12217step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12217step0 raw12217step0Labels permutation56 hz
    mixedMoment B raw12217step1 raw12217step1Labels = mixedMoment B raw12217step2 raw12217step2Labels := by
      have ha : raw12217step2 = (fun i j => raw12217step1 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12217step2 raw12217step1; decide +kernel
      have hl : raw12217step2Labels = raw12217step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12217step1 raw12217step1Labels permutation8 permutation5
    mixedMoment B raw12217step2 raw12217step2Labels = mixedMoment B raw12217step3 raw12217step3Labels := by
      have ha : raw12217step3 = -raw12217step2 := by apply Matrix.ext; change ∀ i j, raw12217step3 i j = -(raw12217step2 i j); unfold raw12217step3 raw12217step2; decide +kernel
      have hl : raw12217step3Labels = raw12217step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12217step3 raw12217step3Labels = mixedMoment B raw12217step4 raw12217step4Labels := by
      have ha : raw12217step4 = raw12217step3 := by apply Matrix.ext; unfold raw12217step4 raw12217step3; decide +kernel
      have hl : raw12217step3Labels = labelEmbedding1 ∘ raw12217step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12217step3 raw12217step3Labels raw12217step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3229 node3229Labels := by rfl

def raw12218 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12218Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12218step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12218step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12218step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12218step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12218step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12218 raw12218Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw12218 raw12218Labels = mixedMoment B raw12218step0 raw12218step0Labels := by
      have hz : ∀ j, raw12218 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12218step0 = (fun i j => raw12218 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12218step0 raw12218; decide +kernel
      have hl : raw12218step0Labels = raw12218Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12218 raw12218Labels permutation265 hz
    mixedMoment B raw12218step0 raw12218step0Labels = mixedMoment B raw12218step1 raw12218step1Labels := by
      have ha : raw12218step1 = (fun i j => raw12218step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12218step1 raw12218step0; decide +kernel
      have hl : raw12218step1Labels = raw12218step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12218step0 raw12218step0Labels permutation37 permutation7
    mixedMoment B raw12218step1 raw12218step1Labels = mixedMoment B raw12218step2 raw12218step2Labels := by
      have ha : raw12218step2 = raw12218step1 := by apply Matrix.ext; unfold raw12218step2 raw12218step1; decide +kernel
      have hl : raw12218step1Labels = labelEmbedding1 ∘ raw12218step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12218step1 raw12218step1Labels raw12218step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw12219 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12219Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12219step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12219step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw12219step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12219step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12219step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12219step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12219step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12219 raw12219Labels = mixedMoment B node3119 node3119Labels := by
  calc
    mixedMoment B raw12219 raw12219Labels = mixedMoment B raw12219step0 raw12219step0Labels := by
      have hz : ∀ j, raw12219 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12219step0 = (fun i j => raw12219 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12219step0 raw12219; decide +kernel
      have hl : raw12219step0Labels = raw12219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12219 raw12219Labels permutation346 hz
    mixedMoment B raw12219step0 raw12219step0Labels = mixedMoment B raw12219step1 raw12219step1Labels := by
      have hz : ∀ j, raw12219step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12219step1 = (fun i j => raw12219step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12219step1 raw12219step0; decide +kernel
      have hl : raw12219step1Labels = raw12219step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12219step0 raw12219step0Labels permutation56 hz
    mixedMoment B raw12219step1 raw12219step1Labels = mixedMoment B raw12219step2 raw12219step2Labels := by
      have ha : raw12219step2 = (fun i j => raw12219step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12219step2 raw12219step1; decide +kernel
      have hl : raw12219step2Labels = raw12219step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12219step1 raw12219step1Labels permutation13 permutation7
    mixedMoment B raw12219step2 raw12219step2Labels = mixedMoment B raw12219step3 raw12219step3Labels := by
      have ha : raw12219step3 = raw12219step2 := by apply Matrix.ext; unfold raw12219step3 raw12219step2; decide +kernel
      have hl : raw12219step2Labels = labelEmbedding1 ∘ raw12219step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12219step2 raw12219step2Labels raw12219step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3119 node3119Labels := by rfl

def raw12220 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12220Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12220step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12220step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12220step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12220step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12220step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12220step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12220step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12220 raw12220Labels = mixedMoment B node3122 node3122Labels := by
  calc
    mixedMoment B raw12220 raw12220Labels = mixedMoment B raw12220step0 raw12220step0Labels := by
      have hz : ∀ j, raw12220 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12220step0 = (fun i j => raw12220 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12220step0 raw12220; decide +kernel
      have hl : raw12220step0Labels = raw12220Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12220 raw12220Labels permutation346 hz
    mixedMoment B raw12220step0 raw12220step0Labels = mixedMoment B raw12220step1 raw12220step1Labels := by
      have hz : ∀ j, raw12220step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12220step1 = (fun i j => raw12220step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12220step1 raw12220step0; decide +kernel
      have hl : raw12220step1Labels = raw12220step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12220step0 raw12220step0Labels permutation56 hz
    mixedMoment B raw12220step1 raw12220step1Labels = mixedMoment B raw12220step2 raw12220step2Labels := by
      have ha : raw12220step2 = (fun i j => raw12220step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12220step2 raw12220step1; decide +kernel
      have hl : raw12220step2Labels = raw12220step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12220step1 raw12220step1Labels permutation11 permutation7
    mixedMoment B raw12220step2 raw12220step2Labels = mixedMoment B raw12220step3 raw12220step3Labels := by
      have ha : raw12220step3 = raw12220step2 := by apply Matrix.ext; unfold raw12220step3 raw12220step2; decide +kernel
      have hl : raw12220step2Labels = labelEmbedding1 ∘ raw12220step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12220step2 raw12220step2Labels raw12220step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3122 node3122Labels := by rfl

def raw12221 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12221Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12221step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12221step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12221step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12221step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw12221step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12221step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw12221step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12221 raw12221Labels = mixedMoment B node2755 node2755Labels := by
  calc
    mixedMoment B raw12221 raw12221Labels = mixedMoment B raw12221step0 raw12221step0Labels := by
      have hz : ∀ j, raw12221 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12221step0 = (fun i j => raw12221 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12221step0 raw12221; decide +kernel
      have hl : raw12221step0Labels = raw12221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12221 raw12221Labels permutation346 hz
    mixedMoment B raw12221step0 raw12221step0Labels = mixedMoment B raw12221step1 raw12221step1Labels := by
      have hz : ∀ j, raw12221step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12221step1 = (fun i j => raw12221step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12221step1 raw12221step0; decide +kernel
      have hl : raw12221step1Labels = raw12221step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12221step0 raw12221step0Labels permutation56 hz
    mixedMoment B raw12221step1 raw12221step1Labels = mixedMoment B raw12221step2 raw12221step2Labels := by
      have ha : raw12221step2 = (fun i j => raw12221step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12221step2 raw12221step1; decide +kernel
      have hl : raw12221step2Labels = raw12221step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12221step1 raw12221step1Labels permutation29 permutation5
    mixedMoment B raw12221step2 raw12221step2Labels = mixedMoment B raw12221step3 raw12221step3Labels := by
      have ha : raw12221step3 = raw12221step2 := by apply Matrix.ext; unfold raw12221step3 raw12221step2; decide +kernel
      have hl : raw12221step2Labels = labelEmbedding1 ∘ raw12221step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12221step2 raw12221step2Labels raw12221step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2755 node2755Labels := by rfl

def raw12222 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12222Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12222step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12222step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12222step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12222step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw12222step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12222 raw12222Labels = mixedMoment B node2754 node2754Labels := by
  calc
    mixedMoment B raw12222 raw12222Labels = mixedMoment B raw12222step0 raw12222step0Labels := by
      have hz : ∀ j, raw12222 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12222step0 = (fun i j => raw12222 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12222step0 raw12222; decide +kernel
      have hl : raw12222step0Labels = raw12222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12222 raw12222Labels permutation265 hz
    mixedMoment B raw12222step0 raw12222step0Labels = mixedMoment B raw12222step1 raw12222step1Labels := by
      have ha : raw12222step1 = (fun i j => raw12222step0 (permutation145 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12222step1 raw12222step0; decide +kernel
      have hl : raw12222step1Labels = raw12222step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12222step0 raw12222step0Labels permutation145 permutation5
    mixedMoment B raw12222step1 raw12222step1Labels = mixedMoment B raw12222step2 raw12222step2Labels := by
      have ha : raw12222step2 = raw12222step1 := by apply Matrix.ext; unfold raw12222step2 raw12222step1; decide +kernel
      have hl : raw12222step1Labels = labelEmbedding1 ∘ raw12222step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12222step1 raw12222step1Labels raw12222step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2754 node2754Labels := by rfl

def raw12223 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12223Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12223step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12223step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw12223step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12223step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12223step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12223step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12223step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12223 raw12223Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw12223 raw12223Labels = mixedMoment B raw12223step0 raw12223step0Labels := by
      have hz : ∀ j, raw12223 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12223step0 = (fun i j => raw12223 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12223step0 raw12223; decide +kernel
      have hl : raw12223step0Labels = raw12223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12223 raw12223Labels permutation346 hz
    mixedMoment B raw12223step0 raw12223step0Labels = mixedMoment B raw12223step1 raw12223step1Labels := by
      have hz : ∀ j, raw12223step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12223step1 = (fun i j => raw12223step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12223step1 raw12223step0; decide +kernel
      have hl : raw12223step1Labels = raw12223step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12223step0 raw12223step0Labels permutation56 hz
    mixedMoment B raw12223step1 raw12223step1Labels = mixedMoment B raw12223step2 raw12223step2Labels := by
      have ha : raw12223step2 = (fun i j => raw12223step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12223step2 raw12223step1; decide +kernel
      have hl : raw12223step2Labels = raw12223step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12223step1 raw12223step1Labels permutation31 permutation5
    mixedMoment B raw12223step2 raw12223step2Labels = mixedMoment B raw12223step3 raw12223step3Labels := by
      have ha : raw12223step3 = raw12223step2 := by apply Matrix.ext; unfold raw12223step3 raw12223step2; decide +kernel
      have hl : raw12223step2Labels = labelEmbedding1 ∘ raw12223step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12223step2 raw12223step2Labels raw12223step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2769 node2769Labels := by rfl

def raw12224 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw12224Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw12224step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12224step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 0, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw12224step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12224step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12224step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12224step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12224step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12224 raw12224Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw12224 raw12224Labels = mixedMoment B raw12224step0 raw12224step0Labels := by
      have hz : ∀ j, raw12224 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12224step0 = (fun i j => raw12224 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12224step0 raw12224; decide +kernel
      have hl : raw12224step0Labels = raw12224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12224 raw12224Labels permutation346 hz
    mixedMoment B raw12224step0 raw12224step0Labels = mixedMoment B raw12224step1 raw12224step1Labels := by
      have hz : ∀ j, raw12224step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12224step1 = (fun i j => raw12224step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12224step1 raw12224step0; decide +kernel
      have hl : raw12224step1Labels = raw12224step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12224step0 raw12224step0Labels permutation56 hz
    mixedMoment B raw12224step1 raw12224step1Labels = mixedMoment B raw12224step2 raw12224step2Labels := by
      have ha : raw12224step2 = (fun i j => raw12224step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12224step2 raw12224step1; decide +kernel
      have hl : raw12224step2Labels = raw12224step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12224step1 raw12224step1Labels permutation29 permutation5
    mixedMoment B raw12224step2 raw12224step2Labels = mixedMoment B raw12224step3 raw12224step3Labels := by
      have ha : raw12224step3 = raw12224step2 := by apply Matrix.ext; unfold raw12224step3 raw12224step2; decide +kernel
      have hl : raw12224step2Labels = labelEmbedding1 ∘ raw12224step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12224step2 raw12224step2Labels raw12224step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2769 node2769Labels := by rfl

def raw12225 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12225Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12225step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12225step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12225step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12225step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw12225step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12225step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw12225step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12225 raw12225Labels = mixedMoment B node3623 node3623Labels := by
  calc
    mixedMoment B raw12225 raw12225Labels = mixedMoment B raw12225step0 raw12225step0Labels := by
      have hz : ∀ j, raw12225 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12225step0 = (fun i j => raw12225 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12225step0 raw12225; decide +kernel
      have hl : raw12225step0Labels = raw12225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12225 raw12225Labels permutation346 hz
    mixedMoment B raw12225step0 raw12225step0Labels = mixedMoment B raw12225step1 raw12225step1Labels := by
      have hz : ∀ j, raw12225step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12225step1 = (fun i j => raw12225step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12225step1 raw12225step0; decide +kernel
      have hl : raw12225step1Labels = raw12225step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12225step0 raw12225step0Labels permutation56 hz
    mixedMoment B raw12225step1 raw12225step1Labels = mixedMoment B raw12225step2 raw12225step2Labels := by
      have ha : raw12225step2 = (fun i j => raw12225step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12225step2 raw12225step1; decide +kernel
      have hl : raw12225step2Labels = raw12225step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12225step1 raw12225step1Labels permutation8 permutation4
    mixedMoment B raw12225step2 raw12225step2Labels = mixedMoment B raw12225step3 raw12225step3Labels := by
      have ha : raw12225step3 = -raw12225step2 := by apply Matrix.ext; change ∀ i j, raw12225step3 i j = -(raw12225step2 i j); unfold raw12225step3 raw12225step2; decide +kernel
      have hl : raw12225step3Labels = raw12225step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3623 node3623Labels := by rfl

def raw12226 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12226Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12226step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw12226step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12226step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12226step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12226 raw12226Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw12226 raw12226Labels = mixedMoment B raw12226step0 raw12226step0Labels := by
      have hz : ∀ j, raw12226 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12226step0 = (fun i j => raw12226 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12226step0 raw12226; decide +kernel
      have hl : raw12226step0Labels = raw12226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12226 raw12226Labels permutation265 hz
    mixedMoment B raw12226step0 raw12226step0Labels = mixedMoment B raw12226step1 raw12226step1Labels := by
      have ha : raw12226step1 = (fun i j => raw12226step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12226step1 raw12226step0; decide +kernel
      have hl : raw12226step1Labels = raw12226step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12226step0 raw12226step0Labels permutation50 permutation2
    mixedMoment B raw12226step1 raw12226step1Labels = mixedMoment B raw12226step2 raw12226step2Labels := by
      have ha : raw12226step2 = -raw12226step1 := by apply Matrix.ext; change ∀ i j, raw12226step2 i j = -(raw12226step1 i j); unfold raw12226step2 raw12226step1; decide +kernel
      have hl : raw12226step2Labels = raw12226step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3581 node3581Labels := by rfl

def raw12227 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12227Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12227step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12227step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12227step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12227step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12227step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12227step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12227step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12227 raw12227Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw12227 raw12227Labels = mixedMoment B raw12227step0 raw12227step0Labels := by
      have hz : ∀ j, raw12227 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12227step0 = (fun i j => raw12227 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12227step0 raw12227; decide +kernel
      have hl : raw12227step0Labels = raw12227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12227 raw12227Labels permutation346 hz
    mixedMoment B raw12227step0 raw12227step0Labels = mixedMoment B raw12227step1 raw12227step1Labels := by
      have hz : ∀ j, raw12227step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12227step1 = (fun i j => raw12227step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12227step1 raw12227step0; decide +kernel
      have hl : raw12227step1Labels = raw12227step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12227step0 raw12227step0Labels permutation56 hz
    mixedMoment B raw12227step1 raw12227step1Labels = mixedMoment B raw12227step2 raw12227step2Labels := by
      have ha : raw12227step2 = (fun i j => raw12227step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12227step2 raw12227step1; decide +kernel
      have hl : raw12227step2Labels = raw12227step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12227step1 raw12227step1Labels permutation13 permutation2
    mixedMoment B raw12227step2 raw12227step2Labels = mixedMoment B raw12227step3 raw12227step3Labels := by
      have ha : raw12227step3 = -raw12227step2 := by apply Matrix.ext; change ∀ i j, raw12227step3 i j = -(raw12227step2 i j); unfold raw12227step3 raw12227step2; decide +kernel
      have hl : raw12227step3Labels = raw12227step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3583 node3583Labels := by rfl

def raw12228 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12228Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12228step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12228step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw12228step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12228step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12228step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12228step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12228step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12228 raw12228Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw12228 raw12228Labels = mixedMoment B raw12228step0 raw12228step0Labels := by
      have hz : ∀ j, raw12228 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12228step0 = (fun i j => raw12228 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12228step0 raw12228; decide +kernel
      have hl : raw12228step0Labels = raw12228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12228 raw12228Labels permutation346 hz
    mixedMoment B raw12228step0 raw12228step0Labels = mixedMoment B raw12228step1 raw12228step1Labels := by
      have hz : ∀ j, raw12228step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12228step1 = (fun i j => raw12228step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12228step1 raw12228step0; decide +kernel
      have hl : raw12228step1Labels = raw12228step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12228step0 raw12228step0Labels permutation56 hz
    mixedMoment B raw12228step1 raw12228step1Labels = mixedMoment B raw12228step2 raw12228step2Labels := by
      have ha : raw12228step2 = (fun i j => raw12228step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12228step2 raw12228step1; decide +kernel
      have hl : raw12228step2Labels = raw12228step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12228step1 raw12228step1Labels permutation12 permutation2
    mixedMoment B raw12228step2 raw12228step2Labels = mixedMoment B raw12228step3 raw12228step3Labels := by
      have ha : raw12228step3 = -raw12228step2 := by apply Matrix.ext; change ∀ i j, raw12228step3 i j = -(raw12228step2 i j); unfold raw12228step3 raw12228step2; decide +kernel
      have hl : raw12228step3Labels = raw12228step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3583 node3583Labels := by rfl

def raw12229 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12229Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12229step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12229step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12229step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12229step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12229step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12229step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12229step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12229 raw12229Labels = mixedMoment B node3628 node3628Labels := by
  calc
    mixedMoment B raw12229 raw12229Labels = mixedMoment B raw12229step0 raw12229step0Labels := by
      have hz : ∀ j, raw12229 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw12229step0 = (fun i j => raw12229 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw12229step0 raw12229; decide +kernel
      have hl : raw12229step0Labels = raw12229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12229 raw12229Labels permutation346 hz
    mixedMoment B raw12229step0 raw12229step0Labels = mixedMoment B raw12229step1 raw12229step1Labels := by
      have hz : ∀ j, raw12229step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12229step1 = (fun i j => raw12229step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12229step1 raw12229step0; decide +kernel
      have hl : raw12229step1Labels = raw12229step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12229step0 raw12229step0Labels permutation56 hz
    mixedMoment B raw12229step1 raw12229step1Labels = mixedMoment B raw12229step2 raw12229step2Labels := by
      have ha : raw12229step2 = (fun i j => raw12229step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12229step2 raw12229step1; decide +kernel
      have hl : raw12229step2Labels = raw12229step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12229step1 raw12229step1Labels permutation12 permutation2
    mixedMoment B raw12229step2 raw12229step2Labels = mixedMoment B raw12229step3 raw12229step3Labels := by
      have ha : raw12229step3 = -raw12229step2 := by apply Matrix.ext; change ∀ i j, raw12229step3 i j = -(raw12229step2 i j); unfold raw12229step3 raw12229step2; decide +kernel
      have hl : raw12229step3Labels = raw12229step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3628 node3628Labels := by rfl

def raw12230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12230 raw12230Labels = mixedMoment B node5430 node5430Labels := by
  calc
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw12231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12231step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw12231step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12231step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw12231step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12231step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw12231step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12231 raw12231Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw12231 raw12231Labels = mixedMoment B raw12231step0 raw12231step0Labels := by
      have hz : ∀ j, raw12231 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12231step0 = (fun i j => raw12231 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12231step0 raw12231; decide +kernel
      have hl : raw12231step0Labels = raw12231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12231 raw12231Labels permutation265 hz
    mixedMoment B raw12231step0 raw12231step0Labels = mixedMoment B raw12231step1 raw12231step1Labels := by
      have ha : raw12231step1 = (fun i j => raw12231step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12231step1 raw12231step0; decide +kernel
      have hl : raw12231step1Labels = raw12231step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12231step0 raw12231step0Labels permutation40 permutation7
    mixedMoment B raw12231step1 raw12231step1Labels = mixedMoment B raw12231step2 raw12231step2Labels := by
      have ha : raw12231step2 = -raw12231step1 := by apply Matrix.ext; change ∀ i j, raw12231step2 i j = -(raw12231step1 i j); unfold raw12231step2 raw12231step1; decide +kernel
      have hl : raw12231step2Labels = raw12231step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12231step2 raw12231step2Labels = mixedMoment B raw12231step3 raw12231step3Labels := by
      have ha : raw12231step3 = raw12231step2 := by apply Matrix.ext; unfold raw12231step3 raw12231step2; decide +kernel
      have hl : raw12231step2Labels = labelEmbedding10 ∘ raw12231step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12231step2 raw12231step2Labels raw12231step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw12232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12232step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw12232step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12232step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12232step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12232step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12232step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12232 raw12232Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw12232 raw12232Labels = mixedMoment B raw12232step0 raw12232step0Labels := by
      have hz : ∀ j, raw12232 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12232step0 = (fun i j => raw12232 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12232step0 raw12232; decide +kernel
      have hl : raw12232step0Labels = raw12232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12232 raw12232Labels permutation265 hz
    mixedMoment B raw12232step0 raw12232step0Labels = mixedMoment B raw12232step1 raw12232step1Labels := by
      have ha : raw12232step1 = (fun i j => raw12232step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12232step1 raw12232step0; decide +kernel
      have hl : raw12232step1Labels = raw12232step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12232step0 raw12232step0Labels permutation40 permutation7
    mixedMoment B raw12232step1 raw12232step1Labels = mixedMoment B raw12232step2 raw12232step2Labels := by
      have ha : raw12232step2 = -raw12232step1 := by apply Matrix.ext; change ∀ i j, raw12232step2 i j = -(raw12232step1 i j); unfold raw12232step2 raw12232step1; decide +kernel
      have hl : raw12232step2Labels = raw12232step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12232step2 raw12232step2Labels = mixedMoment B raw12232step3 raw12232step3Labels := by
      have ha : raw12232step3 = raw12232step2 := by apply Matrix.ext; unfold raw12232step3 raw12232step2; decide +kernel
      have hl : raw12232step2Labels = labelEmbedding10 ∘ raw12232step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12232step2 raw12232step2Labels raw12232step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw12233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw12233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12233step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12233step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12233step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw12233step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12233step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12233step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12233step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12233step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12233 raw12233Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw12233 raw12233Labels = mixedMoment B raw12233step0 raw12233step0Labels := by
      have hz : ∀ j, raw12233 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12233step0 = (fun i j => raw12233 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12233step0 raw12233; decide +kernel
      have hl : raw12233step0Labels = raw12233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12233 raw12233Labels permutation520 hz
    mixedMoment B raw12233step0 raw12233step0Labels = mixedMoment B raw12233step1 raw12233step1Labels := by
      have hz : ∀ j, raw12233step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12233step1 = (fun i j => raw12233step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12233step1 raw12233step0; decide +kernel
      have hl : raw12233step1Labels = raw12233step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12233step0 raw12233step0Labels permutation56 hz
    mixedMoment B raw12233step1 raw12233step1Labels = mixedMoment B raw12233step2 raw12233step2Labels := by
      have ha : raw12233step2 = (fun i j => raw12233step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12233step2 raw12233step1; decide +kernel
      have hl : raw12233step2Labels = raw12233step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12233step1 raw12233step1Labels permutation10 permutation7
    mixedMoment B raw12233step2 raw12233step2Labels = mixedMoment B raw12233step3 raw12233step3Labels := by
      have ha : raw12233step3 = -raw12233step2 := by apply Matrix.ext; change ∀ i j, raw12233step3 i j = -(raw12233step2 i j); unfold raw12233step3 raw12233step2; decide +kernel
      have hl : raw12233step3Labels = raw12233step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12233step3 raw12233step3Labels = mixedMoment B raw12233step4 raw12233step4Labels := by
      have ha : raw12233step4 = raw12233step3 := by apply Matrix.ext; unfold raw12233step4 raw12233step3; decide +kernel
      have hl : raw12233step3Labels = labelEmbedding10 ∘ raw12233step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12233step3 raw12233step3Labels raw12233step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw12234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12234step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12234step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12234step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12234 raw12234Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw12234 raw12234Labels = mixedMoment B raw12234step0 raw12234step0Labels := by
      have hz : ∀ j, raw12234 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12234step0 = (fun i j => raw12234 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12234step0 raw12234; decide +kernel
      have hl : raw12234step0Labels = raw12234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12234 raw12234Labels permutation265 hz
    mixedMoment B raw12234step0 raw12234step0Labels = mixedMoment B raw12234step1 raw12234step1Labels := by
      have ha : raw12234step1 = (fun i j => raw12234step0 (permutation139 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12234step1 raw12234step0; decide +kernel
      have hl : raw12234step1Labels = raw12234step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12234step0 raw12234step0Labels permutation139 permutation6
    mixedMoment B raw12234step1 raw12234step1Labels = mixedMoment B raw12234step2 raw12234step2Labels := by
      have ha : raw12234step2 = raw12234step1 := by apply Matrix.ext; unfold raw12234step2 raw12234step1; decide +kernel
      have hl : raw12234step1Labels = labelEmbedding9 ∘ raw12234step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12234step1 raw12234step1Labels raw12234step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw12235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12235step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw12235step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12235step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw12235step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12235 raw12235Labels = mixedMoment B node4595 node4595Labels := by
  calc
    mixedMoment B raw12235 raw12235Labels = mixedMoment B raw12235step0 raw12235step0Labels := by
      have ha : raw12235step0 = (fun i j => raw12235 (permutation195 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12235step0 raw12235; decide +kernel
      have hl : raw12235step0Labels = raw12235Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12235 raw12235Labels permutation195 permutation3
    mixedMoment B raw12235step0 raw12235step0Labels = mixedMoment B raw12235step1 raw12235step1Labels := by
      have ha : raw12235step1 = raw12235step0 := by apply Matrix.ext; unfold raw12235step1 raw12235step0; decide +kernel
      have hl : raw12235step0Labels = labelEmbedding6 ∘ raw12235step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12235step0 raw12235step0Labels raw12235step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4595 node4595Labels := by rfl

def raw12236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12236step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12236 raw12236Labels = mixedMoment B node5196 node5196Labels := by
  calc
    mixedMoment B raw12236 raw12236Labels = mixedMoment B raw12236step0 raw12236step0Labels := by
      have ha : raw12236step0 = (fun i j => raw12236 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12236step0 raw12236; decide +kernel
      have hl : raw12236step0Labels = raw12236Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12236 raw12236Labels permutation182 permutation2
    _ = mixedMoment B node5196 node5196Labels := by rfl

def raw12237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12237step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12237 raw12237Labels = mixedMoment B node5256 node5256Labels := by
  calc
    mixedMoment B raw12237 raw12237Labels = mixedMoment B raw12237step0 raw12237step0Labels := by
      have ha : raw12237step0 = (fun i j => raw12237 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12237step0 raw12237; decide +kernel
      have hl : raw12237step0Labels = raw12237Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12237 raw12237Labels permutation206 permutation2
    _ = mixedMoment B node5256 node5256Labels := by rfl

def raw12238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw12238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12238step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12238step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12238step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12238 raw12238Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw12238 raw12238Labels = mixedMoment B raw12238step0 raw12238step0Labels := by
      have hz : ∀ j, raw12238 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12238step0 = (fun i j => raw12238 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12238step0 raw12238; decide +kernel
      have hl : raw12238step0Labels = raw12238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12238 raw12238Labels permutation520 hz
    mixedMoment B raw12238step0 raw12238step0Labels = mixedMoment B raw12238step1 raw12238step1Labels := by
      have ha : raw12238step1 = (fun i j => raw12238step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12238step1 raw12238step0; decide +kernel
      have hl : raw12238step1Labels = raw12238step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12238step0 raw12238step0Labels permutation40 permutation2
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw12239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12239step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw12239step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12239 raw12239Labels = mixedMoment B node5286 node5286Labels := by
  calc
    mixedMoment B raw12239 raw12239Labels = mixedMoment B raw12239step0 raw12239step0Labels := by
      have ha : raw12239step0 = (fun i j => raw12239 (permutation196 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12239step0 raw12239; decide +kernel
      have hl : raw12239step0Labels = raw12239Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12239 raw12239Labels permutation196 permutation2
    _ = mixedMoment B node5286 node5286Labels := by rfl

def raw12240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12240step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12240step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12240 raw12240Labels = mixedMoment B node4616 node4616Labels := by
  calc
    mixedMoment B raw12240 raw12240Labels = mixedMoment B raw12240step0 raw12240step0Labels := by
      have hz : ∀ j, raw12240 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12240step0 = (fun i j => raw12240 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12240step0 raw12240; decide +kernel
      have hl : raw12240step0Labels = raw12240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12240 raw12240Labels permutation265 hz
    mixedMoment B raw12240step0 raw12240step0Labels = mixedMoment B raw12240step1 raw12240step1Labels := by
      have ha : raw12240step1 = (fun i j => raw12240step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12240step1 raw12240step0; decide +kernel
      have hl : raw12240step1Labels = raw12240step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12240step0 raw12240step0Labels permutation40 permutation2
    _ = mixedMoment B node4616 node4616Labels := by rfl

def raw12241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12241step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12241 raw12241Labels = mixedMoment B node5160 node5160Labels := by
  calc
    mixedMoment B raw12241 raw12241Labels = mixedMoment B raw12241step0 raw12241step0Labels := by
      have ha : raw12241step0 = (fun i j => raw12241 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12241step0 raw12241; decide +kernel
      have hl : raw12241step0Labels = raw12241Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12241 raw12241Labels permutation160 permutation2
    _ = mixedMoment B node5160 node5160Labels := by rfl

def raw12242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12242step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12242step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12242step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12242 raw12242Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw12242 raw12242Labels = mixedMoment B raw12242step0 raw12242step0Labels := by
      have hz : ∀ j, raw12242 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12242step0 = (fun i j => raw12242 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12242step0 raw12242; decide +kernel
      have hl : raw12242step0Labels = raw12242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12242 raw12242Labels permutation265 hz
    mixedMoment B raw12242step0 raw12242step0Labels = mixedMoment B raw12242step1 raw12242step1Labels := by
      have ha : raw12242step1 = (fun i j => raw12242step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12242step1 raw12242step0; decide +kernel
      have hl : raw12242step1Labels = raw12242step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12242step0 raw12242step0Labels permutation40 permutation2
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw12243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw12243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12243step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12243step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12243step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12243step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12243 raw12243Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw12243 raw12243Labels = mixedMoment B raw12243step0 raw12243step0Labels := by
      have hz : ∀ j, raw12243 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12243step0 = (fun i j => raw12243 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12243step0 raw12243; decide +kernel
      have hl : raw12243step0Labels = raw12243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12243 raw12243Labels permutation520 hz
    mixedMoment B raw12243step0 raw12243step0Labels = mixedMoment B raw12243step1 raw12243step1Labels := by
      have hz : ∀ j, raw12243step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12243step1 = (fun i j => raw12243step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12243step1 raw12243step0; decide +kernel
      have hl : raw12243step1Labels = raw12243step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12243step0 raw12243step0Labels permutation56 hz
    mixedMoment B raw12243step1 raw12243step1Labels = mixedMoment B raw12243step2 raw12243step2Labels := by
      have ha : raw12243step2 = (fun i j => raw12243step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12243step2 raw12243step1; decide +kernel
      have hl : raw12243step2Labels = raw12243step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12243step1 raw12243step1Labels permutation10 permutation2
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw12244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12244step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12244step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12244 raw12244Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw12244 raw12244Labels = mixedMoment B raw12244step0 raw12244step0Labels := by
      have hz : ∀ j, raw12244 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12244step0 = (fun i j => raw12244 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12244step0 raw12244; decide +kernel
      have hl : raw12244step0Labels = raw12244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12244 raw12244Labels permutation265 hz
    mixedMoment B raw12244step0 raw12244step0Labels = mixedMoment B raw12244step1 raw12244step1Labels := by
      have ha : raw12244step1 = (fun i j => raw12244step0 (permutation53 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12244step1 raw12244step0; decide +kernel
      have hl : raw12244step1Labels = raw12244step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12244step0 raw12244step0Labels permutation53 permutation2
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw12245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12245step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw12245step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12245step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw12245step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12245 raw12245Labels = mixedMoment B node4596 node4596Labels := by
  calc
    mixedMoment B raw12245 raw12245Labels = mixedMoment B raw12245step0 raw12245step0Labels := by
      have hz : ∀ j, raw12245 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12245step0 = (fun i j => raw12245 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12245step0 raw12245; decide +kernel
      have hl : raw12245step0Labels = raw12245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12245 raw12245Labels permutation265 hz
    mixedMoment B raw12245step0 raw12245step0Labels = mixedMoment B raw12245step1 raw12245step1Labels := by
      have ha : raw12245step1 = (fun i j => raw12245step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12245step1 raw12245step0; decide +kernel
      have hl : raw12245step1Labels = raw12245step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12245step0 raw12245step0Labels permutation37 permutation3
    mixedMoment B raw12245step1 raw12245step1Labels = mixedMoment B raw12245step2 raw12245step2Labels := by
      have ha : raw12245step2 = raw12245step1 := by apply Matrix.ext; unfold raw12245step2 raw12245step1; decide +kernel
      have hl : raw12245step1Labels = labelEmbedding6 ∘ raw12245step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12245step1 raw12245step1Labels raw12245step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4596 node4596Labels := by rfl

def raw12246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12246step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw12246step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw12246step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw12246step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12246 raw12246Labels = mixedMoment B node5091 node5091Labels := by
  calc
    mixedMoment B raw12246 raw12246Labels = mixedMoment B raw12246step0 raw12246step0Labels := by
      have ha : raw12246step0 = (fun i j => raw12246 (permutation504 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12246step0 raw12246; decide +kernel
      have hl : raw12246step0Labels = raw12246Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12246 raw12246Labels permutation504 permutation5
    mixedMoment B raw12246step0 raw12246step0Labels = mixedMoment B raw12246step1 raw12246step1Labels := by
      have ha : raw12246step1 = raw12246step0 := by apply Matrix.ext; unfold raw12246step1 raw12246step0; decide +kernel
      have hl : raw12246step0Labels = labelEmbedding8 ∘ raw12246step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12246step0 raw12246step0Labels raw12246step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5091 node5091Labels := by rfl

def raw12247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12247step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12247step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw12247step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw12247step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw12247step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12247 raw12247Labels = mixedMoment B node5096 node5096Labels := by
  calc
    mixedMoment B raw12247 raw12247Labels = mixedMoment B raw12247step0 raw12247step0Labels := by
      have hz : ∀ j, raw12247 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12247step0 = (fun i j => raw12247 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12247step0 raw12247; decide +kernel
      have hl : raw12247step0Labels = raw12247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12247 raw12247Labels permutation265 hz
    mixedMoment B raw12247step0 raw12247step0Labels = mixedMoment B raw12247step1 raw12247step1Labels := by
      have ha : raw12247step1 = (fun i j => raw12247step0 (permutation96 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12247step1 raw12247step0; decide +kernel
      have hl : raw12247step1Labels = raw12247step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12247step0 raw12247step0Labels permutation96 permutation5
    mixedMoment B raw12247step1 raw12247step1Labels = mixedMoment B raw12247step2 raw12247step2Labels := by
      have ha : raw12247step2 = raw12247step1 := by apply Matrix.ext; unfold raw12247step2 raw12247step1; decide +kernel
      have hl : raw12247step1Labels = labelEmbedding8 ∘ raw12247step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12247step1 raw12247step1Labels raw12247step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5096 node5096Labels := by rfl

def raw12248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![0, 0, 0], ![1, 1, -2]]
def raw12248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, 1, -2]]
def raw12248step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12248step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -3, 1], ![1, 1, -2]]
def raw12248step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12248step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12248step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12248 raw12248Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw12248 raw12248Labels = mixedMoment B raw12248step0 raw12248step0Labels := by
      have hz : ∀ j, raw12248 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12248step0 = (fun i j => raw12248 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12248step0 raw12248; decide +kernel
      have hl : raw12248step0Labels = raw12248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12248 raw12248Labels permutation520 hz
    mixedMoment B raw12248step0 raw12248step0Labels = mixedMoment B raw12248step1 raw12248step1Labels := by
      have hz : ∀ j, raw12248step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12248step1 = (fun i j => raw12248step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12248step1 raw12248step0; decide +kernel
      have hl : raw12248step1Labels = raw12248step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12248step0 raw12248step0Labels permutation56 hz
    mixedMoment B raw12248step1 raw12248step1Labels = mixedMoment B raw12248step2 raw12248step2Labels := by
      have ha : raw12248step2 = (fun i j => raw12248step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12248step2 raw12248step1; decide +kernel
      have hl : raw12248step2Labels = raw12248step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12248step1 raw12248step1Labels permutation9 permutation2
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw12249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12249step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw12249step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw12249step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw12249step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12249 raw12249Labels = mixedMoment B node5103 node5103Labels := by
  calc
    mixedMoment B raw12249 raw12249Labels = mixedMoment B raw12249step0 raw12249step0Labels := by
      have hz : ∀ j, raw12249 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12249step0 = (fun i j => raw12249 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12249step0 raw12249; decide +kernel
      have hl : raw12249step0Labels = raw12249Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12249 raw12249Labels permutation265 hz
    mixedMoment B raw12249step0 raw12249step0Labels = mixedMoment B raw12249step1 raw12249step1Labels := by
      have ha : raw12249step1 = (fun i j => raw12249step0 (permutation94 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12249step1 raw12249step0; decide +kernel
      have hl : raw12249step1Labels = raw12249step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12249step0 raw12249step0Labels permutation94 permutation5
    mixedMoment B raw12249step1 raw12249step1Labels = mixedMoment B raw12249step2 raw12249step2Labels := by
      have ha : raw12249step2 = raw12249step1 := by apply Matrix.ext; unfold raw12249step2 raw12249step1; decide +kernel
      have hl : raw12249step1Labels = labelEmbedding8 ∘ raw12249step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12249step1 raw12249step1Labels raw12249step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5103 node5103Labels := by rfl

def raw12250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12250step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw12250step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12250step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw12250step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12250 raw12250Labels = mixedMoment B node4597 node4597Labels := by
  calc
    mixedMoment B raw12250 raw12250Labels = mixedMoment B raw12250step0 raw12250step0Labels := by
      have hz : ∀ j, raw12250 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12250step0 = (fun i j => raw12250 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12250step0 raw12250; decide +kernel
      have hl : raw12250step0Labels = raw12250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12250 raw12250Labels permutation265 hz
    mixedMoment B raw12250step0 raw12250step0Labels = mixedMoment B raw12250step1 raw12250step1Labels := by
      have ha : raw12250step1 = (fun i j => raw12250step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12250step1 raw12250step0; decide +kernel
      have hl : raw12250step1Labels = raw12250step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12250step0 raw12250step0Labels permutation36 permutation3
    mixedMoment B raw12250step1 raw12250step1Labels = mixedMoment B raw12250step2 raw12250step2Labels := by
      have ha : raw12250step2 = raw12250step1 := by apply Matrix.ext; unfold raw12250step2 raw12250step1; decide +kernel
      have hl : raw12250step1Labels = labelEmbedding6 ∘ raw12250step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12250step1 raw12250step1Labels raw12250step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4597 node4597Labels := by rfl

def raw12251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12251step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw12251step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12251 raw12251Labels = mixedMoment B node5146 node5146Labels := by
  calc
    mixedMoment B raw12251 raw12251Labels = mixedMoment B raw12251step0 raw12251step0Labels := by
      have ha : raw12251step0 = (fun i j => raw12251 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12251step0 raw12251; decide +kernel
      have hl : raw12251step0Labels = raw12251Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12251 raw12251Labels permutation153 permutation2
    _ = mixedMoment B node5146 node5146Labels := by rfl

def raw12252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12252step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw12252step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12252 raw12252Labels = mixedMoment B node5200 node5200Labels := by
  calc
    mixedMoment B raw12252 raw12252Labels = mixedMoment B raw12252step0 raw12252step0Labels := by
      have hz : ∀ j, raw12252 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12252step0 = (fun i j => raw12252 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12252step0 raw12252; decide +kernel
      have hl : raw12252step0Labels = raw12252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12252 raw12252Labels permutation265 hz
    mixedMoment B raw12252step0 raw12252step0Labels = mixedMoment B raw12252step1 raw12252step1Labels := by
      have ha : raw12252step1 = (fun i j => raw12252step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12252step1 raw12252step0; decide +kernel
      have hl : raw12252step1Labels = raw12252step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12252step0 raw12252step0Labels permutation33 permutation2
    _ = mixedMoment B node5200 node5200Labels := by rfl

def raw12253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12253step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12253step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12253 raw12253Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw12253 raw12253Labels = mixedMoment B raw12253step0 raw12253step0Labels := by
      have hz : ∀ j, raw12253 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12253step0 = (fun i j => raw12253 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12253step0 raw12253; decide +kernel
      have hl : raw12253step0Labels = raw12253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12253 raw12253Labels permutation265 hz
    mixedMoment B raw12253step0 raw12253step0Labels = mixedMoment B raw12253step1 raw12253step1Labels := by
      have ha : raw12253step1 = (fun i j => raw12253step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12253step1 raw12253step0; decide +kernel
      have hl : raw12253step1Labels = raw12253step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12253step0 raw12253step0Labels permutation39 permutation2
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw12254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![0, 2, -2]]
def raw12254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![0, 2, -2]]
def raw12254step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw12254step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12254 raw12254Labels = mixedMoment B node5287 node5287Labels := by
  calc
    mixedMoment B raw12254 raw12254Labels = mixedMoment B raw12254step0 raw12254step0Labels := by
      have hz : ∀ j, raw12254 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12254step0 = (fun i j => raw12254 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12254step0 raw12254; decide +kernel
      have hl : raw12254step0Labels = raw12254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12254 raw12254Labels permutation265 hz
    mixedMoment B raw12254step0 raw12254step0Labels = mixedMoment B raw12254step1 raw12254step1Labels := by
      have ha : raw12254step1 = (fun i j => raw12254step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12254step1 raw12254step0; decide +kernel
      have hl : raw12254step1Labels = raw12254step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12254step0 raw12254step0Labels permutation36 permutation2
    _ = mixedMoment B node5287 node5287Labels := by rfl

def raw12255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12255step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12255step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12255step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12255step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12255step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12255 raw12255Labels = mixedMoment B node4607 node4607Labels := by
  calc
    mixedMoment B raw12255 raw12255Labels = mixedMoment B raw12255step0 raw12255step0Labels := by
      have hz : ∀ j, raw12255 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12255step0 = (fun i j => raw12255 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12255step0 raw12255; decide +kernel
      have hl : raw12255step0Labels = raw12255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12255 raw12255Labels permutation265 hz
    mixedMoment B raw12255step0 raw12255step0Labels = mixedMoment B raw12255step1 raw12255step1Labels := by
      have ha : raw12255step1 = (fun i j => raw12255step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12255step1 raw12255step0; decide +kernel
      have hl : raw12255step1Labels = raw12255step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12255step0 raw12255step0Labels permutation34 permutation3
    mixedMoment B raw12255step1 raw12255step1Labels = mixedMoment B raw12255step2 raw12255step2Labels := by
      have ha : raw12255step2 = raw12255step1 := by apply Matrix.ext; unfold raw12255step2 raw12255step1; decide +kernel
      have hl : raw12255step1Labels = labelEmbedding6 ∘ raw12255step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12255step1 raw12255step1Labels raw12255step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4607 node4607Labels := by rfl

def raw12256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12256 raw12256Labels = mixedMoment B node5144 node5144Labels := by
  calc
    _ = mixedMoment B node5144 node5144Labels := by rfl

def raw12257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12257Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12257step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12257 raw12257Labels = mixedMoment B node5198 node5198Labels := by
  calc
    mixedMoment B raw12257 raw12257Labels = mixedMoment B raw12257step0 raw12257step0Labels := by
      have hz : ∀ j, raw12257 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12257step0 = (fun i j => raw12257 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12257step0 raw12257; decide +kernel
      have hl : raw12257step0Labels = raw12257Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12257 raw12257Labels permutation265 hz
    _ = mixedMoment B node5198 node5198Labels := by rfl

def raw12258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12258step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw12258step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12258 raw12258Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw12258 raw12258Labels = mixedMoment B raw12258step0 raw12258step0Labels := by
      have hz : ∀ j, raw12258 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12258step0 = (fun i j => raw12258 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12258step0 raw12258; decide +kernel
      have hl : raw12258step0Labels = raw12258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12258 raw12258Labels permutation265 hz
    mixedMoment B raw12258step0 raw12258step0Labels = mixedMoment B raw12258step1 raw12258step1Labels := by
      have ha : raw12258step1 = (fun i j => raw12258step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12258step1 raw12258step0; decide +kernel
      have hl : raw12258step1Labels = raw12258step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12258step0 raw12258step0Labels permutation38 permutation2
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw12259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw12259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw12259step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12259step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw12259step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12259 raw12259Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw12259 raw12259Labels = mixedMoment B raw12259step0 raw12259step0Labels := by
      have hz : ∀ j, raw12259 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12259step0 = (fun i j => raw12259 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12259step0 raw12259; decide +kernel
      have hl : raw12259step0Labels = raw12259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12259 raw12259Labels permutation520 hz
    mixedMoment B raw12259step0 raw12259step0Labels = mixedMoment B raw12259step1 raw12259step1Labels := by
      have hz : ∀ j, raw12259step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12259step1 = (fun i j => raw12259step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12259step1 raw12259step0; decide +kernel
      have hl : raw12259step1Labels = raw12259step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12259step0 raw12259step0Labels permutation56 hz
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw12260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12260Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12260step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12260step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12260 raw12260Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw12260 raw12260Labels = mixedMoment B raw12260step0 raw12260step0Labels := by
      have ha : raw12260step0 = (fun i j => raw12260 (permutation634 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12260step0 raw12260; decide +kernel
      have hl : raw12260step0Labels = raw12260Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12260 raw12260Labels permutation634 permutation6
    _ = mixedMoment B node3972 node3972Labels := by rfl

def raw12261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12261Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12261step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12261step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12261 raw12261Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw12261 raw12261Labels = mixedMoment B raw12261step0 raw12261step0Labels := by
      have hz : ∀ j, raw12261 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12261step0 = (fun i j => raw12261 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12261step0 raw12261; decide +kernel
      have hl : raw12261step0Labels = raw12261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12261 raw12261Labels permutation265 hz
    mixedMoment B raw12261step0 raw12261step0Labels = mixedMoment B raw12261step1 raw12261step1Labels := by
      have ha : raw12261step1 = (fun i j => raw12261step0 (permutation139 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12261step1 raw12261step0; decide +kernel
      have hl : raw12261step1Labels = raw12261step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12261step0 raw12261step0Labels permutation139 permutation6
    _ = mixedMoment B node3959 node3959Labels := by rfl

def raw12262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12262Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12262step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12262step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12262 raw12262Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw12262 raw12262Labels = mixedMoment B raw12262step0 raw12262step0Labels := by
      have hz : ∀ j, raw12262 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12262step0 = (fun i j => raw12262 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12262step0 raw12262; decide +kernel
      have hl : raw12262step0Labels = raw12262Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12262 raw12262Labels permutation265 hz
    mixedMoment B raw12262step0 raw12262step0Labels = mixedMoment B raw12262step1 raw12262step1Labels := by
      have ha : raw12262step1 = (fun i j => raw12262step0 (permutation139 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12262step1 raw12262step0; decide +kernel
      have hl : raw12262step1Labels = raw12262step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12262step0 raw12262step0Labels permutation139 permutation6
    _ = mixedMoment B node3982 node3982Labels := by rfl

def raw12263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw12263Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12263step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12263step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12263step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12263step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw12263step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12263 raw12263Labels = mixedMoment B node3987 node3987Labels := by
  calc
    mixedMoment B raw12263 raw12263Labels = mixedMoment B raw12263step0 raw12263step0Labels := by
      have hz : ∀ j, raw12263 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12263step0 = (fun i j => raw12263 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12263step0 raw12263; decide +kernel
      have hl : raw12263step0Labels = raw12263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12263 raw12263Labels permutation520 hz
    mixedMoment B raw12263step0 raw12263step0Labels = mixedMoment B raw12263step1 raw12263step1Labels := by
      have hz : ∀ j, raw12263step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12263step1 = (fun i j => raw12263step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12263step1 raw12263step0; decide +kernel
      have hl : raw12263step1Labels = raw12263step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12263step0 raw12263step0Labels permutation56 hz
    mixedMoment B raw12263step1 raw12263step1Labels = mixedMoment B raw12263step2 raw12263step2Labels := by
      have ha : raw12263step2 = (fun i j => raw12263step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12263step2 raw12263step1; decide +kernel
      have hl : raw12263step2Labels = raw12263step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12263step1 raw12263step1Labels permutation29 permutation6
    _ = mixedMoment B node3987 node3987Labels := by rfl

def raw12264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12264Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12264step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12264step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12264 raw12264Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw12264 raw12264Labels = mixedMoment B raw12264step0 raw12264step0Labels := by
      have hz : ∀ j, raw12264 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12264step0 = (fun i j => raw12264 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12264step0 raw12264; decide +kernel
      have hl : raw12264step0Labels = raw12264Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12264 raw12264Labels permutation265 hz
    mixedMoment B raw12264step0 raw12264step0Labels = mixedMoment B raw12264step1 raw12264step1Labels := by
      have ha : raw12264step1 = (fun i j => raw12264step0 (permutation139 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12264step1 raw12264step0; decide +kernel
      have hl : raw12264step1Labels = raw12264step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12264step0 raw12264step0Labels permutation139 permutation6
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw12265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12265Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw12265step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12265 raw12265Labels = mixedMoment B node1228 node1228Labels := by
  calc
    mixedMoment B raw12265 raw12265Labels = mixedMoment B raw12265step0 raw12265step0Labels := by
      have ha : raw12265step0 = (fun i j => raw12265 (permutation195 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12265step0 raw12265; decide +kernel
      have hl : raw12265step0Labels = raw12265Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12265 raw12265Labels permutation195 permutation3
    _ = mixedMoment B node1228 node1228Labels := by rfl

def raw12266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12266Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12266step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw12266step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12266 raw12266Labels = mixedMoment B node2874 node2874Labels := by
  calc
    mixedMoment B raw12266 raw12266Labels = mixedMoment B raw12266step0 raw12266step0Labels := by
      have ha : raw12266step0 = (fun i j => raw12266 (permutation195 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12266step0 raw12266; decide +kernel
      have hl : raw12266step0Labels = raw12266Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12266 raw12266Labels permutation195 permutation3
    _ = mixedMoment B node2874 node2874Labels := by rfl

def raw12267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12267Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12267step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12267step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12267 raw12267Labels = mixedMoment B node3085 node3085Labels := by
  calc
    mixedMoment B raw12267 raw12267Labels = mixedMoment B raw12267step0 raw12267step0Labels := by
      have ha : raw12267step0 = (fun i j => raw12267 (permutation186 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12267step0 raw12267; decide +kernel
      have hl : raw12267step0Labels = raw12267Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12267 raw12267Labels permutation186 permutation3
    _ = mixedMoment B node3085 node3085Labels := by rfl

def raw12268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw12268Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12268step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12268step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12268 raw12268Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw12268 raw12268Labels = mixedMoment B raw12268step0 raw12268step0Labels := by
      have hz : ∀ j, raw12268 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12268step0 = (fun i j => raw12268 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12268step0 raw12268; decide +kernel
      have hl : raw12268step0Labels = raw12268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12268 raw12268Labels permutation520 hz
    mixedMoment B raw12268step0 raw12268step0Labels = mixedMoment B raw12268step1 raw12268step1Labels := by
      have ha : raw12268step1 = (fun i j => raw12268step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12268step1 raw12268step0; decide +kernel
      have hl : raw12268step1Labels = raw12268step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12268step0 raw12268step0Labels permutation42 permutation3
    _ = mixedMoment B node3097 node3097Labels := by rfl

def raw12269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12269Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw12269step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12269 raw12269Labels = mixedMoment B node3023 node3023Labels := by
  calc
    mixedMoment B raw12269 raw12269Labels = mixedMoment B raw12269step0 raw12269step0Labels := by
      have ha : raw12269step0 = (fun i j => raw12269 (permutation253 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12269step0 raw12269; decide +kernel
      have hl : raw12269step0Labels = raw12269Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12269 raw12269Labels permutation253 permutation3
    _ = mixedMoment B node3023 node3023Labels := by rfl

def raw12270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12270Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12270step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12270step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12270step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12270 raw12270Labels = mixedMoment B node1291 node1291Labels := by
  calc
    mixedMoment B raw12270 raw12270Labels = mixedMoment B raw12270step0 raw12270step0Labels := by
      have hz : ∀ j, raw12270 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12270step0 = (fun i j => raw12270 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12270step0 raw12270; decide +kernel
      have hl : raw12270step0Labels = raw12270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12270 raw12270Labels permutation265 hz
    mixedMoment B raw12270step0 raw12270step0Labels = mixedMoment B raw12270step1 raw12270step1Labels := by
      have ha : raw12270step1 = (fun i j => raw12270step0 (permutation51 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12270step1 raw12270step0; decide +kernel
      have hl : raw12270step1Labels = raw12270step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12270step0 raw12270step0Labels permutation51 permutation3
    _ = mixedMoment B node1291 node1291Labels := by rfl

def raw12271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12271Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12271step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12271step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12271 raw12271Labels = mixedMoment B node2951 node2951Labels := by
  calc
    mixedMoment B raw12271 raw12271Labels = mixedMoment B raw12271step0 raw12271step0Labels := by
      have ha : raw12271step0 = (fun i j => raw12271 (permutation171 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12271step0 raw12271; decide +kernel
      have hl : raw12271step0Labels = raw12271Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12271 raw12271Labels permutation171 permutation3
    _ = mixedMoment B node2951 node2951Labels := by rfl

def raw12272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12272Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12272step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12272step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12272 raw12272Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw12272 raw12272Labels = mixedMoment B raw12272step0 raw12272step0Labels := by
      have hz : ∀ j, raw12272 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12272step0 = (fun i j => raw12272 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12272step0 raw12272; decide +kernel
      have hl : raw12272step0Labels = raw12272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12272 raw12272Labels permutation265 hz
    mixedMoment B raw12272step0 raw12272step0Labels = mixedMoment B raw12272step1 raw12272step1Labels := by
      have ha : raw12272step1 = (fun i j => raw12272step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12272step1 raw12272step0; decide +kernel
      have hl : raw12272step1Labels = raw12272step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12272step0 raw12272step0Labels permutation42 permutation3
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw12273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw12273Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12273step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12273step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12273step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12273step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12273step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12273 raw12273Labels = mixedMoment B node3119 node3119Labels := by
  calc
    mixedMoment B raw12273 raw12273Labels = mixedMoment B raw12273step0 raw12273step0Labels := by
      have hz : ∀ j, raw12273 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12273step0 = (fun i j => raw12273 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12273step0 raw12273; decide +kernel
      have hl : raw12273step0Labels = raw12273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12273 raw12273Labels permutation520 hz
    mixedMoment B raw12273step0 raw12273step0Labels = mixedMoment B raw12273step1 raw12273step1Labels := by
      have hz : ∀ j, raw12273step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12273step1 = (fun i j => raw12273step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12273step1 raw12273step0; decide +kernel
      have hl : raw12273step1Labels = raw12273step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12273step0 raw12273step0Labels permutation56 hz
    mixedMoment B raw12273step1 raw12273step1Labels = mixedMoment B raw12273step2 raw12273step2Labels := by
      have ha : raw12273step2 = (fun i j => raw12273step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12273step2 raw12273step1; decide +kernel
      have hl : raw12273step2Labels = raw12273step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12273step1 raw12273step1Labels permutation12 permutation3
    _ = mixedMoment B node3119 node3119Labels := by rfl

def raw12274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12274Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12274step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12274step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12274step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12274 raw12274Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw12274 raw12274Labels = mixedMoment B raw12274step0 raw12274step0Labels := by
      have hz : ∀ j, raw12274 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12274step0 = (fun i j => raw12274 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12274step0 raw12274; decide +kernel
      have hl : raw12274step0Labels = raw12274Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12274 raw12274Labels permutation265 hz
    mixedMoment B raw12274step0 raw12274step0Labels = mixedMoment B raw12274step1 raw12274step1Labels := by
      have ha : raw12274step1 = (fun i j => raw12274step0 (permutation51 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12274step1 raw12274step0; decide +kernel
      have hl : raw12274step1Labels = raw12274step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12274step0 raw12274step0Labels permutation51 permutation3
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw12275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12275Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12275step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12275step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw12275step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12275 raw12275Labels = mixedMoment B node1229 node1229Labels := by
  calc
    mixedMoment B raw12275 raw12275Labels = mixedMoment B raw12275step0 raw12275step0Labels := by
      have hz : ∀ j, raw12275 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12275step0 = (fun i j => raw12275 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12275step0 raw12275; decide +kernel
      have hl : raw12275step0Labels = raw12275Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12275 raw12275Labels permutation265 hz
    mixedMoment B raw12275step0 raw12275step0Labels = mixedMoment B raw12275step1 raw12275step1Labels := by
      have ha : raw12275step1 = (fun i j => raw12275step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12275step1 raw12275step0; decide +kernel
      have hl : raw12275step1Labels = raw12275step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12275step0 raw12275step0Labels permutation37 permutation3
    _ = mixedMoment B node1229 node1229Labels := by rfl

def raw12276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12276Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12276step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw12276step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12276 raw12276Labels = mixedMoment B node2921 node2921Labels := by
  calc
    mixedMoment B raw12276 raw12276Labels = mixedMoment B raw12276step0 raw12276step0Labels := by
      have ha : raw12276step0 = (fun i j => raw12276 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12276step0 raw12276; decide +kernel
      have hl : raw12276step0Labels = raw12276Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12276 raw12276Labels permutation157 permutation3
    _ = mixedMoment B node2921 node2921Labels := by rfl

def raw12277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12277Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12277step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw12277step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12277 raw12277Labels = mixedMoment B node2875 node2875Labels := by
  calc
    mixedMoment B raw12277 raw12277Labels = mixedMoment B raw12277step0 raw12277step0Labels := by
      have hz : ∀ j, raw12277 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12277step0 = (fun i j => raw12277 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12277step0 raw12277; decide +kernel
      have hl : raw12277step0Labels = raw12277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12277 raw12277Labels permutation265 hz
    mixedMoment B raw12277step0 raw12277step0Labels = mixedMoment B raw12277step1 raw12277step1Labels := by
      have ha : raw12277step1 = (fun i j => raw12277step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12277step1 raw12277step0; decide +kernel
      have hl : raw12277step1Labels = raw12277step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12277step0 raw12277step0Labels permutation37 permutation3
    _ = mixedMoment B node2875 node2875Labels := by rfl

def raw12278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![0, 0, 0], ![1, 1, -2]]
def raw12278Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, 1, -2]]
def raw12278step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12278step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -3, 1], ![1, 1, -2]]
def raw12278step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12278step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw12278step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12278 raw12278Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw12278 raw12278Labels = mixedMoment B raw12278step0 raw12278step0Labels := by
      have hz : ∀ j, raw12278 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12278step0 = (fun i j => raw12278 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12278step0 raw12278; decide +kernel
      have hl : raw12278step0Labels = raw12278Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12278 raw12278Labels permutation520 hz
    mixedMoment B raw12278step0 raw12278step0Labels = mixedMoment B raw12278step1 raw12278step1Labels := by
      have hz : ∀ j, raw12278step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12278step1 = (fun i j => raw12278step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12278step1 raw12278step0; decide +kernel
      have hl : raw12278step1Labels = raw12278step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12278step0 raw12278step0Labels permutation56 hz
    mixedMoment B raw12278step1 raw12278step1Labels = mixedMoment B raw12278step2 raw12278step2Labels := by
      have ha : raw12278step2 = (fun i j => raw12278step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12278step2 raw12278step1; decide +kernel
      have hl : raw12278step2Labels = raw12278step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12278step1 raw12278step1Labels permutation9 permutation3
    _ = mixedMoment B node3098 node3098Labels := by rfl

def raw12279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12279Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12279step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12279step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw12279step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12279 raw12279Labels = mixedMoment B node3024 node3024Labels := by
  calc
    mixedMoment B raw12279 raw12279Labels = mixedMoment B raw12279step0 raw12279step0Labels := by
      have hz : ∀ j, raw12279 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12279step0 = (fun i j => raw12279 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12279step0 raw12279; decide +kernel
      have hl : raw12279step0Labels = raw12279Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12279 raw12279Labels permutation265 hz
    mixedMoment B raw12279step0 raw12279step0Labels = mixedMoment B raw12279step1 raw12279step1Labels := by
      have ha : raw12279step1 = (fun i j => raw12279step0 (permutation51 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12279step1 raw12279step0; decide +kernel
      have hl : raw12279step1Labels = raw12279step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12279step0 raw12279step0Labels permutation51 permutation3
    _ = mixedMoment B node3024 node3024Labels := by rfl

def raw12280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12280Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12280step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw12280step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12280 raw12280Labels = mixedMoment B node1230 node1230Labels := by
  calc
    mixedMoment B raw12280 raw12280Labels = mixedMoment B raw12280step0 raw12280step0Labels := by
      have hz : ∀ j, raw12280 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12280step0 = (fun i j => raw12280 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12280step0 raw12280; decide +kernel
      have hl : raw12280step0Labels = raw12280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12280 raw12280Labels permutation265 hz
    mixedMoment B raw12280step0 raw12280step0Labels = mixedMoment B raw12280step1 raw12280step1Labels := by
      have ha : raw12280step1 = (fun i j => raw12280step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12280step1 raw12280step0; decide +kernel
      have hl : raw12280step1Labels = raw12280step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12280step0 raw12280step0Labels permutation36 permutation3
    _ = mixedMoment B node1230 node1230Labels := by rfl

def raw12281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12281Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12281step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw12281step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12281 raw12281Labels = mixedMoment B node2922 node2922Labels := by
  calc
    mixedMoment B raw12281 raw12281Labels = mixedMoment B raw12281step0 raw12281step0Labels := by
      have ha : raw12281step0 = (fun i j => raw12281 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12281step0 raw12281; decide +kernel
      have hl : raw12281step0Labels = raw12281Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12281 raw12281Labels permutation156 permutation3
    _ = mixedMoment B node2922 node2922Labels := by rfl

def raw12282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12282Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12282step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12282step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw12282step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12282 raw12282Labels = mixedMoment B node2876 node2876Labels := by
  calc
    mixedMoment B raw12282 raw12282Labels = mixedMoment B raw12282step0 raw12282step0Labels := by
      have hz : ∀ j, raw12282 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12282step0 = (fun i j => raw12282 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12282step0 raw12282; decide +kernel
      have hl : raw12282step0Labels = raw12282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12282 raw12282Labels permutation265 hz
    mixedMoment B raw12282step0 raw12282step0Labels = mixedMoment B raw12282step1 raw12282step1Labels := by
      have ha : raw12282step1 = (fun i j => raw12282step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12282step1 raw12282step0; decide +kernel
      have hl : raw12282step1Labels = raw12282step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12282step0 raw12282step0Labels permutation36 permutation3
    _ = mixedMoment B node2876 node2876Labels := by rfl

def raw12283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12283Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12283step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw12283step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12283 raw12283Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw12283 raw12283Labels = mixedMoment B raw12283step0 raw12283step0Labels := by
      have hz : ∀ j, raw12283 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12283step0 = (fun i j => raw12283 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12283step0 raw12283; decide +kernel
      have hl : raw12283step0Labels = raw12283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12283 raw12283Labels permutation265 hz
    mixedMoment B raw12283step0 raw12283step0Labels = mixedMoment B raw12283step1 raw12283step1Labels := by
      have ha : raw12283step1 = (fun i j => raw12283step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12283step1 raw12283step0; decide +kernel
      have hl : raw12283step1Labels = raw12283step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12283step0 raw12283step0Labels permutation33 permutation3
    _ = mixedMoment B node3086 node3086Labels := by rfl

def raw12284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![0, 2, -2]]
def raw12284Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![0, 2, -2]]
def raw12284step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12284step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw12284step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12284 raw12284Labels = mixedMoment B node3025 node3025Labels := by
  calc
    mixedMoment B raw12284 raw12284Labels = mixedMoment B raw12284step0 raw12284step0Labels := by
      have hz : ∀ j, raw12284 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12284step0 = (fun i j => raw12284 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12284step0 raw12284; decide +kernel
      have hl : raw12284step0Labels = raw12284Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12284 raw12284Labels permutation265 hz
    mixedMoment B raw12284step0 raw12284step0Labels = mixedMoment B raw12284step1 raw12284step1Labels := by
      have ha : raw12284step1 = (fun i j => raw12284step0 (permutation50 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12284step1 raw12284step0; decide +kernel
      have hl : raw12284step1Labels = raw12284step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12284step0 raw12284step0Labels permutation50 permutation3
    _ = mixedMoment B node3025 node3025Labels := by rfl

def raw12285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12285Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12285step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12285step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12285step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12285 raw12285Labels = mixedMoment B node1241 node1241Labels := by
  calc
    mixedMoment B raw12285 raw12285Labels = mixedMoment B raw12285step0 raw12285step0Labels := by
      have hz : ∀ j, raw12285 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12285step0 = (fun i j => raw12285 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12285step0 raw12285; decide +kernel
      have hl : raw12285step0Labels = raw12285Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12285 raw12285Labels permutation265 hz
    mixedMoment B raw12285step0 raw12285step0Labels = mixedMoment B raw12285step1 raw12285step1Labels := by
      have ha : raw12285step1 = (fun i j => raw12285step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12285step1 raw12285step0; decide +kernel
      have hl : raw12285step1Labels = raw12285step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12285step0 raw12285step0Labels permutation34 permutation3
    _ = mixedMoment B node1241 node1241Labels := by rfl

def raw12286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12286Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12286step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12286 raw12286Labels = mixedMoment B node2928 node2928Labels := by
  calc
    mixedMoment B raw12286 raw12286Labels = mixedMoment B raw12286step0 raw12286step0Labels := by
      have ha : raw12286step0 = (fun i j => raw12286 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12286step0 raw12286; decide +kernel
      have hl : raw12286step0Labels = raw12286Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12286 raw12286Labels permutation154 permutation3
    _ = mixedMoment B node2928 node2928Labels := by rfl

def raw12287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12287Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12287step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12287step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12287 raw12287Labels = mixedMoment B node2885 node2885Labels := by
  calc
    mixedMoment B raw12287 raw12287Labels = mixedMoment B raw12287step0 raw12287step0Labels := by
      have hz : ∀ j, raw12287 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12287step0 = (fun i j => raw12287 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12287step0 raw12287; decide +kernel
      have hl : raw12287step0Labels = raw12287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12287 raw12287Labels permutation265 hz
    mixedMoment B raw12287step0 raw12287step0Labels = mixedMoment B raw12287step1 raw12287step1Labels := by
      have ha : raw12287step1 = (fun i j => raw12287step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12287step1 raw12287step0; decide +kernel
      have hl : raw12287step1Labels = raw12287step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12287step0 raw12287step0Labels permutation34 permutation3
    _ = mixedMoment B node2885 node2885Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
