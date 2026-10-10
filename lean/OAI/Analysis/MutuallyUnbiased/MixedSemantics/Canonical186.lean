import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw23808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw23808Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw23808step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw23808step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23808 raw23808Labels = mixedMoment B node1058 node1058Labels := by
  calc
    mixedMoment B raw23808 raw23808Labels = mixedMoment B raw23808step0 raw23808step0Labels := by
      have hz : ∀ j, raw23808 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23808step0 = (fun i j => raw23808 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23808step0 raw23808; decide +kernel
      have hl : raw23808step0Labels = raw23808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23808 raw23808Labels permutation265 hz
    mixedMoment B raw23808step0 raw23808step0Labels = mixedMoment B raw23808step1 raw23808step1Labels := by
      have ha : raw23808step1 = (fun i j => raw23808step0 (permutation46 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23808step1 raw23808step0; decide +kernel
      have hl : raw23808step1Labels = raw23808step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23808step0 raw23808step0Labels permutation46 permutation2
    _ = mixedMoment B node1058 node1058Labels := by rfl

def raw23809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw23809Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw23809step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23809step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23809 raw23809Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw23809 raw23809Labels = mixedMoment B raw23809step0 raw23809step0Labels := by
      have hz : ∀ j, raw23809 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23809step0 = (fun i j => raw23809 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23809step0 raw23809; decide +kernel
      have hl : raw23809step0Labels = raw23809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23809 raw23809Labels permutation265 hz
    mixedMoment B raw23809step0 raw23809step0Labels = mixedMoment B raw23809step1 raw23809step1Labels := by
      have ha : raw23809step1 = (fun i j => raw23809step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23809step1 raw23809step0; decide +kernel
      have hl : raw23809step1Labels = raw23809step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23809step0 raw23809step0Labels permutation42 permutation2
    _ = mixedMoment B node1079 node1079Labels := by rfl

def raw23810 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![0, 0], ![2, -2], ![0, 0]]
def raw23810Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23810step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![0, 0], ![2, -2]]
def raw23810step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23810step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2]]
def raw23810step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23810step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw23810step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical23810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23810 raw23810Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw23810 raw23810Labels = mixedMoment B raw23810step0 raw23810step0Labels := by
      have hz : ∀ j, raw23810 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw23810step0 = (fun i j => raw23810 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw23810step0 raw23810; decide +kernel
      have hl : raw23810step0Labels = raw23810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23810 raw23810Labels permutation590 hz
    mixedMoment B raw23810step0 raw23810step0Labels = mixedMoment B raw23810step1 raw23810step1Labels := by
      have hz : ∀ j, raw23810step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw23810step1 = (fun i j => raw23810step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw23810step1 raw23810step0; decide +kernel
      have hl : raw23810step1Labels = raw23810step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23810step0 raw23810step0Labels permutation104 hz
    mixedMoment B raw23810step1 raw23810step1Labels = mixedMoment B raw23810step2 raw23810step2Labels := by
      have hz : ∀ j, raw23810step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23810step2 = (fun i j => raw23810step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23810step2 raw23810step1; decide +kernel
      have hl : raw23810step2Labels = raw23810step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23810step1 raw23810step1Labels permutation14 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw23811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw23811Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw23811step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw23811step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23811 raw23811Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw23811 raw23811Labels = mixedMoment B raw23811step0 raw23811step0Labels := by
      have hz : ∀ j, raw23811 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23811step0 = (fun i j => raw23811 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23811step0 raw23811; decide +kernel
      have hl : raw23811step0Labels = raw23811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23811 raw23811Labels permutation265 hz
    mixedMoment B raw23811step0 raw23811step0Labels = mixedMoment B raw23811step1 raw23811step1Labels := by
      have ha : raw23811step1 = (fun i j => raw23811step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23811step1 raw23811step0; decide +kernel
      have hl : raw23811step1Labels = raw23811step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23811step0 raw23811step0Labels permutation34 permutation2
    _ = mixedMoment B node2954 node2954Labels := by rfl

def raw23812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw23812Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23812step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23812 raw23812Labels = mixedMoment B node1335 node1335Labels := by
  calc
    mixedMoment B raw23812 raw23812Labels = mixedMoment B raw23812step0 raw23812step0Labels := by
      have ha : raw23812step0 = (fun i j => raw23812 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23812step0 raw23812; decide +kernel
      have hl : raw23812step0Labels = raw23812Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23812 raw23812Labels permutation188 permutation2
    _ = mixedMoment B node1335 node1335Labels := by rfl

def raw23813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw23813Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw23813step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23813step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw23813step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23813 raw23813Labels = mixedMoment B node1406 node1406Labels := by
  calc
    mixedMoment B raw23813 raw23813Labels = mixedMoment B raw23813step0 raw23813step0Labels := by
      have hz : ∀ j, raw23813 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23813step0 = (fun i j => raw23813 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23813step0 raw23813; decide +kernel
      have hl : raw23813step0Labels = raw23813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23813 raw23813Labels permutation265 hz
    mixedMoment B raw23813step0 raw23813step0Labels = mixedMoment B raw23813step1 raw23813step1Labels := by
      have ha : raw23813step1 = (fun i j => raw23813step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23813step1 raw23813step0; decide +kernel
      have hl : raw23813step1Labels = raw23813step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23813step0 raw23813step0Labels permutation34 permutation2
    _ = mixedMoment B node1406 node1406Labels := by rfl

def raw23814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw23814Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw23814step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23814step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23814step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23814 raw23814Labels = mixedMoment B node1338 node1338Labels := by
  calc
    mixedMoment B raw23814 raw23814Labels = mixedMoment B raw23814step0 raw23814step0Labels := by
      have hz : ∀ j, raw23814 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23814step0 = (fun i j => raw23814 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23814step0 raw23814; decide +kernel
      have hl : raw23814step0Labels = raw23814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23814 raw23814Labels permutation265 hz
    mixedMoment B raw23814step0 raw23814step0Labels = mixedMoment B raw23814step1 raw23814step1Labels := by
      have ha : raw23814step1 = (fun i j => raw23814step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23814step1 raw23814step0; decide +kernel
      have hl : raw23814step1Labels = raw23814step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23814step0 raw23814step0Labels permutation34 permutation2
    _ = mixedMoment B node1338 node1338Labels := by rfl

def raw23815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23815Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23815step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23815 raw23815Labels = mixedMoment B node1347 node1347Labels := by
  calc
    mixedMoment B raw23815 raw23815Labels = mixedMoment B raw23815step0 raw23815step0Labels := by
      have hz : ∀ j, raw23815 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23815step0 = (fun i j => raw23815 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23815step0 raw23815; decide +kernel
      have hl : raw23815step0Labels = raw23815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23815 raw23815Labels permutation265 hz
    _ = mixedMoment B node1347 node1347Labels := by rfl

def raw23816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw23816Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw23816step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw23816step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23816 raw23816Labels = mixedMoment B node1337 node1337Labels := by
  calc
    mixedMoment B raw23816 raw23816Labels = mixedMoment B raw23816step0 raw23816step0Labels := by
      have hz : ∀ j, raw23816 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23816step0 = (fun i j => raw23816 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23816step0 raw23816; decide +kernel
      have hl : raw23816step0Labels = raw23816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23816 raw23816Labels permutation265 hz
    mixedMoment B raw23816step0 raw23816step0Labels = mixedMoment B raw23816step1 raw23816step1Labels := by
      have ha : raw23816step1 = (fun i j => raw23816step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23816step1 raw23816step0; decide +kernel
      have hl : raw23816step1Labels = raw23816step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23816step0 raw23816step0Labels permutation34 permutation2
    _ = mixedMoment B node1337 node1337Labels := by rfl

def raw23817 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]
def raw23817Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23817step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]
def raw23817step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23817step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw23817step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23817step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw23817step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical23817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23817 raw23817Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw23817 raw23817Labels = mixedMoment B raw23817step0 raw23817step0Labels := by
      have hz : ∀ j, raw23817 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23817step0 = (fun i j => raw23817 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23817step0 raw23817; decide +kernel
      have hl : raw23817step0Labels = raw23817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23817 raw23817Labels permutation265 hz
    mixedMoment B raw23817step0 raw23817step0Labels = mixedMoment B raw23817step1 raw23817step1Labels := by
      have ha : raw23817step1 = (fun i j => raw23817step0 (permutation140 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23817step1 raw23817step0; decide +kernel
      have hl : raw23817step1Labels = raw23817step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23817step0 raw23817step0Labels permutation140 permutation0
    mixedMoment B raw23817step1 raw23817step1Labels = mixedMoment B raw23817step2 raw23817step2Labels := by
      have ha : raw23817step2 = -raw23817step1 := by apply Matrix.ext; change ∀ i j, raw23817step2 i j = -(raw23817step1 i j); unfold raw23817step2 raw23817step1; decide +kernel
      have hl : raw23817step2Labels = raw23817step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw23818 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23818Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23818step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw23818step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23818step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23818step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23818 raw23818Labels = mixedMoment B node3285 node3285Labels := by
  calc
    mixedMoment B raw23818 raw23818Labels = mixedMoment B raw23818step0 raw23818step0Labels := by
      have ha : raw23818step0 = (fun i j => raw23818 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23818step0 raw23818; decide +kernel
      have hl : raw23818step0Labels = raw23818Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23818 raw23818Labels permutation188 permutation2
    mixedMoment B raw23818step0 raw23818step0Labels = mixedMoment B raw23818step1 raw23818step1Labels := by
      have ha : raw23818step1 = -raw23818step0 := by apply Matrix.ext; change ∀ i j, raw23818step1 i j = -(raw23818step0 i j); unfold raw23818step1 raw23818step0; decide +kernel
      have hl : raw23818step1Labels = raw23818step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3285 node3285Labels := by rfl

def raw23819 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23819Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23819step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw23819step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23819step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23819step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23819 raw23819Labels = mixedMoment B node3287 node3287Labels := by
  calc
    mixedMoment B raw23819 raw23819Labels = mixedMoment B raw23819step0 raw23819step0Labels := by
      have hz : ∀ j, raw23819 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23819step0 = (fun i j => raw23819 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23819step0 raw23819; decide +kernel
      have hl : raw23819step0Labels = raw23819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23819 raw23819Labels permutation265 hz
    mixedMoment B raw23819step0 raw23819step0Labels = mixedMoment B raw23819step1 raw23819step1Labels := by
      have ha : raw23819step1 = (fun i j => raw23819step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23819step1 raw23819step0; decide +kernel
      have hl : raw23819step1Labels = raw23819step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23819step0 raw23819step0Labels permutation34 permutation2
    mixedMoment B raw23819step1 raw23819step1Labels = mixedMoment B raw23819step2 raw23819step2Labels := by
      have ha : raw23819step2 = -raw23819step1 := by apply Matrix.ext; change ∀ i j, raw23819step2 i j = -(raw23819step1 i j); unfold raw23819step2 raw23819step1; decide +kernel
      have hl : raw23819step2Labels = raw23819step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3287 node3287Labels := by rfl

def raw23820 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23820Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23820step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23820step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23820step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23820step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23820 raw23820Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw23820 raw23820Labels = mixedMoment B raw23820step0 raw23820step0Labels := by
      have hz : ∀ j, raw23820 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23820step0 = (fun i j => raw23820 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23820step0 raw23820; decide +kernel
      have hl : raw23820step0Labels = raw23820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23820 raw23820Labels permutation265 hz
    mixedMoment B raw23820step0 raw23820step0Labels = mixedMoment B raw23820step1 raw23820step1Labels := by
      have ha : raw23820step1 = (fun i j => raw23820step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23820step1 raw23820step0; decide +kernel
      have hl : raw23820step1Labels = raw23820step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23820step0 raw23820step0Labels permutation34 permutation2
    mixedMoment B raw23820step1 raw23820step1Labels = mixedMoment B raw23820step2 raw23820step2Labels := by
      have ha : raw23820step2 = -raw23820step1 := by apply Matrix.ext; change ∀ i j, raw23820step2 i j = -(raw23820step1 i j); unfold raw23820step2 raw23820step1; decide +kernel
      have hl : raw23820step2Labels = raw23820step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3293 node3293Labels := by rfl

def raw23821 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw23821Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw23821step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23821step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw23821step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23821 raw23821Labels = mixedMoment B node2502 node2502Labels := by
  calc
    mixedMoment B raw23821 raw23821Labels = mixedMoment B raw23821step0 raw23821step0Labels := by
      have hz : ∀ j, raw23821 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23821step0 = (fun i j => raw23821 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23821step0 raw23821; decide +kernel
      have hl : raw23821step0Labels = raw23821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23821 raw23821Labels permutation265 hz
    mixedMoment B raw23821step0 raw23821step0Labels = mixedMoment B raw23821step1 raw23821step1Labels := by
      have ha : raw23821step1 = (fun i j => raw23821step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23821step1 raw23821step0; decide +kernel
      have hl : raw23821step1Labels = raw23821step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23821step0 raw23821step0Labels permutation145 permutation2
    _ = mixedMoment B node2502 node2502Labels := by rfl

def raw23822 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23822Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23822step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23822step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw23822step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23822step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23822step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23822 raw23822Labels = mixedMoment B node824 node824Labels := by
  calc
    mixedMoment B raw23822 raw23822Labels = mixedMoment B raw23822step0 raw23822step0Labels := by
      have hz : ∀ j, raw23822 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23822step0 = (fun i j => raw23822 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23822step0 raw23822; decide +kernel
      have hl : raw23822step0Labels = raw23822Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23822 raw23822Labels permutation265 hz
    mixedMoment B raw23822step0 raw23822step0Labels = mixedMoment B raw23822step1 raw23822step1Labels := by
      have ha : raw23822step1 = (fun i j => raw23822step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23822step1 raw23822step0; decide +kernel
      have hl : raw23822step1Labels = raw23822step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23822step0 raw23822step0Labels permutation50 permutation4
    mixedMoment B raw23822step1 raw23822step1Labels = mixedMoment B raw23822step2 raw23822step2Labels := by
      have ha : raw23822step2 = -raw23822step1 := by apply Matrix.ext; change ∀ i j, raw23822step2 i j = -(raw23822step1 i j); unfold raw23822step2 raw23822step1; decide +kernel
      have hl : raw23822step2Labels = raw23822step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node824 node824Labels := by rfl

def raw23823 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23823Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw23823step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23823step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23823step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23823 raw23823Labels = mixedMoment B node1607 node1607Labels := by
  calc
    mixedMoment B raw23823 raw23823Labels = mixedMoment B raw23823step0 raw23823step0Labels := by
      have ha : raw23823step0 = (fun i j => raw23823 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23823step0 raw23823; decide +kernel
      have hl : raw23823step0Labels = raw23823Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23823 raw23823Labels permutation170 permutation4
    mixedMoment B raw23823step0 raw23823step0Labels = mixedMoment B raw23823step1 raw23823step1Labels := by
      have ha : raw23823step1 = -raw23823step0 := by apply Matrix.ext; change ∀ i j, raw23823step1 i j = -(raw23823step0 i j); unfold raw23823step1 raw23823step0; decide +kernel
      have hl : raw23823step1Labels = raw23823step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1607 node1607Labels := by rfl

def raw23824 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23824Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23824step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw23824step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23824step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw23824step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23824 raw23824Labels = mixedMoment B node1737 node1737Labels := by
  calc
    mixedMoment B raw23824 raw23824Labels = mixedMoment B raw23824step0 raw23824step0Labels := by
      have hz : ∀ j, raw23824 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23824step0 = (fun i j => raw23824 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23824step0 raw23824; decide +kernel
      have hl : raw23824step0Labels = raw23824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23824 raw23824Labels permutation265 hz
    mixedMoment B raw23824step0 raw23824step0Labels = mixedMoment B raw23824step1 raw23824step1Labels := by
      have ha : raw23824step1 = (fun i j => raw23824step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23824step1 raw23824step0; decide +kernel
      have hl : raw23824step1Labels = raw23824step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23824step0 raw23824step0Labels permutation50 permutation4
    mixedMoment B raw23824step1 raw23824step1Labels = mixedMoment B raw23824step2 raw23824step2Labels := by
      have ha : raw23824step2 = -raw23824step1 := by apply Matrix.ext; change ∀ i j, raw23824step2 i j = -(raw23824step1 i j); unfold raw23824step2 raw23824step1; decide +kernel
      have hl : raw23824step2Labels = raw23824step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1737 node1737Labels := by rfl

def raw23825 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw23825Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw23825step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw23825step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23825step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23825step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23825 raw23825Labels = mixedMoment B node1656 node1656Labels := by
  calc
    mixedMoment B raw23825 raw23825Labels = mixedMoment B raw23825step0 raw23825step0Labels := by
      have hz : ∀ j, raw23825 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23825step0 = (fun i j => raw23825 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23825step0 raw23825; decide +kernel
      have hl : raw23825step0Labels = raw23825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23825 raw23825Labels permutation265 hz
    mixedMoment B raw23825step0 raw23825step0Labels = mixedMoment B raw23825step1 raw23825step1Labels := by
      have ha : raw23825step1 = (fun i j => raw23825step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23825step1 raw23825step0; decide +kernel
      have hl : raw23825step1Labels = raw23825step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23825step0 raw23825step0Labels permutation50 permutation4
    mixedMoment B raw23825step1 raw23825step1Labels = mixedMoment B raw23825step2 raw23825step2Labels := by
      have ha : raw23825step2 = -raw23825step1 := by apply Matrix.ext; change ∀ i j, raw23825step2 i j = -(raw23825step1 i j); unfold raw23825step2 raw23825step1; decide +kernel
      have hl : raw23825step2Labels = raw23825step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1656 node1656Labels := by rfl

def raw23826 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23826Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw23826step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23826step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw23826step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23826 raw23826Labels = mixedMoment B node1713 node1713Labels := by
  calc
    mixedMoment B raw23826 raw23826Labels = mixedMoment B raw23826step0 raw23826step0Labels := by
      have ha : raw23826step0 = (fun i j => raw23826 (permutation218 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23826step0 raw23826; decide +kernel
      have hl : raw23826step0Labels = raw23826Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23826 raw23826Labels permutation218 permutation4
    mixedMoment B raw23826step0 raw23826step0Labels = mixedMoment B raw23826step1 raw23826step1Labels := by
      have ha : raw23826step1 = -raw23826step0 := by apply Matrix.ext; change ∀ i j, raw23826step1 i j = -(raw23826step0 i j); unfold raw23826step1 raw23826step0; decide +kernel
      have hl : raw23826step1Labels = raw23826step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1713 node1713Labels := by rfl

def raw23827 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23827Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23827step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23827step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw23827step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23827step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw23827step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23827 raw23827Labels = mixedMoment B node1715 node1715Labels := by
  calc
    mixedMoment B raw23827 raw23827Labels = mixedMoment B raw23827step0 raw23827step0Labels := by
      have hz : ∀ j, raw23827 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23827step0 = (fun i j => raw23827 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23827step0 raw23827; decide +kernel
      have hl : raw23827step0Labels = raw23827Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23827 raw23827Labels permutation265 hz
    mixedMoment B raw23827step0 raw23827step0Labels = mixedMoment B raw23827step1 raw23827step1Labels := by
      have ha : raw23827step1 = (fun i j => raw23827step0 (permutation43 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23827step1 raw23827step0; decide +kernel
      have hl : raw23827step1Labels = raw23827step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23827step0 raw23827step0Labels permutation43 permutation4
    mixedMoment B raw23827step1 raw23827step1Labels = mixedMoment B raw23827step2 raw23827step2Labels := by
      have ha : raw23827step2 = -raw23827step1 := by apply Matrix.ext; change ∀ i j, raw23827step2 i j = -(raw23827step1 i j); unfold raw23827step2 raw23827step1; decide +kernel
      have hl : raw23827step2Labels = raw23827step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1715 node1715Labels := by rfl

def raw23828 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw23828Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw23828step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw23828step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23828step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23828step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23828 raw23828Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw23828 raw23828Labels = mixedMoment B raw23828step0 raw23828step0Labels := by
      have hz : ∀ j, raw23828 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23828step0 = (fun i j => raw23828 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23828step0 raw23828; decide +kernel
      have hl : raw23828step0Labels = raw23828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23828 raw23828Labels permutation265 hz
    mixedMoment B raw23828step0 raw23828step0Labels = mixedMoment B raw23828step1 raw23828step1Labels := by
      have ha : raw23828step1 = (fun i j => raw23828step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23828step1 raw23828step0; decide +kernel
      have hl : raw23828step1Labels = raw23828step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23828step0 raw23828step0Labels permutation38 permutation4
    mixedMoment B raw23828step1 raw23828step1Labels = mixedMoment B raw23828step2 raw23828step2Labels := by
      have ha : raw23828step2 = -raw23828step1 := by apply Matrix.ext; change ∀ i j, raw23828step2 i j = -(raw23828step1 i j); unfold raw23828step2 raw23828step1; decide +kernel
      have hl : raw23828step2Labels = raw23828step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1724 node1724Labels := by rfl

def raw23829 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23829Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23829step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23829step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw23829step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23829step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23829step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23829 raw23829Labels = mixedMoment B node807 node807Labels := by
  calc
    mixedMoment B raw23829 raw23829Labels = mixedMoment B raw23829step0 raw23829step0Labels := by
      have hz : ∀ j, raw23829 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23829step0 = (fun i j => raw23829 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23829step0 raw23829; decide +kernel
      have hl : raw23829step0Labels = raw23829Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23829 raw23829Labels permutation265 hz
    mixedMoment B raw23829step0 raw23829step0Labels = mixedMoment B raw23829step1 raw23829step1Labels := by
      have ha : raw23829step1 = (fun i j => raw23829step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23829step1 raw23829step0; decide +kernel
      have hl : raw23829step1Labels = raw23829step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23829step0 raw23829step0Labels permutation39 permutation4
    mixedMoment B raw23829step1 raw23829step1Labels = mixedMoment B raw23829step2 raw23829step2Labels := by
      have ha : raw23829step2 = -raw23829step1 := by apply Matrix.ext; change ∀ i j, raw23829step2 i j = -(raw23829step1 i j); unfold raw23829step2 raw23829step1; decide +kernel
      have hl : raw23829step2Labels = raw23829step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node807 node807Labels := by rfl

def raw23830 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23830Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23830step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw23830step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23830step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23830step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23830 raw23830Labels = mixedMoment B node1598 node1598Labels := by
  calc
    mixedMoment B raw23830 raw23830Labels = mixedMoment B raw23830step0 raw23830step0Labels := by
      have ha : raw23830step0 = (fun i j => raw23830 (permutation159 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23830step0 raw23830; decide +kernel
      have hl : raw23830step0Labels = raw23830Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23830 raw23830Labels permutation159 permutation4
    mixedMoment B raw23830step0 raw23830step0Labels = mixedMoment B raw23830step1 raw23830step1Labels := by
      have ha : raw23830step1 = -raw23830step0 := by apply Matrix.ext; change ∀ i j, raw23830step1 i j = -(raw23830step0 i j); unfold raw23830step1 raw23830step0; decide +kernel
      have hl : raw23830step1Labels = raw23830step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1598 node1598Labels := by rfl

def raw23831 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23831Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw23831step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw23831step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23831step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23831step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23831 raw23831Labels = mixedMoment B node1646 node1646Labels := by
  calc
    mixedMoment B raw23831 raw23831Labels = mixedMoment B raw23831step0 raw23831step0Labels := by
      have hz : ∀ j, raw23831 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23831step0 = (fun i j => raw23831 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23831step0 raw23831; decide +kernel
      have hl : raw23831step0Labels = raw23831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23831 raw23831Labels permutation265 hz
    mixedMoment B raw23831step0 raw23831step0Labels = mixedMoment B raw23831step1 raw23831step1Labels := by
      have ha : raw23831step1 = (fun i j => raw23831step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23831step1 raw23831step0; decide +kernel
      have hl : raw23831step1Labels = raw23831step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23831step0 raw23831step0Labels permutation39 permutation4
    mixedMoment B raw23831step1 raw23831step1Labels = mixedMoment B raw23831step2 raw23831step2Labels := by
      have ha : raw23831step2 = -raw23831step1 := by apply Matrix.ext; change ∀ i j, raw23831step2 i j = -(raw23831step1 i j); unfold raw23831step2 raw23831step1; decide +kernel
      have hl : raw23831step2Labels = raw23831step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1646 node1646Labels := by rfl

def raw23832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw23832Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw23832step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23832step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23832step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23832 raw23832Labels = mixedMoment B node601 node601Labels := by
  calc
    mixedMoment B raw23832 raw23832Labels = mixedMoment B raw23832step0 raw23832step0Labels := by
      have hz : ∀ j, raw23832 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23832step0 = (fun i j => raw23832 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23832step0 raw23832; decide +kernel
      have hl : raw23832step0Labels = raw23832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23832 raw23832Labels permutation265 hz
    mixedMoment B raw23832step0 raw23832step0Labels = mixedMoment B raw23832step1 raw23832step1Labels := by
      have ha : raw23832step1 = (fun i j => raw23832step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23832step1 raw23832step0; decide +kernel
      have hl : raw23832step1Labels = raw23832step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23832step0 raw23832step0Labels permutation40 permutation2
    _ = mixedMoment B node601 node601Labels := by rfl

def raw23833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw23833Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23833step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23833 raw23833Labels = mixedMoment B node920 node920Labels := by
  calc
    mixedMoment B raw23833 raw23833Labels = mixedMoment B raw23833step0 raw23833step0Labels := by
      have ha : raw23833step0 = (fun i j => raw23833 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23833step0 raw23833; decide +kernel
      have hl : raw23833step0Labels = raw23833Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23833 raw23833Labels permutation160 permutation2
    _ = mixedMoment B node920 node920Labels := by rfl

def raw23834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw23834Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw23834step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23834 raw23834Labels = mixedMoment B node1057 node1057Labels := by
  calc
    mixedMoment B raw23834 raw23834Labels = mixedMoment B raw23834step0 raw23834step0Labels := by
      have hz : ∀ j, raw23834 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23834step0 = (fun i j => raw23834 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23834step0 raw23834; decide +kernel
      have hl : raw23834step0Labels = raw23834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23834 raw23834Labels permutation265 hz
    _ = mixedMoment B node1057 node1057Labels := by rfl

def raw23835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw23835Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw23835step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23835step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw23835step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23835step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23835step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23835 raw23835Labels = mixedMoment B node1083 node1083Labels := by
  calc
    mixedMoment B raw23835 raw23835Labels = mixedMoment B raw23835step0 raw23835step0Labels := by
      have hz : ∀ j, raw23835 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23835step0 = (fun i j => raw23835 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23835step0 raw23835; decide +kernel
      have hl : raw23835step0Labels = raw23835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23835 raw23835Labels permutation434 hz
    mixedMoment B raw23835step0 raw23835step0Labels = mixedMoment B raw23835step1 raw23835step1Labels := by
      have hz : ∀ j, raw23835step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23835step1 = (fun i j => raw23835step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23835step1 raw23835step0; decide +kernel
      have hl : raw23835step1Labels = raw23835step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23835step0 raw23835step0Labels permutation56 hz
    mixedMoment B raw23835step1 raw23835step1Labels = mixedMoment B raw23835step2 raw23835step2Labels := by
      have ha : raw23835step2 = (fun i j => raw23835step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23835step2 raw23835step1; decide +kernel
      have hl : raw23835step2Labels = raw23835step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23835step1 raw23835step1Labels permutation10 permutation2
    _ = mixedMoment B node1083 node1083Labels := by rfl

def raw23836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw23836Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw23836step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23836step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw23836step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23836step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw23836step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23836 raw23836Labels = mixedMoment B node1083 node1083Labels := by
  calc
    mixedMoment B raw23836 raw23836Labels = mixedMoment B raw23836step0 raw23836step0Labels := by
      have hz : ∀ j, raw23836 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw23836step0 = (fun i j => raw23836 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw23836step0 raw23836; decide +kernel
      have hl : raw23836step0Labels = raw23836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23836 raw23836Labels permutation520 hz
    mixedMoment B raw23836step0 raw23836step0Labels = mixedMoment B raw23836step1 raw23836step1Labels := by
      have hz : ∀ j, raw23836step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23836step1 = (fun i j => raw23836step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23836step1 raw23836step0; decide +kernel
      have hl : raw23836step1Labels = raw23836step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23836step0 raw23836step0Labels permutation56 hz
    mixedMoment B raw23836step1 raw23836step1Labels = mixedMoment B raw23836step2 raw23836step2Labels := by
      have ha : raw23836step2 = (fun i j => raw23836step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23836step2 raw23836step1; decide +kernel
      have hl : raw23836step2Labels = raw23836step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23836step1 raw23836step1Labels permutation10 permutation2
    _ = mixedMoment B node1083 node1083Labels := by rfl

def raw23837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw23837Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw23837step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23837step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23837 raw23837Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw23837 raw23837Labels = mixedMoment B raw23837step0 raw23837step0Labels := by
      have hz : ∀ j, raw23837 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23837step0 = (fun i j => raw23837 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23837step0 raw23837; decide +kernel
      have hl : raw23837step0Labels = raw23837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23837 raw23837Labels permutation265 hz
    mixedMoment B raw23837step0 raw23837step0Labels = mixedMoment B raw23837step1 raw23837step1Labels := by
      have ha : raw23837step1 = (fun i j => raw23837step0 (permutation41 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23837step1 raw23837step0; decide +kernel
      have hl : raw23837step1Labels = raw23837step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23837step0 raw23837step0Labels permutation41 permutation2
    _ = mixedMoment B node1079 node1079Labels := by rfl

def raw23838 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![0, 0], ![0, 0], ![1, -1]]
def raw23838Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23838step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![0, 0], ![1, -1]]
def raw23838step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23838step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![1, -1]]
def raw23838step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23838step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]
def raw23838step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23838step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw23838step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical23838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23838 raw23838Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw23838 raw23838Labels = mixedMoment B raw23838step0 raw23838step0Labels := by
      have hz : ∀ j, raw23838 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw23838step0 = (fun i j => raw23838 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw23838step0 raw23838; decide +kernel
      have hl : raw23838step0Labels = raw23838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23838 raw23838Labels permutation520 hz
    mixedMoment B raw23838step0 raw23838step0Labels = mixedMoment B raw23838step1 raw23838step1Labels := by
      have hz : ∀ j, raw23838step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw23838step1 = (fun i j => raw23838step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw23838step1 raw23838step0; decide +kernel
      have hl : raw23838step1Labels = raw23838step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23838step0 raw23838step0Labels permutation104 hz
    mixedMoment B raw23838step1 raw23838step1Labels = mixedMoment B raw23838step2 raw23838step2Labels := by
      have hz : ∀ j, raw23838step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23838step2 = (fun i j => raw23838step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23838step2 raw23838step1; decide +kernel
      have hl : raw23838step2Labels = raw23838step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23838step1 raw23838step1Labels permutation14 hz
    mixedMoment B raw23838step2 raw23838step2Labels = mixedMoment B raw23838step3 raw23838step3Labels := by
      have ha : raw23838step3 = (fun i j => raw23838step2 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23838step3 raw23838step2; decide +kernel
      have hl : raw23838step3Labels = raw23838step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23838step2 raw23838step2Labels permutation3 permutation0
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw23839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23839Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23839step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23839 raw23839Labels = mixedMoment B node2884 node2884Labels := by
  calc
    mixedMoment B raw23839 raw23839Labels = mixedMoment B raw23839step0 raw23839step0Labels := by
      have hz : ∀ j, raw23839 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23839step0 = (fun i j => raw23839 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23839step0 raw23839; decide +kernel
      have hl : raw23839step0Labels = raw23839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23839 raw23839Labels permutation265 hz
    _ = mixedMoment B node2884 node2884Labels := by rfl

def raw23840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23840Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23840step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23840step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23840 raw23840Labels = mixedMoment B node1316 node1316Labels := by
  calc
    mixedMoment B raw23840 raw23840Labels = mixedMoment B raw23840step0 raw23840step0Labels := by
      have ha : raw23840step0 = (fun i j => raw23840 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23840step0 raw23840; decide +kernel
      have hl : raw23840step0Labels = raw23840Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23840 raw23840Labels permutation176 permutation2
    _ = mixedMoment B node1316 node1316Labels := by rfl

def raw23841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23841Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23841step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23841 raw23841Labels = mixedMoment B node1370 node1370Labels := by
  calc
    mixedMoment B raw23841 raw23841Labels = mixedMoment B raw23841step0 raw23841step0Labels := by
      have hz : ∀ j, raw23841 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23841step0 = (fun i j => raw23841 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23841step0 raw23841; decide +kernel
      have hl : raw23841step0Labels = raw23841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23841 raw23841Labels permutation265 hz
    _ = mixedMoment B node1370 node1370Labels := by rfl

def raw23842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23842Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23842step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23842step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23842step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23842 raw23842Labels = mixedMoment B node1322 node1322Labels := by
  calc
    mixedMoment B raw23842 raw23842Labels = mixedMoment B raw23842step0 raw23842step0Labels := by
      have hz : ∀ j, raw23842 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23842step0 = (fun i j => raw23842 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23842step0 raw23842; decide +kernel
      have hl : raw23842step0Labels = raw23842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23842 raw23842Labels permutation265 hz
    mixedMoment B raw23842step0 raw23842step0Labels = mixedMoment B raw23842step1 raw23842step1Labels := by
      have ha : raw23842step1 = (fun i j => raw23842step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23842step1 raw23842step0; decide +kernel
      have hl : raw23842step1Labels = raw23842step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23842step0 raw23842step0Labels permutation34 permutation2
    _ = mixedMoment B node1322 node1322Labels := by rfl

def raw23843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23843Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23843 raw23843Labels = mixedMoment B node1322 node1322Labels := by
  calc
    mixedMoment B raw23843 raw23843Labels = mixedMoment B raw23843step0 raw23843step0Labels := by
      have hz : ∀ j, raw23843 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23843step0 = (fun i j => raw23843 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23843step0 raw23843; decide +kernel
      have hl : raw23843step0Labels = raw23843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23843 raw23843Labels permutation265 hz
    _ = mixedMoment B node1322 node1322Labels := by rfl

def raw23844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw23844Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw23844step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23844 raw23844Labels = mixedMoment B node1320 node1320Labels := by
  calc
    mixedMoment B raw23844 raw23844Labels = mixedMoment B raw23844step0 raw23844step0Labels := by
      have hz : ∀ j, raw23844 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23844step0 = (fun i j => raw23844 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23844step0 raw23844; decide +kernel
      have hl : raw23844step0Labels = raw23844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23844 raw23844Labels permutation265 hz
    _ = mixedMoment B node1320 node1320Labels := by rfl

def raw23845 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23845Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23845step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw23845step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23845step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23845step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23845 raw23845Labels = mixedMoment B node1709 node1709Labels := by
  calc
    mixedMoment B raw23845 raw23845Labels = mixedMoment B raw23845step0 raw23845step0Labels := by
      have hz : ∀ j, raw23845 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23845step0 = (fun i j => raw23845 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23845step0 raw23845; decide +kernel
      have hl : raw23845step0Labels = raw23845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23845 raw23845Labels permutation265 hz
    mixedMoment B raw23845step0 raw23845step0Labels = mixedMoment B raw23845step1 raw23845step1Labels := by
      have ha : raw23845step1 = (fun i j => raw23845step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23845step1 raw23845step0; decide +kernel
      have hl : raw23845step1Labels = raw23845step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23845step0 raw23845step0Labels permutation41 permutation4
    mixedMoment B raw23845step1 raw23845step1Labels = mixedMoment B raw23845step2 raw23845step2Labels := by
      have ha : raw23845step2 = -raw23845step1 := by apply Matrix.ext; change ∀ i j, raw23845step2 i j = -(raw23845step1 i j); unfold raw23845step2 raw23845step1; decide +kernel
      have hl : raw23845step2Labels = raw23845step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1709 node1709Labels := by rfl

def raw23846 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23846Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23846step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23846step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw23846step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23846 raw23846Labels = mixedMoment B node3241 node3241Labels := by
  calc
    mixedMoment B raw23846 raw23846Labels = mixedMoment B raw23846step0 raw23846step0Labels := by
      have ha : raw23846step0 = (fun i j => raw23846 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23846step0 raw23846; decide +kernel
      have hl : raw23846step0Labels = raw23846Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23846 raw23846Labels permutation176 permutation2
    mixedMoment B raw23846step0 raw23846step0Labels = mixedMoment B raw23846step1 raw23846step1Labels := by
      have ha : raw23846step1 = -raw23846step0 := by apply Matrix.ext; change ∀ i j, raw23846step1 i j = -(raw23846step0 i j); unfold raw23846step1 raw23846step0; decide +kernel
      have hl : raw23846step1Labels = raw23846step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3241 node3241Labels := by rfl

def raw23847 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23847Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23847step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23847step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw23847step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23847 raw23847Labels = mixedMoment B node3299 node3299Labels := by
  calc
    mixedMoment B raw23847 raw23847Labels = mixedMoment B raw23847step0 raw23847step0Labels := by
      have hz : ∀ j, raw23847 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23847step0 = (fun i j => raw23847 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23847step0 raw23847; decide +kernel
      have hl : raw23847step0Labels = raw23847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23847 raw23847Labels permutation265 hz
    mixedMoment B raw23847step0 raw23847step0Labels = mixedMoment B raw23847step1 raw23847step1Labels := by
      have ha : raw23847step1 = -raw23847step0 := by apply Matrix.ext; change ∀ i j, raw23847step1 i j = -(raw23847step0 i j); unfold raw23847step1 raw23847step0; decide +kernel
      have hl : raw23847step1Labels = raw23847step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3299 node3299Labels := by rfl

def raw23848 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23848Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23848step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23848step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23848step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23848 raw23848Labels = mixedMoment B node3246 node3246Labels := by
  calc
    mixedMoment B raw23848 raw23848Labels = mixedMoment B raw23848step0 raw23848step0Labels := by
      have hz : ∀ j, raw23848 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23848step0 = (fun i j => raw23848 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23848step0 raw23848; decide +kernel
      have hl : raw23848step0Labels = raw23848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23848 raw23848Labels permutation265 hz
    mixedMoment B raw23848step0 raw23848step0Labels = mixedMoment B raw23848step1 raw23848step1Labels := by
      have ha : raw23848step1 = (fun i j => raw23848step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23848step1 raw23848step0; decide +kernel
      have hl : raw23848step1Labels = raw23848step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23848step0 raw23848step0Labels permutation35 permutation2
    mixedMoment B raw23848step1 raw23848step1Labels = mixedMoment B raw23848step2 raw23848step2Labels := by
      have ha : raw23848step2 = -raw23848step1 := by apply Matrix.ext; change ∀ i j, raw23848step2 i j = -(raw23848step1 i j); unfold raw23848step2 raw23848step1; decide +kernel
      have hl : raw23848step2Labels = raw23848step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3246 node3246Labels := by rfl

def raw23849 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw23849Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw23849step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23849step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23849step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23849step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23849step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23849 raw23849Labels = mixedMoment B node3246 node3246Labels := by
  calc
    mixedMoment B raw23849 raw23849Labels = mixedMoment B raw23849step0 raw23849step0Labels := by
      have hz : ∀ j, raw23849 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23849step0 = (fun i j => raw23849 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23849step0 raw23849; decide +kernel
      have hl : raw23849step0Labels = raw23849Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23849 raw23849Labels permutation265 hz
    mixedMoment B raw23849step0 raw23849step0Labels = mixedMoment B raw23849step1 raw23849step1Labels := by
      have ha : raw23849step1 = (fun i j => raw23849step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23849step1 raw23849step0; decide +kernel
      have hl : raw23849step1Labels = raw23849step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23849step0 raw23849step0Labels permutation33 permutation2
    mixedMoment B raw23849step1 raw23849step1Labels = mixedMoment B raw23849step2 raw23849step2Labels := by
      have ha : raw23849step2 = -raw23849step1 := by apply Matrix.ext; change ∀ i j, raw23849step2 i j = -(raw23849step1 i j); unfold raw23849step2 raw23849step1; decide +kernel
      have hl : raw23849step2Labels = raw23849step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3246 node3246Labels := by rfl

def raw23850 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23850Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23850step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23850step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23850 raw23850Labels = mixedMoment B node3245 node3245Labels := by
  calc
    mixedMoment B raw23850 raw23850Labels = mixedMoment B raw23850step0 raw23850step0Labels := by
      have hz : ∀ j, raw23850 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23850step0 = (fun i j => raw23850 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23850step0 raw23850; decide +kernel
      have hl : raw23850step0Labels = raw23850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23850 raw23850Labels permutation265 hz
    mixedMoment B raw23850step0 raw23850step0Labels = mixedMoment B raw23850step1 raw23850step1Labels := by
      have ha : raw23850step1 = -raw23850step0 := by apply Matrix.ext; change ∀ i j, raw23850step1 i j = -(raw23850step0 i j); unfold raw23850step1 raw23850step0; decide +kernel
      have hl : raw23850step1Labels = raw23850step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3245 node3245Labels := by rfl

def raw23851 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23851Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23851step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw23851step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23851step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw23851step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23851 raw23851Labels = mixedMoment B node1705 node1705Labels := by
  calc
    mixedMoment B raw23851 raw23851Labels = mixedMoment B raw23851step0 raw23851step0Labels := by
      have ha : raw23851step0 = (fun i j => raw23851 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23851step0 raw23851; decide +kernel
      have hl : raw23851step0Labels = raw23851Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23851 raw23851Labels permutation212 permutation4
    mixedMoment B raw23851step0 raw23851step0Labels = mixedMoment B raw23851step1 raw23851step1Labels := by
      have ha : raw23851step1 = -raw23851step0 := by apply Matrix.ext; change ∀ i j, raw23851step1 i j = -(raw23851step0 i j); unfold raw23851step1 raw23851step0; decide +kernel
      have hl : raw23851step1Labels = raw23851step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1705 node1705Labels := by rfl

def raw23852 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23852Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23852step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw23852step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23852step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23852step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23852 raw23852Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw23852 raw23852Labels = mixedMoment B raw23852step0 raw23852step0Labels := by
      have hz : ∀ j, raw23852 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23852step0 = (fun i j => raw23852 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23852step0 raw23852; decide +kernel
      have hl : raw23852step0Labels = raw23852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23852 raw23852Labels permutation265 hz
    mixedMoment B raw23852step0 raw23852step0Labels = mixedMoment B raw23852step1 raw23852step1Labels := by
      have ha : raw23852step1 = (fun i j => raw23852step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23852step1 raw23852step0; decide +kernel
      have hl : raw23852step1Labels = raw23852step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23852step0 raw23852step0Labels permutation44 permutation4
    mixedMoment B raw23852step1 raw23852step1Labels = mixedMoment B raw23852step2 raw23852step2Labels := by
      have ha : raw23852step2 = -raw23852step1 := by apply Matrix.ext; change ∀ i j, raw23852step2 i j = -(raw23852step1 i j); unfold raw23852step2 raw23852step1; decide +kernel
      have hl : raw23852step2Labels = raw23852step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1724 node1724Labels := by rfl

def raw23853 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23853Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23853step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23853step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw23853step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23853step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23853step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23853 raw23853Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw23853 raw23853Labels = mixedMoment B raw23853step0 raw23853step0Labels := by
      have hz : ∀ j, raw23853 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23853step0 = (fun i j => raw23853 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23853step0 raw23853; decide +kernel
      have hl : raw23853step0Labels = raw23853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23853 raw23853Labels permutation265 hz
    mixedMoment B raw23853step0 raw23853step0Labels = mixedMoment B raw23853step1 raw23853step1Labels := by
      have ha : raw23853step1 = (fun i j => raw23853step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23853step1 raw23853step0; decide +kernel
      have hl : raw23853step1Labels = raw23853step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23853step0 raw23853step0Labels permutation40 permutation4
    mixedMoment B raw23853step1 raw23853step1Labels = mixedMoment B raw23853step2 raw23853step2Labels := by
      have ha : raw23853step2 = -raw23853step1 := by apply Matrix.ext; change ∀ i j, raw23853step2 i j = -(raw23853step1 i j); unfold raw23853step2 raw23853step1; decide +kernel
      have hl : raw23853step2Labels = raw23853step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1707 node1707Labels := by rfl

def raw23854 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23854Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23854step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23854step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw23854step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23854step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23854step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23854 raw23854Labels = mixedMoment B node811 node811Labels := by
  calc
    mixedMoment B raw23854 raw23854Labels = mixedMoment B raw23854step0 raw23854step0Labels := by
      have hz : ∀ j, raw23854 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23854step0 = (fun i j => raw23854 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23854step0 raw23854; decide +kernel
      have hl : raw23854step0Labels = raw23854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23854 raw23854Labels permutation265 hz
    mixedMoment B raw23854step0 raw23854step0Labels = mixedMoment B raw23854step1 raw23854step1Labels := by
      have ha : raw23854step1 = (fun i j => raw23854step0 (permutation47 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23854step1 raw23854step0; decide +kernel
      have hl : raw23854step1Labels = raw23854step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23854step0 raw23854step0Labels permutation47 permutation4
    mixedMoment B raw23854step1 raw23854step1Labels = mixedMoment B raw23854step2 raw23854step2Labels := by
      have ha : raw23854step2 = -raw23854step1 := by apply Matrix.ext; change ∀ i j, raw23854step2 i j = -(raw23854step1 i j); unfold raw23854step2 raw23854step1; decide +kernel
      have hl : raw23854step2Labels = raw23854step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node811 node811Labels := by rfl

def raw23855 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23855Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw23855step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23855step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23855step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23855 raw23855Labels = mixedMoment B node1601 node1601Labels := by
  calc
    mixedMoment B raw23855 raw23855Labels = mixedMoment B raw23855step0 raw23855step0Labels := by
      have ha : raw23855step0 = (fun i j => raw23855 (permutation167 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23855step0 raw23855; decide +kernel
      have hl : raw23855step0Labels = raw23855Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23855 raw23855Labels permutation167 permutation4
    mixedMoment B raw23855step0 raw23855step0Labels = mixedMoment B raw23855step1 raw23855step1Labels := by
      have ha : raw23855step1 = -raw23855step0 := by apply Matrix.ext; change ∀ i j, raw23855step1 i j = -(raw23855step0 i j); unfold raw23855step1 raw23855step0; decide +kernel
      have hl : raw23855step1Labels = raw23855step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1601 node1601Labels := by rfl

def raw23856 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw23856Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw23856step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23856step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw23856step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23856step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw23856step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23856 raw23856Labels = mixedMoment B node1649 node1649Labels := by
  calc
    mixedMoment B raw23856 raw23856Labels = mixedMoment B raw23856step0 raw23856step0Labels := by
      have hz : ∀ j, raw23856 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23856step0 = (fun i j => raw23856 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23856step0 raw23856; decide +kernel
      have hl : raw23856step0Labels = raw23856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23856 raw23856Labels permutation265 hz
    mixedMoment B raw23856step0 raw23856step0Labels = mixedMoment B raw23856step1 raw23856step1Labels := by
      have ha : raw23856step1 = (fun i j => raw23856step0 (permutation47 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23856step1 raw23856step0; decide +kernel
      have hl : raw23856step1Labels = raw23856step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23856step0 raw23856step0Labels permutation47 permutation4
    mixedMoment B raw23856step1 raw23856step1Labels = mixedMoment B raw23856step2 raw23856step2Labels := by
      have ha : raw23856step2 = -raw23856step1 := by apply Matrix.ext; change ∀ i j, raw23856step2 i j = -(raw23856step1 i j); unfold raw23856step2 raw23856step1; decide +kernel
      have hl : raw23856step2Labels = raw23856step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1649 node1649Labels := by rfl

def raw23857 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23857Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23857step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw23857step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23857step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw23857step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23857 raw23857Labels = mixedMoment B node1715 node1715Labels := by
  calc
    mixedMoment B raw23857 raw23857Labels = mixedMoment B raw23857step0 raw23857step0Labels := by
      have hz : ∀ j, raw23857 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23857step0 = (fun i j => raw23857 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23857step0 raw23857; decide +kernel
      have hl : raw23857step0Labels = raw23857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23857 raw23857Labels permutation265 hz
    mixedMoment B raw23857step0 raw23857step0Labels = mixedMoment B raw23857step1 raw23857step1Labels := by
      have ha : raw23857step1 = (fun i j => raw23857step0 (permutation49 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23857step1 raw23857step0; decide +kernel
      have hl : raw23857step1Labels = raw23857step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23857step0 raw23857step0Labels permutation49 permutation4
    mixedMoment B raw23857step1 raw23857step1Labels = mixedMoment B raw23857step2 raw23857step2Labels := by
      have ha : raw23857step2 = -raw23857step1 := by apply Matrix.ext; change ∀ i j, raw23857step2 i j = -(raw23857step1 i j); unfold raw23857step2 raw23857step1; decide +kernel
      have hl : raw23857step2Labels = raw23857step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1715 node1715Labels := by rfl

def raw23858 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23858Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw23858step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23858step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw23858step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23858 raw23858Labels = mixedMoment B node1701 node1701Labels := by
  calc
    mixedMoment B raw23858 raw23858Labels = mixedMoment B raw23858step0 raw23858step0Labels := by
      have ha : raw23858step0 = (fun i j => raw23858 (permutation216 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23858step0 raw23858; decide +kernel
      have hl : raw23858step0Labels = raw23858Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23858 raw23858Labels permutation216 permutation4
    mixedMoment B raw23858step0 raw23858step0Labels = mixedMoment B raw23858step1 raw23858step1Labels := by
      have ha : raw23858step1 = -raw23858step0 := by apply Matrix.ext; change ∀ i j, raw23858step1 i j = -(raw23858step0 i j); unfold raw23858step1 raw23858step0; decide +kernel
      have hl : raw23858step1Labels = raw23858step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1701 node1701Labels := by rfl

def raw23859 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23859Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23859step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23859step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw23859step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23859step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw23859step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23859 raw23859Labels = mixedMoment B node1702 node1702Labels := by
  calc
    mixedMoment B raw23859 raw23859Labels = mixedMoment B raw23859step0 raw23859step0Labels := by
      have hz : ∀ j, raw23859 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23859step0 = (fun i j => raw23859 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23859step0 raw23859; decide +kernel
      have hl : raw23859step0Labels = raw23859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23859 raw23859Labels permutation265 hz
    mixedMoment B raw23859step0 raw23859step0Labels = mixedMoment B raw23859step1 raw23859step1Labels := by
      have ha : raw23859step1 = (fun i j => raw23859step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23859step1 raw23859step0; decide +kernel
      have hl : raw23859step1Labels = raw23859step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23859step0 raw23859step0Labels permutation41 permutation4
    mixedMoment B raw23859step1 raw23859step1Labels = mixedMoment B raw23859step2 raw23859step2Labels := by
      have ha : raw23859step2 = -raw23859step1 := by apply Matrix.ext; change ∀ i j, raw23859step2 i j = -(raw23859step1 i j); unfold raw23859step2 raw23859step1; decide +kernel
      have hl : raw23859step2Labels = raw23859step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1702 node1702Labels := by rfl

def raw23860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23860Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23860step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23860step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23860 raw23860Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw23860 raw23860Labels = mixedMoment B raw23860step0 raw23860step0Labels := by
      have hz : ∀ j, raw23860 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23860step0 = (fun i j => raw23860 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23860step0 raw23860; decide +kernel
      have hl : raw23860step0Labels = raw23860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23860 raw23860Labels permutation265 hz
    mixedMoment B raw23860step0 raw23860step0Labels = mixedMoment B raw23860step1 raw23860step1Labels := by
      have ha : raw23860step1 = (fun i j => raw23860step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23860step1 raw23860step0; decide +kernel
      have hl : raw23860step1Labels = raw23860step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23860step0 raw23860step0Labels permutation34 permutation2
    _ = mixedMoment B node2881 node2881Labels := by rfl

def raw23861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23861Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23861step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23861step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23861 raw23861Labels = mixedMoment B node1314 node1314Labels := by
  calc
    mixedMoment B raw23861 raw23861Labels = mixedMoment B raw23861step0 raw23861step0Labels := by
      have ha : raw23861step0 = (fun i j => raw23861 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23861step0 raw23861; decide +kernel
      have hl : raw23861step0Labels = raw23861Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23861 raw23861Labels permutation178 permutation2
    _ = mixedMoment B node1314 node1314Labels := by rfl

def raw23862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23862Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23862step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23862step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23862 raw23862Labels = mixedMoment B node1367 node1367Labels := by
  calc
    mixedMoment B raw23862 raw23862Labels = mixedMoment B raw23862step0 raw23862step0Labels := by
      have hz : ∀ j, raw23862 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23862step0 = (fun i j => raw23862 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23862step0 raw23862; decide +kernel
      have hl : raw23862step0Labels = raw23862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23862 raw23862Labels permutation265 hz
    mixedMoment B raw23862step0 raw23862step0Labels = mixedMoment B raw23862step1 raw23862step1Labels := by
      have ha : raw23862step1 = (fun i j => raw23862step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23862step1 raw23862step0; decide +kernel
      have hl : raw23862step1Labels = raw23862step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23862step0 raw23862step0Labels permutation34 permutation2
    _ = mixedMoment B node1367 node1367Labels := by rfl

def raw23863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23863Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23863step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23863step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23863 raw23863Labels = mixedMoment B node1318 node1318Labels := by
  calc
    mixedMoment B raw23863 raw23863Labels = mixedMoment B raw23863step0 raw23863step0Labels := by
      have hz : ∀ j, raw23863 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23863step0 = (fun i j => raw23863 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23863step0 raw23863; decide +kernel
      have hl : raw23863step0Labels = raw23863Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23863 raw23863Labels permutation265 hz
    mixedMoment B raw23863step0 raw23863step0Labels = mixedMoment B raw23863step1 raw23863step1Labels := by
      have ha : raw23863step1 = (fun i j => raw23863step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23863step1 raw23863step0; decide +kernel
      have hl : raw23863step1Labels = raw23863step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23863step0 raw23863step0Labels permutation34 permutation2
    _ = mixedMoment B node1318 node1318Labels := by rfl

def raw23864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23864Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23864step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23864 raw23864Labels = mixedMoment B node1321 node1321Labels := by
  calc
    mixedMoment B raw23864 raw23864Labels = mixedMoment B raw23864step0 raw23864step0Labels := by
      have hz : ∀ j, raw23864 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23864step0 = (fun i j => raw23864 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23864step0 raw23864; decide +kernel
      have hl : raw23864step0Labels = raw23864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23864 raw23864Labels permutation265 hz
    _ = mixedMoment B node1321 node1321Labels := by rfl

def raw23865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw23865Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw23865step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw23865step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23865 raw23865Labels = mixedMoment B node1317 node1317Labels := by
  calc
    mixedMoment B raw23865 raw23865Labels = mixedMoment B raw23865step0 raw23865step0Labels := by
      have hz : ∀ j, raw23865 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23865step0 = (fun i j => raw23865 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23865step0 raw23865; decide +kernel
      have hl : raw23865step0Labels = raw23865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23865 raw23865Labels permutation265 hz
    mixedMoment B raw23865step0 raw23865step0Labels = mixedMoment B raw23865step1 raw23865step1Labels := by
      have ha : raw23865step1 = (fun i j => raw23865step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23865step1 raw23865step0; decide +kernel
      have hl : raw23865step1Labels = raw23865step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23865step0 raw23865step0Labels permutation34 permutation2
    _ = mixedMoment B node1317 node1317Labels := by rfl

def raw23866 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![1, -1], ![0, 0], ![2, -2]]
def raw23866Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23866step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![1, -1], ![2, -2]]
def raw23866step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23866step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]
def raw23866step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23866step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw23866step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical23866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23866 raw23866Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw23866 raw23866Labels = mixedMoment B raw23866step0 raw23866step0Labels := by
      have hz : ∀ j, raw23866 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw23866step0 = (fun i j => raw23866 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw23866step0 raw23866; decide +kernel
      have hl : raw23866step0Labels = raw23866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23866 raw23866Labels permutation520 hz
    mixedMoment B raw23866step0 raw23866step0Labels = mixedMoment B raw23866step1 raw23866step1Labels := by
      have hz : ∀ j, raw23866step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23866step1 = (fun i j => raw23866step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23866step1 raw23866step0; decide +kernel
      have hl : raw23866step1Labels = raw23866step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23866step0 raw23866step0Labels permutation56 hz
    mixedMoment B raw23866step1 raw23866step1Labels = mixedMoment B raw23866step2 raw23866step2Labels := by
      have ha : raw23866step2 = (fun i j => raw23866step1 (permutation14 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23866step2 raw23866step1; decide +kernel
      have hl : raw23866step2Labels = raw23866step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23866step1 raw23866step1Labels permutation14 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw23867 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23867Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw23867step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23867step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23867step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23867 raw23867Labels = mixedMoment B node3238 node3238Labels := by
  calc
    mixedMoment B raw23867 raw23867Labels = mixedMoment B raw23867step0 raw23867step0Labels := by
      have ha : raw23867step0 = (fun i j => raw23867 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23867step0 raw23867; decide +kernel
      have hl : raw23867step0Labels = raw23867Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23867 raw23867Labels permutation188 permutation2
    mixedMoment B raw23867step0 raw23867step0Labels = mixedMoment B raw23867step1 raw23867step1Labels := by
      have ha : raw23867step1 = -raw23867step0 := by apply Matrix.ext; change ∀ i j, raw23867step1 i j = -(raw23867step0 i j); unfold raw23867step1 raw23867step0; decide +kernel
      have hl : raw23867step1Labels = raw23867step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3238 node3238Labels := by rfl

def raw23868 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23868Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23868step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23868step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw23868step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23868step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23868step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23868 raw23868Labels = mixedMoment B node3240 node3240Labels := by
  calc
    mixedMoment B raw23868 raw23868Labels = mixedMoment B raw23868step0 raw23868step0Labels := by
      have hz : ∀ j, raw23868 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23868step0 = (fun i j => raw23868 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23868step0 raw23868; decide +kernel
      have hl : raw23868step0Labels = raw23868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23868 raw23868Labels permutation265 hz
    mixedMoment B raw23868step0 raw23868step0Labels = mixedMoment B raw23868step1 raw23868step1Labels := by
      have ha : raw23868step1 = (fun i j => raw23868step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23868step1 raw23868step0; decide +kernel
      have hl : raw23868step1Labels = raw23868step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23868step0 raw23868step0Labels permutation34 permutation2
    mixedMoment B raw23868step1 raw23868step1Labels = mixedMoment B raw23868step2 raw23868step2Labels := by
      have ha : raw23868step2 = -raw23868step1 := by apply Matrix.ext; change ∀ i j, raw23868step2 i j = -(raw23868step1 i j); unfold raw23868step2 raw23868step1; decide +kernel
      have hl : raw23868step2Labels = raw23868step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3240 node3240Labels := by rfl

def raw23869 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw23869Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw23869step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw23869step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23869 raw23869Labels = mixedMoment B node2466 node2466Labels := by
  calc
    mixedMoment B raw23869 raw23869Labels = mixedMoment B raw23869step0 raw23869step0Labels := by
      have hz : ∀ j, raw23869 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23869step0 = (fun i j => raw23869 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23869step0 raw23869; decide +kernel
      have hl : raw23869step0Labels = raw23869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23869 raw23869Labels permutation265 hz
    mixedMoment B raw23869step0 raw23869step0Labels = mixedMoment B raw23869step1 raw23869step1Labels := by
      have ha : raw23869step1 = (fun i j => raw23869step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23869step1 raw23869step0; decide +kernel
      have hl : raw23869step1Labels = raw23869step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23869step0 raw23869step0Labels permutation145 permutation2
    _ = mixedMoment B node2466 node2466Labels := by rfl

def raw23870 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23870Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23870step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23870step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw23870step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23870step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw23870step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23870 raw23870Labels = mixedMoment B node827 node827Labels := by
  calc
    mixedMoment B raw23870 raw23870Labels = mixedMoment B raw23870step0 raw23870step0Labels := by
      have hz : ∀ j, raw23870 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23870step0 = (fun i j => raw23870 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23870step0 raw23870; decide +kernel
      have hl : raw23870step0Labels = raw23870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23870 raw23870Labels permutation265 hz
    mixedMoment B raw23870step0 raw23870step0Labels = mixedMoment B raw23870step1 raw23870step1Labels := by
      have ha : raw23870step1 = (fun i j => raw23870step0 (permutation53 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23870step1 raw23870step0; decide +kernel
      have hl : raw23870step1Labels = raw23870step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23870step0 raw23870step0Labels permutation53 permutation4
    mixedMoment B raw23870step1 raw23870step1Labels = mixedMoment B raw23870step2 raw23870step2Labels := by
      have ha : raw23870step2 = -raw23870step1 := by apply Matrix.ext; change ∀ i j, raw23870step2 i j = -(raw23870step1 i j); unfold raw23870step2 raw23870step1; decide +kernel
      have hl : raw23870step2Labels = raw23870step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node827 node827Labels := by rfl

def raw23871 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23871Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw23871step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23871step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw23871step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23871 raw23871Labels = mixedMoment B node1609 node1609Labels := by
  calc
    mixedMoment B raw23871 raw23871Labels = mixedMoment B raw23871step0 raw23871step0Labels := by
      have ha : raw23871step0 = (fun i j => raw23871 (permutation173 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23871step0 raw23871; decide +kernel
      have hl : raw23871step0Labels = raw23871Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23871 raw23871Labels permutation173 permutation4
    mixedMoment B raw23871step0 raw23871step0Labels = mixedMoment B raw23871step1 raw23871step1Labels := by
      have ha : raw23871step1 = -raw23871step0 := by apply Matrix.ext; change ∀ i j, raw23871step1 i j = -(raw23871step0 i j); unfold raw23871step1 raw23871step0; decide +kernel
      have hl : raw23871step1Labels = raw23871step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1609 node1609Labels := by rfl

def raw23872 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw23872Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw23872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23872step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw23872step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23872step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw23872step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23872 raw23872Labels = mixedMoment B node1658 node1658Labels := by
  calc
    mixedMoment B raw23872 raw23872Labels = mixedMoment B raw23872step0 raw23872step0Labels := by
      have hz : ∀ j, raw23872 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23872step0 = (fun i j => raw23872 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23872step0 raw23872; decide +kernel
      have hl : raw23872step0Labels = raw23872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23872 raw23872Labels permutation265 hz
    mixedMoment B raw23872step0 raw23872step0Labels = mixedMoment B raw23872step1 raw23872step1Labels := by
      have ha : raw23872step1 = (fun i j => raw23872step0 (permutation53 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23872step1 raw23872step0; decide +kernel
      have hl : raw23872step1Labels = raw23872step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23872step0 raw23872step0Labels permutation53 permutation4
    mixedMoment B raw23872step1 raw23872step1Labels = mixedMoment B raw23872step2 raw23872step2Labels := by
      have ha : raw23872step2 = -raw23872step1 := by apply Matrix.ext; change ∀ i j, raw23872step2 i j = -(raw23872step1 i j); unfold raw23872step2 raw23872step1; decide +kernel
      have hl : raw23872step2Labels = raw23872step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1658 node1658Labels := by rfl

def raw23873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23873Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23873step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23873 raw23873Labels = mixedMoment B node1351 node1351Labels := by
  calc
    mixedMoment B raw23873 raw23873Labels = mixedMoment B raw23873step0 raw23873step0Labels := by
      have hz : ∀ j, raw23873 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23873step0 = (fun i j => raw23873 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23873step0 raw23873; decide +kernel
      have hl : raw23873step0Labels = raw23873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23873 raw23873Labels permutation265 hz
    _ = mixedMoment B node1351 node1351Labels := by rfl

def raw23874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23874Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -3, 1]]
def raw23874step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23874 raw23874Labels = mixedMoment B node2237 node2237Labels := by
  calc
    mixedMoment B raw23874 raw23874Labels = mixedMoment B raw23874step0 raw23874step0Labels := by
      have ha : raw23874step0 = (fun i j => raw23874 (permutation394 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23874step0 raw23874; decide +kernel
      have hl : raw23874step0Labels = raw23874Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23874 raw23874Labels permutation394 permutation4
    _ = mixedMoment B node2237 node2237Labels := by rfl

def raw23875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23875Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23875step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23875 raw23875Labels = mixedMoment B node2840 node2840Labels := by
  calc
    mixedMoment B raw23875 raw23875Labels = mixedMoment B raw23875step0 raw23875step0Labels := by
      have hz : ∀ j, raw23875 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23875step0 = (fun i j => raw23875 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23875step0 raw23875; decide +kernel
      have hl : raw23875step0Labels = raw23875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23875 raw23875Labels permutation265 hz
    _ = mixedMoment B node2840 node2840Labels := by rfl

def raw23876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23876Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -3, 3], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23876step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23876step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw23876step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23876 raw23876Labels = mixedMoment B node2254 node2254Labels := by
  calc
    mixedMoment B raw23876 raw23876Labels = mixedMoment B raw23876step0 raw23876step0Labels := by
      have hz : ∀ j, raw23876 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23876step0 = (fun i j => raw23876 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23876step0 raw23876; decide +kernel
      have hl : raw23876step0Labels = raw23876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23876 raw23876Labels permutation265 hz
    mixedMoment B raw23876step0 raw23876step0Labels = mixedMoment B raw23876step1 raw23876step1Labels := by
      have ha : raw23876step1 = (fun i j => raw23876step0 (permutation73 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23876step1 raw23876step0; decide +kernel
      have hl : raw23876step1Labels = raw23876step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23876step0 raw23876step0Labels permutation73 permutation4
    _ = mixedMoment B node2254 node2254Labels := by rfl

def raw23877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -3, 3], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw23877Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -3, 3], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw23877step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw23877step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23877 raw23877Labels = mixedMoment B node2254 node2254Labels := by
  calc
    mixedMoment B raw23877 raw23877Labels = mixedMoment B raw23877step0 raw23877step0Labels := by
      have hz : ∀ j, raw23877 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23877step0 = (fun i j => raw23877 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23877step0 raw23877; decide +kernel
      have hl : raw23877step0Labels = raw23877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23877 raw23877Labels permutation265 hz
    mixedMoment B raw23877step0 raw23877step0Labels = mixedMoment B raw23877step1 raw23877step1Labels := by
      have ha : raw23877step1 = (fun i j => raw23877step0 (permutation67 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23877step1 raw23877step0; decide +kernel
      have hl : raw23877step1Labels = raw23877step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23877step0 raw23877step0Labels permutation67 permutation4
    _ = mixedMoment B node2254 node2254Labels := by rfl

def raw23878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw23878Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw23878step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw23878step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23878 raw23878Labels = mixedMoment B node2246 node2246Labels := by
  calc
    mixedMoment B raw23878 raw23878Labels = mixedMoment B raw23878step0 raw23878step0Labels := by
      have hz : ∀ j, raw23878 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23878step0 = (fun i j => raw23878 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23878step0 raw23878; decide +kernel
      have hl : raw23878step0Labels = raw23878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23878 raw23878Labels permutation265 hz
    mixedMoment B raw23878step0 raw23878step0Labels = mixedMoment B raw23878step1 raw23878step1Labels := by
      have ha : raw23878step1 = (fun i j => raw23878step0 (permutation65 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23878step1 raw23878step0; decide +kernel
      have hl : raw23878step1Labels = raw23878step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23878step0 raw23878step0Labels permutation65 permutation4
    _ = mixedMoment B node2246 node2246Labels := by rfl

def raw23879 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-3, 3], ![1, -1], ![1, -1], ![2, -2]]
def raw23879Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23879step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![1, -1], ![1, -1], ![2, -2]]
def raw23879step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23879step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw23879step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical23879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23879 raw23879Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw23879 raw23879Labels = mixedMoment B raw23879step0 raw23879step0Labels := by
      have hz : ∀ j, raw23879 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23879step0 = (fun i j => raw23879 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23879step0 raw23879; decide +kernel
      have hl : raw23879step0Labels = raw23879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23879 raw23879Labels permutation265 hz
    mixedMoment B raw23879step0 raw23879step0Labels = mixedMoment B raw23879step1 raw23879step1Labels := by
      have ha : raw23879step1 = (fun i j => raw23879step0 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23879step1 raw23879step0; decide +kernel
      have hl : raw23879step1Labels = raw23879step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23879step0 raw23879step0Labels permutation56 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw23880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw23880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23880 raw23880Labels = mixedMoment B node578 node578Labels := by
  calc
    mixedMoment B raw23880 raw23880Labels = mixedMoment B raw23880step0 raw23880step0Labels := by
      have ha : raw23880step0 = (fun i j => raw23880 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23880step0 raw23880; decide +kernel
      have hl : raw23880step0Labels = raw23880Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23880 raw23880Labels permutation184 permutation2
    _ = mixedMoment B node578 node578Labels := by rfl

def raw23881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw23881Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23881step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23881 raw23881Labels = mixedMoment B node942 node942Labels := by
  calc
    mixedMoment B raw23881 raw23881Labels = mixedMoment B raw23881step0 raw23881step0Labels := by
      have ha : raw23881step0 = (fun i j => raw23881 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23881step0 raw23881; decide +kernel
      have hl : raw23881step0Labels = raw23881Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23881 raw23881Labels permutation184 permutation2
    _ = mixedMoment B node942 node942Labels := by rfl

def raw23882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw23882Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw23882step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23882step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23882 raw23882Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw23882 raw23882Labels = mixedMoment B raw23882step0 raw23882step0Labels := by
      have hz : ∀ j, raw23882 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw23882step0 = (fun i j => raw23882 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw23882step0 raw23882; decide +kernel
      have hl : raw23882step0Labels = raw23882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23882 raw23882Labels permutation520 hz
    mixedMoment B raw23882step0 raw23882step0Labels = mixedMoment B raw23882step1 raw23882step1Labels := by
      have ha : raw23882step1 = (fun i j => raw23882step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23882step1 raw23882step0; decide +kernel
      have hl : raw23882step1Labels = raw23882step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23882step0 raw23882step0Labels permutation40 permutation2
    _ = mixedMoment B node1041 node1041Labels := by rfl

def raw23883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw23883Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23883step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw23883step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23883 raw23883Labels = mixedMoment B node1039 node1039Labels := by
  calc
    mixedMoment B raw23883 raw23883Labels = mixedMoment B raw23883step0 raw23883step0Labels := by
      have ha : raw23883step0 = (fun i j => raw23883 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23883step0 raw23883; decide +kernel
      have hl : raw23883step0Labels = raw23883Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23883 raw23883Labels permutation184 permutation2
    _ = mixedMoment B node1039 node1039Labels := by rfl

def raw23884 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23884Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23884step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw23884step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23884 raw23884Labels = mixedMoment B node3299 node3299Labels := by
  calc
    mixedMoment B raw23884 raw23884Labels = mixedMoment B raw23884step0 raw23884step0Labels := by
      have hz : ∀ j, raw23884 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23884step0 = (fun i j => raw23884 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23884step0 raw23884; decide +kernel
      have hl : raw23884step0Labels = raw23884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23884 raw23884Labels permutation346 hz
    mixedMoment B raw23884step0 raw23884step0Labels = mixedMoment B raw23884step1 raw23884step1Labels := by
      have ha : raw23884step1 = -raw23884step0 := by apply Matrix.ext; change ∀ i j, raw23884step1 i j = -(raw23884step0 i j); unfold raw23884step1 raw23884step0; decide +kernel
      have hl : raw23884step1Labels = raw23884step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3299 node3299Labels := by rfl

def raw23885 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23885Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23885step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23885step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23885step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23885 raw23885Labels = mixedMoment B node3282 node3282Labels := by
  calc
    mixedMoment B raw23885 raw23885Labels = mixedMoment B raw23885step0 raw23885step0Labels := by
      have ha : raw23885step0 = (fun i j => raw23885 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23885step0 raw23885; decide +kernel
      have hl : raw23885step0Labels = raw23885Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23885 raw23885Labels permutation155 permutation2
    mixedMoment B raw23885step0 raw23885step0Labels = mixedMoment B raw23885step1 raw23885step1Labels := by
      have ha : raw23885step1 = -raw23885step0 := by apply Matrix.ext; change ∀ i j, raw23885step1 i j = -(raw23885step0 i j); unfold raw23885step1 raw23885step0; decide +kernel
      have hl : raw23885step1Labels = raw23885step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3282 node3282Labels := by rfl

def raw23886 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw23886Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw23886step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23886step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw23886step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23886 raw23886Labels = mixedMoment B node3282 node3282Labels := by
  calc
    mixedMoment B raw23886 raw23886Labels = mixedMoment B raw23886step0 raw23886step0Labels := by
      have ha : raw23886step0 = (fun i j => raw23886 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23886step0 raw23886; decide +kernel
      have hl : raw23886step0Labels = raw23886Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23886 raw23886Labels permutation153 permutation2
    mixedMoment B raw23886step0 raw23886step0Labels = mixedMoment B raw23886step1 raw23886step1Labels := by
      have ha : raw23886step1 = -raw23886step0 := by apply Matrix.ext; change ∀ i j, raw23886step1 i j = -(raw23886step0 i j); unfold raw23886step1 raw23886step0; decide +kernel
      have hl : raw23886step1Labels = raw23886step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3282 node3282Labels := by rfl

def raw23887 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23887Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23887step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23887 raw23887Labels = mixedMoment B node3281 node3281Labels := by
  calc
    mixedMoment B raw23887 raw23887Labels = mixedMoment B raw23887step0 raw23887step0Labels := by
      have ha : raw23887step0 = -raw23887 := by apply Matrix.ext; change ∀ i j, raw23887step0 i j = -(raw23887 i j); unfold raw23887step0 raw23887; decide +kernel
      have hl : raw23887step0Labels = raw23887Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3281 node3281Labels := by rfl

def raw23888 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23888Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw23888step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23888step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23888step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23888 raw23888Labels = mixedMoment B node784 node784Labels := by
  calc
    mixedMoment B raw23888 raw23888Labels = mixedMoment B raw23888step0 raw23888step0Labels := by
      have ha : raw23888step0 = (fun i j => raw23888 (permutation215 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23888step0 raw23888; decide +kernel
      have hl : raw23888step0Labels = raw23888Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23888 raw23888Labels permutation215 permutation4
    mixedMoment B raw23888step0 raw23888step0Labels = mixedMoment B raw23888step1 raw23888step1Labels := by
      have ha : raw23888step1 = -raw23888step0 := by apply Matrix.ext; change ∀ i j, raw23888step1 i j = -(raw23888step0 i j); unfold raw23888step1 raw23888step0; decide +kernel
      have hl : raw23888step1Labels = raw23888step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node784 node784Labels := by rfl

def raw23889 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23889Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw23889step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23889step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw23889step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23889 raw23889Labels = mixedMoment B node784 node784Labels := by
  calc
    mixedMoment B raw23889 raw23889Labels = mixedMoment B raw23889step0 raw23889step0Labels := by
      have ha : raw23889step0 = (fun i j => raw23889 (permutation213 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23889step0 raw23889; decide +kernel
      have hl : raw23889step0Labels = raw23889Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23889 raw23889Labels permutation213 permutation4
    mixedMoment B raw23889step0 raw23889step0Labels = mixedMoment B raw23889step1 raw23889step1Labels := by
      have ha : raw23889step1 = -raw23889step0 := by apply Matrix.ext; change ∀ i j, raw23889step1 i j = -(raw23889step0 i j); unfold raw23889step1 raw23889step0; decide +kernel
      have hl : raw23889step1Labels = raw23889step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node784 node784Labels := by rfl

def raw23890 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23890Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw23890step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23890step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23890 raw23890Labels = mixedMoment B node803 node803Labels := by
  calc
    mixedMoment B raw23890 raw23890Labels = mixedMoment B raw23890step0 raw23890step0Labels := by
      have ha : raw23890step0 = (fun i j => raw23890 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23890step0 raw23890; decide +kernel
      have hl : raw23890step0Labels = raw23890Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23890 raw23890Labels permutation224 permutation4
    mixedMoment B raw23890step0 raw23890step0Labels = mixedMoment B raw23890step1 raw23890step1Labels := by
      have ha : raw23890step1 = -raw23890step0 := by apply Matrix.ext; change ∀ i j, raw23890step1 i j = -(raw23890step0 i j); unfold raw23890step1 raw23890step0; decide +kernel
      have hl : raw23890step1Labels = raw23890step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node803 node803Labels := by rfl

def raw23891 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw23891Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw23891step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23891step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23891step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23891 raw23891Labels = mixedMoment B node803 node803Labels := by
  calc
    mixedMoment B raw23891 raw23891Labels = mixedMoment B raw23891step0 raw23891step0Labels := by
      have ha : raw23891step0 = (fun i j => raw23891 (permutation200 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23891step0 raw23891; decide +kernel
      have hl : raw23891step0Labels = raw23891Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23891 raw23891Labels permutation200 permutation4
    mixedMoment B raw23891step0 raw23891step0Labels = mixedMoment B raw23891step1 raw23891step1Labels := by
      have ha : raw23891step1 = -raw23891step0 := by apply Matrix.ext; change ∀ i j, raw23891step1 i j = -(raw23891step0 i j); unfold raw23891step1 raw23891step0; decide +kernel
      have hl : raw23891step1Labels = raw23891step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node803 node803Labels := by rfl

def raw23892 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23892Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23892step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw23892step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23892step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw23892step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23892 raw23892Labels = mixedMoment B node782 node782Labels := by
  calc
    mixedMoment B raw23892 raw23892Labels = mixedMoment B raw23892step0 raw23892step0Labels := by
      have ha : raw23892step0 = (fun i j => raw23892 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23892step0 raw23892; decide +kernel
      have hl : raw23892step0Labels = raw23892Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23892 raw23892Labels permutation212 permutation4
    mixedMoment B raw23892step0 raw23892step0Labels = mixedMoment B raw23892step1 raw23892step1Labels := by
      have ha : raw23892step1 = -raw23892step0 := by apply Matrix.ext; change ∀ i j, raw23892step1 i j = -(raw23892step0 i j); unfold raw23892step1 raw23892step0; decide +kernel
      have hl : raw23892step1Labels = raw23892step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node782 node782Labels := by rfl

def raw23893 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23893Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw23893step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw23893step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23893step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23893step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23893 raw23893Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw23893 raw23893Labels = mixedMoment B raw23893step0 raw23893step0Labels := by
      have hz : ∀ j, raw23893 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23893step0 = (fun i j => raw23893 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23893step0 raw23893; decide +kernel
      have hl : raw23893step0Labels = raw23893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23893 raw23893Labels permutation346 hz
    mixedMoment B raw23893step0 raw23893step0Labels = mixedMoment B raw23893step1 raw23893step1Labels := by
      have ha : raw23893step1 = (fun i j => raw23893step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23893step1 raw23893step0; decide +kernel
      have hl : raw23893step1Labels = raw23893step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23893step0 raw23893step0Labels permutation44 permutation4
    mixedMoment B raw23893step1 raw23893step1Labels = mixedMoment B raw23893step2 raw23893step2Labels := by
      have ha : raw23893step2 = -raw23893step1 := by apply Matrix.ext; change ∀ i j, raw23893step2 i j = -(raw23893step1 i j); unfold raw23893step2 raw23893step1; decide +kernel
      have hl : raw23893step2Labels = raw23893step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1724 node1724Labels := by rfl

def raw23894 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw23894Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw23894step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23894step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw23894step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23894 raw23894Labels = mixedMoment B node1642 node1642Labels := by
  calc
    mixedMoment B raw23894 raw23894Labels = mixedMoment B raw23894step0 raw23894step0Labels := by
      have ha : raw23894step0 = (fun i j => raw23894 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23894step0 raw23894; decide +kernel
      have hl : raw23894step0Labels = raw23894Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23894 raw23894Labels permutation224 permutation4
    mixedMoment B raw23894step0 raw23894step0Labels = mixedMoment B raw23894step1 raw23894step1Labels := by
      have ha : raw23894step1 = -raw23894step0 := by apply Matrix.ext; change ∀ i j, raw23894step1 i j = -(raw23894step0 i j); unfold raw23894step1 raw23894step0; decide +kernel
      have hl : raw23894step1Labels = raw23894step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1642 node1642Labels := by rfl

def raw23895 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23895Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw23895step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23895step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw23895step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23895 raw23895Labels = mixedMoment B node1713 node1713Labels := by
  calc
    mixedMoment B raw23895 raw23895Labels = mixedMoment B raw23895step0 raw23895step0Labels := by
      have ha : raw23895step0 = (fun i j => raw23895 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23895step0 raw23895; decide +kernel
      have hl : raw23895step0Labels = raw23895Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23895 raw23895Labels permutation240 permutation4
    mixedMoment B raw23895step0 raw23895step0Labels = mixedMoment B raw23895step1 raw23895step1Labels := by
      have ha : raw23895step1 = -raw23895step0 := by apply Matrix.ext; change ∀ i j, raw23895step1 i j = -(raw23895step0 i j); unfold raw23895step1 raw23895step0; decide +kernel
      have hl : raw23895step1Labels = raw23895step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1713 node1713Labels := by rfl

def raw23896 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23896Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23896step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw23896step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23896step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23896step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23896 raw23896Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw23896 raw23896Labels = mixedMoment B raw23896step0 raw23896step0Labels := by
      have hz : ∀ j, raw23896 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23896step0 = (fun i j => raw23896 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23896step0 raw23896; decide +kernel
      have hl : raw23896step0Labels = raw23896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23896 raw23896Labels permutation346 hz
    mixedMoment B raw23896step0 raw23896step0Labels = mixedMoment B raw23896step1 raw23896step1Labels := by
      have ha : raw23896step1 = (fun i j => raw23896step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23896step1 raw23896step0; decide +kernel
      have hl : raw23896step1Labels = raw23896step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23896step0 raw23896step0Labels permutation40 permutation4
    mixedMoment B raw23896step1 raw23896step1Labels = mixedMoment B raw23896step2 raw23896step2Labels := by
      have ha : raw23896step2 = -raw23896step1 := by apply Matrix.ext; change ∀ i j, raw23896step2 i j = -(raw23896step1 i j); unfold raw23896step2 raw23896step1; decide +kernel
      have hl : raw23896step2Labels = raw23896step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1707 node1707Labels := by rfl

def raw23897 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw23897Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw23897step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23897step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw23897step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23897 raw23897Labels = mixedMoment B node1635 node1635Labels := by
  calc
    mixedMoment B raw23897 raw23897Labels = mixedMoment B raw23897step0 raw23897step0Labels := by
      have ha : raw23897step0 = (fun i j => raw23897 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23897step0 raw23897; decide +kernel
      have hl : raw23897step0Labels = raw23897Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23897 raw23897Labels permutation212 permutation4
    mixedMoment B raw23897step0 raw23897step0Labels = mixedMoment B raw23897step1 raw23897step1Labels := by
      have ha : raw23897step1 = -raw23897step0 := by apply Matrix.ext; change ∀ i j, raw23897step1 i j = -(raw23897step0 i j); unfold raw23897step1 raw23897step0; decide +kernel
      have hl : raw23897step1Labels = raw23897step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1635 node1635Labels := by rfl

def raw23898 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw23898Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw23898step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23898step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw23898step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23898 raw23898Labels = mixedMoment B node1635 node1635Labels := by
  calc
    mixedMoment B raw23898 raw23898Labels = mixedMoment B raw23898step0 raw23898step0Labels := by
      have ha : raw23898step0 = (fun i j => raw23898 (permutation234 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23898step0 raw23898; decide +kernel
      have hl : raw23898step0Labels = raw23898Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23898 raw23898Labels permutation234 permutation4
    mixedMoment B raw23898step0 raw23898step0Labels = mixedMoment B raw23898step1 raw23898step1Labels := by
      have ha : raw23898step1 = -raw23898step0 := by apply Matrix.ext; change ∀ i j, raw23898step1 i j = -(raw23898step0 i j); unfold raw23898step1 raw23898step0; decide +kernel
      have hl : raw23898step1Labels = raw23898step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1635 node1635Labels := by rfl

def raw23899 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23899Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23899step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw23899step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23899step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw23899step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23899 raw23899Labels = mixedMoment B node1701 node1701Labels := by
  calc
    mixedMoment B raw23899 raw23899Labels = mixedMoment B raw23899step0 raw23899step0Labels := by
      have ha : raw23899step0 = (fun i j => raw23899 (permutation217 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23899step0 raw23899; decide +kernel
      have hl : raw23899step0Labels = raw23899Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23899 raw23899Labels permutation217 permutation4
    mixedMoment B raw23899step0 raw23899step0Labels = mixedMoment B raw23899step1 raw23899step1Labels := by
      have ha : raw23899step1 = -raw23899step0 := by apply Matrix.ext; change ∀ i j, raw23899step1 i j = -(raw23899step0 i j); unfold raw23899step1 raw23899step0; decide +kernel
      have hl : raw23899step1Labels = raw23899step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1701 node1701Labels := by rfl

def raw23900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw23900Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23900step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw23900step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23900 raw23900Labels = mixedMoment B node580 node580Labels := by
  calc
    mixedMoment B raw23900 raw23900Labels = mixedMoment B raw23900step0 raw23900step0Labels := by
      have ha : raw23900step0 = (fun i j => raw23900 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23900step0 raw23900; decide +kernel
      have hl : raw23900step0Labels = raw23900Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23900 raw23900Labels permutation182 permutation2
    _ = mixedMoment B node580 node580Labels := by rfl

def raw23901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw23901Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23901 raw23901Labels = mixedMoment B node1021 node1021Labels := by
  calc
    _ = mixedMoment B node1021 node1021Labels := by rfl

def raw23902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw23902Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23902step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw23902step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23902 raw23902Labels = mixedMoment B node944 node944Labels := by
  calc
    mixedMoment B raw23902 raw23902Labels = mixedMoment B raw23902step0 raw23902step0Labels := by
      have ha : raw23902step0 = (fun i j => raw23902 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23902step0 raw23902; decide +kernel
      have hl : raw23902step0Labels = raw23902Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23902 raw23902Labels permutation182 permutation2
    _ = mixedMoment B node944 node944Labels := by rfl

def raw23903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw23903Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw23903step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23903 raw23903Labels = mixedMoment B node1021 node1021Labels := by
  calc
    mixedMoment B raw23903 raw23903Labels = mixedMoment B raw23903step0 raw23903step0Labels := by
      have ha : raw23903step0 = (fun i j => raw23903 (permutation190 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23903step0 raw23903; decide +kernel
      have hl : raw23903step0Labels = raw23903Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23903 raw23903Labels permutation190 permutation2
    _ = mixedMoment B node1021 node1021Labels := by rfl

def raw23904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw23904Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw23904step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23904 raw23904Labels = mixedMoment B node1039 node1039Labels := by
  calc
    mixedMoment B raw23904 raw23904Labels = mixedMoment B raw23904step0 raw23904step0Labels := by
      have ha : raw23904step0 = (fun i j => raw23904 (permutation186 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23904step0 raw23904; decide +kernel
      have hl : raw23904step0Labels = raw23904Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23904 raw23904Labels permutation186 permutation2
    _ = mixedMoment B node1039 node1039Labels := by rfl

def raw23905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23905Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23905step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23905 raw23905Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw23905 raw23905Labels = mixedMoment B raw23905step0 raw23905step0Labels := by
      have ha : raw23905step0 = (fun i j => raw23905 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23905step0 raw23905; decide +kernel
      have hl : raw23905step0Labels = raw23905Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23905 raw23905Labels permutation154 permutation2
    _ = mixedMoment B node2924 node2924Labels := by rfl

def raw23906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23906Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23906step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23906 raw23906Labels = mixedMoment B node1383 node1383Labels := by
  calc
    mixedMoment B raw23906 raw23906Labels = mixedMoment B raw23906step0 raw23906step0Labels := by
      have ha : raw23906step0 = (fun i j => raw23906 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23906step0 raw23906; decide +kernel
      have hl : raw23906step0Labels = raw23906Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23906 raw23906Labels permutation154 permutation2
    _ = mixedMoment B node1383 node1383Labels := by rfl

def raw23907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23907Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23907step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw23907step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23907 raw23907Labels = mixedMoment B node1335 node1335Labels := by
  calc
    mixedMoment B raw23907 raw23907Labels = mixedMoment B raw23907step0 raw23907step0Labels := by
      have ha : raw23907step0 = (fun i j => raw23907 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23907step0 raw23907; decide +kernel
      have hl : raw23907step0Labels = raw23907Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23907 raw23907Labels permutation154 permutation2
    _ = mixedMoment B node1335 node1335Labels := by rfl

def raw23908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw23908Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23908step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw23908step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23908 raw23908Labels = mixedMoment B node1328 node1328Labels := by
  calc
    mixedMoment B raw23908 raw23908Labels = mixedMoment B raw23908step0 raw23908step0Labels := by
      have ha : raw23908step0 = (fun i j => raw23908 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23908step0 raw23908; decide +kernel
      have hl : raw23908step0Labels = raw23908Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23908 raw23908Labels permutation154 permutation2
    _ = mixedMoment B node1328 node1328Labels := by rfl

def raw23909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23909 raw23909Labels = mixedMoment B node1330 node1330Labels := by
  calc
    _ = mixedMoment B node1330 node1330Labels := by rfl

def raw23910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw23910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23910step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw23910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23910 raw23910Labels = mixedMoment B node1327 node1327Labels := by
  calc
    mixedMoment B raw23910 raw23910Labels = mixedMoment B raw23910step0 raw23910step0Labels := by
      have ha : raw23910step0 = (fun i j => raw23910 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23910step0 raw23910; decide +kernel
      have hl : raw23910step0Labels = raw23910Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23910 raw23910Labels permutation154 permutation2
    _ = mixedMoment B node1327 node1327Labels := by rfl

def raw23911 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![0, 0], ![2, -2]]
def raw23911Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23911step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw23911step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23911step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw23911step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23911step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw23911step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical23911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23911 raw23911Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw23911 raw23911Labels = mixedMoment B raw23911step0 raw23911step0Labels := by
      have hz : ∀ j, raw23911 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw23911step0 = (fun i j => raw23911 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw23911step0 raw23911; decide +kernel
      have hl : raw23911step0Labels = raw23911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23911 raw23911Labels permutation520 hz
    mixedMoment B raw23911step0 raw23911step0Labels = mixedMoment B raw23911step1 raw23911step1Labels := by
      have ha : raw23911step1 = (fun i j => raw23911step0 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23911step1 raw23911step0; decide +kernel
      have hl : raw23911step1Labels = raw23911step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23911step0 raw23911step0Labels permutation146 permutation0
    mixedMoment B raw23911step1 raw23911step1Labels = mixedMoment B raw23911step2 raw23911step2Labels := by
      have ha : raw23911step2 = -raw23911step1 := by apply Matrix.ext; change ∀ i j, raw23911step2 i j = -(raw23911step1 i j); unfold raw23911step2 raw23911step1; decide +kernel
      have hl : raw23911step2Labels = raw23911step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw23912 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23912step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw23912step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23912step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23912step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23912 raw23912Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw23912 raw23912Labels = mixedMoment B raw23912step0 raw23912step0Labels := by
      have hz : ∀ j, raw23912 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23912step0 = (fun i j => raw23912 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23912step0 raw23912; decide +kernel
      have hl : raw23912step0Labels = raw23912Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23912 raw23912Labels permutation346 hz
    mixedMoment B raw23912step0 raw23912step0Labels = mixedMoment B raw23912step1 raw23912step1Labels := by
      have ha : raw23912step1 = (fun i j => raw23912step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23912step1 raw23912step0; decide +kernel
      have hl : raw23912step1Labels = raw23912step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23912step0 raw23912step0Labels permutation34 permutation2
    mixedMoment B raw23912step1 raw23912step1Labels = mixedMoment B raw23912step2 raw23912step2Labels := by
      have ha : raw23912step2 = -raw23912step1 := by apply Matrix.ext; change ∀ i j, raw23912step2 i j = -(raw23912step1 i j); unfold raw23912step2 raw23912step1; decide +kernel
      have hl : raw23912step2Labels = raw23912step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3293 node3293Labels := by rfl

def raw23913 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23913Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw23913step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23913step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23913step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23913 raw23913Labels = mixedMoment B node3278 node3278Labels := by
  calc
    mixedMoment B raw23913 raw23913Labels = mixedMoment B raw23913step0 raw23913step0Labels := by
      have ha : raw23913step0 = (fun i j => raw23913 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23913step0 raw23913; decide +kernel
      have hl : raw23913step0Labels = raw23913Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23913 raw23913Labels permutation154 permutation2
    mixedMoment B raw23913step0 raw23913step0Labels = mixedMoment B raw23913step1 raw23913step1Labels := by
      have ha : raw23913step1 = -raw23913step0 := by apply Matrix.ext; change ∀ i j, raw23913step1 i j = -(raw23913step0 i j); unfold raw23913step1 raw23913step0; decide +kernel
      have hl : raw23913step1Labels = raw23913step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3278 node3278Labels := by rfl

def raw23914 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw23914Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw23914step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23914 raw23914Labels = mixedMoment B node2457 node2457Labels := by
  calc
    mixedMoment B raw23914 raw23914Labels = mixedMoment B raw23914step0 raw23914step0Labels := by
      have ha : raw23914step0 = (fun i j => raw23914 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23914step0 raw23914; decide +kernel
      have hl : raw23914step0Labels = raw23914Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23914 raw23914Labels permutation662 permutation2
    _ = mixedMoment B node2457 node2457Labels := by rfl

def raw23915 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23915Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23915step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw23915step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23915step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw23915step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23915 raw23915Labels = mixedMoment B node793 node793Labels := by
  calc
    mixedMoment B raw23915 raw23915Labels = mixedMoment B raw23915step0 raw23915step0Labels := by
      have ha : raw23915step0 = (fun i j => raw23915 (permutation221 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23915step0 raw23915; decide +kernel
      have hl : raw23915step0Labels = raw23915Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23915 raw23915Labels permutation221 permutation4
    mixedMoment B raw23915step0 raw23915step0Labels = mixedMoment B raw23915step1 raw23915step1Labels := by
      have ha : raw23915step1 = -raw23915step0 := by apply Matrix.ext; change ∀ i j, raw23915step1 i j = -(raw23915step0 i j); unfold raw23915step1 raw23915step0; decide +kernel
      have hl : raw23915step1Labels = raw23915step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node793 node793Labels := by rfl

def raw23916 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23916Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw23916step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23916step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw23916step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23916 raw23916Labels = mixedMoment B node793 node793Labels := by
  calc
    mixedMoment B raw23916 raw23916Labels = mixedMoment B raw23916step0 raw23916step0Labels := by
      have ha : raw23916step0 = (fun i j => raw23916 (permutation219 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23916step0 raw23916; decide +kernel
      have hl : raw23916step0Labels = raw23916Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23916 raw23916Labels permutation219 permutation4
    mixedMoment B raw23916step0 raw23916step0Labels = mixedMoment B raw23916step1 raw23916step1Labels := by
      have ha : raw23916step1 = -raw23916step0 := by apply Matrix.ext; change ∀ i j, raw23916step1 i j = -(raw23916step0 i j); unfold raw23916step1 raw23916step0; decide +kernel
      have hl : raw23916step1Labels = raw23916step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node793 node793Labels := by rfl

def raw23917 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23917Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw23917step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23917step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw23917step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23917 raw23917Labels = mixedMoment B node822 node822Labels := by
  calc
    mixedMoment B raw23917 raw23917Labels = mixedMoment B raw23917step0 raw23917step0Labels := by
      have ha : raw23917step0 = (fun i j => raw23917 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23917step0 raw23917; decide +kernel
      have hl : raw23917step0Labels = raw23917Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23917 raw23917Labels permutation246 permutation4
    mixedMoment B raw23917step0 raw23917step0Labels = mixedMoment B raw23917step1 raw23917step1Labels := by
      have ha : raw23917step1 = -raw23917step0 := by apply Matrix.ext; change ∀ i j, raw23917step1 i j = -(raw23917step0 i j); unfold raw23917step1 raw23917step0; decide +kernel
      have hl : raw23917step1Labels = raw23917step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node822 node822Labels := by rfl

def raw23918 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw23918Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23918step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw23918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23918step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw23918step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23918 raw23918Labels = mixedMoment B node792 node792Labels := by
  calc
    mixedMoment B raw23918 raw23918Labels = mixedMoment B raw23918step0 raw23918step0Labels := by
      have ha : raw23918step0 = (fun i j => raw23918 (permutation218 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23918step0 raw23918; decide +kernel
      have hl : raw23918step0Labels = raw23918Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23918 raw23918Labels permutation218 permutation4
    mixedMoment B raw23918step0 raw23918step0Labels = mixedMoment B raw23918step1 raw23918step1Labels := by
      have ha : raw23918step1 = -raw23918step0 := by apply Matrix.ext; change ∀ i j, raw23918step1 i j = -(raw23918step0 i j); unfold raw23918step1 raw23918step0; decide +kernel
      have hl : raw23918step1Labels = raw23918step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node792 node792Labels := by rfl

def raw23919 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23919Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw23919step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw23919step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23919step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw23919step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23919 raw23919Labels = mixedMoment B node1737 node1737Labels := by
  calc
    mixedMoment B raw23919 raw23919Labels = mixedMoment B raw23919step0 raw23919step0Labels := by
      have hz : ∀ j, raw23919 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23919step0 = (fun i j => raw23919 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23919step0 raw23919; decide +kernel
      have hl : raw23919step0Labels = raw23919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23919 raw23919Labels permutation346 hz
    mixedMoment B raw23919step0 raw23919step0Labels = mixedMoment B raw23919step1 raw23919step1Labels := by
      have ha : raw23919step1 = (fun i j => raw23919step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23919step1 raw23919step0; decide +kernel
      have hl : raw23919step1Labels = raw23919step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23919step0 raw23919step0Labels permutation50 permutation4
    mixedMoment B raw23919step1 raw23919step1Labels = mixedMoment B raw23919step2 raw23919step2Labels := by
      have ha : raw23919step2 = -raw23919step1 := by apply Matrix.ext; change ∀ i j, raw23919step2 i j = -(raw23919step1 i j); unfold raw23919step2 raw23919step1; decide +kernel
      have hl : raw23919step2Labels = raw23919step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1737 node1737Labels := by rfl

def raw23920 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw23920Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23920step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw23920step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23920step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw23920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23920 raw23920Labels = mixedMoment B node1654 node1654Labels := by
  calc
    mixedMoment B raw23920 raw23920Labels = mixedMoment B raw23920step0 raw23920step0Labels := by
      have ha : raw23920step0 = (fun i j => raw23920 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23920step0 raw23920; decide +kernel
      have hl : raw23920step0Labels = raw23920Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23920 raw23920Labels permutation246 permutation4
    mixedMoment B raw23920step0 raw23920step0Labels = mixedMoment B raw23920step1 raw23920step1Labels := by
      have ha : raw23920step1 = -raw23920step0 := by apply Matrix.ext; change ∀ i j, raw23920step1 i j = -(raw23920step0 i j); unfold raw23920step1 raw23920step0; decide +kernel
      have hl : raw23920step1Labels = raw23920step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1654 node1654Labels := by rfl

def raw23921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23921Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23921step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23921 raw23921Labels = mixedMoment B node1354 node1354Labels := by
  calc
    mixedMoment B raw23921 raw23921Labels = mixedMoment B raw23921step0 raw23921step0Labels := by
      have ha : raw23921step0 = (fun i j => raw23921 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23921step0 raw23921; decide +kernel
      have hl : raw23921step0Labels = raw23921Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23921 raw23921Labels permutation176 permutation2
    _ = mixedMoment B node1354 node1354Labels := by rfl

def raw23922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23922Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23922 raw23922Labels = mixedMoment B node2908 node2908Labels := by
  calc
    _ = mixedMoment B node2908 node2908Labels := by rfl

def raw23923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23923Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23923step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23923step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23923 raw23923Labels = mixedMoment B node2853 node2853Labels := by
  calc
    mixedMoment B raw23923 raw23923Labels = mixedMoment B raw23923step0 raw23923step0Labels := by
      have ha : raw23923step0 = (fun i j => raw23923 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23923step0 raw23923; decide +kernel
      have hl : raw23923step0Labels = raw23923Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23923 raw23923Labels permutation176 permutation2
    _ = mixedMoment B node2853 node2853Labels := by rfl

def raw23924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23924Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23924step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23924 raw23924Labels = mixedMoment B node3016 node3016Labels := by
  calc
    mixedMoment B raw23924 raw23924Labels = mixedMoment B raw23924step0 raw23924step0Labels := by
      have ha : raw23924step0 = (fun i j => raw23924 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23924step0 raw23924; decide +kernel
      have hl : raw23924step0Labels = raw23924Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23924 raw23924Labels permutation176 permutation2
    _ = mixedMoment B node3016 node3016Labels := by rfl

def raw23925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw23925Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw23925step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23925 raw23925Labels = mixedMoment B node3016 node3016Labels := by
  calc
    mixedMoment B raw23925 raw23925Labels = mixedMoment B raw23925step0 raw23925step0Labels := by
      have ha : raw23925step0 = (fun i j => raw23925 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23925step0 raw23925; decide +kernel
      have hl : raw23925step0Labels = raw23925Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23925 raw23925Labels permutation178 permutation2
    _ = mixedMoment B node3016 node3016Labels := by rfl

def raw23926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw23926Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23926step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw23926step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23926 raw23926Labels = mixedMoment B node3023 node3023Labels := by
  calc
    mixedMoment B raw23926 raw23926Labels = mixedMoment B raw23926step0 raw23926step0Labels := by
      have ha : raw23926step0 = (fun i j => raw23926 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23926step0 raw23926; decide +kernel
      have hl : raw23926step0Labels = raw23926Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23926 raw23926Labels permutation176 permutation2
    _ = mixedMoment B node3023 node3023Labels := by rfl

def raw23927 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw23927Labels : Fin 2 → Fin 2 := ![0, 1]

def raw23927step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw23927step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical23927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23927 raw23927Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw23927 raw23927Labels = mixedMoment B raw23927step0 raw23927step0Labels := by
      have ha : raw23927step0 = (fun i j => raw23927 (permutation346 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23927step0 raw23927; decide +kernel
      have hl : raw23927step0Labels = raw23927Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23927 raw23927Labels permutation346 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

def raw23928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw23928Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw23928step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23928 raw23928Labels = mixedMoment B node2509 node2509Labels := by
  calc
    mixedMoment B raw23928 raw23928Labels = mixedMoment B raw23928step0 raw23928step0Labels := by
      have hz : ∀ j, raw23928 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23928step0 = (fun i j => raw23928 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23928step0 raw23928; decide +kernel
      have hl : raw23928step0Labels = raw23928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23928 raw23928Labels permutation346 hz
    _ = mixedMoment B node2509 node2509Labels := by rfl

def raw23929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw23929Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw23929step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23929 raw23929Labels = mixedMoment B node1234 node1234Labels := by
  calc
    mixedMoment B raw23929 raw23929Labels = mixedMoment B raw23929step0 raw23929step0Labels := by
      have hz : ∀ j, raw23929 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23929step0 = (fun i j => raw23929 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23929step0 raw23929; decide +kernel
      have hl : raw23929step0Labels = raw23929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23929 raw23929Labels permutation346 hz
    _ = mixedMoment B node1234 node1234Labels := by rfl

def raw23930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw23930Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23930 raw23930Labels = mixedMoment B node1125 node1125Labels := by
  calc
    _ = mixedMoment B node1125 node1125Labels := by rfl

def raw23931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw23931Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw23931step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw23931step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23931 raw23931Labels = mixedMoment B node1133 node1133Labels := by
  calc
    mixedMoment B raw23931 raw23931Labels = mixedMoment B raw23931step0 raw23931step0Labels := by
      have hz : ∀ j, raw23931 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23931step0 = (fun i j => raw23931 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23931step0 raw23931; decide +kernel
      have hl : raw23931step0Labels = raw23931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23931 raw23931Labels permutation346 hz
    mixedMoment B raw23931step0 raw23931step0Labels = mixedMoment B raw23931step1 raw23931step1Labels := by
      have ha : raw23931step1 = (fun i j => raw23931step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23931step1 raw23931step0; decide +kernel
      have hl : raw23931step1Labels = raw23931step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23931step0 raw23931step0Labels permutation34 permutation2
    _ = mixedMoment B node1133 node1133Labels := by rfl

def raw23932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw23932Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw23932step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23932 raw23932Labels = mixedMoment B node1128 node1128Labels := by
  calc
    mixedMoment B raw23932 raw23932Labels = mixedMoment B raw23932step0 raw23932step0Labels := by
      have hz : ∀ j, raw23932 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23932step0 = (fun i j => raw23932 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23932step0 raw23932; decide +kernel
      have hl : raw23932step0Labels = raw23932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23932 raw23932Labels permutation346 hz
    _ = mixedMoment B node1128 node1128Labels := by rfl

def raw23933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw23933Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw23933step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23933 raw23933Labels = mixedMoment B node651 node651Labels := by
  calc
    mixedMoment B raw23933 raw23933Labels = mixedMoment B raw23933step0 raw23933step0Labels := by
      have hz : ∀ j, raw23933 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23933step0 = (fun i j => raw23933 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23933step0 raw23933; decide +kernel
      have hl : raw23933step0Labels = raw23933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23933 raw23933Labels permutation346 hz
    _ = mixedMoment B node651 node651Labels := by rfl

def raw23934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw23934Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23934step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw23934step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23934 raw23934Labels = mixedMoment B node1169 node1169Labels := by
  calc
    mixedMoment B raw23934 raw23934Labels = mixedMoment B raw23934step0 raw23934step0Labels := by
      have ha : raw23934step0 = (fun i j => raw23934 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23934step0 raw23934; decide +kernel
      have hl : raw23934step0Labels = raw23934Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23934 raw23934Labels permutation176 permutation2
    _ = mixedMoment B node1169 node1169Labels := by rfl

def raw23935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw23935Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw23935step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw23935step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw23935step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23935 raw23935Labels = mixedMoment B node1270 node1270Labels := by
  calc
    mixedMoment B raw23935 raw23935Labels = mixedMoment B raw23935step0 raw23935step0Labels := by
      have hz : ∀ j, raw23935 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23935step0 = (fun i j => raw23935 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23935step0 raw23935; decide +kernel
      have hl : raw23935step0Labels = raw23935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23935 raw23935Labels permutation346 hz
    mixedMoment B raw23935step0 raw23935step0Labels = mixedMoment B raw23935step1 raw23935step1Labels := by
      have ha : raw23935step1 = (fun i j => raw23935step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23935step1 raw23935step0; decide +kernel
      have hl : raw23935step1Labels = raw23935step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23935step0 raw23935step0Labels permutation38 permutation2
    _ = mixedMoment B node1270 node1270Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
