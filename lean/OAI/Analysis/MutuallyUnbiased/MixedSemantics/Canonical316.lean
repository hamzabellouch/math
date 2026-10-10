import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw40448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw40448Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![2, 1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40448step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40448step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40448step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40448 raw40448Labels = mixedMoment B node3128 node3128Labels := by
  calc
    mixedMoment B raw40448 raw40448Labels = mixedMoment B raw40448step0 raw40448step0Labels := by
      have ha : raw40448step0 = (fun i j => raw40448 (permutation260 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40448step0 raw40448; decide +kernel
      have hl : raw40448step0Labels = raw40448Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40448 raw40448Labels permutation260 permutation6
    mixedMoment B raw40448step0 raw40448step0Labels = mixedMoment B raw40448step1 raw40448step1Labels := by
      have ha : raw40448step1 = -raw40448step0 := by apply Matrix.ext; change ∀ i j, raw40448step1 i j = -(raw40448step0 i j); unfold raw40448step1 raw40448step0; decide +kernel
      have hl : raw40448step1Labels = raw40448step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3128 node3128Labels := by rfl

def raw40449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw40449Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40449step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40449step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40449step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40449step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40449 raw40449Labels = mixedMoment B node3172 node3172Labels := by
  calc
    mixedMoment B raw40449 raw40449Labels = mixedMoment B raw40449step0 raw40449step0Labels := by
      have ha : raw40449step0 = (fun i j => raw40449 (permutation260 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40449step0 raw40449; decide +kernel
      have hl : raw40449step0Labels = raw40449Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40449 raw40449Labels permutation260 permutation6
    mixedMoment B raw40449step0 raw40449step0Labels = mixedMoment B raw40449step1 raw40449step1Labels := by
      have ha : raw40449step1 = -raw40449step0 := by apply Matrix.ext; change ∀ i j, raw40449step1 i j = -(raw40449step0 i j); unfold raw40449step1 raw40449step0; decide +kernel
      have hl : raw40449step1Labels = raw40449step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3172 node3172Labels := by rfl

def raw40450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw40450Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw40450step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40450step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw40450step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40450step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw40450step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40450 raw40450Labels = mixedMoment B node2520 node2520Labels := by
  calc
    mixedMoment B raw40450 raw40450Labels = mixedMoment B raw40450step0 raw40450step0Labels := by
      have hz : ∀ j, raw40450 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40450step0 = (fun i j => raw40450 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40450step0 raw40450; decide +kernel
      have hl : raw40450step0Labels = raw40450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40450 raw40450Labels permutation434 hz
    mixedMoment B raw40450step0 raw40450step0Labels = mixedMoment B raw40450step1 raw40450step1Labels := by
      have hz : ∀ j, raw40450step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40450step1 = (fun i j => raw40450step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40450step1 raw40450step0; decide +kernel
      have hl : raw40450step1Labels = raw40450step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40450step0 raw40450step0Labels permutation80 hz
    mixedMoment B raw40450step1 raw40450step1Labels = mixedMoment B raw40450step2 raw40450step2Labels := by
      have ha : raw40450step2 = (fun i j => raw40450step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40450step2 raw40450step1; decide +kernel
      have hl : raw40450step2Labels = raw40450step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40450step1 raw40450step1Labels permutation23 permutation6
    _ = mixedMoment B node2520 node2520Labels := by rfl

def raw40451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw40451Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw40451step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40451step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw40451step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40451step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw40451step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40451 raw40451Labels = mixedMoment B node1146 node1146Labels := by
  calc
    mixedMoment B raw40451 raw40451Labels = mixedMoment B raw40451step0 raw40451step0Labels := by
      have hz : ∀ j, raw40451 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40451step0 = (fun i j => raw40451 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40451step0 raw40451; decide +kernel
      have hl : raw40451step0Labels = raw40451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40451 raw40451Labels permutation434 hz
    mixedMoment B raw40451step0 raw40451step0Labels = mixedMoment B raw40451step1 raw40451step1Labels := by
      have hz : ∀ j, raw40451step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40451step1 = (fun i j => raw40451step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40451step1 raw40451step0; decide +kernel
      have hl : raw40451step1Labels = raw40451step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40451step0 raw40451step0Labels permutation80 hz
    mixedMoment B raw40451step1 raw40451step1Labels = mixedMoment B raw40451step2 raw40451step2Labels := by
      have ha : raw40451step2 = (fun i j => raw40451step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40451step2 raw40451step1; decide +kernel
      have hl : raw40451step2Labels = raw40451step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40451step1 raw40451step1Labels permutation29 permutation6
    _ = mixedMoment B node1146 node1146Labels := by rfl

def raw40452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw40452Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw40452step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40452step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw40452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40452 raw40452Labels = mixedMoment B node2497 node2497Labels := by
  calc
    mixedMoment B raw40452 raw40452Labels = mixedMoment B raw40452step0 raw40452step0Labels := by
      have hz : ∀ j, raw40452 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40452step0 = (fun i j => raw40452 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40452step0 raw40452; decide +kernel
      have hl : raw40452step0Labels = raw40452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40452 raw40452Labels permutation346 hz
    mixedMoment B raw40452step0 raw40452step0Labels = mixedMoment B raw40452step1 raw40452step1Labels := by
      have ha : raw40452step1 = (fun i j => raw40452step0 (permutation115 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40452step1 raw40452step0; decide +kernel
      have hl : raw40452step1Labels = raw40452step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40452step0 raw40452step0Labels permutation115 permutation6
    _ = mixedMoment B node2497 node2497Labels := by rfl

def raw40453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw40453Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw40453step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw40453step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40453 raw40453Labels = mixedMoment B node1137 node1137Labels := by
  calc
    mixedMoment B raw40453 raw40453Labels = mixedMoment B raw40453step0 raw40453step0Labels := by
      have hz : ∀ j, raw40453 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40453step0 = (fun i j => raw40453 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40453step0 raw40453; decide +kernel
      have hl : raw40453step0Labels = raw40453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40453 raw40453Labels permutation346 hz
    mixedMoment B raw40453step0 raw40453step0Labels = mixedMoment B raw40453step1 raw40453step1Labels := by
      have ha : raw40453step1 = (fun i j => raw40453step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40453step1 raw40453step0; decide +kernel
      have hl : raw40453step1Labels = raw40453step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40453step0 raw40453step0Labels permutation137 permutation6
    _ = mixedMoment B node1137 node1137Labels := by rfl

def raw40454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw40454Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw40454step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40454step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw40454step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40454 raw40454Labels = mixedMoment B node2443 node2443Labels := by
  calc
    mixedMoment B raw40454 raw40454Labels = mixedMoment B raw40454step0 raw40454step0Labels := by
      have hz : ∀ j, raw40454 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40454step0 = (fun i j => raw40454 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40454step0 raw40454; decide +kernel
      have hl : raw40454step0Labels = raw40454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40454 raw40454Labels permutation346 hz
    mixedMoment B raw40454step0 raw40454step0Labels = mixedMoment B raw40454step1 raw40454step1Labels := by
      have ha : raw40454step1 = (fun i j => raw40454step0 (permutation115 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40454step1 raw40454step0; decide +kernel
      have hl : raw40454step1Labels = raw40454step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40454step0 raw40454step0Labels permutation115 permutation6
    _ = mixedMoment B node2443 node2443Labels := by rfl

def raw40455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw40455Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw40455step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40455step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw40455step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40455 raw40455Labels = mixedMoment B node1121 node1121Labels := by
  calc
    mixedMoment B raw40455 raw40455Labels = mixedMoment B raw40455step0 raw40455step0Labels := by
      have hz : ∀ j, raw40455 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40455step0 = (fun i j => raw40455 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40455step0 raw40455; decide +kernel
      have hl : raw40455step0Labels = raw40455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40455 raw40455Labels permutation346 hz
    mixedMoment B raw40455step0 raw40455step0Labels = mixedMoment B raw40455step1 raw40455step1Labels := by
      have ha : raw40455step1 = (fun i j => raw40455step0 (permutation139 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40455step1 raw40455step0; decide +kernel
      have hl : raw40455step1Labels = raw40455step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40455step0 raw40455step0Labels permutation139 permutation6
    _ = mixedMoment B node1121 node1121Labels := by rfl

def raw40456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw40456Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw40456step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40456step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw40456step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40456 raw40456Labels = mixedMoment B node2435 node2435Labels := by
  calc
    mixedMoment B raw40456 raw40456Labels = mixedMoment B raw40456step0 raw40456step0Labels := by
      have hz : ∀ j, raw40456 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40456step0 = (fun i j => raw40456 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40456step0 raw40456; decide +kernel
      have hl : raw40456step0Labels = raw40456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40456 raw40456Labels permutation346 hz
    mixedMoment B raw40456step0 raw40456step0Labels = mixedMoment B raw40456step1 raw40456step1Labels := by
      have ha : raw40456step1 = (fun i j => raw40456step0 (permutation89 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40456step1 raw40456step0; decide +kernel
      have hl : raw40456step1Labels = raw40456step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40456step0 raw40456step0Labels permutation89 permutation6
    _ = mixedMoment B node2435 node2435Labels := by rfl

def raw40457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw40457Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw40457step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40457step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw40457step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40457 raw40457Labels = mixedMoment B node2486 node2486Labels := by
  calc
    mixedMoment B raw40457 raw40457Labels = mixedMoment B raw40457step0 raw40457step0Labels := by
      have hz : ∀ j, raw40457 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40457step0 = (fun i j => raw40457 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40457step0 raw40457; decide +kernel
      have hl : raw40457step0Labels = raw40457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40457 raw40457Labels permutation346 hz
    mixedMoment B raw40457step0 raw40457step0Labels = mixedMoment B raw40457step1 raw40457step1Labels := by
      have ha : raw40457step1 = (fun i j => raw40457step0 (permutation89 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40457step1 raw40457step0; decide +kernel
      have hl : raw40457step1Labels = raw40457step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40457step0 raw40457step0Labels permutation89 permutation6
    _ = mixedMoment B node2486 node2486Labels := by rfl

def raw40458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw40458Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw40458step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40458step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![2, 1, -3], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw40458step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40458step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw40458step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40458 raw40458Labels = mixedMoment B node3132 node3132Labels := by
  calc
    mixedMoment B raw40458 raw40458Labels = mixedMoment B raw40458step0 raw40458step0Labels := by
      have hz : ∀ j, raw40458 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40458step0 = (fun i j => raw40458 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40458step0 raw40458; decide +kernel
      have hl : raw40458step0Labels = raw40458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40458 raw40458Labels permutation346 hz
    mixedMoment B raw40458step0 raw40458step0Labels = mixedMoment B raw40458step1 raw40458step1Labels := by
      have ha : raw40458step1 = (fun i j => raw40458step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40458step1 raw40458step0; decide +kernel
      have hl : raw40458step1Labels = raw40458step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40458step0 raw40458step0Labels permutation50 permutation6
    mixedMoment B raw40458step1 raw40458step1Labels = mixedMoment B raw40458step2 raw40458step2Labels := by
      have ha : raw40458step2 = -raw40458step1 := by apply Matrix.ext; change ∀ i j, raw40458step2 i j = -(raw40458step1 i j); unfold raw40458step2 raw40458step1; decide +kernel
      have hl : raw40458step2Labels = raw40458step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3132 node3132Labels := by rfl

def raw40459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw40459Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw40459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40459 raw40459Labels = mixedMoment B node2440 node2440Labels := by
  calc
    mixedMoment B raw40459 raw40459Labels = mixedMoment B raw40459step0 raw40459step0Labels := by
      have ha : raw40459step0 = (fun i j => raw40459 (permutation540 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40459step0 raw40459; decide +kernel
      have hl : raw40459step0Labels = raw40459Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40459 raw40459Labels permutation540 permutation6
    _ = mixedMoment B node2440 node2440Labels := by rfl

def raw40460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw40460Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40460step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw40460step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40460 raw40460Labels = mixedMoment B node1116 node1116Labels := by
  calc
    mixedMoment B raw40460 raw40460Labels = mixedMoment B raw40460step0 raw40460step0Labels := by
      have ha : raw40460step0 = (fun i j => raw40460 (permutation620 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40460step0 raw40460; decide +kernel
      have hl : raw40460step0Labels = raw40460Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40460 raw40460Labels permutation620 permutation6
    _ = mixedMoment B node1116 node1116Labels := by rfl

def raw40461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw40461Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40461step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw40461step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40461 raw40461Labels = mixedMoment B node2430 node2430Labels := by
  calc
    mixedMoment B raw40461 raw40461Labels = mixedMoment B raw40461step0 raw40461step0Labels := by
      have ha : raw40461step0 = (fun i j => raw40461 (permutation462 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40461step0 raw40461; decide +kernel
      have hl : raw40461step0Labels = raw40461Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40461 raw40461Labels permutation462 permutation6
    _ = mixedMoment B node2430 node2430Labels := by rfl

def raw40462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw40462Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40462step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw40462step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40462 raw40462Labels = mixedMoment B node2471 node2471Labels := by
  calc
    mixedMoment B raw40462 raw40462Labels = mixedMoment B raw40462step0 raw40462step0Labels := by
      have ha : raw40462step0 = (fun i j => raw40462 (permutation463 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40462step0 raw40462; decide +kernel
      have hl : raw40462step0Labels = raw40462Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40462 raw40462Labels permutation463 permutation6
    _ = mixedMoment B node2471 node2471Labels := by rfl

def raw40463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw40463Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![1, 0, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw40463step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40463step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw40463step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40463 raw40463Labels = mixedMoment B node3164 node3164Labels := by
  calc
    mixedMoment B raw40463 raw40463Labels = mixedMoment B raw40463step0 raw40463step0Labels := by
      have ha : raw40463step0 = (fun i j => raw40463 (permutation252 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40463step0 raw40463; decide +kernel
      have hl : raw40463step0Labels = raw40463Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40463 raw40463Labels permutation252 permutation6
    mixedMoment B raw40463step0 raw40463step0Labels = mixedMoment B raw40463step1 raw40463step1Labels := by
      have ha : raw40463step1 = -raw40463step0 := by apply Matrix.ext; change ∀ i j, raw40463step1 i j = -(raw40463step0 i j); unfold raw40463step1 raw40463step0; decide +kernel
      have hl : raw40463step1Labels = raw40463step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3164 node3164Labels := by rfl

def raw40464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw40464Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw40464step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40464 raw40464Labels = mixedMoment B node2423 node2423Labels := by
  calc
    mixedMoment B raw40464 raw40464Labels = mixedMoment B raw40464step0 raw40464step0Labels := by
      have ha : raw40464step0 = (fun i j => raw40464 (permutation463 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40464step0 raw40464; decide +kernel
      have hl : raw40464step0Labels = raw40464Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40464 raw40464Labels permutation463 permutation6
    _ = mixedMoment B node2423 node2423Labels := by rfl

def raw40465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw40465Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw40465step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40465step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw40465step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40465step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![2, 3, -5]]
def raw40465step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40465step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 1, -3], ![3, -3, 0]]
def raw40465step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40465 raw40465Labels = mixedMoment B node621 node621Labels := by
  calc
    mixedMoment B raw40465 raw40465Labels = mixedMoment B raw40465step0 raw40465step0Labels := by
      have hz : ∀ j, raw40465 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40465step0 = (fun i j => raw40465 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40465step0 raw40465; decide +kernel
      have hl : raw40465step0Labels = raw40465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40465 raw40465Labels permutation434 hz
    mixedMoment B raw40465step0 raw40465step0Labels = mixedMoment B raw40465step1 raw40465step1Labels := by
      have hz : ∀ j, raw40465step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40465step1 = (fun i j => raw40465step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40465step1 raw40465step0; decide +kernel
      have hl : raw40465step1Labels = raw40465step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40465step0 raw40465step0Labels permutation80 hz
    mixedMoment B raw40465step1 raw40465step1Labels = mixedMoment B raw40465step2 raw40465step2Labels := by
      have hz : ∀ j, raw40465step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40465step2 = (fun i j => raw40465step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40465step2 raw40465step1; decide +kernel
      have hl : raw40465step2Labels = raw40465step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40465step1 raw40465step1Labels permutation14 hz
    mixedMoment B raw40465step2 raw40465step2Labels = mixedMoment B raw40465step3 raw40465step3Labels := by
      have ha : raw40465step3 = (fun i j => raw40465step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40465step3 raw40465step2; decide +kernel
      have hl : raw40465step3Labels = raw40465step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40465step2 raw40465step2Labels permutation7 permutation6
    _ = mixedMoment B node621 node621Labels := by rfl

def raw40466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw40466Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw40466step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40466step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw40466step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40466step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw40466step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40466 raw40466Labels = mixedMoment B node1061 node1061Labels := by
  calc
    mixedMoment B raw40466 raw40466Labels = mixedMoment B raw40466step0 raw40466step0Labels := by
      have hz : ∀ j, raw40466 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40466step0 = (fun i j => raw40466 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40466step0 raw40466; decide +kernel
      have hl : raw40466step0Labels = raw40466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40466 raw40466Labels permutation346 hz
    mixedMoment B raw40466step0 raw40466step0Labels = mixedMoment B raw40466step1 raw40466step1Labels := by
      have hz : ∀ j, raw40466step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40466step1 = (fun i j => raw40466step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40466step1 raw40466step0; decide +kernel
      have hl : raw40466step1Labels = raw40466step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40466step0 raw40466step0Labels permutation56 hz
    mixedMoment B raw40466step1 raw40466step1Labels = mixedMoment B raw40466step2 raw40466step2Labels := by
      have ha : raw40466step2 = (fun i j => raw40466step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40466step2 raw40466step1; decide +kernel
      have hl : raw40466step2Labels = raw40466step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40466step1 raw40466step1Labels permutation25 permutation6
    _ = mixedMoment B node1061 node1061Labels := by rfl

def raw40467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw40467Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw40467step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40467step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw40467step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40467step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw40467step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40467 raw40467Labels = mixedMoment B node612 node612Labels := by
  calc
    mixedMoment B raw40467 raw40467Labels = mixedMoment B raw40467step0 raw40467step0Labels := by
      have hz : ∀ j, raw40467 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40467step0 = (fun i j => raw40467 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40467step0 raw40467; decide +kernel
      have hl : raw40467step0Labels = raw40467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40467 raw40467Labels permutation346 hz
    mixedMoment B raw40467step0 raw40467step0Labels = mixedMoment B raw40467step1 raw40467step1Labels := by
      have hz : ∀ j, raw40467step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40467step1 = (fun i j => raw40467step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40467step1 raw40467step0; decide +kernel
      have hl : raw40467step1Labels = raw40467step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40467step0 raw40467step0Labels permutation56 hz
    mixedMoment B raw40467step1 raw40467step1Labels = mixedMoment B raw40467step2 raw40467step2Labels := by
      have ha : raw40467step2 = (fun i j => raw40467step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40467step2 raw40467step1; decide +kernel
      have hl : raw40467step2Labels = raw40467step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40467step1 raw40467step1Labels permutation29 permutation6
    _ = mixedMoment B node612 node612Labels := by rfl

def raw40468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![2, -1, -1]]
def raw40468Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![2, -1, -1]]
def raw40468step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40468step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 3, -4], ![2, -1, -1]]
def raw40468step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40468step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw40468step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40468 raw40468Labels = mixedMoment B node954 node954Labels := by
  calc
    mixedMoment B raw40468 raw40468Labels = mixedMoment B raw40468step0 raw40468step0Labels := by
      have hz : ∀ j, raw40468 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40468step0 = (fun i j => raw40468 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40468step0 raw40468; decide +kernel
      have hl : raw40468step0Labels = raw40468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40468 raw40468Labels permutation346 hz
    mixedMoment B raw40468step0 raw40468step0Labels = mixedMoment B raw40468step1 raw40468step1Labels := by
      have hz : ∀ j, raw40468step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40468step1 = (fun i j => raw40468step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40468step1 raw40468step0; decide +kernel
      have hl : raw40468step1Labels = raw40468step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40468step0 raw40468step0Labels permutation56 hz
    mixedMoment B raw40468step1 raw40468step1Labels = mixedMoment B raw40468step2 raw40468step2Labels := by
      have ha : raw40468step2 = (fun i j => raw40468step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40468step2 raw40468step1; decide +kernel
      have hl : raw40468step2Labels = raw40468step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40468step1 raw40468step1Labels permutation25 permutation6
    _ = mixedMoment B node954 node954Labels := by rfl

def raw40469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw40469Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw40469step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40469step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw40469step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40469step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw40469step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40469 raw40469Labels = mixedMoment B node590 node590Labels := by
  calc
    mixedMoment B raw40469 raw40469Labels = mixedMoment B raw40469step0 raw40469step0Labels := by
      have hz : ∀ j, raw40469 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40469step0 = (fun i j => raw40469 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40469step0 raw40469; decide +kernel
      have hl : raw40469step0Labels = raw40469Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40469 raw40469Labels permutation346 hz
    mixedMoment B raw40469step0 raw40469step0Labels = mixedMoment B raw40469step1 raw40469step1Labels := by
      have hz : ∀ j, raw40469step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40469step1 = (fun i j => raw40469step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40469step1 raw40469step0; decide +kernel
      have hl : raw40469step1Labels = raw40469step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40469step0 raw40469step0Labels permutation56 hz
    mixedMoment B raw40469step1 raw40469step1Labels = mixedMoment B raw40469step2 raw40469step2Labels := by
      have ha : raw40469step2 = (fun i j => raw40469step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40469step2 raw40469step1; decide +kernel
      have hl : raw40469step2Labels = raw40469step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40469step1 raw40469step1Labels permutation31 permutation6
    _ = mixedMoment B node590 node590Labels := by rfl

def raw40470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -3, 2]]
def raw40470Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -3, 2]]
def raw40470step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40470step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 3, -4], ![1, 0, -1], ![1, -3, 2]]
def raw40470step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40470step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw40470step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40470 raw40470Labels = mixedMoment B node940 node940Labels := by
  calc
    mixedMoment B raw40470 raw40470Labels = mixedMoment B raw40470step0 raw40470step0Labels := by
      have hz : ∀ j, raw40470 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40470step0 = (fun i j => raw40470 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40470step0 raw40470; decide +kernel
      have hl : raw40470step0Labels = raw40470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40470 raw40470Labels permutation346 hz
    mixedMoment B raw40470step0 raw40470step0Labels = mixedMoment B raw40470step1 raw40470step1Labels := by
      have hz : ∀ j, raw40470step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40470step1 = (fun i j => raw40470step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40470step1 raw40470step0; decide +kernel
      have hl : raw40470step1Labels = raw40470step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40470step0 raw40470step0Labels permutation56 hz
    mixedMoment B raw40470step1 raw40470step1Labels = mixedMoment B raw40470step2 raw40470step2Labels := by
      have ha : raw40470step2 = (fun i j => raw40470step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40470step2 raw40470step1; decide +kernel
      have hl : raw40470step2Labels = raw40470step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40470step1 raw40470step1Labels permutation17 permutation6
    _ = mixedMoment B node940 node940Labels := by rfl

def raw40471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -2, 1]]
def raw40471Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -2, 1]]
def raw40471step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40471step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 3, -4], ![1, -1, 0], ![1, -2, 1]]
def raw40471step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40471step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw40471step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40471 raw40471Labels = mixedMoment B node1047 node1047Labels := by
  calc
    mixedMoment B raw40471 raw40471Labels = mixedMoment B raw40471step0 raw40471step0Labels := by
      have hz : ∀ j, raw40471 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40471step0 = (fun i j => raw40471 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40471step0 raw40471; decide +kernel
      have hl : raw40471step0Labels = raw40471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40471 raw40471Labels permutation346 hz
    mixedMoment B raw40471step0 raw40471step0Labels = mixedMoment B raw40471step1 raw40471step1Labels := by
      have hz : ∀ j, raw40471step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40471step1 = (fun i j => raw40471step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40471step1 raw40471step0; decide +kernel
      have hl : raw40471step1Labels = raw40471step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40471step0 raw40471step0Labels permutation56 hz
    mixedMoment B raw40471step1 raw40471step1Labels = mixedMoment B raw40471step2 raw40471step2Labels := by
      have ha : raw40471step2 = (fun i j => raw40471step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40471step2 raw40471step1; decide +kernel
      have hl : raw40471step2Labels = raw40471step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40471step1 raw40471step1Labels permutation17 permutation6
    _ = mixedMoment B node1047 node1047Labels := by rfl

def raw40472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -3, 2]]
def raw40472Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -3, 2]]
def raw40472step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40472step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![1, 1, -2], ![1, -3, 2]]
def raw40472step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40472step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 1, -3], ![3, -3, 0]]
def raw40472step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40472 raw40472Labels = mixedMoment B node2346 node2346Labels := by
  calc
    mixedMoment B raw40472 raw40472Labels = mixedMoment B raw40472step0 raw40472step0Labels := by
      have hz : ∀ j, raw40472 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40472step0 = (fun i j => raw40472 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40472step0 raw40472; decide +kernel
      have hl : raw40472step0Labels = raw40472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40472 raw40472Labels permutation346 hz
    mixedMoment B raw40472step0 raw40472step0Labels = mixedMoment B raw40472step1 raw40472step1Labels := by
      have hz : ∀ j, raw40472step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40472step1 = (fun i j => raw40472step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40472step1 raw40472step0; decide +kernel
      have hl : raw40472step1Labels = raw40472step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40472step0 raw40472step0Labels permutation56 hz
    mixedMoment B raw40472step1 raw40472step1Labels = mixedMoment B raw40472step2 raw40472step2Labels := by
      have ha : raw40472step2 = (fun i j => raw40472step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40472step2 raw40472step1; decide +kernel
      have hl : raw40472step2Labels = raw40472step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40472step1 raw40472step1Labels permutation17 permutation6
    _ = mixedMoment B node2346 node2346Labels := by rfl

def raw40473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw40473Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw40473step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40473step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw40473step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40473 raw40473Labels = mixedMoment B node949 node949Labels := by
  calc
    mixedMoment B raw40473 raw40473Labels = mixedMoment B raw40473step0 raw40473step0Labels := by
      have hz : ∀ j, raw40473 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40473step0 = (fun i j => raw40473 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40473step0 raw40473; decide +kernel
      have hl : raw40473step0Labels = raw40473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40473 raw40473Labels permutation265 hz
    mixedMoment B raw40473step0 raw40473step0Labels = mixedMoment B raw40473step1 raw40473step1Labels := by
      have ha : raw40473step1 = (fun i j => raw40473step0 (permutation125 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40473step1 raw40473step0; decide +kernel
      have hl : raw40473step1Labels = raw40473step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40473step0 raw40473step0Labels permutation125 permutation6
    _ = mixedMoment B node949 node949Labels := by rfl

def raw40474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw40474Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw40474step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40474step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw40474step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40474 raw40474Labels = mixedMoment B node585 node585Labels := by
  calc
    mixedMoment B raw40474 raw40474Labels = mixedMoment B raw40474step0 raw40474step0Labels := by
      have hz : ∀ j, raw40474 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40474step0 = (fun i j => raw40474 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40474step0 raw40474; decide +kernel
      have hl : raw40474step0Labels = raw40474Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40474 raw40474Labels permutation265 hz
    mixedMoment B raw40474step0 raw40474step0Labels = mixedMoment B raw40474step1 raw40474step1Labels := by
      have ha : raw40474step1 = (fun i j => raw40474step0 (permutation149 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40474step1 raw40474step0; decide +kernel
      have hl : raw40474step1Labels = raw40474step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40474step0 raw40474step0Labels permutation149 permutation6
    _ = mixedMoment B node585 node585Labels := by rfl

def raw40475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw40475Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw40475step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40475step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw40475step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40475 raw40475Labels = mixedMoment B node931 node931Labels := by
  calc
    mixedMoment B raw40475 raw40475Labels = mixedMoment B raw40475step0 raw40475step0Labels := by
      have hz : ∀ j, raw40475 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40475step0 = (fun i j => raw40475 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40475step0 raw40475; decide +kernel
      have hl : raw40475step0Labels = raw40475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40475 raw40475Labels permutation265 hz
    mixedMoment B raw40475step0 raw40475step0Labels = mixedMoment B raw40475step1 raw40475step1Labels := by
      have ha : raw40475step1 = (fun i j => raw40475step0 (permutation95 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40475step1 raw40475step0; decide +kernel
      have hl : raw40475step1Labels = raw40475step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40475step0 raw40475step0Labels permutation95 permutation6
    _ = mixedMoment B node931 node931Labels := by rfl

def raw40476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw40476Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw40476step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40476step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw40476step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40476 raw40476Labels = mixedMoment B node1024 node1024Labels := by
  calc
    mixedMoment B raw40476 raw40476Labels = mixedMoment B raw40476step0 raw40476step0Labels := by
      have hz : ∀ j, raw40476 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40476step0 = (fun i j => raw40476 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40476step0 raw40476; decide +kernel
      have hl : raw40476step0Labels = raw40476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40476 raw40476Labels permutation265 hz
    mixedMoment B raw40476step0 raw40476step0Labels = mixedMoment B raw40476step1 raw40476step1Labels := by
      have ha : raw40476step1 = (fun i j => raw40476step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40476step1 raw40476step0; decide +kernel
      have hl : raw40476step1Labels = raw40476step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40476step0 raw40476step0Labels permutation97 permutation6
    _ = mixedMoment B node1024 node1024Labels := by rfl

def raw40477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw40477Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw40477step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40477step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw40477step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40477 raw40477Labels = mixedMoment B node2340 node2340Labels := by
  calc
    mixedMoment B raw40477 raw40477Labels = mixedMoment B raw40477step0 raw40477step0Labels := by
      have hz : ∀ j, raw40477 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40477step0 = (fun i j => raw40477 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40477step0 raw40477; decide +kernel
      have hl : raw40477step0Labels = raw40477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40477 raw40477Labels permutation265 hz
    mixedMoment B raw40477step0 raw40477step0Labels = mixedMoment B raw40477step1 raw40477step1Labels := by
      have ha : raw40477step1 = (fun i j => raw40477step0 (permutation95 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40477step1 raw40477step0; decide +kernel
      have hl : raw40477step1Labels = raw40477step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40477step0 raw40477step0Labels permutation95 permutation6
    _ = mixedMoment B node2340 node2340Labels := by rfl

def raw40478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw40478Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw40478step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw40478step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40478 raw40478Labels = mixedMoment B node914 node914Labels := by
  calc
    mixedMoment B raw40478 raw40478Labels = mixedMoment B raw40478step0 raw40478step0Labels := by
      have hz : ∀ j, raw40478 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40478step0 = (fun i j => raw40478 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40478step0 raw40478; decide +kernel
      have hl : raw40478step0Labels = raw40478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40478 raw40478Labels permutation265 hz
    mixedMoment B raw40478step0 raw40478step0Labels = mixedMoment B raw40478step1 raw40478step1Labels := by
      have ha : raw40478step1 = (fun i j => raw40478step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40478step1 raw40478step0; decide +kernel
      have hl : raw40478step1Labels = raw40478step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40478step0 raw40478step0Labels permutation97 permutation6
    _ = mixedMoment B node914 node914Labels := by rfl

def raw40479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw40479Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw40479step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40479step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw40479step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40479 raw40479Labels = mixedMoment B node2327 node2327Labels := by
  calc
    mixedMoment B raw40479 raw40479Labels = mixedMoment B raw40479step0 raw40479step0Labels := by
      have hz : ∀ j, raw40479 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40479step0 = (fun i j => raw40479 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40479step0 raw40479; decide +kernel
      have hl : raw40479step0Labels = raw40479Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40479 raw40479Labels permutation265 hz
    mixedMoment B raw40479step0 raw40479step0Labels = mixedMoment B raw40479step1 raw40479step1Labels := by
      have ha : raw40479step1 = (fun i j => raw40479step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40479step1 raw40479step0; decide +kernel
      have hl : raw40479step1Labels = raw40479step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40479step0 raw40479step0Labels permutation97 permutation6
    _ = mixedMoment B node2327 node2327Labels := by rfl

def raw40480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw40480Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw40480step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40480 raw40480Labels = mixedMoment B node909 node909Labels := by
  calc
    mixedMoment B raw40480 raw40480Labels = mixedMoment B raw40480step0 raw40480step0Labels := by
      have ha : raw40480step0 = (fun i j => raw40480 (permutation502 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40480step0 raw40480; decide +kernel
      have hl : raw40480step0Labels = raw40480Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40480 raw40480Labels permutation502 permutation6
    _ = mixedMoment B node909 node909Labels := by rfl

def raw40481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw40481Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40481step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw40481step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40481 raw40481Labels = mixedMoment B node2323 node2323Labels := by
  calc
    mixedMoment B raw40481 raw40481Labels = mixedMoment B raw40481step0 raw40481step0Labels := by
      have ha : raw40481step0 = (fun i j => raw40481 (permutation502 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40481step0 raw40481; decide +kernel
      have hl : raw40481step0Labels = raw40481Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40481 raw40481Labels permutation502 permutation6
    _ = mixedMoment B node2323 node2323Labels := by rfl

def raw40482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw40482Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw40482step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40482step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![3, -2, -1]]
def raw40482step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40482step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]
def raw40482step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40482step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -3, -1], ![-1, 3, -2], ![-3, 0, 3]]
def raw40482step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40482step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![3, 0, -3]]
def raw40482step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40482 raw40482Labels = mixedMoment B node1438 node1438Labels := by
  calc
    mixedMoment B raw40482 raw40482Labels = mixedMoment B raw40482step0 raw40482step0Labels := by
      have hz : ∀ j, raw40482 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40482step0 = (fun i j => raw40482 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40482step0 raw40482; decide +kernel
      have hl : raw40482step0Labels = raw40482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40482 raw40482Labels permutation520 hz
    mixedMoment B raw40482step0 raw40482step0Labels = mixedMoment B raw40482step1 raw40482step1Labels := by
      have hz : ∀ j, raw40482step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40482step1 = (fun i j => raw40482step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40482step1 raw40482step0; decide +kernel
      have hl : raw40482step1Labels = raw40482step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40482step0 raw40482step0Labels permutation104 hz
    mixedMoment B raw40482step1 raw40482step1Labels = mixedMoment B raw40482step2 raw40482step2Labels := by
      have hz : ∀ j, raw40482step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40482step2 = (fun i j => raw40482step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40482step2 raw40482step1; decide +kernel
      have hl : raw40482step2Labels = raw40482step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40482step1 raw40482step1Labels permutation20 hz
    mixedMoment B raw40482step2 raw40482step2Labels = mixedMoment B raw40482step3 raw40482step3Labels := by
      have ha : raw40482step3 = (fun i j => raw40482step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40482step3 raw40482step2; decide +kernel
      have hl : raw40482step3Labels = raw40482step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40482step2 raw40482step2Labels permutation3 permutation6
    mixedMoment B raw40482step3 raw40482step3Labels = mixedMoment B raw40482step4 raw40482step4Labels := by
      have ha : raw40482step4 = -raw40482step3 := by apply Matrix.ext; change ∀ i j, raw40482step4 i j = -(raw40482step3 i j); unfold raw40482step4 raw40482step3; decide +kernel
      have hl : raw40482step4Labels = raw40482step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1438 node1438Labels := by rfl

def raw40483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw40483Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw40483step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40483step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, -1, 1], ![3, -1, -2]]
def raw40483step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40483step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![-2, 3, -1], ![-3, 0, 3]]
def raw40483step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40483step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -3, 1], ![3, 0, -3]]
def raw40483step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40483 raw40483Labels = mixedMoment B node1348 node1348Labels := by
  calc
    mixedMoment B raw40483 raw40483Labels = mixedMoment B raw40483step0 raw40483step0Labels := by
      have hz : ∀ j, raw40483 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40483step0 = (fun i j => raw40483 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40483step0 raw40483; decide +kernel
      have hl : raw40483step0Labels = raw40483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40483 raw40483Labels permutation434 hz
    mixedMoment B raw40483step0 raw40483step0Labels = mixedMoment B raw40483step1 raw40483step1Labels := by
      have hz : ∀ j, raw40483step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40483step1 = (fun i j => raw40483step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40483step1 raw40483step0; decide +kernel
      have hl : raw40483step1Labels = raw40483step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40483step0 raw40483step0Labels permutation80 hz
    mixedMoment B raw40483step1 raw40483step1Labels = mixedMoment B raw40483step2 raw40483step2Labels := by
      have ha : raw40483step2 = (fun i j => raw40483step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40483step2 raw40483step1; decide +kernel
      have hl : raw40483step2Labels = raw40483step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40483step1 raw40483step1Labels permutation11 permutation6
    mixedMoment B raw40483step2 raw40483step2Labels = mixedMoment B raw40483step3 raw40483step3Labels := by
      have ha : raw40483step3 = -raw40483step2 := by apply Matrix.ext; change ∀ i j, raw40483step3 i j = -(raw40483step2 i j); unfold raw40483step3 raw40483step2; decide +kernel
      have hl : raw40483step3Labels = raw40483step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1348 node1348Labels := by rfl

def raw40484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw40484Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw40484step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40484step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw40484step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40484step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-1, 1, 0], ![-3, 0, 3]]
def raw40484step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40484step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw40484step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40484 raw40484Labels = mixedMoment B node1369 node1369Labels := by
  calc
    mixedMoment B raw40484 raw40484Labels = mixedMoment B raw40484step0 raw40484step0Labels := by
      have hz : ∀ j, raw40484 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40484step0 = (fun i j => raw40484 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40484step0 raw40484; decide +kernel
      have hl : raw40484step0Labels = raw40484Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40484 raw40484Labels permutation434 hz
    mixedMoment B raw40484step0 raw40484step0Labels = mixedMoment B raw40484step1 raw40484step1Labels := by
      have hz : ∀ j, raw40484step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40484step1 = (fun i j => raw40484step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40484step1 raw40484step0; decide +kernel
      have hl : raw40484step1Labels = raw40484step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40484step0 raw40484step0Labels permutation80 hz
    mixedMoment B raw40484step1 raw40484step1Labels = mixedMoment B raw40484step2 raw40484step2Labels := by
      have ha : raw40484step2 = (fun i j => raw40484step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40484step2 raw40484step1; decide +kernel
      have hl : raw40484step2Labels = raw40484step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40484step1 raw40484step1Labels permutation13 permutation6
    mixedMoment B raw40484step2 raw40484step2Labels = mixedMoment B raw40484step3 raw40484step3Labels := by
      have ha : raw40484step3 = -raw40484step2 := by apply Matrix.ext; change ∀ i j, raw40484step3 i j = -(raw40484step2 i j); unfold raw40484step3 raw40484step2; decide +kernel
      have hl : raw40484step3Labels = raw40484step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1369 node1369Labels := by rfl

def raw40485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw40485Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw40485step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40485step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw40485step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40485step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![-1, 2, -1], ![-3, 0, 3]]
def raw40485step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40485step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw40485step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40485 raw40485Labels = mixedMoment B node1408 node1408Labels := by
  calc
    mixedMoment B raw40485 raw40485Labels = mixedMoment B raw40485step0 raw40485step0Labels := by
      have hz : ∀ j, raw40485 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40485step0 = (fun i j => raw40485 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40485step0 raw40485; decide +kernel
      have hl : raw40485step0Labels = raw40485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40485 raw40485Labels permutation434 hz
    mixedMoment B raw40485step0 raw40485step0Labels = mixedMoment B raw40485step1 raw40485step1Labels := by
      have hz : ∀ j, raw40485step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40485step1 = (fun i j => raw40485step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40485step1 raw40485step0; decide +kernel
      have hl : raw40485step1Labels = raw40485step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40485step0 raw40485step0Labels permutation80 hz
    mixedMoment B raw40485step1 raw40485step1Labels = mixedMoment B raw40485step2 raw40485step2Labels := by
      have ha : raw40485step2 = (fun i j => raw40485step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40485step2 raw40485step1; decide +kernel
      have hl : raw40485step2Labels = raw40485step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40485step1 raw40485step1Labels permutation11 permutation6
    mixedMoment B raw40485step2 raw40485step2Labels = mixedMoment B raw40485step3 raw40485step3Labels := by
      have ha : raw40485step3 = -raw40485step2 := by apply Matrix.ext; change ∀ i j, raw40485step3 i j = -(raw40485step2 i j); unfold raw40485step3 raw40485step2; decide +kernel
      have hl : raw40485step3Labels = raw40485step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1408 node1408Labels := by rfl

def raw40486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw40486Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw40486step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40486step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw40486step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40486step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-2, 2, 0], ![-3, 0, 3]]
def raw40486step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40486step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -2, 0], ![3, 0, -3]]
def raw40486step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40486 raw40486Labels = mixedMoment B node1323 node1323Labels := by
  calc
    mixedMoment B raw40486 raw40486Labels = mixedMoment B raw40486step0 raw40486step0Labels := by
      have hz : ∀ j, raw40486 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40486step0 = (fun i j => raw40486 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40486step0 raw40486; decide +kernel
      have hl : raw40486step0Labels = raw40486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40486 raw40486Labels permutation434 hz
    mixedMoment B raw40486step0 raw40486step0Labels = mixedMoment B raw40486step1 raw40486step1Labels := by
      have hz : ∀ j, raw40486step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40486step1 = (fun i j => raw40486step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40486step1 raw40486step0; decide +kernel
      have hl : raw40486step1Labels = raw40486step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40486step0 raw40486step0Labels permutation80 hz
    mixedMoment B raw40486step1 raw40486step1Labels = mixedMoment B raw40486step2 raw40486step2Labels := by
      have ha : raw40486step2 = (fun i j => raw40486step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40486step2 raw40486step1; decide +kernel
      have hl : raw40486step2Labels = raw40486step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40486step1 raw40486step1Labels permutation11 permutation6
    mixedMoment B raw40486step2 raw40486step2Labels = mixedMoment B raw40486step3 raw40486step3Labels := by
      have ha : raw40486step3 = -raw40486step2 := by apply Matrix.ext; change ∀ i j, raw40486step3 i j = -(raw40486step2 i j); unfold raw40486step3 raw40486step2; decide +kernel
      have hl : raw40486step3Labels = raw40486step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1323 node1323Labels := by rfl

def raw40487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40487Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40487step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0], ![-3, 0, 3]]
def raw40487step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40487step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw40487step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40487 raw40487Labels = mixedMoment B node1336 node1336Labels := by
  calc
    mixedMoment B raw40487 raw40487Labels = mixedMoment B raw40487step0 raw40487step0Labels := by
      have hz : ∀ j, raw40487 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40487step0 = (fun i j => raw40487 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40487step0 raw40487; decide +kernel
      have hl : raw40487step0Labels = raw40487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40487 raw40487Labels permutation346 hz
    mixedMoment B raw40487step0 raw40487step0Labels = mixedMoment B raw40487step1 raw40487step1Labels := by
      have ha : raw40487step1 = (fun i j => raw40487step0 (permutation43 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40487step1 raw40487step0; decide +kernel
      have hl : raw40487step1Labels = raw40487step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40487step0 raw40487step0Labels permutation43 permutation6
    mixedMoment B raw40487step1 raw40487step1Labels = mixedMoment B raw40487step2 raw40487step2Labels := by
      have ha : raw40487step2 = -raw40487step1 := by apply Matrix.ext; change ∀ i j, raw40487step2 i j = -(raw40487step1 i j); unfold raw40487step2 raw40487step1; decide +kernel
      have hl : raw40487step2Labels = raw40487step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1336 node1336Labels := by rfl

def raw40488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40488Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40488step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![-3, 0, 3]]
def raw40488step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40488step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw40488step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40488 raw40488Labels = mixedMoment B node1332 node1332Labels := by
  calc
    mixedMoment B raw40488 raw40488Labels = mixedMoment B raw40488step0 raw40488step0Labels := by
      have hz : ∀ j, raw40488 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40488step0 = (fun i j => raw40488 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40488step0 raw40488; decide +kernel
      have hl : raw40488step0Labels = raw40488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40488 raw40488Labels permutation346 hz
    mixedMoment B raw40488step0 raw40488step0Labels = mixedMoment B raw40488step1 raw40488step1Labels := by
      have ha : raw40488step1 = (fun i j => raw40488step0 (permutation41 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40488step1 raw40488step0; decide +kernel
      have hl : raw40488step1Labels = raw40488step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40488step0 raw40488step0Labels permutation41 permutation6
    mixedMoment B raw40488step1 raw40488step1Labels = mixedMoment B raw40488step2 raw40488step2Labels := by
      have ha : raw40488step2 = -raw40488step1 := by apply Matrix.ext; change ∀ i j, raw40488step2 i j = -(raw40488step1 i j); unfold raw40488step2 raw40488step1; decide +kernel
      have hl : raw40488step2Labels = raw40488step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1332 node1332Labels := by rfl

def raw40489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw40489Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw40489step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40489step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw40489step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40489step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw40489step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40489 raw40489Labels = mixedMoment B node1315 node1315Labels := by
  calc
    mixedMoment B raw40489 raw40489Labels = mixedMoment B raw40489step0 raw40489step0Labels := by
      have hz : ∀ j, raw40489 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40489step0 = (fun i j => raw40489 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40489step0 raw40489; decide +kernel
      have hl : raw40489step0Labels = raw40489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40489 raw40489Labels permutation346 hz
    mixedMoment B raw40489step0 raw40489step0Labels = mixedMoment B raw40489step1 raw40489step1Labels := by
      have ha : raw40489step1 = (fun i j => raw40489step0 (permutation53 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40489step1 raw40489step0; decide +kernel
      have hl : raw40489step1Labels = raw40489step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40489step0 raw40489step0Labels permutation53 permutation6
    mixedMoment B raw40489step1 raw40489step1Labels = mixedMoment B raw40489step2 raw40489step2Labels := by
      have ha : raw40489step2 = -raw40489step1 := by apply Matrix.ext; change ∀ i j, raw40489step2 i j = -(raw40489step1 i j); unfold raw40489step2 raw40489step1; decide +kernel
      have hl : raw40489step2Labels = raw40489step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1315 node1315Labels := by rfl

def raw40490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40490Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40490step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-3, 0, 3]]
def raw40490step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40490step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw40490step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40490 raw40490Labels = mixedMoment B node1385 node1385Labels := by
  calc
    mixedMoment B raw40490 raw40490Labels = mixedMoment B raw40490step0 raw40490step0Labels := by
      have hz : ∀ j, raw40490 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40490step0 = (fun i j => raw40490 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40490step0 raw40490; decide +kernel
      have hl : raw40490step0Labels = raw40490Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40490 raw40490Labels permutation346 hz
    mixedMoment B raw40490step0 raw40490step0Labels = mixedMoment B raw40490step1 raw40490step1Labels := by
      have ha : raw40490step1 = (fun i j => raw40490step0 (permutation49 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40490step1 raw40490step0; decide +kernel
      have hl : raw40490step1Labels = raw40490step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40490step0 raw40490step0Labels permutation49 permutation6
    mixedMoment B raw40490step1 raw40490step1Labels = mixedMoment B raw40490step2 raw40490step2Labels := by
      have ha : raw40490step2 = -raw40490step1 := by apply Matrix.ext; change ∀ i j, raw40490step2 i j = -(raw40490step1 i j); unfold raw40490step2 raw40490step1; decide +kernel
      have hl : raw40490step2Labels = raw40490step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1385 node1385Labels := by rfl

def raw40491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40491Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw40491step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40491step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw40491step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40491 raw40491Labels = mixedMoment B node1326 node1326Labels := by
  calc
    mixedMoment B raw40491 raw40491Labels = mixedMoment B raw40491step0 raw40491step0Labels := by
      have ha : raw40491step0 = (fun i j => raw40491 (permutation197 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40491step0 raw40491; decide +kernel
      have hl : raw40491step0Labels = raw40491Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40491 raw40491Labels permutation197 permutation6
    mixedMoment B raw40491step0 raw40491step0Labels = mixedMoment B raw40491step1 raw40491step1Labels := by
      have ha : raw40491step1 = -raw40491step0 := by apply Matrix.ext; change ∀ i j, raw40491step1 i j = -(raw40491step0 i j); unfold raw40491step1 raw40491step0; decide +kernel
      have hl : raw40491step1Labels = raw40491step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1326 node1326Labels := by rfl

def raw40492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw40492Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw40492step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40492step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![3, -2, -1]]
def raw40492step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40492step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![-1, 3, -2], ![-1, 0, 1], ![-2, 0, 2]]
def raw40492step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40492step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw40492step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40492 raw40492Labels = mixedMoment B node1436 node1436Labels := by
  calc
    mixedMoment B raw40492 raw40492Labels = mixedMoment B raw40492step0 raw40492step0Labels := by
      have hz : ∀ j, raw40492 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40492step0 = (fun i j => raw40492 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40492step0 raw40492; decide +kernel
      have hl : raw40492step0Labels = raw40492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40492 raw40492Labels permutation520 hz
    mixedMoment B raw40492step0 raw40492step0Labels = mixedMoment B raw40492step1 raw40492step1Labels := by
      have hz : ∀ j, raw40492step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40492step1 = (fun i j => raw40492step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40492step1 raw40492step0; decide +kernel
      have hl : raw40492step1Labels = raw40492step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40492step0 raw40492step0Labels permutation104 hz
    mixedMoment B raw40492step1 raw40492step1Labels = mixedMoment B raw40492step2 raw40492step2Labels := by
      have ha : raw40492step2 = (fun i j => raw40492step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40492step2 raw40492step1; decide +kernel
      have hl : raw40492step2Labels = raw40492step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40492step1 raw40492step1Labels permutation13 permutation6
    mixedMoment B raw40492step2 raw40492step2Labels = mixedMoment B raw40492step3 raw40492step3Labels := by
      have ha : raw40492step3 = -raw40492step2 := by apply Matrix.ext; change ∀ i j, raw40492step3 i j = -(raw40492step2 i j); unfold raw40492step3 raw40492step2; decide +kernel
      have hl : raw40492step3Labels = raw40492step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1436 node1436Labels := by rfl

def raw40493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw40493Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40493step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40493step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40493step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40493step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40493 raw40493Labels = mixedMoment B node1367 node1367Labels := by
  calc
    mixedMoment B raw40493 raw40493Labels = mixedMoment B raw40493step0 raw40493step0Labels := by
      have hz : ∀ j, raw40493 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40493step0 = (fun i j => raw40493 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40493step0 raw40493; decide +kernel
      have hl : raw40493step0Labels = raw40493Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40493 raw40493Labels permutation434 hz
    mixedMoment B raw40493step0 raw40493step0Labels = mixedMoment B raw40493step1 raw40493step1Labels := by
      have ha : raw40493step1 = (fun i j => raw40493step0 (permutation55 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40493step1 raw40493step0; decide +kernel
      have hl : raw40493step1Labels = raw40493step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40493step0 raw40493step0Labels permutation55 permutation6
    mixedMoment B raw40493step1 raw40493step1Labels = mixedMoment B raw40493step2 raw40493step2Labels := by
      have ha : raw40493step2 = -raw40493step1 := by apply Matrix.ext; change ∀ i j, raw40493step2 i j = -(raw40493step1 i j); unfold raw40493step2 raw40493step1; decide +kernel
      have hl : raw40493step2Labels = raw40493step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1367 node1367Labels := by rfl

def raw40494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw40494Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40494step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw40494step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40494step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw40494step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40494 raw40494Labels = mixedMoment B node1406 node1406Labels := by
  calc
    mixedMoment B raw40494 raw40494Labels = mixedMoment B raw40494step0 raw40494step0Labels := by
      have hz : ∀ j, raw40494 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40494step0 = (fun i j => raw40494 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40494step0 raw40494; decide +kernel
      have hl : raw40494step0Labels = raw40494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40494 raw40494Labels permutation434 hz
    mixedMoment B raw40494step0 raw40494step0Labels = mixedMoment B raw40494step1 raw40494step1Labels := by
      have ha : raw40494step1 = (fun i j => raw40494step0 (permutation49 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40494step1 raw40494step0; decide +kernel
      have hl : raw40494step1Labels = raw40494step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40494step0 raw40494step0Labels permutation49 permutation6
    mixedMoment B raw40494step1 raw40494step1Labels = mixedMoment B raw40494step2 raw40494step2Labels := by
      have ha : raw40494step2 = -raw40494step1 := by apply Matrix.ext; change ∀ i j, raw40494step2 i j = -(raw40494step1 i j); unfold raw40494step2 raw40494step1; decide +kernel
      have hl : raw40494step2Labels = raw40494step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1406 node1406Labels := by rfl

def raw40495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw40495Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw40495step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40495step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40495step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40495step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40495 raw40495Labels = mixedMoment B node1321 node1321Labels := by
  calc
    mixedMoment B raw40495 raw40495Labels = mixedMoment B raw40495step0 raw40495step0Labels := by
      have hz : ∀ j, raw40495 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40495step0 = (fun i j => raw40495 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40495step0 raw40495; decide +kernel
      have hl : raw40495step0Labels = raw40495Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40495 raw40495Labels permutation434 hz
    mixedMoment B raw40495step0 raw40495step0Labels = mixedMoment B raw40495step1 raw40495step1Labels := by
      have ha : raw40495step1 = (fun i j => raw40495step0 (permutation47 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40495step1 raw40495step0; decide +kernel
      have hl : raw40495step1Labels = raw40495step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40495step0 raw40495step0Labels permutation47 permutation6
    mixedMoment B raw40495step1 raw40495step1Labels = mixedMoment B raw40495step2 raw40495step2Labels := by
      have ha : raw40495step2 = -raw40495step1 := by apply Matrix.ext; change ∀ i j, raw40495step2 i j = -(raw40495step1 i j); unfold raw40495step2 raw40495step1; decide +kernel
      have hl : raw40495step2Labels = raw40495step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1321 node1321Labels := by rfl

def raw40496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40496Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40496step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40496step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40496step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40496step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40496 raw40496Labels = mixedMoment B node1335 node1335Labels := by
  calc
    mixedMoment B raw40496 raw40496Labels = mixedMoment B raw40496step0 raw40496step0Labels := by
      have ha : raw40496step0 = (fun i j => raw40496 (permutation223 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40496step0 raw40496; decide +kernel
      have hl : raw40496step0Labels = raw40496Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40496 raw40496Labels permutation223 permutation6
    mixedMoment B raw40496step0 raw40496step0Labels = mixedMoment B raw40496step1 raw40496step1Labels := by
      have ha : raw40496step1 = -raw40496step0 := by apply Matrix.ext; change ∀ i j, raw40496step1 i j = -(raw40496step0 i j); unfold raw40496step1 raw40496step0; decide +kernel
      have hl : raw40496step1Labels = raw40496step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1335 node1335Labels := by rfl

def raw40497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40497Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40497step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40497step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40497 raw40497Labels = mixedMoment B node1330 node1330Labels := by
  calc
    mixedMoment B raw40497 raw40497Labels = mixedMoment B raw40497step0 raw40497step0Labels := by
      have ha : raw40497step0 = (fun i j => raw40497 (permutation215 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40497step0 raw40497; decide +kernel
      have hl : raw40497step0Labels = raw40497Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40497 raw40497Labels permutation215 permutation6
    mixedMoment B raw40497step0 raw40497step0Labels = mixedMoment B raw40497step1 raw40497step1Labels := by
      have ha : raw40497step1 = -raw40497step0 := by apply Matrix.ext; change ∀ i j, raw40497step1 i j = -(raw40497step0 i j); unfold raw40497step1 raw40497step0; decide +kernel
      have hl : raw40497step1Labels = raw40497step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1330 node1330Labels := by rfl

def raw40498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw40498Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40498step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40498step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40498 raw40498Labels = mixedMoment B node1314 node1314Labels := by
  calc
    mixedMoment B raw40498 raw40498Labels = mixedMoment B raw40498step0 raw40498step0Labels := by
      have ha : raw40498step0 = (fun i j => raw40498 (permutation259 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40498step0 raw40498; decide +kernel
      have hl : raw40498step0Labels = raw40498Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40498 raw40498Labels permutation259 permutation6
    mixedMoment B raw40498step0 raw40498step0Labels = mixedMoment B raw40498step1 raw40498step1Labels := by
      have ha : raw40498step1 = -raw40498step0 := by apply Matrix.ext; change ∀ i j, raw40498step1 i j = -(raw40498step0 i j); unfold raw40498step1 raw40498step0; decide +kernel
      have hl : raw40498step1Labels = raw40498step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1314 node1314Labels := by rfl

def raw40499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40499Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40499step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40499step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40499step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40499 raw40499Labels = mixedMoment B node1383 node1383Labels := by
  calc
    mixedMoment B raw40499 raw40499Labels = mixedMoment B raw40499step0 raw40499step0Labels := by
      have ha : raw40499step0 = (fun i j => raw40499 (permutation245 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40499step0 raw40499; decide +kernel
      have hl : raw40499step0Labels = raw40499Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40499 raw40499Labels permutation245 permutation6
    mixedMoment B raw40499step0 raw40499step0Labels = mixedMoment B raw40499step1 raw40499step1Labels := by
      have ha : raw40499step1 = -raw40499step0 := by apply Matrix.ext; change ∀ i j, raw40499step1 i j = -(raw40499step0 i j); unfold raw40499step1 raw40499step0; decide +kernel
      have hl : raw40499step1Labels = raw40499step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1383 node1383Labels := by rfl

def raw40500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw40500Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw40500step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40500step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw40500step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40500step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-2, 1, 1], ![-2, 0, 2]]
def raw40500step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40500step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw40500step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40500 raw40500Labels = mixedMoment B node1375 node1375Labels := by
  calc
    mixedMoment B raw40500 raw40500Labels = mixedMoment B raw40500step0 raw40500step0Labels := by
      have hz : ∀ j, raw40500 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40500step0 = (fun i j => raw40500 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40500step0 raw40500; decide +kernel
      have hl : raw40500step0Labels = raw40500Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40500 raw40500Labels permutation434 hz
    mixedMoment B raw40500step0 raw40500step0Labels = mixedMoment B raw40500step1 raw40500step1Labels := by
      have hz : ∀ j, raw40500step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40500step1 = (fun i j => raw40500step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40500step1 raw40500step0; decide +kernel
      have hl : raw40500step1Labels = raw40500step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40500step0 raw40500step0Labels permutation80 hz
    mixedMoment B raw40500step1 raw40500step1Labels = mixedMoment B raw40500step2 raw40500step2Labels := by
      have ha : raw40500step2 = (fun i j => raw40500step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40500step2 raw40500step1; decide +kernel
      have hl : raw40500step2Labels = raw40500step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40500step1 raw40500step1Labels permutation13 permutation6
    mixedMoment B raw40500step2 raw40500step2Labels = mixedMoment B raw40500step3 raw40500step3Labels := by
      have ha : raw40500step3 = -raw40500step2 := by apply Matrix.ext; change ∀ i j, raw40500step3 i j = -(raw40500step2 i j); unfold raw40500step3 raw40500step2; decide +kernel
      have hl : raw40500step3Labels = raw40500step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1375 node1375Labels := by rfl

def raw40501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw40501Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw40501step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40501step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw40501step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40501step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-2, 0, 2], ![-3, 2, 1]]
def raw40501step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40501step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw40501step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40501 raw40501Labels = mixedMoment B node1325 node1325Labels := by
  calc
    mixedMoment B raw40501 raw40501Labels = mixedMoment B raw40501step0 raw40501step0Labels := by
      have hz : ∀ j, raw40501 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40501step0 = (fun i j => raw40501 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40501step0 raw40501; decide +kernel
      have hl : raw40501step0Labels = raw40501Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40501 raw40501Labels permutation434 hz
    mixedMoment B raw40501step0 raw40501step0Labels = mixedMoment B raw40501step1 raw40501step1Labels := by
      have hz : ∀ j, raw40501step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40501step1 = (fun i j => raw40501step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40501step1 raw40501step0; decide +kernel
      have hl : raw40501step1Labels = raw40501step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40501step0 raw40501step0Labels permutation80 hz
    mixedMoment B raw40501step1 raw40501step1Labels = mixedMoment B raw40501step2 raw40501step2Labels := by
      have ha : raw40501step2 = (fun i j => raw40501step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40501step2 raw40501step1; decide +kernel
      have hl : raw40501step2Labels = raw40501step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40501step1 raw40501step1Labels permutation10 permutation6
    mixedMoment B raw40501step2 raw40501step2Labels = mixedMoment B raw40501step3 raw40501step3Labels := by
      have ha : raw40501step3 = -raw40501step2 := by apply Matrix.ext; change ∀ i j, raw40501step3 i j = -(raw40501step2 i j); unfold raw40501step3 raw40501step2; decide +kernel
      have hl : raw40501step3Labels = raw40501step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1325 node1325Labels := by rfl

def raw40502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40502Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40502step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![-1, 2, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw40502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40502step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw40502step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40502 raw40502Labels = mixedMoment B node1338 node1338Labels := by
  calc
    mixedMoment B raw40502 raw40502Labels = mixedMoment B raw40502step0 raw40502step0Labels := by
      have hz : ∀ j, raw40502 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40502step0 = (fun i j => raw40502 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40502step0 raw40502; decide +kernel
      have hl : raw40502step0Labels = raw40502Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40502 raw40502Labels permutation346 hz
    mixedMoment B raw40502step0 raw40502step0Labels = mixedMoment B raw40502step1 raw40502step1Labels := by
      have ha : raw40502step1 = (fun i j => raw40502step0 (permutation43 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40502step1 raw40502step0; decide +kernel
      have hl : raw40502step1Labels = raw40502step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40502step0 raw40502step0Labels permutation43 permutation6
    mixedMoment B raw40502step1 raw40502step1Labels = mixedMoment B raw40502step2 raw40502step2Labels := by
      have ha : raw40502step2 = -raw40502step1 := by apply Matrix.ext; change ∀ i j, raw40502step2 i j = -(raw40502step1 i j); unfold raw40502step2 raw40502step1; decide +kernel
      have hl : raw40502step2Labels = raw40502step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1338 node1338Labels := by rfl

def raw40503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40503Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40503step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw40503step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40503step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw40503step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40503 raw40503Labels = mixedMoment B node1334 node1334Labels := by
  calc
    mixedMoment B raw40503 raw40503Labels = mixedMoment B raw40503step0 raw40503step0Labels := by
      have hz : ∀ j, raw40503 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40503step0 = (fun i j => raw40503 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40503step0 raw40503; decide +kernel
      have hl : raw40503step0Labels = raw40503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40503 raw40503Labels permutation346 hz
    mixedMoment B raw40503step0 raw40503step0Labels = mixedMoment B raw40503step1 raw40503step1Labels := by
      have ha : raw40503step1 = (fun i j => raw40503step0 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40503step1 raw40503step0; decide +kernel
      have hl : raw40503step1Labels = raw40503step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40503step0 raw40503step0Labels permutation40 permutation6
    mixedMoment B raw40503step1 raw40503step1Labels = mixedMoment B raw40503step2 raw40503step2Labels := by
      have ha : raw40503step2 = -raw40503step1 := by apply Matrix.ext; change ∀ i j, raw40503step2 i j = -(raw40503step1 i j); unfold raw40503step2 raw40503step1; decide +kernel
      have hl : raw40503step2Labels = raw40503step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1334 node1334Labels := by rfl

def raw40504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw40504Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw40504step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40504step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw40504step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40504step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw40504step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40504 raw40504Labels = mixedMoment B node1318 node1318Labels := by
  calc
    mixedMoment B raw40504 raw40504Labels = mixedMoment B raw40504step0 raw40504step0Labels := by
      have hz : ∀ j, raw40504 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40504step0 = (fun i j => raw40504 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40504step0 raw40504; decide +kernel
      have hl : raw40504step0Labels = raw40504Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40504 raw40504Labels permutation346 hz
    mixedMoment B raw40504step0 raw40504step0Labels = mixedMoment B raw40504step1 raw40504step1Labels := by
      have ha : raw40504step1 = (fun i j => raw40504step0 (permutation55 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40504step1 raw40504step0; decide +kernel
      have hl : raw40504step1Labels = raw40504step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40504step0 raw40504step0Labels permutation55 permutation6
    mixedMoment B raw40504step1 raw40504step1Labels = mixedMoment B raw40504step2 raw40504step2Labels := by
      have ha : raw40504step2 = -raw40504step1 := by apply Matrix.ext; change ∀ i j, raw40504step2 i j = -(raw40504step1 i j); unfold raw40504step2 raw40504step1; decide +kernel
      have hl : raw40504step2Labels = raw40504step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1318 node1318Labels := by rfl

def raw40505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw40505Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw40505step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40505step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw40505step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40505step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw40505step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40505 raw40505Labels = mixedMoment B node1391 node1391Labels := by
  calc
    mixedMoment B raw40505 raw40505Labels = mixedMoment B raw40505step0 raw40505step0Labels := by
      have hz : ∀ j, raw40505 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40505step0 = (fun i j => raw40505 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40505step0 raw40505; decide +kernel
      have hl : raw40505step0Labels = raw40505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40505 raw40505Labels permutation346 hz
    mixedMoment B raw40505step0 raw40505step0Labels = mixedMoment B raw40505step1 raw40505step1Labels := by
      have ha : raw40505step1 = (fun i j => raw40505step0 (permutation49 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40505step1 raw40505step0; decide +kernel
      have hl : raw40505step1Labels = raw40505step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40505step0 raw40505step0Labels permutation49 permutation6
    mixedMoment B raw40505step1 raw40505step1Labels = mixedMoment B raw40505step2 raw40505step2Labels := by
      have ha : raw40505step2 = -raw40505step1 := by apply Matrix.ext; change ∀ i j, raw40505step2 i j = -(raw40505step1 i j); unfold raw40505step2 raw40505step1; decide +kernel
      have hl : raw40505step2Labels = raw40505step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1391 node1391Labels := by rfl

def raw40506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw40506Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw40506step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40506step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw40506step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40506 raw40506Labels = mixedMoment B node1328 node1328Labels := by
  calc
    mixedMoment B raw40506 raw40506Labels = mixedMoment B raw40506step0 raw40506step0Labels := by
      have ha : raw40506step0 = (fun i j => raw40506 (permutation199 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40506step0 raw40506; decide +kernel
      have hl : raw40506step0Labels = raw40506Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40506 raw40506Labels permutation199 permutation6
    mixedMoment B raw40506step0 raw40506step0Labels = mixedMoment B raw40506step1 raw40506step1Labels := by
      have ha : raw40506step1 = -raw40506step0 := by apply Matrix.ext; change ∀ i j, raw40506step1 i j = -(raw40506step0 i j); unfold raw40506step1 raw40506step0; decide +kernel
      have hl : raw40506step1Labels = raw40506step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1328 node1328Labels := by rfl

def raw40507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw40507Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw40507step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw40507step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40507step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40507step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40507 raw40507Labels = mixedMoment B node1435 node1435Labels := by
  calc
    mixedMoment B raw40507 raw40507Labels = mixedMoment B raw40507step0 raw40507step0Labels := by
      have hz : ∀ j, raw40507 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40507step0 = (fun i j => raw40507 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40507step0 raw40507; decide +kernel
      have hl : raw40507step0Labels = raw40507Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40507 raw40507Labels permutation520 hz
    mixedMoment B raw40507step0 raw40507step0Labels = mixedMoment B raw40507step1 raw40507step1Labels := by
      have ha : raw40507step1 = (fun i j => raw40507step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40507step1 raw40507step0; decide +kernel
      have hl : raw40507step1Labels = raw40507step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40507step0 raw40507step0Labels permutation50 permutation6
    mixedMoment B raw40507step1 raw40507step1Labels = mixedMoment B raw40507step2 raw40507step2Labels := by
      have ha : raw40507step2 = -raw40507step1 := by apply Matrix.ext; change ∀ i j, raw40507step2 i j = -(raw40507step1 i j); unfold raw40507step2 raw40507step1; decide +kernel
      have hl : raw40507step2Labels = raw40507step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1435 node1435Labels := by rfl

def raw40508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40508Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw40508step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40508step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40508 raw40508Labels = mixedMoment B node1366 node1366Labels := by
  calc
    mixedMoment B raw40508 raw40508Labels = mixedMoment B raw40508step0 raw40508step0Labels := by
      have ha : raw40508step0 = (fun i j => raw40508 (permutation260 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40508step0 raw40508; decide +kernel
      have hl : raw40508step0Labels = raw40508Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40508 raw40508Labels permutation260 permutation6
    mixedMoment B raw40508step0 raw40508step0Labels = mixedMoment B raw40508step1 raw40508step1Labels := by
      have ha : raw40508step1 = -raw40508step0 := by apply Matrix.ext; change ∀ i j, raw40508step1 i j = -(raw40508step0 i j); unfold raw40508step1 raw40508step0; decide +kernel
      have hl : raw40508step1Labels = raw40508step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1366 node1366Labels := by rfl

def raw40509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw40509Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40509step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40509step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40509step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40509 raw40509Labels = mixedMoment B node1319 node1319Labels := by
  calc
    mixedMoment B raw40509 raw40509Labels = mixedMoment B raw40509step0 raw40509step0Labels := by
      have ha : raw40509step0 = (fun i j => raw40509 (permutation224 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40509step0 raw40509; decide +kernel
      have hl : raw40509step0Labels = raw40509Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40509 raw40509Labels permutation224 permutation6
    mixedMoment B raw40509step0 raw40509step0Labels = mixedMoment B raw40509step1 raw40509step1Labels := by
      have ha : raw40509step1 = -raw40509step0 := by apply Matrix.ext; change ∀ i j, raw40509step1 i j = -(raw40509step0 i j); unfold raw40509step1 raw40509step0; decide +kernel
      have hl : raw40509step1Labels = raw40509step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1319 node1319Labels := by rfl

def raw40510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw40510Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40510step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40510step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40510step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40510step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40510step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40510 raw40510Labels = mixedMoment B node1370 node1370Labels := by
  calc
    mixedMoment B raw40510 raw40510Labels = mixedMoment B raw40510step0 raw40510step0Labels := by
      have hz : ∀ j, raw40510 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40510step0 = (fun i j => raw40510 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40510step0 raw40510; decide +kernel
      have hl : raw40510step0Labels = raw40510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40510 raw40510Labels permutation434 hz
    mixedMoment B raw40510step0 raw40510step0Labels = mixedMoment B raw40510step1 raw40510step1Labels := by
      have ha : raw40510step1 = (fun i j => raw40510step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40510step1 raw40510step0; decide +kernel
      have hl : raw40510step1Labels = raw40510step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40510step0 raw40510step0Labels permutation50 permutation6
    mixedMoment B raw40510step1 raw40510step1Labels = mixedMoment B raw40510step2 raw40510step2Labels := by
      have ha : raw40510step2 = -raw40510step1 := by apply Matrix.ext; change ∀ i j, raw40510step2 i j = -(raw40510step1 i j); unfold raw40510step2 raw40510step1; decide +kernel
      have hl : raw40510step2Labels = raw40510step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1370 node1370Labels := by rfl

def raw40511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw40511Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw40511step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw40511step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40511step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw40511step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40511 raw40511Labels = mixedMoment B node1320 node1320Labels := by
  calc
    mixedMoment B raw40511 raw40511Labels = mixedMoment B raw40511step0 raw40511step0Labels := by
      have hz : ∀ j, raw40511 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40511step0 = (fun i j => raw40511 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40511step0 raw40511; decide +kernel
      have hl : raw40511step0Labels = raw40511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40511 raw40511Labels permutation434 hz
    mixedMoment B raw40511step0 raw40511step0Labels = mixedMoment B raw40511step1 raw40511step1Labels := by
      have ha : raw40511step1 = (fun i j => raw40511step0 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40511step1 raw40511step0; decide +kernel
      have hl : raw40511step1Labels = raw40511step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40511step0 raw40511step0Labels permutation44 permutation6
    mixedMoment B raw40511step1 raw40511step1Labels = mixedMoment B raw40511step2 raw40511step2Labels := by
      have ha : raw40511step2 = -raw40511step1 := by apply Matrix.ext; change ∀ i j, raw40511step2 i j = -(raw40511step1 i j); unfold raw40511step2 raw40511step1; decide +kernel
      have hl : raw40511step2Labels = raw40511step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1320 node1320Labels := by rfl

def raw40512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw40512Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40512step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40512step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40512step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40512 raw40512Labels = mixedMoment B node1316 node1316Labels := by
  calc
    mixedMoment B raw40512 raw40512Labels = mixedMoment B raw40512step0 raw40512step0Labels := by
      have ha : raw40512step0 = (fun i j => raw40512 (permutation260 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40512step0 raw40512; decide +kernel
      have hl : raw40512step0Labels = raw40512Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40512 raw40512Labels permutation260 permutation6
    mixedMoment B raw40512step0 raw40512step0Labels = mixedMoment B raw40512step1 raw40512step1Labels := by
      have ha : raw40512step1 = -raw40512step0 := by apply Matrix.ext; change ∀ i j, raw40512step1 i j = -(raw40512step0 i j); unfold raw40512step1 raw40512step0; decide +kernel
      have hl : raw40512step1Labels = raw40512step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1316 node1316Labels := by rfl

def raw40513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw40513Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw40513step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40513step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw40513step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40513step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-1, 0, 1], ![-3, 1, 2]]
def raw40513step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40513step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw40513step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40513 raw40513Labels = mixedMoment B node1372 node1372Labels := by
  calc
    mixedMoment B raw40513 raw40513Labels = mixedMoment B raw40513step0 raw40513step0Labels := by
      have hz : ∀ j, raw40513 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40513step0 = (fun i j => raw40513 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40513step0 raw40513; decide +kernel
      have hl : raw40513step0Labels = raw40513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40513 raw40513Labels permutation434 hz
    mixedMoment B raw40513step0 raw40513step0Labels = mixedMoment B raw40513step1 raw40513step1Labels := by
      have hz : ∀ j, raw40513step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40513step1 = (fun i j => raw40513step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40513step1 raw40513step0; decide +kernel
      have hl : raw40513step1Labels = raw40513step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40513step0 raw40513step0Labels permutation80 hz
    mixedMoment B raw40513step1 raw40513step1Labels = mixedMoment B raw40513step2 raw40513step2Labels := by
      have ha : raw40513step2 = (fun i j => raw40513step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40513step2 raw40513step1; decide +kernel
      have hl : raw40513step2Labels = raw40513step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40513step1 raw40513step1Labels permutation12 permutation6
    mixedMoment B raw40513step2 raw40513step2Labels = mixedMoment B raw40513step3 raw40513step3Labels := by
      have ha : raw40513step3 = -raw40513step2 := by apply Matrix.ext; change ∀ i j, raw40513step3 i j = -(raw40513step2 i j); unfold raw40513step3 raw40513step2; decide +kernel
      have hl : raw40513step3Labels = raw40513step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1372 node1372Labels := by rfl

def raw40514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw40514Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw40514step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40514step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw40514step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40514step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![4, -3, -1]]
def raw40514step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40514 raw40514Labels = mixedMoment B node1142 node1142Labels := by
  calc
    mixedMoment B raw40514 raw40514Labels = mixedMoment B raw40514step0 raw40514step0Labels := by
      have hz : ∀ j, raw40514 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40514step0 = (fun i j => raw40514 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40514step0 raw40514; decide +kernel
      have hl : raw40514step0Labels = raw40514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40514 raw40514Labels permutation434 hz
    mixedMoment B raw40514step0 raw40514step0Labels = mixedMoment B raw40514step1 raw40514step1Labels := by
      have hz : ∀ j, raw40514step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40514step1 = (fun i j => raw40514step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40514step1 raw40514step0; decide +kernel
      have hl : raw40514step1Labels = raw40514step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40514step0 raw40514step0Labels permutation80 hz
    mixedMoment B raw40514step1 raw40514step1Labels = mixedMoment B raw40514step2 raw40514step2Labels := by
      have ha : raw40514step2 = (fun i j => raw40514step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40514step2 raw40514step1; decide +kernel
      have hl : raw40514step2Labels = raw40514step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40514step1 raw40514step1Labels permutation29 permutation6
    _ = mixedMoment B node1142 node1142Labels := by rfl

def raw40515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw40515Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw40515step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40515step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw40515step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40515step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw40515step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40515 raw40515Labels = mixedMoment B node1337 node1337Labels := by
  calc
    mixedMoment B raw40515 raw40515Labels = mixedMoment B raw40515step0 raw40515step0Labels := by
      have hz : ∀ j, raw40515 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40515step0 = (fun i j => raw40515 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40515step0 raw40515; decide +kernel
      have hl : raw40515step0Labels = raw40515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40515 raw40515Labels permutation346 hz
    mixedMoment B raw40515step0 raw40515step0Labels = mixedMoment B raw40515step1 raw40515step1Labels := by
      have ha : raw40515step1 = (fun i j => raw40515step0 (permutation42 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40515step1 raw40515step0; decide +kernel
      have hl : raw40515step1Labels = raw40515step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40515step0 raw40515step0Labels permutation42 permutation6
    mixedMoment B raw40515step1 raw40515step1Labels = mixedMoment B raw40515step2 raw40515step2Labels := by
      have ha : raw40515step2 = -raw40515step1 := by apply Matrix.ext; change ∀ i j, raw40515step2 i j = -(raw40515step1 i j); unfold raw40515step2 raw40515step1; decide +kernel
      have hl : raw40515step2Labels = raw40515step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1337 node1337Labels := by rfl

def raw40516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw40516Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw40516step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40516step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw40516step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40516 raw40516Labels = mixedMoment B node1118 node1118Labels := by
  calc
    mixedMoment B raw40516 raw40516Labels = mixedMoment B raw40516step0 raw40516step0Labels := by
      have hz : ∀ j, raw40516 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40516step0 = (fun i j => raw40516 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40516step0 raw40516; decide +kernel
      have hl : raw40516step0Labels = raw40516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40516 raw40516Labels permutation346 hz
    mixedMoment B raw40516step0 raw40516step0Labels = mixedMoment B raw40516step1 raw40516step1Labels := by
      have ha : raw40516step1 = (fun i j => raw40516step0 (permutation139 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40516step1 raw40516step0; decide +kernel
      have hl : raw40516step1Labels = raw40516step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40516step0 raw40516step0Labels permutation139 permutation6
    _ = mixedMoment B node1118 node1118Labels := by rfl

def raw40517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw40517Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw40517step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw40517step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40517step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw40517step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40517 raw40517Labels = mixedMoment B node1317 node1317Labels := by
  calc
    mixedMoment B raw40517 raw40517Labels = mixedMoment B raw40517step0 raw40517step0Labels := by
      have hz : ∀ j, raw40517 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40517step0 = (fun i j => raw40517 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40517step0 raw40517; decide +kernel
      have hl : raw40517step0Labels = raw40517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40517 raw40517Labels permutation346 hz
    mixedMoment B raw40517step0 raw40517step0Labels = mixedMoment B raw40517step1 raw40517step1Labels := by
      have ha : raw40517step1 = (fun i j => raw40517step0 (permutation54 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40517step1 raw40517step0; decide +kernel
      have hl : raw40517step1Labels = raw40517step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40517step0 raw40517step0Labels permutation54 permutation6
    mixedMoment B raw40517step1 raw40517step1Labels = mixedMoment B raw40517step2 raw40517step2Labels := by
      have ha : raw40517step2 = -raw40517step1 := by apply Matrix.ext; change ∀ i j, raw40517step2 i j = -(raw40517step1 i j); unfold raw40517step2 raw40517step1; decide +kernel
      have hl : raw40517step2Labels = raw40517step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1317 node1317Labels := by rfl

def raw40518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw40518Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw40518step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40518step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw40518step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40518step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw40518step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40518 raw40518Labels = mixedMoment B node1388 node1388Labels := by
  calc
    mixedMoment B raw40518 raw40518Labels = mixedMoment B raw40518step0 raw40518step0Labels := by
      have hz : ∀ j, raw40518 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40518step0 = (fun i j => raw40518 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40518step0 raw40518; decide +kernel
      have hl : raw40518step0Labels = raw40518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40518 raw40518Labels permutation346 hz
    mixedMoment B raw40518step0 raw40518step0Labels = mixedMoment B raw40518step1 raw40518step1Labels := by
      have ha : raw40518step1 = (fun i j => raw40518step0 (permutation48 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40518step1 raw40518step0; decide +kernel
      have hl : raw40518step1Labels = raw40518step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40518step0 raw40518step0Labels permutation48 permutation6
    mixedMoment B raw40518step1 raw40518step1Labels = mixedMoment B raw40518step2 raw40518step2Labels := by
      have ha : raw40518step2 = -raw40518step1 := by apply Matrix.ext; change ∀ i j, raw40518step2 i j = -(raw40518step1 i j); unfold raw40518step2 raw40518step1; decide +kernel
      have hl : raw40518step2Labels = raw40518step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1388 node1388Labels := by rfl

def raw40519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw40519Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw40519step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40519step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw40519step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40519step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw40519step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40519 raw40519Labels = mixedMoment B node1322 node1322Labels := by
  calc
    mixedMoment B raw40519 raw40519Labels = mixedMoment B raw40519step0 raw40519step0Labels := by
      have hz : ∀ j, raw40519 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40519step0 = (fun i j => raw40519 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40519step0 raw40519; decide +kernel
      have hl : raw40519step0Labels = raw40519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40519 raw40519Labels permutation346 hz
    mixedMoment B raw40519step0 raw40519step0Labels = mixedMoment B raw40519step1 raw40519step1Labels := by
      have ha : raw40519step1 = (fun i j => raw40519step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40519step1 raw40519step0; decide +kernel
      have hl : raw40519step1Labels = raw40519step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40519step0 raw40519step0Labels permutation50 permutation6
    mixedMoment B raw40519step1 raw40519step1Labels = mixedMoment B raw40519step2 raw40519step2Labels := by
      have ha : raw40519step2 = -raw40519step1 := by apply Matrix.ext; change ∀ i j, raw40519step2 i j = -(raw40519step1 i j); unfold raw40519step2 raw40519step1; decide +kernel
      have hl : raw40519step2Labels = raw40519step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1322 node1322Labels := by rfl

def raw40520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw40520Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw40520step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40520step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw40520step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40520 raw40520Labels = mixedMoment B node1327 node1327Labels := by
  calc
    mixedMoment B raw40520 raw40520Labels = mixedMoment B raw40520step0 raw40520step0Labels := by
      have ha : raw40520step0 = (fun i j => raw40520 (permutation198 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40520step0 raw40520; decide +kernel
      have hl : raw40520step0Labels = raw40520Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40520 raw40520Labels permutation198 permutation6
    mixedMoment B raw40520step0 raw40520step0Labels = mixedMoment B raw40520step1 raw40520step1Labels := by
      have ha : raw40520step1 = -raw40520step0 := by apply Matrix.ext; change ∀ i j, raw40520step1 i j = -(raw40520step0 i j); unfold raw40520step1 raw40520step0; decide +kernel
      have hl : raw40520step1Labels = raw40520step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1327 node1327Labels := by rfl

def raw40521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw40521Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw40521step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40521step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw40521step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40521step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![2, -2, 0]]
def raw40521step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40521step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![4, -3, -1]]
def raw40521step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40521 raw40521Labels = mixedMoment B node1064 node1064Labels := by
  calc
    mixedMoment B raw40521 raw40521Labels = mixedMoment B raw40521step0 raw40521step0Labels := by
      have hz : ∀ j, raw40521 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40521step0 = (fun i j => raw40521 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40521step0 raw40521; decide +kernel
      have hl : raw40521step0Labels = raw40521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40521 raw40521Labels permutation434 hz
    mixedMoment B raw40521step0 raw40521step0Labels = mixedMoment B raw40521step1 raw40521step1Labels := by
      have hz : ∀ j, raw40521step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40521step1 = (fun i j => raw40521step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40521step1 raw40521step0; decide +kernel
      have hl : raw40521step1Labels = raw40521step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40521step0 raw40521step0Labels permutation80 hz
    mixedMoment B raw40521step1 raw40521step1Labels = mixedMoment B raw40521step2 raw40521step2Labels := by
      have hz : ∀ j, raw40521step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40521step2 = (fun i j => raw40521step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40521step2 raw40521step1; decide +kernel
      have hl : raw40521step2Labels = raw40521step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40521step1 raw40521step1Labels permutation14 hz
    mixedMoment B raw40521step2 raw40521step2Labels = mixedMoment B raw40521step3 raw40521step3Labels := by
      have ha : raw40521step3 = (fun i j => raw40521step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40521step3 raw40521step2; decide +kernel
      have hl : raw40521step3Labels = raw40521step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40521step2 raw40521step2Labels permutation5 permutation6
    _ = mixedMoment B node1064 node1064Labels := by rfl

def raw40522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw40522Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw40522step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40522step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw40522step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40522step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -2, 1], ![2, 3, -5]]
def raw40522step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40522step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![4, -3, -1]]
def raw40522step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40522 raw40522Labels = mixedMoment B node617 node617Labels := by
  calc
    mixedMoment B raw40522 raw40522Labels = mixedMoment B raw40522step0 raw40522step0Labels := by
      have hz : ∀ j, raw40522 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40522step0 = (fun i j => raw40522 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40522step0 raw40522; decide +kernel
      have hl : raw40522step0Labels = raw40522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40522 raw40522Labels permutation434 hz
    mixedMoment B raw40522step0 raw40522step0Labels = mixedMoment B raw40522step1 raw40522step1Labels := by
      have hz : ∀ j, raw40522step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40522step1 = (fun i j => raw40522step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40522step1 raw40522step0; decide +kernel
      have hl : raw40522step1Labels = raw40522step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40522step0 raw40522step0Labels permutation80 hz
    mixedMoment B raw40522step1 raw40522step1Labels = mixedMoment B raw40522step2 raw40522step2Labels := by
      have hz : ∀ j, raw40522step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40522step2 = (fun i j => raw40522step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40522step2 raw40522step1; decide +kernel
      have hl : raw40522step2Labels = raw40522step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40522step1 raw40522step1Labels permutation14 hz
    mixedMoment B raw40522step2 raw40522step2Labels = mixedMoment B raw40522step3 raw40522step3Labels := by
      have ha : raw40522step3 = (fun i j => raw40522step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40522step3 raw40522step2; decide +kernel
      have hl : raw40522step3Labels = raw40522step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40522step2 raw40522step2Labels permutation7 permutation6
    _ = mixedMoment B node617 node617Labels := by rfl

def raw40523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw40523Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw40523step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40523step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw40523step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40523step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![4, -3, -1]]
def raw40523step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40523 raw40523Labels = mixedMoment B node951 node951Labels := by
  calc
    mixedMoment B raw40523 raw40523Labels = mixedMoment B raw40523step0 raw40523step0Labels := by
      have hz : ∀ j, raw40523 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40523step0 = (fun i j => raw40523 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40523step0 raw40523; decide +kernel
      have hl : raw40523step0Labels = raw40523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40523 raw40523Labels permutation346 hz
    mixedMoment B raw40523step0 raw40523step0Labels = mixedMoment B raw40523step1 raw40523step1Labels := by
      have hz : ∀ j, raw40523step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40523step1 = (fun i j => raw40523step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40523step1 raw40523step0; decide +kernel
      have hl : raw40523step1Labels = raw40523step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40523step0 raw40523step0Labels permutation56 hz
    mixedMoment B raw40523step1 raw40523step1Labels = mixedMoment B raw40523step2 raw40523step2Labels := by
      have ha : raw40523step2 = (fun i j => raw40523step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40523step2 raw40523step1; decide +kernel
      have hl : raw40523step2Labels = raw40523step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40523step1 raw40523step1Labels permutation25 permutation6
    _ = mixedMoment B node951 node951Labels := by rfl

def raw40524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw40524Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw40524step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40524step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw40524step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40524step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw40524step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40524 raw40524Labels = mixedMoment B node587 node587Labels := by
  calc
    mixedMoment B raw40524 raw40524Labels = mixedMoment B raw40524step0 raw40524step0Labels := by
      have hz : ∀ j, raw40524 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40524step0 = (fun i j => raw40524 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40524step0 raw40524; decide +kernel
      have hl : raw40524step0Labels = raw40524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40524 raw40524Labels permutation346 hz
    mixedMoment B raw40524step0 raw40524step0Labels = mixedMoment B raw40524step1 raw40524step1Labels := by
      have hz : ∀ j, raw40524step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40524step1 = (fun i j => raw40524step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40524step1 raw40524step0; decide +kernel
      have hl : raw40524step1Labels = raw40524step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40524step0 raw40524step0Labels permutation56 hz
    mixedMoment B raw40524step1 raw40524step1Labels = mixedMoment B raw40524step2 raw40524step2Labels := by
      have ha : raw40524step2 = (fun i j => raw40524step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40524step2 raw40524step1; decide +kernel
      have hl : raw40524step2Labels = raw40524step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40524step1 raw40524step1Labels permutation31 permutation6
    _ = mixedMoment B node587 node587Labels := by rfl

def raw40525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw40525Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw40525step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw40525step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40525step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw40525step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40525 raw40525Labels = mixedMoment B node936 node936Labels := by
  calc
    mixedMoment B raw40525 raw40525Labels = mixedMoment B raw40525step0 raw40525step0Labels := by
      have hz : ∀ j, raw40525 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40525step0 = (fun i j => raw40525 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40525step0 raw40525; decide +kernel
      have hl : raw40525step0Labels = raw40525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40525 raw40525Labels permutation346 hz
    mixedMoment B raw40525step0 raw40525step0Labels = mixedMoment B raw40525step1 raw40525step1Labels := by
      have hz : ∀ j, raw40525step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40525step1 = (fun i j => raw40525step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40525step1 raw40525step0; decide +kernel
      have hl : raw40525step1Labels = raw40525step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40525step0 raw40525step0Labels permutation56 hz
    mixedMoment B raw40525step1 raw40525step1Labels = mixedMoment B raw40525step2 raw40525step2Labels := by
      have ha : raw40525step2 = (fun i j => raw40525step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40525step2 raw40525step1; decide +kernel
      have hl : raw40525step2Labels = raw40525step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40525step1 raw40525step1Labels permutation17 permutation6
    _ = mixedMoment B node936 node936Labels := by rfl

def raw40526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw40526Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw40526step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40526step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw40526step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40526step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw40526step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40526 raw40526Labels = mixedMoment B node1027 node1027Labels := by
  calc
    mixedMoment B raw40526 raw40526Labels = mixedMoment B raw40526step0 raw40526step0Labels := by
      have hz : ∀ j, raw40526 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40526step0 = (fun i j => raw40526 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40526step0 raw40526; decide +kernel
      have hl : raw40526step0Labels = raw40526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40526 raw40526Labels permutation346 hz
    mixedMoment B raw40526step0 raw40526step0Labels = mixedMoment B raw40526step1 raw40526step1Labels := by
      have hz : ∀ j, raw40526step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40526step1 = (fun i j => raw40526step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40526step1 raw40526step0; decide +kernel
      have hl : raw40526step1Labels = raw40526step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40526step0 raw40526step0Labels permutation56 hz
    mixedMoment B raw40526step1 raw40526step1Labels = mixedMoment B raw40526step2 raw40526step2Labels := by
      have ha : raw40526step2 = (fun i j => raw40526step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40526step2 raw40526step1; decide +kernel
      have hl : raw40526step2Labels = raw40526step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40526step1 raw40526step1Labels permutation17 permutation6
    _ = mixedMoment B node1027 node1027Labels := by rfl

def raw40527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw40527Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw40527step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40527step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw40527step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40527step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-2, 1, 1], ![-3, 1, 2]]
def raw40527step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40527step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![3, -1, -2]]
def raw40527step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40527 raw40527Labels = mixedMoment B node1324 node1324Labels := by
  calc
    mixedMoment B raw40527 raw40527Labels = mixedMoment B raw40527step0 raw40527step0Labels := by
      have hz : ∀ j, raw40527 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40527step0 = (fun i j => raw40527 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40527step0 raw40527; decide +kernel
      have hl : raw40527step0Labels = raw40527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40527 raw40527Labels permutation346 hz
    mixedMoment B raw40527step0 raw40527step0Labels = mixedMoment B raw40527step1 raw40527step1Labels := by
      have hz : ∀ j, raw40527step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40527step1 = (fun i j => raw40527step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40527step1 raw40527step0; decide +kernel
      have hl : raw40527step1Labels = raw40527step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40527step0 raw40527step0Labels permutation56 hz
    mixedMoment B raw40527step1 raw40527step1Labels = mixedMoment B raw40527step2 raw40527step2Labels := by
      have ha : raw40527step2 = (fun i j => raw40527step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40527step2 raw40527step1; decide +kernel
      have hl : raw40527step2Labels = raw40527step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40527step1 raw40527step1Labels permutation13 permutation6
    mixedMoment B raw40527step2 raw40527step2Labels = mixedMoment B raw40527step3 raw40527step3Labels := by
      have ha : raw40527step3 = -raw40527step2 := by apply Matrix.ext; change ∀ i j, raw40527step3 i j = -(raw40527step2 i j); unfold raw40527step3 raw40527step2; decide +kernel
      have hl : raw40527step3Labels = raw40527step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1324 node1324Labels := by rfl

def raw40528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw40528Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw40528step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw40528step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40528 raw40528Labels = mixedMoment B node911 node911Labels := by
  calc
    mixedMoment B raw40528 raw40528Labels = mixedMoment B raw40528step0 raw40528step0Labels := by
      have hz : ∀ j, raw40528 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40528step0 = (fun i j => raw40528 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40528step0 raw40528; decide +kernel
      have hl : raw40528step0Labels = raw40528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40528 raw40528Labels permutation265 hz
    mixedMoment B raw40528step0 raw40528step0Labels = mixedMoment B raw40528step1 raw40528step1Labels := by
      have ha : raw40528step1 = (fun i j => raw40528step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40528step1 raw40528step0; decide +kernel
      have hl : raw40528step1Labels = raw40528step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40528step0 raw40528step0Labels permutation97 permutation6
    _ = mixedMoment B node911 node911Labels := by rfl

def raw40529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw40529Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw40529step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40529step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 1, 1], ![-3, 1, 2]]
def raw40529step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40529step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw40529step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40529 raw40529Labels = mixedMoment B node1333 node1333Labels := by
  calc
    mixedMoment B raw40529 raw40529Labels = mixedMoment B raw40529step0 raw40529step0Labels := by
      have hz : ∀ j, raw40529 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40529step0 = (fun i j => raw40529 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40529step0 raw40529; decide +kernel
      have hl : raw40529step0Labels = raw40529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40529 raw40529Labels permutation265 hz
    mixedMoment B raw40529step0 raw40529step0Labels = mixedMoment B raw40529step1 raw40529step1Labels := by
      have ha : raw40529step1 = (fun i j => raw40529step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40529step1 raw40529step0; decide +kernel
      have hl : raw40529step1Labels = raw40529step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40529step0 raw40529step0Labels permutation37 permutation6
    mixedMoment B raw40529step1 raw40529step1Labels = mixedMoment B raw40529step2 raw40529step2Labels := by
      have ha : raw40529step2 = -raw40529step1 := by apply Matrix.ext; change ∀ i j, raw40529step2 i j = -(raw40529step1 i j); unfold raw40529step2 raw40529step1; decide +kernel
      have hl : raw40529step2Labels = raw40529step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1333 node1333Labels := by rfl

def raw40530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw40530Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw40530step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![3, -1, -2]]
def raw40530step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40530step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![3, -1, -2]]
def raw40530step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40530step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -3, -2], ![-2, 3, -1], ![-3, 0, 3]]
def raw40530step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40530step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -3, 1], ![3, 0, -3]]
def raw40530step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40530 raw40530Labels = mixedMoment B node654 node654Labels := by
  calc
    mixedMoment B raw40530 raw40530Labels = mixedMoment B raw40530step0 raw40530step0Labels := by
      have hz : ∀ j, raw40530 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40530step0 = (fun i j => raw40530 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40530step0 raw40530; decide +kernel
      have hl : raw40530step0Labels = raw40530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40530 raw40530Labels permutation520 hz
    mixedMoment B raw40530step0 raw40530step0Labels = mixedMoment B raw40530step1 raw40530step1Labels := by
      have hz : ∀ j, raw40530step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40530step1 = (fun i j => raw40530step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40530step1 raw40530step0; decide +kernel
      have hl : raw40530step1Labels = raw40530step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40530step0 raw40530step0Labels permutation104 hz
    mixedMoment B raw40530step1 raw40530step1Labels = mixedMoment B raw40530step2 raw40530step2Labels := by
      have hz : ∀ j, raw40530step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40530step2 = (fun i j => raw40530step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40530step2 raw40530step1; decide +kernel
      have hl : raw40530step2Labels = raw40530step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40530step1 raw40530step1Labels permutation20 hz
    mixedMoment B raw40530step2 raw40530step2Labels = mixedMoment B raw40530step3 raw40530step3Labels := by
      have ha : raw40530step3 = (fun i j => raw40530step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40530step3 raw40530step2; decide +kernel
      have hl : raw40530step3Labels = raw40530step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40530step2 raw40530step2Labels permutation3 permutation6
    mixedMoment B raw40530step3 raw40530step3Labels = mixedMoment B raw40530step4 raw40530step4Labels := by
      have ha : raw40530step4 = -raw40530step3 := by apply Matrix.ext; change ∀ i j, raw40530step4 i j = -(raw40530step3 i j); unfold raw40530step4 raw40530step3; decide +kernel
      have hl : raw40530step4Labels = raw40530step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node654 node654Labels := by rfl

def raw40531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40531Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40531step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40531step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw40531step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40531step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -3, -2], ![-1, 2, -1], ![-1, 1, 0], ![-3, 0, 3]]
def raw40531step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40531step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw40531step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40531 raw40531Labels = mixedMoment B node639 node639Labels := by
  calc
    mixedMoment B raw40531 raw40531Labels = mixedMoment B raw40531step0 raw40531step0Labels := by
      have hz : ∀ j, raw40531 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40531step0 = (fun i j => raw40531 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40531step0 raw40531; decide +kernel
      have hl : raw40531step0Labels = raw40531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40531 raw40531Labels permutation434 hz
    mixedMoment B raw40531step0 raw40531step0Labels = mixedMoment B raw40531step1 raw40531step1Labels := by
      have hz : ∀ j, raw40531step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40531step1 = (fun i j => raw40531step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40531step1 raw40531step0; decide +kernel
      have hl : raw40531step1Labels = raw40531step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40531step0 raw40531step0Labels permutation80 hz
    mixedMoment B raw40531step1 raw40531step1Labels = mixedMoment B raw40531step2 raw40531step2Labels := by
      have ha : raw40531step2 = (fun i j => raw40531step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40531step2 raw40531step1; decide +kernel
      have hl : raw40531step2Labels = raw40531step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40531step1 raw40531step1Labels permutation13 permutation6
    mixedMoment B raw40531step2 raw40531step2Labels = mixedMoment B raw40531step3 raw40531step3Labels := by
      have ha : raw40531step3 = -raw40531step2 := by apply Matrix.ext; change ∀ i j, raw40531step3 i j = -(raw40531step2 i j); unfold raw40531step3 raw40531step2; decide +kernel
      have hl : raw40531step3Labels = raw40531step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node639 node639Labels := by rfl

def raw40532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40532Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40532step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40532step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw40532step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40532step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -3, -2], ![0, 1, -1], ![-2, 2, 0], ![-3, 0, 3]]
def raw40532step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40532step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw40532step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40532 raw40532Labels = mixedMoment B node634 node634Labels := by
  calc
    mixedMoment B raw40532 raw40532Labels = mixedMoment B raw40532step0 raw40532step0Labels := by
      have hz : ∀ j, raw40532 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40532step0 = (fun i j => raw40532 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40532step0 raw40532; decide +kernel
      have hl : raw40532step0Labels = raw40532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40532 raw40532Labels permutation434 hz
    mixedMoment B raw40532step0 raw40532step0Labels = mixedMoment B raw40532step1 raw40532step1Labels := by
      have hz : ∀ j, raw40532step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40532step1 = (fun i j => raw40532step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40532step1 raw40532step0; decide +kernel
      have hl : raw40532step1Labels = raw40532step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40532step0 raw40532step0Labels permutation80 hz
    mixedMoment B raw40532step1 raw40532step1Labels = mixedMoment B raw40532step2 raw40532step2Labels := by
      have ha : raw40532step2 = (fun i j => raw40532step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40532step2 raw40532step1; decide +kernel
      have hl : raw40532step2Labels = raw40532step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40532step1 raw40532step1Labels permutation11 permutation6
    mixedMoment B raw40532step2 raw40532step2Labels = mixedMoment B raw40532step3 raw40532step3Labels := by
      have ha : raw40532step3 = -raw40532step2 := by apply Matrix.ext; change ∀ i j, raw40532step3 i j = -(raw40532step2 i j); unfold raw40532step3 raw40532step2; decide +kernel
      have hl : raw40532step3Labels = raw40532step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node634 node634Labels := by rfl

def raw40533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40533Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40533step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40533step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -3, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw40533step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40533step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw40533step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40533 raw40533Labels = mixedMoment B node624 node624Labels := by
  calc
    mixedMoment B raw40533 raw40533Labels = mixedMoment B raw40533step0 raw40533step0Labels := by
      have hz : ∀ j, raw40533 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40533step0 = (fun i j => raw40533 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40533step0 raw40533; decide +kernel
      have hl : raw40533step0Labels = raw40533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40533 raw40533Labels permutation346 hz
    mixedMoment B raw40533step0 raw40533step0Labels = mixedMoment B raw40533step1 raw40533step1Labels := by
      have ha : raw40533step1 = (fun i j => raw40533step0 (permutation53 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40533step1 raw40533step0; decide +kernel
      have hl : raw40533step1Labels = raw40533step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40533step0 raw40533step0Labels permutation53 permutation6
    mixedMoment B raw40533step1 raw40533step1Labels = mixedMoment B raw40533step2 raw40533step2Labels := by
      have ha : raw40533step2 = -raw40533step1 := by apply Matrix.ext; change ∀ i j, raw40533step2 i j = -(raw40533step1 i j); unfold raw40533step2 raw40533step1; decide +kernel
      have hl : raw40533step2Labels = raw40533step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node624 node624Labels := by rfl

def raw40534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw40534Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw40534step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![3, -1, -2]]
def raw40534step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40534step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -3, -2], ![-1, 0, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw40534step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40534step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw40534step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40534 raw40534Labels = mixedMoment B node653 node653Labels := by
  calc
    mixedMoment B raw40534 raw40534Labels = mixedMoment B raw40534step0 raw40534step0Labels := by
      have hz : ∀ j, raw40534 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40534step0 = (fun i j => raw40534 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40534step0 raw40534; decide +kernel
      have hl : raw40534step0Labels = raw40534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40534 raw40534Labels permutation520 hz
    mixedMoment B raw40534step0 raw40534step0Labels = mixedMoment B raw40534step1 raw40534step1Labels := by
      have hz : ∀ j, raw40534step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40534step1 = (fun i j => raw40534step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40534step1 raw40534step0; decide +kernel
      have hl : raw40534step1Labels = raw40534step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40534step0 raw40534step0Labels permutation104 hz
    mixedMoment B raw40534step1 raw40534step1Labels = mixedMoment B raw40534step2 raw40534step2Labels := by
      have ha : raw40534step2 = (fun i j => raw40534step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40534step2 raw40534step1; decide +kernel
      have hl : raw40534step2Labels = raw40534step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40534step1 raw40534step1Labels permutation11 permutation6
    mixedMoment B raw40534step2 raw40534step2Labels = mixedMoment B raw40534step3 raw40534step3Labels := by
      have ha : raw40534step3 = -raw40534step2 := by apply Matrix.ext; change ∀ i j, raw40534step3 i j = -(raw40534step2 i j); unfold raw40534step3 raw40534step2; decide +kernel
      have hl : raw40534step3Labels = raw40534step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node653 node653Labels := by rfl

def raw40535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40535Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40535step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40535step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -3, -2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40535step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40535step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40535step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40535 raw40535Labels = mixedMoment B node638 node638Labels := by
  calc
    mixedMoment B raw40535 raw40535Labels = mixedMoment B raw40535step0 raw40535step0Labels := by
      have hz : ∀ j, raw40535 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40535step0 = (fun i j => raw40535 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40535step0 raw40535; decide +kernel
      have hl : raw40535step0Labels = raw40535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40535 raw40535Labels permutation434 hz
    mixedMoment B raw40535step0 raw40535step0Labels = mixedMoment B raw40535step1 raw40535step1Labels := by
      have ha : raw40535step1 = (fun i j => raw40535step0 (permutation55 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40535step1 raw40535step0; decide +kernel
      have hl : raw40535step1Labels = raw40535step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40535step0 raw40535step0Labels permutation55 permutation6
    mixedMoment B raw40535step1 raw40535step1Labels = mixedMoment B raw40535step2 raw40535step2Labels := by
      have ha : raw40535step2 = -raw40535step1 := by apply Matrix.ext; change ∀ i j, raw40535step2 i j = -(raw40535step1 i j); unfold raw40535step2 raw40535step1; decide +kernel
      have hl : raw40535step2Labels = raw40535step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node638 node638Labels := by rfl

def raw40536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40536Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40536step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40536step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -3, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40536step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40536step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40536step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40536 raw40536Labels = mixedMoment B node631 node631Labels := by
  calc
    mixedMoment B raw40536 raw40536Labels = mixedMoment B raw40536step0 raw40536step0Labels := by
      have hz : ∀ j, raw40536 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40536step0 = (fun i j => raw40536 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40536step0 raw40536; decide +kernel
      have hl : raw40536step0Labels = raw40536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40536 raw40536Labels permutation434 hz
    mixedMoment B raw40536step0 raw40536step0Labels = mixedMoment B raw40536step1 raw40536step1Labels := by
      have ha : raw40536step1 = (fun i j => raw40536step0 (permutation47 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40536step1 raw40536step0; decide +kernel
      have hl : raw40536step1Labels = raw40536step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40536step0 raw40536step0Labels permutation47 permutation6
    mixedMoment B raw40536step1 raw40536step1Labels = mixedMoment B raw40536step2 raw40536step2Labels := by
      have ha : raw40536step2 = -raw40536step1 := by apply Matrix.ext; change ∀ i j, raw40536step2 i j = -(raw40536step1 i j); unfold raw40536step2 raw40536step1; decide +kernel
      have hl : raw40536step2Labels = raw40536step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node631 node631Labels := by rfl

def raw40537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40537Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![5, -3, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40537step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40537step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40537step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40537 raw40537Labels = mixedMoment B node623 node623Labels := by
  calc
    mixedMoment B raw40537 raw40537Labels = mixedMoment B raw40537step0 raw40537step0Labels := by
      have ha : raw40537step0 = (fun i j => raw40537 (permutation259 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40537step0 raw40537; decide +kernel
      have hl : raw40537step0Labels = raw40537Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40537 raw40537Labels permutation259 permutation6
    mixedMoment B raw40537step0 raw40537step0Labels = mixedMoment B raw40537step1 raw40537step1Labels := by
      have ha : raw40537step1 = -raw40537step0 := by apply Matrix.ext; change ∀ i j, raw40537step1 i j = -(raw40537step0 i j); unfold raw40537step1 raw40537step0; decide +kernel
      have hl : raw40537step1Labels = raw40537step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node623 node623Labels := by rfl

def raw40538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw40538Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw40538step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40538step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw40538step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40538step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -3, -2], ![-1, 2, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw40538step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40538step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw40538step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40538 raw40538Labels = mixedMoment B node642 node642Labels := by
  calc
    mixedMoment B raw40538 raw40538Labels = mixedMoment B raw40538step0 raw40538step0Labels := by
      have hz : ∀ j, raw40538 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40538step0 = (fun i j => raw40538 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40538step0 raw40538; decide +kernel
      have hl : raw40538step0Labels = raw40538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40538 raw40538Labels permutation434 hz
    mixedMoment B raw40538step0 raw40538step0Labels = mixedMoment B raw40538step1 raw40538step1Labels := by
      have hz : ∀ j, raw40538step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40538step1 = (fun i j => raw40538step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40538step1 raw40538step0; decide +kernel
      have hl : raw40538step1Labels = raw40538step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40538step0 raw40538step0Labels permutation80 hz
    mixedMoment B raw40538step1 raw40538step1Labels = mixedMoment B raw40538step2 raw40538step2Labels := by
      have ha : raw40538step2 = (fun i j => raw40538step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40538step2 raw40538step1; decide +kernel
      have hl : raw40538step2Labels = raw40538step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40538step1 raw40538step1Labels permutation13 permutation6
    mixedMoment B raw40538step2 raw40538step2Labels = mixedMoment B raw40538step3 raw40538step3Labels := by
      have ha : raw40538step3 = -raw40538step2 := by apply Matrix.ext; change ∀ i j, raw40538step3 i j = -(raw40538step2 i j); unfold raw40538step3 raw40538step2; decide +kernel
      have hl : raw40538step3Labels = raw40538step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node642 node642Labels := by rfl

def raw40539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw40539Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw40539step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40539step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw40539step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40539step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -3, -2], ![0, 1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw40539step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40539step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw40539step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40539 raw40539Labels = mixedMoment B node636 node636Labels := by
  calc
    mixedMoment B raw40539 raw40539Labels = mixedMoment B raw40539step0 raw40539step0Labels := by
      have hz : ∀ j, raw40539 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40539step0 = (fun i j => raw40539 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40539step0 raw40539; decide +kernel
      have hl : raw40539step0Labels = raw40539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40539 raw40539Labels permutation434 hz
    mixedMoment B raw40539step0 raw40539step0Labels = mixedMoment B raw40539step1 raw40539step1Labels := by
      have hz : ∀ j, raw40539step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40539step1 = (fun i j => raw40539step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40539step1 raw40539step0; decide +kernel
      have hl : raw40539step1Labels = raw40539step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40539step0 raw40539step0Labels permutation80 hz
    mixedMoment B raw40539step1 raw40539step1Labels = mixedMoment B raw40539step2 raw40539step2Labels := by
      have ha : raw40539step2 = (fun i j => raw40539step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40539step2 raw40539step1; decide +kernel
      have hl : raw40539step2Labels = raw40539step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40539step1 raw40539step1Labels permutation10 permutation6
    mixedMoment B raw40539step2 raw40539step2Labels = mixedMoment B raw40539step3 raw40539step3Labels := by
      have ha : raw40539step3 = -raw40539step2 := by apply Matrix.ext; change ∀ i j, raw40539step3 i j = -(raw40539step2 i j); unfold raw40539step3 raw40539step2; decide +kernel
      have hl : raw40539step3Labels = raw40539step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node636 node636Labels := by rfl

def raw40540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw40540Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw40540step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40540step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -3, -2], ![0, 1, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw40540step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40540step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw40540step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40540 raw40540Labels = mixedMoment B node627 node627Labels := by
  calc
    mixedMoment B raw40540 raw40540Labels = mixedMoment B raw40540step0 raw40540step0Labels := by
      have hz : ∀ j, raw40540 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40540step0 = (fun i j => raw40540 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40540step0 raw40540; decide +kernel
      have hl : raw40540step0Labels = raw40540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40540 raw40540Labels permutation346 hz
    mixedMoment B raw40540step0 raw40540step0Labels = mixedMoment B raw40540step1 raw40540step1Labels := by
      have ha : raw40540step1 = (fun i j => raw40540step0 (permutation55 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40540step1 raw40540step0; decide +kernel
      have hl : raw40540step1Labels = raw40540step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40540step0 raw40540step0Labels permutation55 permutation6
    mixedMoment B raw40540step1 raw40540step1Labels = mixedMoment B raw40540step2 raw40540step2Labels := by
      have ha : raw40540step2 = -raw40540step1 := by apply Matrix.ext; change ∀ i j, raw40540step2 i j = -(raw40540step1 i j); unfold raw40540step2 raw40540step1; decide +kernel
      have hl : raw40540step2Labels = raw40540step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node627 node627Labels := by rfl

def raw40541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40541Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40541step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![5, -3, -2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw40541step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40541step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40541step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40541 raw40541Labels = mixedMoment B node637 node637Labels := by
  calc
    mixedMoment B raw40541 raw40541Labels = mixedMoment B raw40541step0 raw40541step0Labels := by
      have ha : raw40541step0 = (fun i j => raw40541 (permutation260 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40541step0 raw40541; decide +kernel
      have hl : raw40541step0Labels = raw40541Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40541 raw40541Labels permutation260 permutation6
    mixedMoment B raw40541step0 raw40541step0Labels = mixedMoment B raw40541step1 raw40541step1Labels := by
      have ha : raw40541step1 = -raw40541step0 := by apply Matrix.ext; change ∀ i j, raw40541step1 i j = -(raw40541step0 i j); unfold raw40541step1 raw40541step0; decide +kernel
      have hl : raw40541step1Labels = raw40541step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node637 node637Labels := by rfl

def raw40542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40542Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40542step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![5, -3, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40542step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40542step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40542step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40542 raw40542Labels = mixedMoment B node629 node629Labels := by
  calc
    mixedMoment B raw40542 raw40542Labels = mixedMoment B raw40542step0 raw40542step0Labels := by
      have ha : raw40542step0 = (fun i j => raw40542 (permutation224 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40542step0 raw40542; decide +kernel
      have hl : raw40542step0Labels = raw40542Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40542 raw40542Labels permutation224 permutation6
    mixedMoment B raw40542step0 raw40542step0Labels = mixedMoment B raw40542step1 raw40542step1Labels := by
      have ha : raw40542step1 = -raw40542step0 := by apply Matrix.ext; change ∀ i j, raw40542step1 i j = -(raw40542step0 i j); unfold raw40542step1 raw40542step0; decide +kernel
      have hl : raw40542step1Labels = raw40542step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node629 node629Labels := by rfl

def raw40543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw40543Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw40543step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -3, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40543step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40543step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40543step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40543 raw40543Labels = mixedMoment B node640 node640Labels := by
  calc
    mixedMoment B raw40543 raw40543Labels = mixedMoment B raw40543step0 raw40543step0Labels := by
      have hz : ∀ j, raw40543 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40543step0 = (fun i j => raw40543 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40543step0 raw40543; decide +kernel
      have hl : raw40543step0Labels = raw40543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40543 raw40543Labels permutation434 hz
    mixedMoment B raw40543step0 raw40543step0Labels = mixedMoment B raw40543step1 raw40543step1Labels := by
      have ha : raw40543step1 = (fun i j => raw40543step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40543step1 raw40543step0; decide +kernel
      have hl : raw40543step1Labels = raw40543step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40543step0 raw40543step0Labels permutation50 permutation6
    mixedMoment B raw40543step1 raw40543step1Labels = mixedMoment B raw40543step2 raw40543step2Labels := by
      have ha : raw40543step2 = -raw40543step1 := by apply Matrix.ext; change ∀ i j, raw40543step2 i j = -(raw40543step1 i j); unfold raw40543step2 raw40543step1; decide +kernel
      have hl : raw40543step2Labels = raw40543step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node640 node640Labels := by rfl

def raw40544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw40544Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw40544step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40544step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -3, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw40544step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40544step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw40544step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40544 raw40544Labels = mixedMoment B node630 node630Labels := by
  calc
    mixedMoment B raw40544 raw40544Labels = mixedMoment B raw40544step0 raw40544step0Labels := by
      have hz : ∀ j, raw40544 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40544step0 = (fun i j => raw40544 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40544step0 raw40544; decide +kernel
      have hl : raw40544step0Labels = raw40544Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40544 raw40544Labels permutation434 hz
    mixedMoment B raw40544step0 raw40544step0Labels = mixedMoment B raw40544step1 raw40544step1Labels := by
      have ha : raw40544step1 = (fun i j => raw40544step0 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40544step1 raw40544step0; decide +kernel
      have hl : raw40544step1Labels = raw40544step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40544step0 raw40544step0Labels permutation44 permutation6
    mixedMoment B raw40544step1 raw40544step1Labels = mixedMoment B raw40544step2 raw40544step2Labels := by
      have ha : raw40544step2 = -raw40544step1 := by apply Matrix.ext; change ∀ i j, raw40544step2 i j = -(raw40544step1 i j); unfold raw40544step2 raw40544step1; decide +kernel
      have hl : raw40544step2Labels = raw40544step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node630 node630Labels := by rfl

def raw40545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -1, -1]]
def raw40545Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -1, -1]]
def raw40545step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40545step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw40545step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40545step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -3, -2], ![-1, 2, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw40545step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40545step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw40545step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40545 raw40545Labels = mixedMoment B node641 node641Labels := by
  calc
    mixedMoment B raw40545 raw40545Labels = mixedMoment B raw40545step0 raw40545step0Labels := by
      have hz : ∀ j, raw40545 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40545step0 = (fun i j => raw40545 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40545step0 raw40545; decide +kernel
      have hl : raw40545step0Labels = raw40545Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40545 raw40545Labels permutation434 hz
    mixedMoment B raw40545step0 raw40545step0Labels = mixedMoment B raw40545step1 raw40545step1Labels := by
      have hz : ∀ j, raw40545step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40545step1 = (fun i j => raw40545step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40545step1 raw40545step0; decide +kernel
      have hl : raw40545step1Labels = raw40545step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40545step0 raw40545step0Labels permutation80 hz
    mixedMoment B raw40545step1 raw40545step1Labels = mixedMoment B raw40545step2 raw40545step2Labels := by
      have ha : raw40545step2 = (fun i j => raw40545step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40545step2 raw40545step1; decide +kernel
      have hl : raw40545step2Labels = raw40545step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40545step1 raw40545step1Labels permutation12 permutation6
    mixedMoment B raw40545step2 raw40545step2Labels = mixedMoment B raw40545step3 raw40545step3Labels := by
      have ha : raw40545step3 = -raw40545step2 := by apply Matrix.ext; change ∀ i j, raw40545step3 i j = -(raw40545step2 i j); unfold raw40545step3 raw40545step2; decide +kernel
      have hl : raw40545step3Labels = raw40545step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node641 node641Labels := by rfl

def raw40546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw40546Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw40546step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw40546step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40546step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -3, -2], ![0, 1, -1], ![-1, 0, 1], ![-4, 2, 2]]
def raw40546step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40546step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw40546step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40546 raw40546Labels = mixedMoment B node633 node633Labels := by
  calc
    mixedMoment B raw40546 raw40546Labels = mixedMoment B raw40546step0 raw40546step0Labels := by
      have hz : ∀ j, raw40546 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40546step0 = (fun i j => raw40546 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40546step0 raw40546; decide +kernel
      have hl : raw40546step0Labels = raw40546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40546 raw40546Labels permutation434 hz
    mixedMoment B raw40546step0 raw40546step0Labels = mixedMoment B raw40546step1 raw40546step1Labels := by
      have hz : ∀ j, raw40546step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40546step1 = (fun i j => raw40546step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40546step1 raw40546step0; decide +kernel
      have hl : raw40546step1Labels = raw40546step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40546step0 raw40546step0Labels permutation80 hz
    mixedMoment B raw40546step1 raw40546step1Labels = mixedMoment B raw40546step2 raw40546step2Labels := by
      have ha : raw40546step2 = (fun i j => raw40546step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40546step2 raw40546step1; decide +kernel
      have hl : raw40546step2Labels = raw40546step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40546step1 raw40546step1Labels permutation10 permutation6
    mixedMoment B raw40546step2 raw40546step2Labels = mixedMoment B raw40546step3 raw40546step3Labels := by
      have ha : raw40546step3 = -raw40546step2 := by apply Matrix.ext; change ∀ i j, raw40546step3 i j = -(raw40546step2 i j); unfold raw40546step3 raw40546step2; decide +kernel
      have hl : raw40546step3Labels = raw40546step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node633 node633Labels := by rfl

def raw40547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw40547Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw40547step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40547step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -3, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw40547step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40547step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw40547step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40547 raw40547Labels = mixedMoment B node626 node626Labels := by
  calc
    mixedMoment B raw40547 raw40547Labels = mixedMoment B raw40547step0 raw40547step0Labels := by
      have hz : ∀ j, raw40547 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40547step0 = (fun i j => raw40547 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40547step0 raw40547; decide +kernel
      have hl : raw40547step0Labels = raw40547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40547 raw40547Labels permutation346 hz
    mixedMoment B raw40547step0 raw40547step0Labels = mixedMoment B raw40547step1 raw40547step1Labels := by
      have ha : raw40547step1 = (fun i j => raw40547step0 (permutation54 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40547step1 raw40547step0; decide +kernel
      have hl : raw40547step1Labels = raw40547step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40547step0 raw40547step0Labels permutation54 permutation6
    mixedMoment B raw40547step1 raw40547step1Labels = mixedMoment B raw40547step2 raw40547step2Labels := by
      have ha : raw40547step2 = -raw40547step1 := by apply Matrix.ext; change ∀ i j, raw40547step2 i j = -(raw40547step1 i j); unfold raw40547step2 raw40547step1; decide +kernel
      have hl : raw40547step2Labels = raw40547step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node626 node626Labels := by rfl

def raw40548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -1, -1]]
def raw40548Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -1, -1]]
def raw40548step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40548step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![1, 3, -4], ![2, -1, -1]]
def raw40548step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40548step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 3, -4], ![2, -1, -1]]
def raw40548step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40548step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -3, -2], ![-1, 2, -1], ![-4, 1, 3]]
def raw40548step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40548step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![4, -1, -3]]
def raw40548step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40548 raw40548Labels = mixedMoment B node643 node643Labels := by
  calc
    mixedMoment B raw40548 raw40548Labels = mixedMoment B raw40548step0 raw40548step0Labels := by
      have hz : ∀ j, raw40548 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40548step0 = (fun i j => raw40548 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40548step0 raw40548; decide +kernel
      have hl : raw40548step0Labels = raw40548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40548 raw40548Labels permutation434 hz
    mixedMoment B raw40548step0 raw40548step0Labels = mixedMoment B raw40548step1 raw40548step1Labels := by
      have hz : ∀ j, raw40548step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40548step1 = (fun i j => raw40548step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40548step1 raw40548step0; decide +kernel
      have hl : raw40548step1Labels = raw40548step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40548step0 raw40548step0Labels permutation80 hz
    mixedMoment B raw40548step1 raw40548step1Labels = mixedMoment B raw40548step2 raw40548step2Labels := by
      have hz : ∀ j, raw40548step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40548step2 = (fun i j => raw40548step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40548step2 raw40548step1; decide +kernel
      have hl : raw40548step2Labels = raw40548step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40548step1 raw40548step1Labels permutation14 hz
    mixedMoment B raw40548step2 raw40548step2Labels = mixedMoment B raw40548step3 raw40548step3Labels := by
      have ha : raw40548step3 = (fun i j => raw40548step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40548step3 raw40548step2; decide +kernel
      have hl : raw40548step3Labels = raw40548step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40548step2 raw40548step2Labels permutation3 permutation6
    mixedMoment B raw40548step3 raw40548step3Labels = mixedMoment B raw40548step4 raw40548step4Labels := by
      have ha : raw40548step4 = -raw40548step3 := by apply Matrix.ext; change ∀ i j, raw40548step4 i j = -(raw40548step3 i j); unfold raw40548step4 raw40548step3; decide +kernel
      have hl : raw40548step4Labels = raw40548step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node643 node643Labels := by rfl

def raw40549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw40549Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw40549step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40549step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw40549step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40549step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![2, 3, -5]]
def raw40549step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40549step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![5, -3, -2]]
def raw40549step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40549 raw40549Labels = mixedMoment B node591 node591Labels := by
  calc
    mixedMoment B raw40549 raw40549Labels = mixedMoment B raw40549step0 raw40549step0Labels := by
      have hz : ∀ j, raw40549 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40549step0 = (fun i j => raw40549 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40549step0 raw40549; decide +kernel
      have hl : raw40549step0Labels = raw40549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40549 raw40549Labels permutation434 hz
    mixedMoment B raw40549step0 raw40549step0Labels = mixedMoment B raw40549step1 raw40549step1Labels := by
      have hz : ∀ j, raw40549step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40549step1 = (fun i j => raw40549step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40549step1 raw40549step0; decide +kernel
      have hl : raw40549step1Labels = raw40549step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40549step0 raw40549step0Labels permutation80 hz
    mixedMoment B raw40549step1 raw40549step1Labels = mixedMoment B raw40549step2 raw40549step2Labels := by
      have hz : ∀ j, raw40549step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40549step2 = (fun i j => raw40549step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40549step2 raw40549step1; decide +kernel
      have hl : raw40549step2Labels = raw40549step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40549step1 raw40549step1Labels permutation14 hz
    mixedMoment B raw40549step2 raw40549step2Labels = mixedMoment B raw40549step3 raw40549step3Labels := by
      have ha : raw40549step3 = (fun i j => raw40549step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40549step3 raw40549step2; decide +kernel
      have hl : raw40549step3Labels = raw40549step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40549step2 raw40549step2Labels permutation7 permutation6
    _ = mixedMoment B node591 node591Labels := by rfl

def raw40550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw40550Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw40550step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40550step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw40550step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40550step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -3, -2], ![0, 1, -1], ![-1, 1, 0], ![-4, 1, 3]]
def raw40550step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40550step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw40550step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40550 raw40550Labels = mixedMoment B node628 node628Labels := by
  calc
    mixedMoment B raw40550 raw40550Labels = mixedMoment B raw40550step0 raw40550step0Labels := by
      have hz : ∀ j, raw40550 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40550step0 = (fun i j => raw40550 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40550step0 raw40550; decide +kernel
      have hl : raw40550step0Labels = raw40550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40550 raw40550Labels permutation346 hz
    mixedMoment B raw40550step0 raw40550step0Labels = mixedMoment B raw40550step1 raw40550step1Labels := by
      have hz : ∀ j, raw40550step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40550step1 = (fun i j => raw40550step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40550step1 raw40550step0; decide +kernel
      have hl : raw40550step1Labels = raw40550step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40550step0 raw40550step0Labels permutation56 hz
    mixedMoment B raw40550step1 raw40550step1Labels = mixedMoment B raw40550step2 raw40550step2Labels := by
      have ha : raw40550step2 = (fun i j => raw40550step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40550step2 raw40550step1; decide +kernel
      have hl : raw40550step2Labels = raw40550step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40550step1 raw40550step1Labels permutation13 permutation6
    mixedMoment B raw40550step2 raw40550step2Labels = mixedMoment B raw40550step3 raw40550step3Labels := by
      have ha : raw40550step3 = -raw40550step2 := by apply Matrix.ext; change ∀ i j, raw40550step3 i j = -(raw40550step2 i j); unfold raw40550step3 raw40550step2; decide +kernel
      have hl : raw40550step3Labels = raw40550step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node628 node628Labels := by rfl

def raw40551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw40551Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw40551step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40551step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw40551step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40551step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -3, -2], ![0, 1, -1], ![-2, 1, 1], ![-3, 1, 2]]
def raw40551step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40551step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw40551step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40551 raw40551Labels = mixedMoment B node635 node635Labels := by
  calc
    mixedMoment B raw40551 raw40551Labels = mixedMoment B raw40551step0 raw40551step0Labels := by
      have hz : ∀ j, raw40551 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40551step0 = (fun i j => raw40551 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40551step0 raw40551; decide +kernel
      have hl : raw40551step0Labels = raw40551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40551 raw40551Labels permutation346 hz
    mixedMoment B raw40551step0 raw40551step0Labels = mixedMoment B raw40551step1 raw40551step1Labels := by
      have hz : ∀ j, raw40551step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40551step1 = (fun i j => raw40551step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40551step1 raw40551step0; decide +kernel
      have hl : raw40551step1Labels = raw40551step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40551step0 raw40551step0Labels permutation56 hz
    mixedMoment B raw40551step1 raw40551step1Labels = mixedMoment B raw40551step2 raw40551step2Labels := by
      have ha : raw40551step2 = (fun i j => raw40551step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40551step2 raw40551step1; decide +kernel
      have hl : raw40551step2Labels = raw40551step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40551step1 raw40551step1Labels permutation13 permutation6
    mixedMoment B raw40551step2 raw40551step2Labels = mixedMoment B raw40551step3 raw40551step3Labels := by
      have ha : raw40551step3 = -raw40551step2 := by apply Matrix.ext; change ∀ i j, raw40551step3 i j = -(raw40551step2 i j); unfold raw40551step3 raw40551step2; decide +kernel
      have hl : raw40551step3Labels = raw40551step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node635 node635Labels := by rfl

def raw40552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40552Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40552step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40552step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![3, -2, -1]]
def raw40552step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40552step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-2, -1, 3]]
def raw40552step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40552step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40552step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40552 raw40552Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw40552 raw40552Labels = mixedMoment B raw40552step0 raw40552step0Labels := by
      have hz : ∀ j, raw40552 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40552step0 = (fun i j => raw40552 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40552step0 raw40552; decide +kernel
      have hl : raw40552step0Labels = raw40552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40552 raw40552Labels permutation434 hz
    mixedMoment B raw40552step0 raw40552step0Labels = mixedMoment B raw40552step1 raw40552step1Labels := by
      have hz : ∀ j, raw40552step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40552step1 = (fun i j => raw40552step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40552step1 raw40552step0; decide +kernel
      have hl : raw40552step1Labels = raw40552step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40552step0 raw40552step0Labels permutation80 hz
    mixedMoment B raw40552step1 raw40552step1Labels = mixedMoment B raw40552step2 raw40552step2Labels := by
      have ha : raw40552step2 = (fun i j => raw40552step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40552step2 raw40552step1; decide +kernel
      have hl : raw40552step2Labels = raw40552step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40552step1 raw40552step1Labels permutation31 permutation3
    mixedMoment B raw40552step2 raw40552step2Labels = mixedMoment B raw40552step3 raw40552step3Labels := by
      have ha : raw40552step3 = -raw40552step2 := by apply Matrix.ext; change ∀ i j, raw40552step3 i j = -(raw40552step2 i j); unfold raw40552step3 raw40552step2; decide +kernel
      have hl : raw40552step3Labels = raw40552step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2740 node2740Labels := by rfl

def raw40553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40553Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40553step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40553step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -2, 2], ![3, -1, -2]]
def raw40553step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40553step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 1, 0], ![-2, -1, 3]]
def raw40553step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40553step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40553step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40553 raw40553Labels = mixedMoment B node3052 node3052Labels := by
  calc
    mixedMoment B raw40553 raw40553Labels = mixedMoment B raw40553step0 raw40553step0Labels := by
      have hz : ∀ j, raw40553 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40553step0 = (fun i j => raw40553 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40553step0 raw40553; decide +kernel
      have hl : raw40553step0Labels = raw40553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40553 raw40553Labels permutation434 hz
    mixedMoment B raw40553step0 raw40553step0Labels = mixedMoment B raw40553step1 raw40553step1Labels := by
      have hz : ∀ j, raw40553step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40553step1 = (fun i j => raw40553step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40553step1 raw40553step0; decide +kernel
      have hl : raw40553step1Labels = raw40553step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40553step0 raw40553step0Labels permutation80 hz
    mixedMoment B raw40553step1 raw40553step1Labels = mixedMoment B raw40553step2 raw40553step2Labels := by
      have ha : raw40553step2 = (fun i j => raw40553step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40553step2 raw40553step1; decide +kernel
      have hl : raw40553step2Labels = raw40553step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40553step1 raw40553step1Labels permutation31 permutation3
    mixedMoment B raw40553step2 raw40553step2Labels = mixedMoment B raw40553step3 raw40553step3Labels := by
      have ha : raw40553step3 = -raw40553step2 := by apply Matrix.ext; change ∀ i j, raw40553step3 i j = -(raw40553step2 i j); unfold raw40553step3 raw40553step2; decide +kernel
      have hl : raw40553step3Labels = raw40553step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3052 node3052Labels := by rfl

def raw40554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40554Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40554step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40554step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0]]
def raw40554step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40554step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40554step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40554 raw40554Labels = mixedMoment B node3547 node3547Labels := by
  calc
    mixedMoment B raw40554 raw40554Labels = mixedMoment B raw40554step0 raw40554step0Labels := by
      have hz : ∀ j, raw40554 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40554step0 = (fun i j => raw40554 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40554step0 raw40554; decide +kernel
      have hl : raw40554step0Labels = raw40554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40554 raw40554Labels permutation434 hz
    mixedMoment B raw40554step0 raw40554step0Labels = mixedMoment B raw40554step1 raw40554step1Labels := by
      have hz : ∀ j, raw40554step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40554step1 = (fun i j => raw40554step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40554step1 raw40554step0; decide +kernel
      have hl : raw40554step1Labels = raw40554step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40554step0 raw40554step0Labels permutation80 hz
    mixedMoment B raw40554step1 raw40554step1Labels = mixedMoment B raw40554step2 raw40554step2Labels := by
      have ha : raw40554step2 = (fun i j => raw40554step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40554step2 raw40554step1; decide +kernel
      have hl : raw40554step2Labels = raw40554step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40554step1 raw40554step1Labels permutation8 permutation3
    _ = mixedMoment B node3547 node3547Labels := by rfl

def raw40555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40555Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40555step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40555step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1]]
def raw40555step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40555step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw40555step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40555 raw40555Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw40555 raw40555Labels = mixedMoment B raw40555step0 raw40555step0Labels := by
      have hz : ∀ j, raw40555 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40555step0 = (fun i j => raw40555 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40555step0 raw40555; decide +kernel
      have hl : raw40555step0Labels = raw40555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40555 raw40555Labels permutation434 hz
    mixedMoment B raw40555step0 raw40555step0Labels = mixedMoment B raw40555step1 raw40555step1Labels := by
      have hz : ∀ j, raw40555step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40555step1 = (fun i j => raw40555step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40555step1 raw40555step0; decide +kernel
      have hl : raw40555step1Labels = raw40555step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40555step0 raw40555step0Labels permutation80 hz
    mixedMoment B raw40555step1 raw40555step1Labels = mixedMoment B raw40555step2 raw40555step2Labels := by
      have ha : raw40555step2 = (fun i j => raw40555step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40555step2 raw40555step1; decide +kernel
      have hl : raw40555step2Labels = raw40555step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40555step1 raw40555step1Labels permutation8 permutation3
    _ = mixedMoment B node3548 node3548Labels := by rfl

def raw40556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40556Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40556step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40556step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![1, -3, 2], ![2, 0, -2]]
def raw40556step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40556step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw40556step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40556 raw40556Labels = mixedMoment B node3549 node3549Labels := by
  calc
    mixedMoment B raw40556 raw40556Labels = mixedMoment B raw40556step0 raw40556step0Labels := by
      have hz : ∀ j, raw40556 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40556step0 = (fun i j => raw40556 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40556step0 raw40556; decide +kernel
      have hl : raw40556step0Labels = raw40556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40556 raw40556Labels permutation434 hz
    mixedMoment B raw40556step0 raw40556step0Labels = mixedMoment B raw40556step1 raw40556step1Labels := by
      have hz : ∀ j, raw40556step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40556step1 = (fun i j => raw40556step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40556step1 raw40556step0; decide +kernel
      have hl : raw40556step1Labels = raw40556step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40556step0 raw40556step0Labels permutation80 hz
    mixedMoment B raw40556step1 raw40556step1Labels = mixedMoment B raw40556step2 raw40556step2Labels := by
      have ha : raw40556step2 = (fun i j => raw40556step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40556step2 raw40556step1; decide +kernel
      have hl : raw40556step2Labels = raw40556step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40556step1 raw40556step1Labels permutation8 permutation3
    _ = mixedMoment B node3549 node3549Labels := by rfl

def raw40557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40557Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40557step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40557step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-2, -1, 3]]
def raw40557step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40557step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40557step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40557 raw40557Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw40557 raw40557Labels = mixedMoment B raw40557step0 raw40557step0Labels := by
      have hz : ∀ j, raw40557 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40557step0 = (fun i j => raw40557 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40557step0 raw40557; decide +kernel
      have hl : raw40557step0Labels = raw40557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40557 raw40557Labels permutation346 hz
    mixedMoment B raw40557step0 raw40557step0Labels = mixedMoment B raw40557step1 raw40557step1Labels := by
      have ha : raw40557step1 = (fun i j => raw40557step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40557step1 raw40557step0; decide +kernel
      have hl : raw40557step1Labels = raw40557step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40557step0 raw40557step0Labels permutation145 permutation3
    mixedMoment B raw40557step1 raw40557step1Labels = mixedMoment B raw40557step2 raw40557step2Labels := by
      have ha : raw40557step2 = -raw40557step1 := by apply Matrix.ext; change ∀ i j, raw40557step2 i j = -(raw40557step1 i j); unfold raw40557step2 raw40557step1; decide +kernel
      have hl : raw40557step2Labels = raw40557step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3075 node3075Labels := by rfl

def raw40558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40558Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40558step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40558step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40558step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40558 raw40558Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw40558 raw40558Labels = mixedMoment B raw40558step0 raw40558step0Labels := by
      have hz : ∀ j, raw40558 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40558step0 = (fun i j => raw40558 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40558step0 raw40558; decide +kernel
      have hl : raw40558step0Labels = raw40558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40558 raw40558Labels permutation346 hz
    mixedMoment B raw40558step0 raw40558step0Labels = mixedMoment B raw40558step1 raw40558step1Labels := by
      have ha : raw40558step1 = (fun i j => raw40558step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40558step1 raw40558step0; decide +kernel
      have hl : raw40558step1Labels = raw40558step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40558step0 raw40558step0Labels permutation32 permutation3
    _ = mixedMoment B node3534 node3534Labels := by rfl

def raw40559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40559Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40559step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40559step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40559 raw40559Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw40559 raw40559Labels = mixedMoment B raw40559step0 raw40559step0Labels := by
      have hz : ∀ j, raw40559 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40559step0 = (fun i j => raw40559 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40559step0 raw40559; decide +kernel
      have hl : raw40559step0Labels = raw40559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40559 raw40559Labels permutation346 hz
    mixedMoment B raw40559step0 raw40559step0Labels = mixedMoment B raw40559step1 raw40559step1Labels := by
      have ha : raw40559step1 = (fun i j => raw40559step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40559step1 raw40559step0; decide +kernel
      have hl : raw40559step1Labels = raw40559step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40559step0 raw40559step0Labels permutation32 permutation3
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw40560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40560Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40560step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40560step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40560step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40560 raw40560Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw40560 raw40560Labels = mixedMoment B raw40560step0 raw40560step0Labels := by
      have hz : ∀ j, raw40560 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40560step0 = (fun i j => raw40560 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40560step0 raw40560; decide +kernel
      have hl : raw40560step0Labels = raw40560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40560 raw40560Labels permutation346 hz
    mixedMoment B raw40560step0 raw40560step0Labels = mixedMoment B raw40560step1 raw40560step1Labels := by
      have ha : raw40560step1 = (fun i j => raw40560step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40560step1 raw40560step0; decide +kernel
      have hl : raw40560step1Labels = raw40560step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40560step0 raw40560step0Labels permutation32 permutation3
    _ = mixedMoment B node3541 node3541Labels := by rfl

def raw40561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40561Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40561step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40561 raw40561Labels = mixedMoment B node3525 node3525Labels := by
  calc
    mixedMoment B raw40561 raw40561Labels = mixedMoment B raw40561step0 raw40561step0Labels := by
      have ha : raw40561step0 = (fun i j => raw40561 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40561step0 raw40561; decide +kernel
      have hl : raw40561step0Labels = raw40561Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40561 raw40561Labels permutation152 permutation3
    _ = mixedMoment B node3525 node3525Labels := by rfl

def raw40562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40562Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40562step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40562step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40562 raw40562Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw40562 raw40562Labels = mixedMoment B raw40562step0 raw40562step0Labels := by
      have ha : raw40562step0 = (fun i j => raw40562 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40562step0 raw40562; decide +kernel
      have hl : raw40562step0Labels = raw40562Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40562 raw40562Labels permutation152 permutation3
    _ = mixedMoment B node3526 node3526Labels := by rfl

def raw40563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw40563Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw40563step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40563step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![3, -2, -1]]
def raw40563step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40563step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![3, -2, -1]]
def raw40563step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40563step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-2, -1, 3]]
def raw40563step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40563step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw40563step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40563 raw40563Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw40563 raw40563Labels = mixedMoment B raw40563step0 raw40563step0Labels := by
      have hz : ∀ j, raw40563 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40563step0 = (fun i j => raw40563 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40563step0 raw40563; decide +kernel
      have hl : raw40563step0Labels = raw40563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40563 raw40563Labels permutation520 hz
    mixedMoment B raw40563step0 raw40563step0Labels = mixedMoment B raw40563step1 raw40563step1Labels := by
      have hz : ∀ j, raw40563step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40563step1 = (fun i j => raw40563step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40563step1 raw40563step0; decide +kernel
      have hl : raw40563step1Labels = raw40563step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40563step0 raw40563step0Labels permutation104 hz
    mixedMoment B raw40563step1 raw40563step1Labels = mixedMoment B raw40563step2 raw40563step2Labels := by
      have hz : ∀ j, raw40563step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40563step2 = (fun i j => raw40563step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40563step2 raw40563step1; decide +kernel
      have hl : raw40563step2Labels = raw40563step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40563step1 raw40563step1Labels permutation20 hz
    mixedMoment B raw40563step2 raw40563step2Labels = mixedMoment B raw40563step3 raw40563step3Labels := by
      have ha : raw40563step3 = (fun i j => raw40563step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40563step3 raw40563step2; decide +kernel
      have hl : raw40563step3Labels = raw40563step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40563step2 raw40563step2Labels permutation7 permutation3
    mixedMoment B raw40563step3 raw40563step3Labels = mixedMoment B raw40563step4 raw40563step4Labels := by
      have ha : raw40563step4 = -raw40563step3 := by apply Matrix.ext; change ∀ i j, raw40563step4 i j = -(raw40563step3 i j); unfold raw40563step4 raw40563step3; decide +kernel
      have hl : raw40563step4Labels = raw40563step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2783 node2783Labels := by rfl

def raw40564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw40564Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw40564step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40564step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, -1, 1], ![3, -1, -2]]
def raw40564step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40564step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, 2, -1], ![-2, -1, 3]]
def raw40564step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40564step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw40564step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40564 raw40564Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw40564 raw40564Labels = mixedMoment B raw40564step0 raw40564step0Labels := by
      have hz : ∀ j, raw40564 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40564step0 = (fun i j => raw40564 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40564step0 raw40564; decide +kernel
      have hl : raw40564step0Labels = raw40564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40564 raw40564Labels permutation434 hz
    mixedMoment B raw40564step0 raw40564step0Labels = mixedMoment B raw40564step1 raw40564step1Labels := by
      have hz : ∀ j, raw40564step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40564step1 = (fun i j => raw40564step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40564step1 raw40564step0; decide +kernel
      have hl : raw40564step1Labels = raw40564step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40564step0 raw40564step0Labels permutation80 hz
    mixedMoment B raw40564step1 raw40564step1Labels = mixedMoment B raw40564step2 raw40564step2Labels := by
      have ha : raw40564step2 = (fun i j => raw40564step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40564step2 raw40564step1; decide +kernel
      have hl : raw40564step2Labels = raw40564step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40564step1 raw40564step1Labels permutation31 permutation3
    mixedMoment B raw40564step2 raw40564step2Labels = mixedMoment B raw40564step3 raw40564step3Labels := by
      have ha : raw40564step3 = -raw40564step2 := by apply Matrix.ext; change ∀ i j, raw40564step3 i j = -(raw40564step2 i j); unfold raw40564step3 raw40564step2; decide +kernel
      have hl : raw40564step3Labels = raw40564step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3098 node3098Labels := by rfl

def raw40565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw40565Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw40565step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40565step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1]]
def raw40565step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40565step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40565step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40565 raw40565Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw40565 raw40565Labels = mixedMoment B raw40565step0 raw40565step0Labels := by
      have hz : ∀ j, raw40565 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40565step0 = (fun i j => raw40565 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40565step0 raw40565; decide +kernel
      have hl : raw40565step0Labels = raw40565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40565 raw40565Labels permutation434 hz
    mixedMoment B raw40565step0 raw40565step0Labels = mixedMoment B raw40565step1 raw40565step1Labels := by
      have hz : ∀ j, raw40565step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40565step1 = (fun i j => raw40565step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40565step1 raw40565step0; decide +kernel
      have hl : raw40565step1Labels = raw40565step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40565step0 raw40565step0Labels permutation80 hz
    mixedMoment B raw40565step1 raw40565step1Labels = mixedMoment B raw40565step2 raw40565step2Labels := by
      have ha : raw40565step2 = (fun i j => raw40565step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40565step2 raw40565step1; decide +kernel
      have hl : raw40565step2Labels = raw40565step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40565step1 raw40565step1Labels permutation8 permutation3
    _ = mixedMoment B node3583 node3583Labels := by rfl

def raw40566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw40566Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw40566step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40566step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![1, -2, 1], ![2, 0, -2]]
def raw40566step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40566step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40566step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40566 raw40566Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw40566 raw40566Labels = mixedMoment B raw40566step0 raw40566step0Labels := by
      have hz : ∀ j, raw40566 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40566step0 = (fun i j => raw40566 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40566step0 raw40566; decide +kernel
      have hl : raw40566step0Labels = raw40566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40566 raw40566Labels permutation434 hz
    mixedMoment B raw40566step0 raw40566step0Labels = mixedMoment B raw40566step1 raw40566step1Labels := by
      have hz : ∀ j, raw40566step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40566step1 = (fun i j => raw40566step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40566step1 raw40566step0; decide +kernel
      have hl : raw40566step1Labels = raw40566step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40566step0 raw40566step0Labels permutation80 hz
    mixedMoment B raw40566step1 raw40566step1Labels = mixedMoment B raw40566step2 raw40566step2Labels := by
      have ha : raw40566step2 = (fun i j => raw40566step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40566step2 raw40566step1; decide +kernel
      have hl : raw40566step2Labels = raw40566step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40566step1 raw40566step1Labels permutation8 permutation3
    _ = mixedMoment B node3584 node3584Labels := by rfl

def raw40567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40567Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40567step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40567step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40567 raw40567Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw40567 raw40567Labels = mixedMoment B raw40567step0 raw40567step0Labels := by
      have hz : ∀ j, raw40567 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40567step0 = (fun i j => raw40567 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40567step0 raw40567; decide +kernel
      have hl : raw40567step0Labels = raw40567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40567 raw40567Labels permutation346 hz
    mixedMoment B raw40567step0 raw40567step0Labels = mixedMoment B raw40567step1 raw40567step1Labels := by
      have ha : raw40567step1 = (fun i j => raw40567step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40567step1 raw40567step0; decide +kernel
      have hl : raw40567step1Labels = raw40567step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40567step0 raw40567step0Labels permutation32 permutation3
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw40568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40568Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40568step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40568step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40568 raw40568Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw40568 raw40568Labels = mixedMoment B raw40568step0 raw40568step0Labels := by
      have hz : ∀ j, raw40568 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40568step0 = (fun i j => raw40568 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40568step0 raw40568; decide +kernel
      have hl : raw40568step0Labels = raw40568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40568 raw40568Labels permutation346 hz
    mixedMoment B raw40568step0 raw40568step0Labels = mixedMoment B raw40568step1 raw40568step1Labels := by
      have ha : raw40568step1 = (fun i j => raw40568step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40568step1 raw40568step0; decide +kernel
      have hl : raw40568step1Labels = raw40568step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40568step0 raw40568step0Labels permutation32 permutation3
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw40569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw40569Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw40569step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40569step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![0, 0, 0], ![3, -1, -2]]
def raw40569step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40569step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![3, -1, -2]]
def raw40569step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40569step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -2, 3], ![-2, 3, -1]]
def raw40569step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40569step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw40569step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40569 raw40569Labels = mixedMoment B node2789 node2789Labels := by
  calc
    mixedMoment B raw40569 raw40569Labels = mixedMoment B raw40569step0 raw40569step0Labels := by
      have hz : ∀ j, raw40569 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40569step0 = (fun i j => raw40569 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40569step0 raw40569; decide +kernel
      have hl : raw40569step0Labels = raw40569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40569 raw40569Labels permutation520 hz
    mixedMoment B raw40569step0 raw40569step0Labels = mixedMoment B raw40569step1 raw40569step1Labels := by
      have hz : ∀ j, raw40569step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40569step1 = (fun i j => raw40569step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40569step1 raw40569step0; decide +kernel
      have hl : raw40569step1Labels = raw40569step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40569step0 raw40569step0Labels permutation104 hz
    mixedMoment B raw40569step1 raw40569step1Labels = mixedMoment B raw40569step2 raw40569step2Labels := by
      have hz : ∀ j, raw40569step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40569step2 = (fun i j => raw40569step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40569step2 raw40569step1; decide +kernel
      have hl : raw40569step2Labels = raw40569step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40569step1 raw40569step1Labels permutation20 hz
    mixedMoment B raw40569step2 raw40569step2Labels = mixedMoment B raw40569step3 raw40569step3Labels := by
      have ha : raw40569step3 = (fun i j => raw40569step2 (permutation4 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40569step3 raw40569step2; decide +kernel
      have hl : raw40569step3Labels = raw40569step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40569step2 raw40569step2Labels permutation4 permutation6
    mixedMoment B raw40569step3 raw40569step3Labels = mixedMoment B raw40569step4 raw40569step4Labels := by
      have ha : raw40569step4 = -raw40569step3 := by apply Matrix.ext; change ∀ i j, raw40569step4 i j = -(raw40569step3 i j); unfold raw40569step4 raw40569step3; decide +kernel
      have hl : raw40569step4Labels = raw40569step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2789 node2789Labels := by rfl

def raw40570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40570Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40570step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40570step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![1, -1, 0], ![2, 0, -2]]
def raw40570step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40570step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -2, 3], ![-2, 2, 0]]
def raw40570step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40570step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw40570step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40570 raw40570Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw40570 raw40570Labels = mixedMoment B raw40570step0 raw40570step0Labels := by
      have hz : ∀ j, raw40570 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40570step0 = (fun i j => raw40570 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40570step0 raw40570; decide +kernel
      have hl : raw40570step0Labels = raw40570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40570 raw40570Labels permutation434 hz
    mixedMoment B raw40570step0 raw40570step0Labels = mixedMoment B raw40570step1 raw40570step1Labels := by
      have hz : ∀ j, raw40570step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40570step1 = (fun i j => raw40570step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40570step1 raw40570step0; decide +kernel
      have hl : raw40570step1Labels = raw40570step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40570step0 raw40570step0Labels permutation80 hz
    mixedMoment B raw40570step1 raw40570step1Labels = mixedMoment B raw40570step2 raw40570step2Labels := by
      have ha : raw40570step2 = (fun i j => raw40570step1 (permutation16 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40570step2 raw40570step1; decide +kernel
      have hl : raw40570step2Labels = raw40570step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40570step1 raw40570step1Labels permutation16 permutation6
    mixedMoment B raw40570step2 raw40570step2Labels = mixedMoment B raw40570step3 raw40570step3Labels := by
      have ha : raw40570step3 = -raw40570step2 := by apply Matrix.ext; change ∀ i j, raw40570step3 i j = -(raw40570step2 i j); unfold raw40570step3 raw40570step2; decide +kernel
      have hl : raw40570step3Labels = raw40570step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2744 node2744Labels := by rfl

def raw40571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw40571Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw40571step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40571step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw40571step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40571step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![2, -3, 1]]
def raw40571step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40571step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, 3, -1], ![2, -3, 1]]
def raw40571step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40571step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, -1, 3], ![2, 1, -3]]
def raw40571step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40571 raw40571Labels = mixedMoment B node3636 node3636Labels := by
  calc
    mixedMoment B raw40571 raw40571Labels = mixedMoment B raw40571step0 raw40571step0Labels := by
      have hz : ∀ j, raw40571 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40571step0 = (fun i j => raw40571 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40571step0 raw40571; decide +kernel
      have hl : raw40571step0Labels = raw40571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40571 raw40571Labels permutation520 hz
    mixedMoment B raw40571step0 raw40571step0Labels = mixedMoment B raw40571step1 raw40571step1Labels := by
      have hz : ∀ j, raw40571step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40571step1 = (fun i j => raw40571step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40571step1 raw40571step0; decide +kernel
      have hl : raw40571step1Labels = raw40571step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40571step0 raw40571step0Labels permutation104 hz
    mixedMoment B raw40571step1 raw40571step1Labels = mixedMoment B raw40571step2 raw40571step2Labels := by
      have hz : ∀ j, raw40571step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40571step2 = (fun i j => raw40571step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40571step2 raw40571step1; decide +kernel
      have hl : raw40571step2Labels = raw40571step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40571step1 raw40571step1Labels permutation20 hz
    mixedMoment B raw40571step2 raw40571step2Labels = mixedMoment B raw40571step3 raw40571step3Labels := by
      have hz : ∀ j, raw40571step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw40571step3 = (fun i j => raw40571step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw40571step3 raw40571step2; decide +kernel
      have hl : raw40571step3Labels = raw40571step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40571step2 raw40571step2Labels permutation4 hz
    mixedMoment B raw40571step3 raw40571step3Labels = mixedMoment B raw40571step4 raw40571step4Labels := by
      have ha : raw40571step4 = (fun i j => raw40571step3 (permutation0 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40571step4 raw40571step3; decide +kernel
      have hl : raw40571step4Labels = raw40571step3Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40571step3 raw40571step3Labels permutation0 permutation3
    _ = mixedMoment B node3636 node3636Labels := by rfl

def raw40572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw40572Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw40572step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40572step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw40572step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40572step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -1, 1], ![2, -2, 0]]
def raw40572step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40572step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![2, 0, -2]]
def raw40572step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40572 raw40572Labels = mixedMoment B node3629 node3629Labels := by
  calc
    mixedMoment B raw40572 raw40572Labels = mixedMoment B raw40572step0 raw40572step0Labels := by
      have hz : ∀ j, raw40572 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40572step0 = (fun i j => raw40572 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40572step0 raw40572; decide +kernel
      have hl : raw40572step0Labels = raw40572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40572 raw40572Labels permutation434 hz
    mixedMoment B raw40572step0 raw40572step0Labels = mixedMoment B raw40572step1 raw40572step1Labels := by
      have hz : ∀ j, raw40572step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40572step1 = (fun i j => raw40572step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40572step1 raw40572step0; decide +kernel
      have hl : raw40572step1Labels = raw40572step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40572step0 raw40572step0Labels permutation80 hz
    mixedMoment B raw40572step1 raw40572step1Labels = mixedMoment B raw40572step2 raw40572step2Labels := by
      have hz : ∀ j, raw40572step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40572step2 = (fun i j => raw40572step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40572step2 raw40572step1; decide +kernel
      have hl : raw40572step2Labels = raw40572step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40572step1 raw40572step1Labels permutation14 hz
    mixedMoment B raw40572step2 raw40572step2Labels = mixedMoment B raw40572step3 raw40572step3Labels := by
      have ha : raw40572step3 = (fun i j => raw40572step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40572step3 raw40572step2; decide +kernel
      have hl : raw40572step3Labels = raw40572step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40572step2 raw40572step2Labels permutation2 permutation3
    _ = mixedMoment B node3629 node3629Labels := by rfl

def raw40573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw40573Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw40573step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40573step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw40573step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40573step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -2, 2], ![2, -1, -1]]
def raw40573step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40573step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]
def raw40573step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40573 raw40573Labels = mixedMoment B node3633 node3633Labels := by
  calc
    mixedMoment B raw40573 raw40573Labels = mixedMoment B raw40573step0 raw40573step0Labels := by
      have hz : ∀ j, raw40573 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40573step0 = (fun i j => raw40573 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40573step0 raw40573; decide +kernel
      have hl : raw40573step0Labels = raw40573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40573 raw40573Labels permutation434 hz
    mixedMoment B raw40573step0 raw40573step0Labels = mixedMoment B raw40573step1 raw40573step1Labels := by
      have hz : ∀ j, raw40573step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40573step1 = (fun i j => raw40573step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40573step1 raw40573step0; decide +kernel
      have hl : raw40573step1Labels = raw40573step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40573step0 raw40573step0Labels permutation80 hz
    mixedMoment B raw40573step1 raw40573step1Labels = mixedMoment B raw40573step2 raw40573step2Labels := by
      have hz : ∀ j, raw40573step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40573step2 = (fun i j => raw40573step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40573step2 raw40573step1; decide +kernel
      have hl : raw40573step2Labels = raw40573step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40573step1 raw40573step1Labels permutation14 hz
    mixedMoment B raw40573step2 raw40573step2Labels = mixedMoment B raw40573step3 raw40573step3Labels := by
      have ha : raw40573step3 = (fun i j => raw40573step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40573step3 raw40573step2; decide +kernel
      have hl : raw40573step3Labels = raw40573step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40573step2 raw40573step2Labels permutation2 permutation3
    _ = mixedMoment B node3633 node3633Labels := by rfl

def raw40574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw40574Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw40574step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40574step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw40574step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40574step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 3, -1], ![0, -3, 3], ![2, 0, -2]]
def raw40574step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40574step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -2, 3], ![-2, 2, 0]]
def raw40574step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40574step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw40574step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40574 raw40574Labels = mixedMoment B node2294 node2294Labels := by
  calc
    mixedMoment B raw40574 raw40574Labels = mixedMoment B raw40574step0 raw40574step0Labels := by
      have hz : ∀ j, raw40574 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40574step0 = (fun i j => raw40574 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40574step0 raw40574; decide +kernel
      have hl : raw40574step0Labels = raw40574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40574 raw40574Labels permutation434 hz
    mixedMoment B raw40574step0 raw40574step0Labels = mixedMoment B raw40574step1 raw40574step1Labels := by
      have hz : ∀ j, raw40574step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40574step1 = (fun i j => raw40574step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40574step1 raw40574step0; decide +kernel
      have hl : raw40574step1Labels = raw40574step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40574step0 raw40574step0Labels permutation80 hz
    mixedMoment B raw40574step1 raw40574step1Labels = mixedMoment B raw40574step2 raw40574step2Labels := by
      have hz : ∀ j, raw40574step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40574step2 = (fun i j => raw40574step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40574step2 raw40574step1; decide +kernel
      have hl : raw40574step2Labels = raw40574step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40574step1 raw40574step1Labels permutation14 hz
    mixedMoment B raw40574step2 raw40574step2Labels = mixedMoment B raw40574step3 raw40574step3Labels := by
      have ha : raw40574step3 = (fun i j => raw40574step2 (permutation4 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40574step3 raw40574step2; decide +kernel
      have hl : raw40574step3Labels = raw40574step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40574step2 raw40574step2Labels permutation4 permutation6
    mixedMoment B raw40574step3 raw40574step3Labels = mixedMoment B raw40574step4 raw40574step4Labels := by
      have ha : raw40574step4 = -raw40574step3 := by apply Matrix.ext; change ∀ i j, raw40574step4 i j = -(raw40574step3 i j); unfold raw40574step4 raw40574step3; decide +kernel
      have hl : raw40574step4Labels = raw40574step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2294 node2294Labels := by rfl

def raw40575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40575Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40575step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40575step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40575step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40575step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 3, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40575step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40575step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 0, -1], ![1, 1, -2]]
def raw40575step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40575 raw40575Labels = mixedMoment B node3635 node3635Labels := by
  calc
    mixedMoment B raw40575 raw40575Labels = mixedMoment B raw40575step0 raw40575step0Labels := by
      have hz : ∀ j, raw40575 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40575step0 = (fun i j => raw40575 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40575step0 raw40575; decide +kernel
      have hl : raw40575step0Labels = raw40575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40575 raw40575Labels permutation434 hz
    mixedMoment B raw40575step0 raw40575step0Labels = mixedMoment B raw40575step1 raw40575step1Labels := by
      have hz : ∀ j, raw40575step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40575step1 = (fun i j => raw40575step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40575step1 raw40575step0; decide +kernel
      have hl : raw40575step1Labels = raw40575step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40575step0 raw40575step0Labels permutation80 hz
    mixedMoment B raw40575step1 raw40575step1Labels = mixedMoment B raw40575step2 raw40575step2Labels := by
      have hz : ∀ j, raw40575step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40575step2 = (fun i j => raw40575step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40575step2 raw40575step1; decide +kernel
      have hl : raw40575step2Labels = raw40575step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40575step1 raw40575step1Labels permutation14 hz
    mixedMoment B raw40575step2 raw40575step2Labels = mixedMoment B raw40575step3 raw40575step3Labels := by
      have ha : raw40575step3 = (fun i j => raw40575step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40575step3 raw40575step2; decide +kernel
      have hl : raw40575step3Labels = raw40575step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40575step2 raw40575step2Labels permutation2 permutation3
    _ = mixedMoment B node3635 node3635Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
