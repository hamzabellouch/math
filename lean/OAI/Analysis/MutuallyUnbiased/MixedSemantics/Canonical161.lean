import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw20608 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20608Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20608step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20608step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20608step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20608step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![3, 0, -3]]
def raw20608step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20608 raw20608Labels = mixedMoment B node1258 node1258Labels := by
  calc
    mixedMoment B raw20608 raw20608Labels = mixedMoment B raw20608step0 raw20608step0Labels := by
      have hz : ∀ j, raw20608 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20608step0 = (fun i j => raw20608 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20608step0 raw20608; decide +kernel
      have hl : raw20608step0Labels = raw20608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20608 raw20608Labels permutation346 hz
    mixedMoment B raw20608step0 raw20608step0Labels = mixedMoment B raw20608step1 raw20608step1Labels := by
      have hz : ∀ j, raw20608step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20608step1 = (fun i j => raw20608step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20608step1 raw20608step0; decide +kernel
      have hl : raw20608step1Labels = raw20608step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20608step0 raw20608step0Labels permutation56 hz
    mixedMoment B raw20608step1 raw20608step1Labels = mixedMoment B raw20608step2 raw20608step2Labels := by
      have ha : raw20608step2 = (fun i j => raw20608step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20608step2 raw20608step1; decide +kernel
      have hl : raw20608step2Labels = raw20608step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20608step1 raw20608step1Labels permutation8 permutation6
    _ = mixedMoment B node1258 node1258Labels := by rfl

def raw20609 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20609Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20609step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20609step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20609step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20609step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw20609step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20609 raw20609Labels = mixedMoment B node1264 node1264Labels := by
  calc
    mixedMoment B raw20609 raw20609Labels = mixedMoment B raw20609step0 raw20609step0Labels := by
      have hz : ∀ j, raw20609 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20609step0 = (fun i j => raw20609 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20609step0 raw20609; decide +kernel
      have hl : raw20609step0Labels = raw20609Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20609 raw20609Labels permutation346 hz
    mixedMoment B raw20609step0 raw20609step0Labels = mixedMoment B raw20609step1 raw20609step1Labels := by
      have hz : ∀ j, raw20609step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20609step1 = (fun i j => raw20609step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20609step1 raw20609step0; decide +kernel
      have hl : raw20609step1Labels = raw20609step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20609step0 raw20609step0Labels permutation56 hz
    mixedMoment B raw20609step1 raw20609step1Labels = mixedMoment B raw20609step2 raw20609step2Labels := by
      have ha : raw20609step2 = (fun i j => raw20609step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20609step2 raw20609step1; decide +kernel
      have hl : raw20609step2Labels = raw20609step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20609step1 raw20609step1Labels permutation8 permutation6
    _ = mixedMoment B node1264 node1264Labels := by rfl

def raw20610 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20610Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20610step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20610step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20610step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20610step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![0, -3, 3]]
def raw20610step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20610step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw20610step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20610 raw20610Labels = mixedMoment B node1085 node1085Labels := by
  calc
    mixedMoment B raw20610 raw20610Labels = mixedMoment B raw20610step0 raw20610step0Labels := by
      have hz : ∀ j, raw20610 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20610step0 = (fun i j => raw20610 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20610step0 raw20610; decide +kernel
      have hl : raw20610step0Labels = raw20610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20610 raw20610Labels permutation434 hz
    mixedMoment B raw20610step0 raw20610step0Labels = mixedMoment B raw20610step1 raw20610step1Labels := by
      have hz : ∀ j, raw20610step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20610step1 = (fun i j => raw20610step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20610step1 raw20610step0; decide +kernel
      have hl : raw20610step1Labels = raw20610step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20610step0 raw20610step0Labels permutation80 hz
    mixedMoment B raw20610step1 raw20610step1Labels = mixedMoment B raw20610step2 raw20610step2Labels := by
      have hz : ∀ j, raw20610step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20610step2 = (fun i j => raw20610step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20610step2 raw20610step1; decide +kernel
      have hl : raw20610step2Labels = raw20610step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20610step1 raw20610step1Labels permutation14 hz
    mixedMoment B raw20610step2 raw20610step2Labels = mixedMoment B raw20610step3 raw20610step3Labels := by
      have ha : raw20610step3 = (fun i j => raw20610step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20610step3 raw20610step2; decide +kernel
      have hl : raw20610step3Labels = raw20610step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20610step2 raw20610step2Labels permutation2 permutation6
    _ = mixedMoment B node1085 node1085Labels := by rfl

def raw20611 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20611Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20611step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20611step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20611step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20611step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20611step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20611 raw20611Labels = mixedMoment B node1239 node1239Labels := by
  calc
    mixedMoment B raw20611 raw20611Labels = mixedMoment B raw20611step0 raw20611step0Labels := by
      have hz : ∀ j, raw20611 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20611step0 = (fun i j => raw20611 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20611step0 raw20611; decide +kernel
      have hl : raw20611step0Labels = raw20611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20611 raw20611Labels permutation434 hz
    mixedMoment B raw20611step0 raw20611step0Labels = mixedMoment B raw20611step1 raw20611step1Labels := by
      have hz : ∀ j, raw20611step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20611step1 = (fun i j => raw20611step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20611step1 raw20611step0; decide +kernel
      have hl : raw20611step1Labels = raw20611step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20611step0 raw20611step0Labels permutation80 hz
    mixedMoment B raw20611step1 raw20611step1Labels = mixedMoment B raw20611step2 raw20611step2Labels := by
      have ha : raw20611step2 = (fun i j => raw20611step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20611step2 raw20611step1; decide +kernel
      have hl : raw20611step2Labels = raw20611step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20611step1 raw20611step1Labels permutation8 permutation6
    _ = mixedMoment B node1239 node1239Labels := by rfl

def raw20612 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20612Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20612step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20612step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20612step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20612step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20612step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20612 raw20612Labels = mixedMoment B node1239 node1239Labels := by
  calc
    mixedMoment B raw20612 raw20612Labels = mixedMoment B raw20612step0 raw20612step0Labels := by
      have hz : ∀ j, raw20612 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20612step0 = (fun i j => raw20612 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20612step0 raw20612; decide +kernel
      have hl : raw20612step0Labels = raw20612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20612 raw20612Labels permutation434 hz
    mixedMoment B raw20612step0 raw20612step0Labels = mixedMoment B raw20612step1 raw20612step1Labels := by
      have hz : ∀ j, raw20612step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20612step1 = (fun i j => raw20612step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20612step1 raw20612step0; decide +kernel
      have hl : raw20612step1Labels = raw20612step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20612step0 raw20612step0Labels permutation56 hz
    mixedMoment B raw20612step1 raw20612step1Labels = mixedMoment B raw20612step2 raw20612step2Labels := by
      have ha : raw20612step2 = (fun i j => raw20612step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20612step2 raw20612step1; decide +kernel
      have hl : raw20612step2Labels = raw20612step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20612step1 raw20612step1Labels permutation8 permutation6
    _ = mixedMoment B node1239 node1239Labels := by rfl

def raw20613 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20613Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20613step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20613step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20613step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20613step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20613step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20613 raw20613Labels = mixedMoment B node1239 node1239Labels := by
  calc
    mixedMoment B raw20613 raw20613Labels = mixedMoment B raw20613step0 raw20613step0Labels := by
      have hz : ∀ j, raw20613 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20613step0 = (fun i j => raw20613 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20613step0 raw20613; decide +kernel
      have hl : raw20613step0Labels = raw20613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20613 raw20613Labels permutation346 hz
    mixedMoment B raw20613step0 raw20613step0Labels = mixedMoment B raw20613step1 raw20613step1Labels := by
      have hz : ∀ j, raw20613step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20613step1 = (fun i j => raw20613step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20613step1 raw20613step0; decide +kernel
      have hl : raw20613step1Labels = raw20613step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20613step0 raw20613step0Labels permutation56 hz
    mixedMoment B raw20613step1 raw20613step1Labels = mixedMoment B raw20613step2 raw20613step2Labels := by
      have ha : raw20613step2 = (fun i j => raw20613step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20613step2 raw20613step1; decide +kernel
      have hl : raw20613step2Labels = raw20613step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20613step1 raw20613step1Labels permutation8 permutation6
    _ = mixedMoment B node1239 node1239Labels := by rfl

def raw20614 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20614Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20614step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20614step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20614step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20614step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-1, -2, 3]]
def raw20614step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20614step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw20614step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20614 raw20614Labels = mixedMoment B node1304 node1304Labels := by
  calc
    mixedMoment B raw20614 raw20614Labels = mixedMoment B raw20614step0 raw20614step0Labels := by
      have hz : ∀ j, raw20614 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20614step0 = (fun i j => raw20614 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20614step0 raw20614; decide +kernel
      have hl : raw20614step0Labels = raw20614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20614 raw20614Labels permutation434 hz
    mixedMoment B raw20614step0 raw20614step0Labels = mixedMoment B raw20614step1 raw20614step1Labels := by
      have hz : ∀ j, raw20614step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20614step1 = (fun i j => raw20614step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20614step1 raw20614step0; decide +kernel
      have hl : raw20614step1Labels = raw20614step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20614step0 raw20614step0Labels permutation80 hz
    mixedMoment B raw20614step1 raw20614step1Labels = mixedMoment B raw20614step2 raw20614step2Labels := by
      have hz : ∀ j, raw20614step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20614step2 = (fun i j => raw20614step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20614step2 raw20614step1; decide +kernel
      have hl : raw20614step2Labels = raw20614step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20614step1 raw20614step1Labels permutation14 hz
    mixedMoment B raw20614step2 raw20614step2Labels = mixedMoment B raw20614step3 raw20614step3Labels := by
      have ha : raw20614step3 = (fun i j => raw20614step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20614step3 raw20614step2; decide +kernel
      have hl : raw20614step3Labels = raw20614step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20614step2 raw20614step2Labels permutation2 permutation6
    _ = mixedMoment B node1304 node1304Labels := by rfl

def raw20615 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20615Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20615step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20615step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20615step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20615step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 1, 1], ![1, -4, 3]]
def raw20615step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20615step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw20615step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20615 raw20615Labels = mixedMoment B node1077 node1077Labels := by
  calc
    mixedMoment B raw20615 raw20615Labels = mixedMoment B raw20615step0 raw20615step0Labels := by
      have hz : ∀ j, raw20615 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20615step0 = (fun i j => raw20615 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20615step0 raw20615; decide +kernel
      have hl : raw20615step0Labels = raw20615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20615 raw20615Labels permutation434 hz
    mixedMoment B raw20615step0 raw20615step0Labels = mixedMoment B raw20615step1 raw20615step1Labels := by
      have hz : ∀ j, raw20615step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20615step1 = (fun i j => raw20615step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20615step1 raw20615step0; decide +kernel
      have hl : raw20615step1Labels = raw20615step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20615step0 raw20615step0Labels permutation80 hz
    mixedMoment B raw20615step1 raw20615step1Labels = mixedMoment B raw20615step2 raw20615step2Labels := by
      have hz : ∀ j, raw20615step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20615step2 = (fun i j => raw20615step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20615step2 raw20615step1; decide +kernel
      have hl : raw20615step2Labels = raw20615step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20615step1 raw20615step1Labels permutation14 hz
    mixedMoment B raw20615step2 raw20615step2Labels = mixedMoment B raw20615step3 raw20615step3Labels := by
      have ha : raw20615step3 = (fun i j => raw20615step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20615step3 raw20615step2; decide +kernel
      have hl : raw20615step3Labels = raw20615step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20615step2 raw20615step2Labels permutation2 permutation6
    _ = mixedMoment B node1077 node1077Labels := by rfl

def raw20616 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20616Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20616step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20616step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20616step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20616step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![3, 1, -4]]
def raw20616step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20616 raw20616Labels = mixedMoment B node1231 node1231Labels := by
  calc
    mixedMoment B raw20616 raw20616Labels = mixedMoment B raw20616step0 raw20616step0Labels := by
      have hz : ∀ j, raw20616 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20616step0 = (fun i j => raw20616 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20616step0 raw20616; decide +kernel
      have hl : raw20616step0Labels = raw20616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20616 raw20616Labels permutation434 hz
    mixedMoment B raw20616step0 raw20616step0Labels = mixedMoment B raw20616step1 raw20616step1Labels := by
      have hz : ∀ j, raw20616step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20616step1 = (fun i j => raw20616step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20616step1 raw20616step0; decide +kernel
      have hl : raw20616step1Labels = raw20616step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20616step0 raw20616step0Labels permutation80 hz
    mixedMoment B raw20616step1 raw20616step1Labels = mixedMoment B raw20616step2 raw20616step2Labels := by
      have ha : raw20616step2 = (fun i j => raw20616step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20616step2 raw20616step1; decide +kernel
      have hl : raw20616step2Labels = raw20616step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20616step1 raw20616step1Labels permutation8 permutation6
    _ = mixedMoment B node1231 node1231Labels := by rfl

def raw20617 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20617Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20617step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20617step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20617step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20617step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![3, 1, -4]]
def raw20617step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20617 raw20617Labels = mixedMoment B node1231 node1231Labels := by
  calc
    mixedMoment B raw20617 raw20617Labels = mixedMoment B raw20617step0 raw20617step0Labels := by
      have hz : ∀ j, raw20617 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20617step0 = (fun i j => raw20617 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20617step0 raw20617; decide +kernel
      have hl : raw20617step0Labels = raw20617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20617 raw20617Labels permutation434 hz
    mixedMoment B raw20617step0 raw20617step0Labels = mixedMoment B raw20617step1 raw20617step1Labels := by
      have hz : ∀ j, raw20617step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20617step1 = (fun i j => raw20617step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20617step1 raw20617step0; decide +kernel
      have hl : raw20617step1Labels = raw20617step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20617step0 raw20617step0Labels permutation56 hz
    mixedMoment B raw20617step1 raw20617step1Labels = mixedMoment B raw20617step2 raw20617step2Labels := by
      have ha : raw20617step2 = (fun i j => raw20617step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20617step2 raw20617step1; decide +kernel
      have hl : raw20617step2Labels = raw20617step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20617step1 raw20617step1Labels permutation8 permutation6
    _ = mixedMoment B node1231 node1231Labels := by rfl

def raw20618 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20618Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20618step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20618step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20618step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20618step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![3, 1, -4]]
def raw20618step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20618 raw20618Labels = mixedMoment B node1231 node1231Labels := by
  calc
    mixedMoment B raw20618 raw20618Labels = mixedMoment B raw20618step0 raw20618step0Labels := by
      have hz : ∀ j, raw20618 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20618step0 = (fun i j => raw20618 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20618step0 raw20618; decide +kernel
      have hl : raw20618step0Labels = raw20618Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20618 raw20618Labels permutation346 hz
    mixedMoment B raw20618step0 raw20618step0Labels = mixedMoment B raw20618step1 raw20618step1Labels := by
      have hz : ∀ j, raw20618step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20618step1 = (fun i j => raw20618step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20618step1 raw20618step0; decide +kernel
      have hl : raw20618step1Labels = raw20618step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20618step0 raw20618step0Labels permutation56 hz
    mixedMoment B raw20618step1 raw20618step1Labels = mixedMoment B raw20618step2 raw20618step2Labels := by
      have ha : raw20618step2 = (fun i j => raw20618step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20618step2 raw20618step1; decide +kernel
      have hl : raw20618step2Labels = raw20618step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20618step1 raw20618step1Labels permutation8 permutation6
    _ = mixedMoment B node1231 node1231Labels := by rfl

def raw20619 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -4, 3]]
def raw20619Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -4, 3]]
def raw20619step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20619step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-3, 2, 1], ![1, -4, 3]]
def raw20619step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20619step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-3, 2, 1], ![1, -4, 3]]
def raw20619step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20619step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![3, 1, -4]]
def raw20619step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20619 raw20619Labels = mixedMoment B node1289 node1289Labels := by
  calc
    mixedMoment B raw20619 raw20619Labels = mixedMoment B raw20619step0 raw20619step0Labels := by
      have hz : ∀ j, raw20619 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20619step0 = (fun i j => raw20619 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20619step0 raw20619; decide +kernel
      have hl : raw20619step0Labels = raw20619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20619 raw20619Labels permutation434 hz
    mixedMoment B raw20619step0 raw20619step0Labels = mixedMoment B raw20619step1 raw20619step1Labels := by
      have hz : ∀ j, raw20619step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20619step1 = (fun i j => raw20619step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20619step1 raw20619step0; decide +kernel
      have hl : raw20619step1Labels = raw20619step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20619step0 raw20619step0Labels permutation80 hz
    mixedMoment B raw20619step1 raw20619step1Labels = mixedMoment B raw20619step2 raw20619step2Labels := by
      have hz : ∀ j, raw20619step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20619step2 = (fun i j => raw20619step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20619step2 raw20619step1; decide +kernel
      have hl : raw20619step2Labels = raw20619step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20619step1 raw20619step1Labels permutation14 hz
    mixedMoment B raw20619step2 raw20619step2Labels = mixedMoment B raw20619step3 raw20619step3Labels := by
      have ha : raw20619step3 = (fun i j => raw20619step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20619step3 raw20619step2; decide +kernel
      have hl : raw20619step3Labels = raw20619step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20619step2 raw20619step2Labels permutation2 permutation6
    _ = mixedMoment B node1289 node1289Labels := by rfl

def raw20620 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20620Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20620step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20620step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20620step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20620step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20620step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20620step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20620step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20620 raw20620Labels = mixedMoment B node1047 node1047Labels := by
  calc
    mixedMoment B raw20620 raw20620Labels = mixedMoment B raw20620step0 raw20620step0Labels := by
      have hz : ∀ j, raw20620 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20620step0 = (fun i j => raw20620 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20620step0 raw20620; decide +kernel
      have hl : raw20620step0Labels = raw20620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20620 raw20620Labels permutation434 hz
    mixedMoment B raw20620step0 raw20620step0Labels = mixedMoment B raw20620step1 raw20620step1Labels := by
      have hz : ∀ j, raw20620step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20620step1 = (fun i j => raw20620step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20620step1 raw20620step0; decide +kernel
      have hl : raw20620step1Labels = raw20620step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20620step0 raw20620step0Labels permutation80 hz
    mixedMoment B raw20620step1 raw20620step1Labels = mixedMoment B raw20620step2 raw20620step2Labels := by
      have ha : raw20620step2 = (fun i j => raw20620step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20620step2 raw20620step1; decide +kernel
      have hl : raw20620step2Labels = raw20620step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20620step1 raw20620step1Labels permutation8 permutation7
    mixedMoment B raw20620step2 raw20620step2Labels = mixedMoment B raw20620step3 raw20620step3Labels := by
      have ha : raw20620step3 = raw20620step2 := by apply Matrix.ext; unfold raw20620step3 raw20620step2; decide +kernel
      have hl : raw20620step2Labels = labelEmbedding1 ∘ raw20620step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20620step2 raw20620step2Labels raw20620step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1047 node1047Labels := by rfl

def raw20621 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20621Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20621step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20621step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20621step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20621step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20621step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20621step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20621step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20621 raw20621Labels = mixedMoment B node1047 node1047Labels := by
  calc
    mixedMoment B raw20621 raw20621Labels = mixedMoment B raw20621step0 raw20621step0Labels := by
      have hz : ∀ j, raw20621 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20621step0 = (fun i j => raw20621 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20621step0 raw20621; decide +kernel
      have hl : raw20621step0Labels = raw20621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20621 raw20621Labels permutation434 hz
    mixedMoment B raw20621step0 raw20621step0Labels = mixedMoment B raw20621step1 raw20621step1Labels := by
      have hz : ∀ j, raw20621step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20621step1 = (fun i j => raw20621step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20621step1 raw20621step0; decide +kernel
      have hl : raw20621step1Labels = raw20621step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20621step0 raw20621step0Labels permutation56 hz
    mixedMoment B raw20621step1 raw20621step1Labels = mixedMoment B raw20621step2 raw20621step2Labels := by
      have ha : raw20621step2 = (fun i j => raw20621step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20621step2 raw20621step1; decide +kernel
      have hl : raw20621step2Labels = raw20621step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20621step1 raw20621step1Labels permutation8 permutation7
    mixedMoment B raw20621step2 raw20621step2Labels = mixedMoment B raw20621step3 raw20621step3Labels := by
      have ha : raw20621step3 = raw20621step2 := by apply Matrix.ext; unfold raw20621step3 raw20621step2; decide +kernel
      have hl : raw20621step2Labels = labelEmbedding1 ∘ raw20621step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20621step2 raw20621step2Labels raw20621step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1047 node1047Labels := by rfl

def raw20622 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20622Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20622step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20622step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20622step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20622step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20622step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20622step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20622step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20622 raw20622Labels = mixedMoment B node1047 node1047Labels := by
  calc
    mixedMoment B raw20622 raw20622Labels = mixedMoment B raw20622step0 raw20622step0Labels := by
      have hz : ∀ j, raw20622 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20622step0 = (fun i j => raw20622 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20622step0 raw20622; decide +kernel
      have hl : raw20622step0Labels = raw20622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20622 raw20622Labels permutation346 hz
    mixedMoment B raw20622step0 raw20622step0Labels = mixedMoment B raw20622step1 raw20622step1Labels := by
      have hz : ∀ j, raw20622step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20622step1 = (fun i j => raw20622step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20622step1 raw20622step0; decide +kernel
      have hl : raw20622step1Labels = raw20622step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20622step0 raw20622step0Labels permutation56 hz
    mixedMoment B raw20622step1 raw20622step1Labels = mixedMoment B raw20622step2 raw20622step2Labels := by
      have ha : raw20622step2 = (fun i j => raw20622step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20622step2 raw20622step1; decide +kernel
      have hl : raw20622step2Labels = raw20622step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20622step1 raw20622step1Labels permutation8 permutation7
    mixedMoment B raw20622step2 raw20622step2Labels = mixedMoment B raw20622step3 raw20622step3Labels := by
      have ha : raw20622step3 = raw20622step2 := by apply Matrix.ext; unfold raw20622step3 raw20622step2; decide +kernel
      have hl : raw20622step2Labels = labelEmbedding1 ∘ raw20622step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20622step2 raw20622step2Labels raw20622step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1047 node1047Labels := by rfl

def raw20623 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20623Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20623step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20623step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20623step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20623step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-3, 2, 1], ![0, -3, 3]]
def raw20623step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20623step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw20623step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20623step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw20623step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20623 raw20623Labels = mixedMoment B node1092 node1092Labels := by
  calc
    mixedMoment B raw20623 raw20623Labels = mixedMoment B raw20623step0 raw20623step0Labels := by
      have hz : ∀ j, raw20623 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20623step0 = (fun i j => raw20623 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20623step0 raw20623; decide +kernel
      have hl : raw20623step0Labels = raw20623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20623 raw20623Labels permutation434 hz
    mixedMoment B raw20623step0 raw20623step0Labels = mixedMoment B raw20623step1 raw20623step1Labels := by
      have hz : ∀ j, raw20623step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20623step1 = (fun i j => raw20623step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20623step1 raw20623step0; decide +kernel
      have hl : raw20623step1Labels = raw20623step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20623step0 raw20623step0Labels permutation80 hz
    mixedMoment B raw20623step1 raw20623step1Labels = mixedMoment B raw20623step2 raw20623step2Labels := by
      have hz : ∀ j, raw20623step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20623step2 = (fun i j => raw20623step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20623step2 raw20623step1; decide +kernel
      have hl : raw20623step2Labels = raw20623step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20623step1 raw20623step1Labels permutation14 hz
    mixedMoment B raw20623step2 raw20623step2Labels = mixedMoment B raw20623step3 raw20623step3Labels := by
      have ha : raw20623step3 = (fun i j => raw20623step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20623step3 raw20623step2; decide +kernel
      have hl : raw20623step3Labels = raw20623step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20623step2 raw20623step2Labels permutation2 permutation7
    mixedMoment B raw20623step3 raw20623step3Labels = mixedMoment B raw20623step4 raw20623step4Labels := by
      have ha : raw20623step4 = raw20623step3 := by apply Matrix.ext; unfold raw20623step4 raw20623step3; decide +kernel
      have hl : raw20623step3Labels = labelEmbedding1 ∘ raw20623step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20623step3 raw20623step3Labels raw20623step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1092 node1092Labels := by rfl

def raw20624 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20624Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20624step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20624step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20624step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20624step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw20624step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20624step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw20624step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20624 raw20624Labels = mixedMoment B node1417 node1417Labels := by
  calc
    mixedMoment B raw20624 raw20624Labels = mixedMoment B raw20624step0 raw20624step0Labels := by
      have hz : ∀ j, raw20624 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20624step0 = (fun i j => raw20624 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20624step0 raw20624; decide +kernel
      have hl : raw20624step0Labels = raw20624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20624 raw20624Labels permutation434 hz
    mixedMoment B raw20624step0 raw20624step0Labels = mixedMoment B raw20624step1 raw20624step1Labels := by
      have hz : ∀ j, raw20624step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20624step1 = (fun i j => raw20624step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20624step1 raw20624step0; decide +kernel
      have hl : raw20624step1Labels = raw20624step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20624step0 raw20624step0Labels permutation80 hz
    mixedMoment B raw20624step1 raw20624step1Labels = mixedMoment B raw20624step2 raw20624step2Labels := by
      have ha : raw20624step2 = (fun i j => raw20624step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20624step2 raw20624step1; decide +kernel
      have hl : raw20624step2Labels = raw20624step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20624step1 raw20624step1Labels permutation8 permutation7
    mixedMoment B raw20624step2 raw20624step2Labels = mixedMoment B raw20624step3 raw20624step3Labels := by
      have ha : raw20624step3 = raw20624step2 := by apply Matrix.ext; unfold raw20624step3 raw20624step2; decide +kernel
      have hl : raw20624step2Labels = labelEmbedding1 ∘ raw20624step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20624step2 raw20624step2Labels raw20624step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1417 node1417Labels := by rfl

def raw20625 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20625Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20625step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20625step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20625step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20625 raw20625Labels = mixedMoment B node1218 node1218Labels := by
  calc
    mixedMoment B raw20625 raw20625Labels = mixedMoment B raw20625step0 raw20625step0Labels := by
      have hz : ∀ j, raw20625 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20625step0 = (fun i j => raw20625 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20625step0 raw20625; decide +kernel
      have hl : raw20625step0Labels = raw20625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20625 raw20625Labels permutation434 hz
    mixedMoment B raw20625step0 raw20625step0Labels = mixedMoment B raw20625step1 raw20625step1Labels := by
      have ha : raw20625step1 = (fun i j => raw20625step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20625step1 raw20625step0; decide +kernel
      have hl : raw20625step1Labels = raw20625step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20625step0 raw20625step0Labels permutation32 permutation7
    mixedMoment B raw20625step1 raw20625step1Labels = mixedMoment B raw20625step2 raw20625step2Labels := by
      have ha : raw20625step2 = raw20625step1 := by apply Matrix.ext; unfold raw20625step2 raw20625step1; decide +kernel
      have hl : raw20625step1Labels = labelEmbedding1 ∘ raw20625step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20625step1 raw20625step1Labels raw20625step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1218 node1218Labels := by rfl

def raw20626 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20626Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20626step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20626step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20626step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20626step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20626 raw20626Labels = mixedMoment B node1218 node1218Labels := by
  calc
    mixedMoment B raw20626 raw20626Labels = mixedMoment B raw20626step0 raw20626step0Labels := by
      have hz : ∀ j, raw20626 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20626step0 = (fun i j => raw20626 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20626step0 raw20626; decide +kernel
      have hl : raw20626step0Labels = raw20626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20626 raw20626Labels permutation346 hz
    mixedMoment B raw20626step0 raw20626step0Labels = mixedMoment B raw20626step1 raw20626step1Labels := by
      have ha : raw20626step1 = (fun i j => raw20626step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20626step1 raw20626step0; decide +kernel
      have hl : raw20626step1Labels = raw20626step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20626step0 raw20626step0Labels permutation32 permutation7
    mixedMoment B raw20626step1 raw20626step1Labels = mixedMoment B raw20626step2 raw20626step2Labels := by
      have ha : raw20626step2 = raw20626step1 := by apply Matrix.ext; unfold raw20626step2 raw20626step1; decide +kernel
      have hl : raw20626step1Labels = labelEmbedding1 ∘ raw20626step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20626step1 raw20626step1Labels raw20626step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1218 node1218Labels := by rfl

def raw20627 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20627Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20627step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20627step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20627step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20627step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw20627step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20627step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw20627step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20627 raw20627Labels = mixedMoment B node1244 node1244Labels := by
  calc
    mixedMoment B raw20627 raw20627Labels = mixedMoment B raw20627step0 raw20627step0Labels := by
      have hz : ∀ j, raw20627 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20627step0 = (fun i j => raw20627 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20627step0 raw20627; decide +kernel
      have hl : raw20627step0Labels = raw20627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20627 raw20627Labels permutation434 hz
    mixedMoment B raw20627step0 raw20627step0Labels = mixedMoment B raw20627step1 raw20627step1Labels := by
      have hz : ∀ j, raw20627step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20627step1 = (fun i j => raw20627step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20627step1 raw20627step0; decide +kernel
      have hl : raw20627step1Labels = raw20627step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20627step0 raw20627step0Labels permutation80 hz
    mixedMoment B raw20627step1 raw20627step1Labels = mixedMoment B raw20627step2 raw20627step2Labels := by
      have ha : raw20627step2 = (fun i j => raw20627step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20627step2 raw20627step1; decide +kernel
      have hl : raw20627step2Labels = raw20627step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20627step1 raw20627step1Labels permutation8 permutation7
    mixedMoment B raw20627step2 raw20627step2Labels = mixedMoment B raw20627step3 raw20627step3Labels := by
      have ha : raw20627step3 = raw20627step2 := by apply Matrix.ext; unfold raw20627step3 raw20627step2; decide +kernel
      have hl : raw20627step2Labels = labelEmbedding1 ∘ raw20627step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20627step2 raw20627step2Labels raw20627step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1244 node1244Labels := by rfl

def raw20628 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20628Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20628step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20628step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20628step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20628step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw20628step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20628step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw20628step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20628 raw20628Labels = mixedMoment B node1417 node1417Labels := by
  calc
    mixedMoment B raw20628 raw20628Labels = mixedMoment B raw20628step0 raw20628step0Labels := by
      have hz : ∀ j, raw20628 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20628step0 = (fun i j => raw20628 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20628step0 raw20628; decide +kernel
      have hl : raw20628step0Labels = raw20628Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20628 raw20628Labels permutation434 hz
    mixedMoment B raw20628step0 raw20628step0Labels = mixedMoment B raw20628step1 raw20628step1Labels := by
      have hz : ∀ j, raw20628step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20628step1 = (fun i j => raw20628step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20628step1 raw20628step0; decide +kernel
      have hl : raw20628step1Labels = raw20628step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20628step0 raw20628step0Labels permutation56 hz
    mixedMoment B raw20628step1 raw20628step1Labels = mixedMoment B raw20628step2 raw20628step2Labels := by
      have ha : raw20628step2 = (fun i j => raw20628step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20628step2 raw20628step1; decide +kernel
      have hl : raw20628step2Labels = raw20628step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20628step1 raw20628step1Labels permutation8 permutation7
    mixedMoment B raw20628step2 raw20628step2Labels = mixedMoment B raw20628step3 raw20628step3Labels := by
      have ha : raw20628step3 = raw20628step2 := by apply Matrix.ext; unfold raw20628step3 raw20628step2; decide +kernel
      have hl : raw20628step2Labels = labelEmbedding1 ∘ raw20628step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20628step2 raw20628step2Labels raw20628step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1417 node1417Labels := by rfl

def raw20629 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20629Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20629step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20629step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20629step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20629step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20629step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20629 raw20629Labels = mixedMoment B node1218 node1218Labels := by
  calc
    mixedMoment B raw20629 raw20629Labels = mixedMoment B raw20629step0 raw20629step0Labels := by
      have hz : ∀ j, raw20629 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20629step0 = (fun i j => raw20629 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20629step0 raw20629; decide +kernel
      have hl : raw20629step0Labels = raw20629Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20629 raw20629Labels permutation434 hz
    mixedMoment B raw20629step0 raw20629step0Labels = mixedMoment B raw20629step1 raw20629step1Labels := by
      have ha : raw20629step1 = (fun i j => raw20629step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20629step1 raw20629step0; decide +kernel
      have hl : raw20629step1Labels = raw20629step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20629step0 raw20629step0Labels permutation38 permutation7
    mixedMoment B raw20629step1 raw20629step1Labels = mixedMoment B raw20629step2 raw20629step2Labels := by
      have ha : raw20629step2 = raw20629step1 := by apply Matrix.ext; unfold raw20629step2 raw20629step1; decide +kernel
      have hl : raw20629step1Labels = labelEmbedding1 ∘ raw20629step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20629step1 raw20629step1Labels raw20629step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1218 node1218Labels := by rfl

def raw20630 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20630Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20630step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20630step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20630step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20630step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20630 raw20630Labels = mixedMoment B node1218 node1218Labels := by
  calc
    mixedMoment B raw20630 raw20630Labels = mixedMoment B raw20630step0 raw20630step0Labels := by
      have hz : ∀ j, raw20630 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20630step0 = (fun i j => raw20630 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20630step0 raw20630; decide +kernel
      have hl : raw20630step0Labels = raw20630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20630 raw20630Labels permutation265 hz
    mixedMoment B raw20630step0 raw20630step0Labels = mixedMoment B raw20630step1 raw20630step1Labels := by
      have ha : raw20630step1 = (fun i j => raw20630step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20630step1 raw20630step0; decide +kernel
      have hl : raw20630step1Labels = raw20630step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20630step0 raw20630step0Labels permutation32 permutation7
    mixedMoment B raw20630step1 raw20630step1Labels = mixedMoment B raw20630step2 raw20630step2Labels := by
      have ha : raw20630step2 = raw20630step1 := by apply Matrix.ext; unfold raw20630step2 raw20630step1; decide +kernel
      have hl : raw20630step1Labels = labelEmbedding1 ∘ raw20630step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20630step1 raw20630step1Labels raw20630step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1218 node1218Labels := by rfl

def raw20631 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20631Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20631step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20631step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20631step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20631step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw20631step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20631step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw20631step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20631 raw20631Labels = mixedMoment B node1244 node1244Labels := by
  calc
    mixedMoment B raw20631 raw20631Labels = mixedMoment B raw20631step0 raw20631step0Labels := by
      have hz : ∀ j, raw20631 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20631step0 = (fun i j => raw20631 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20631step0 raw20631; decide +kernel
      have hl : raw20631step0Labels = raw20631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20631 raw20631Labels permutation434 hz
    mixedMoment B raw20631step0 raw20631step0Labels = mixedMoment B raw20631step1 raw20631step1Labels := by
      have hz : ∀ j, raw20631step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20631step1 = (fun i j => raw20631step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20631step1 raw20631step0; decide +kernel
      have hl : raw20631step1Labels = raw20631step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20631step0 raw20631step0Labels permutation56 hz
    mixedMoment B raw20631step1 raw20631step1Labels = mixedMoment B raw20631step2 raw20631step2Labels := by
      have ha : raw20631step2 = (fun i j => raw20631step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20631step2 raw20631step1; decide +kernel
      have hl : raw20631step2Labels = raw20631step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20631step1 raw20631step1Labels permutation8 permutation7
    mixedMoment B raw20631step2 raw20631step2Labels = mixedMoment B raw20631step3 raw20631step3Labels := by
      have ha : raw20631step3 = raw20631step2 := by apply Matrix.ext; unfold raw20631step3 raw20631step2; decide +kernel
      have hl : raw20631step2Labels = labelEmbedding1 ∘ raw20631step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20631step2 raw20631step2Labels raw20631step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1244 node1244Labels := by rfl

def raw20632 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20632Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20632step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20632step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20632step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20632step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw20632step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20632step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw20632step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20632 raw20632Labels = mixedMoment B node1417 node1417Labels := by
  calc
    mixedMoment B raw20632 raw20632Labels = mixedMoment B raw20632step0 raw20632step0Labels := by
      have hz : ∀ j, raw20632 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20632step0 = (fun i j => raw20632 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20632step0 raw20632; decide +kernel
      have hl : raw20632step0Labels = raw20632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20632 raw20632Labels permutation346 hz
    mixedMoment B raw20632step0 raw20632step0Labels = mixedMoment B raw20632step1 raw20632step1Labels := by
      have hz : ∀ j, raw20632step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20632step1 = (fun i j => raw20632step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20632step1 raw20632step0; decide +kernel
      have hl : raw20632step1Labels = raw20632step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20632step0 raw20632step0Labels permutation56 hz
    mixedMoment B raw20632step1 raw20632step1Labels = mixedMoment B raw20632step2 raw20632step2Labels := by
      have ha : raw20632step2 = (fun i j => raw20632step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20632step2 raw20632step1; decide +kernel
      have hl : raw20632step2Labels = raw20632step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20632step1 raw20632step1Labels permutation8 permutation7
    mixedMoment B raw20632step2 raw20632step2Labels = mixedMoment B raw20632step3 raw20632step3Labels := by
      have ha : raw20632step3 = raw20632step2 := by apply Matrix.ext; unfold raw20632step3 raw20632step2; decide +kernel
      have hl : raw20632step2Labels = labelEmbedding1 ∘ raw20632step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20632step2 raw20632step2Labels raw20632step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1417 node1417Labels := by rfl

def raw20633 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20633Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20633step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20633step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20633step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20633step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20633 raw20633Labels = mixedMoment B node1218 node1218Labels := by
  calc
    mixedMoment B raw20633 raw20633Labels = mixedMoment B raw20633step0 raw20633step0Labels := by
      have hz : ∀ j, raw20633 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20633step0 = (fun i j => raw20633 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20633step0 raw20633; decide +kernel
      have hl : raw20633step0Labels = raw20633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20633 raw20633Labels permutation346 hz
    mixedMoment B raw20633step0 raw20633step0Labels = mixedMoment B raw20633step1 raw20633step1Labels := by
      have ha : raw20633step1 = (fun i j => raw20633step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20633step1 raw20633step0; decide +kernel
      have hl : raw20633step1Labels = raw20633step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20633step0 raw20633step0Labels permutation38 permutation7
    mixedMoment B raw20633step1 raw20633step1Labels = mixedMoment B raw20633step2 raw20633step2Labels := by
      have ha : raw20633step2 = raw20633step1 := by apply Matrix.ext; unfold raw20633step2 raw20633step1; decide +kernel
      have hl : raw20633step1Labels = labelEmbedding1 ∘ raw20633step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20633step1 raw20633step1Labels raw20633step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1218 node1218Labels := by rfl

def raw20634 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20634Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20634step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20634step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20634step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20634step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20634 raw20634Labels = mixedMoment B node1218 node1218Labels := by
  calc
    mixedMoment B raw20634 raw20634Labels = mixedMoment B raw20634step0 raw20634step0Labels := by
      have hz : ∀ j, raw20634 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20634step0 = (fun i j => raw20634 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20634step0 raw20634; decide +kernel
      have hl : raw20634step0Labels = raw20634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20634 raw20634Labels permutation265 hz
    mixedMoment B raw20634step0 raw20634step0Labels = mixedMoment B raw20634step1 raw20634step1Labels := by
      have ha : raw20634step1 = (fun i j => raw20634step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20634step1 raw20634step0; decide +kernel
      have hl : raw20634step1Labels = raw20634step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20634step0 raw20634step0Labels permutation38 permutation7
    mixedMoment B raw20634step1 raw20634step1Labels = mixedMoment B raw20634step2 raw20634step2Labels := by
      have ha : raw20634step2 = raw20634step1 := by apply Matrix.ext; unfold raw20634step2 raw20634step1; decide +kernel
      have hl : raw20634step1Labels = labelEmbedding1 ∘ raw20634step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20634step1 raw20634step1Labels raw20634step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1218 node1218Labels := by rfl

def raw20635 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20635Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20635step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20635step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, 2, 1], ![0, -3, 3]]
def raw20635step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20635step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw20635step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20635step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw20635step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20635 raw20635Labels = mixedMoment B node1244 node1244Labels := by
  calc
    mixedMoment B raw20635 raw20635Labels = mixedMoment B raw20635step0 raw20635step0Labels := by
      have hz : ∀ j, raw20635 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20635step0 = (fun i j => raw20635 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20635step0 raw20635; decide +kernel
      have hl : raw20635step0Labels = raw20635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20635 raw20635Labels permutation346 hz
    mixedMoment B raw20635step0 raw20635step0Labels = mixedMoment B raw20635step1 raw20635step1Labels := by
      have hz : ∀ j, raw20635step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20635step1 = (fun i j => raw20635step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20635step1 raw20635step0; decide +kernel
      have hl : raw20635step1Labels = raw20635step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20635step0 raw20635step0Labels permutation56 hz
    mixedMoment B raw20635step1 raw20635step1Labels = mixedMoment B raw20635step2 raw20635step2Labels := by
      have ha : raw20635step2 = (fun i j => raw20635step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20635step2 raw20635step1; decide +kernel
      have hl : raw20635step2Labels = raw20635step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20635step1 raw20635step1Labels permutation8 permutation7
    mixedMoment B raw20635step2 raw20635step2Labels = mixedMoment B raw20635step3 raw20635step3Labels := by
      have ha : raw20635step3 = raw20635step2 := by apply Matrix.ext; unfold raw20635step3 raw20635step2; decide +kernel
      have hl : raw20635step2Labels = labelEmbedding1 ∘ raw20635step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20635step2 raw20635step2Labels raw20635step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1244 node1244Labels := by rfl

def raw20636 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20636Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20636step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20636step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20636step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20636step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-1, -2, 3]]
def raw20636step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20636step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw20636step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20636step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw20636step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20636 raw20636Labels = mixedMoment B node1307 node1307Labels := by
  calc
    mixedMoment B raw20636 raw20636Labels = mixedMoment B raw20636step0 raw20636step0Labels := by
      have hz : ∀ j, raw20636 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20636step0 = (fun i j => raw20636 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20636step0 raw20636; decide +kernel
      have hl : raw20636step0Labels = raw20636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20636 raw20636Labels permutation434 hz
    mixedMoment B raw20636step0 raw20636step0Labels = mixedMoment B raw20636step1 raw20636step1Labels := by
      have hz : ∀ j, raw20636step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20636step1 = (fun i j => raw20636step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20636step1 raw20636step0; decide +kernel
      have hl : raw20636step1Labels = raw20636step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20636step0 raw20636step0Labels permutation80 hz
    mixedMoment B raw20636step1 raw20636step1Labels = mixedMoment B raw20636step2 raw20636step2Labels := by
      have hz : ∀ j, raw20636step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20636step2 = (fun i j => raw20636step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20636step2 raw20636step1; decide +kernel
      have hl : raw20636step2Labels = raw20636step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20636step1 raw20636step1Labels permutation14 hz
    mixedMoment B raw20636step2 raw20636step2Labels = mixedMoment B raw20636step3 raw20636step3Labels := by
      have ha : raw20636step3 = (fun i j => raw20636step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20636step3 raw20636step2; decide +kernel
      have hl : raw20636step3Labels = raw20636step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20636step2 raw20636step2Labels permutation2 permutation7
    mixedMoment B raw20636step3 raw20636step3Labels = mixedMoment B raw20636step4 raw20636step4Labels := by
      have ha : raw20636step4 = raw20636step3 := by apply Matrix.ext; unfold raw20636step4 raw20636step3; decide +kernel
      have hl : raw20636step3Labels = labelEmbedding1 ∘ raw20636step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20636step3 raw20636step3Labels raw20636step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1307 node1307Labels := by rfl

def raw20637 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20637Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20637step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20637step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20637step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20637step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 1, 1], ![1, -4, 3]]
def raw20637step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20637step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 1, -2], ![3, -4, 1]]
def raw20637step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20637step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 1, -2], ![3, -4, 1]]
def raw20637step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20637 raw20637Labels = mixedMoment B node1453 node1453Labels := by
  calc
    mixedMoment B raw20637 raw20637Labels = mixedMoment B raw20637step0 raw20637step0Labels := by
      have hz : ∀ j, raw20637 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20637step0 = (fun i j => raw20637 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20637step0 raw20637; decide +kernel
      have hl : raw20637step0Labels = raw20637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20637 raw20637Labels permutation434 hz
    mixedMoment B raw20637step0 raw20637step0Labels = mixedMoment B raw20637step1 raw20637step1Labels := by
      have hz : ∀ j, raw20637step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20637step1 = (fun i j => raw20637step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20637step1 raw20637step0; decide +kernel
      have hl : raw20637step1Labels = raw20637step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20637step0 raw20637step0Labels permutation80 hz
    mixedMoment B raw20637step1 raw20637step1Labels = mixedMoment B raw20637step2 raw20637step2Labels := by
      have hz : ∀ j, raw20637step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20637step2 = (fun i j => raw20637step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20637step2 raw20637step1; decide +kernel
      have hl : raw20637step2Labels = raw20637step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20637step1 raw20637step1Labels permutation14 hz
    mixedMoment B raw20637step2 raw20637step2Labels = mixedMoment B raw20637step3 raw20637step3Labels := by
      have ha : raw20637step3 = (fun i j => raw20637step2 (permutation7 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20637step3 raw20637step2; decide +kernel
      have hl : raw20637step3Labels = raw20637step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20637step2 raw20637step2Labels permutation7 permutation5
    mixedMoment B raw20637step3 raw20637step3Labels = mixedMoment B raw20637step4 raw20637step4Labels := by
      have ha : raw20637step4 = raw20637step3 := by apply Matrix.ext; unfold raw20637step4 raw20637step3; decide +kernel
      have hl : raw20637step3Labels = labelEmbedding1 ∘ raw20637step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20637step3 raw20637step3Labels raw20637step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1453 node1453Labels := by rfl

def raw20638 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20638Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20638step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20638step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20638step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20638step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw20638step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20638step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw20638step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20638 raw20638Labels = mixedMoment B node1272 node1272Labels := by
  calc
    mixedMoment B raw20638 raw20638Labels = mixedMoment B raw20638step0 raw20638step0Labels := by
      have hz : ∀ j, raw20638 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20638step0 = (fun i j => raw20638 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20638step0 raw20638; decide +kernel
      have hl : raw20638step0Labels = raw20638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20638 raw20638Labels permutation434 hz
    mixedMoment B raw20638step0 raw20638step0Labels = mixedMoment B raw20638step1 raw20638step1Labels := by
      have hz : ∀ j, raw20638step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20638step1 = (fun i j => raw20638step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20638step1 raw20638step0; decide +kernel
      have hl : raw20638step1Labels = raw20638step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20638step0 raw20638step0Labels permutation80 hz
    mixedMoment B raw20638step1 raw20638step1Labels = mixedMoment B raw20638step2 raw20638step2Labels := by
      have ha : raw20638step2 = (fun i j => raw20638step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20638step2 raw20638step1; decide +kernel
      have hl : raw20638step2Labels = raw20638step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20638step1 raw20638step1Labels permutation8 permutation7
    mixedMoment B raw20638step2 raw20638step2Labels = mixedMoment B raw20638step3 raw20638step3Labels := by
      have ha : raw20638step3 = raw20638step2 := by apply Matrix.ext; unfold raw20638step3 raw20638step2; decide +kernel
      have hl : raw20638step2Labels = labelEmbedding1 ∘ raw20638step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20638step2 raw20638step2Labels raw20638step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1272 node1272Labels := by rfl

def raw20639 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20639Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20639step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20639step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20639step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20639step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw20639step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20639step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw20639step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20639 raw20639Labels = mixedMoment B node1272 node1272Labels := by
  calc
    mixedMoment B raw20639 raw20639Labels = mixedMoment B raw20639step0 raw20639step0Labels := by
      have hz : ∀ j, raw20639 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20639step0 = (fun i j => raw20639 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20639step0 raw20639; decide +kernel
      have hl : raw20639step0Labels = raw20639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20639 raw20639Labels permutation434 hz
    mixedMoment B raw20639step0 raw20639step0Labels = mixedMoment B raw20639step1 raw20639step1Labels := by
      have hz : ∀ j, raw20639step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20639step1 = (fun i j => raw20639step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20639step1 raw20639step0; decide +kernel
      have hl : raw20639step1Labels = raw20639step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20639step0 raw20639step0Labels permutation56 hz
    mixedMoment B raw20639step1 raw20639step1Labels = mixedMoment B raw20639step2 raw20639step2Labels := by
      have ha : raw20639step2 = (fun i j => raw20639step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20639step2 raw20639step1; decide +kernel
      have hl : raw20639step2Labels = raw20639step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20639step1 raw20639step1Labels permutation8 permutation7
    mixedMoment B raw20639step2 raw20639step2Labels = mixedMoment B raw20639step3 raw20639step3Labels := by
      have ha : raw20639step3 = raw20639step2 := by apply Matrix.ext; unfold raw20639step3 raw20639step2; decide +kernel
      have hl : raw20639step2Labels = labelEmbedding1 ∘ raw20639step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20639step2 raw20639step2Labels raw20639step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1272 node1272Labels := by rfl

def raw20640 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20640Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20640step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20640step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20640step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20640step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw20640step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20640step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw20640step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20640 raw20640Labels = mixedMoment B node1272 node1272Labels := by
  calc
    mixedMoment B raw20640 raw20640Labels = mixedMoment B raw20640step0 raw20640step0Labels := by
      have hz : ∀ j, raw20640 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20640step0 = (fun i j => raw20640 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20640step0 raw20640; decide +kernel
      have hl : raw20640step0Labels = raw20640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20640 raw20640Labels permutation346 hz
    mixedMoment B raw20640step0 raw20640step0Labels = mixedMoment B raw20640step1 raw20640step1Labels := by
      have hz : ∀ j, raw20640step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20640step1 = (fun i j => raw20640step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20640step1 raw20640step0; decide +kernel
      have hl : raw20640step1Labels = raw20640step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20640step0 raw20640step0Labels permutation56 hz
    mixedMoment B raw20640step1 raw20640step1Labels = mixedMoment B raw20640step2 raw20640step2Labels := by
      have ha : raw20640step2 = (fun i j => raw20640step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20640step2 raw20640step1; decide +kernel
      have hl : raw20640step2Labels = raw20640step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20640step1 raw20640step1Labels permutation8 permutation7
    mixedMoment B raw20640step2 raw20640step2Labels = mixedMoment B raw20640step3 raw20640step3Labels := by
      have ha : raw20640step3 = raw20640step2 := by apply Matrix.ext; unfold raw20640step3 raw20640step2; decide +kernel
      have hl : raw20640step2Labels = labelEmbedding1 ∘ raw20640step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20640step2 raw20640step2Labels raw20640step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1272 node1272Labels := by rfl

def raw20641 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -4, 3]]
def raw20641Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -4, 3]]
def raw20641step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-3, 2, 1], ![1, -4, 3]]
def raw20641step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20641step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-3, 2, 1], ![1, -4, 3]]
def raw20641step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20641step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 2, -3], ![3, -4, 1]]
def raw20641step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20641step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 2, -3], ![3, -4, 1]]
def raw20641step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20641 raw20641Labels = mixedMoment B node1309 node1309Labels := by
  calc
    mixedMoment B raw20641 raw20641Labels = mixedMoment B raw20641step0 raw20641step0Labels := by
      have hz : ∀ j, raw20641 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20641step0 = (fun i j => raw20641 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20641step0 raw20641; decide +kernel
      have hl : raw20641step0Labels = raw20641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20641 raw20641Labels permutation434 hz
    mixedMoment B raw20641step0 raw20641step0Labels = mixedMoment B raw20641step1 raw20641step1Labels := by
      have hz : ∀ j, raw20641step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20641step1 = (fun i j => raw20641step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20641step1 raw20641step0; decide +kernel
      have hl : raw20641step1Labels = raw20641step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20641step0 raw20641step0Labels permutation80 hz
    mixedMoment B raw20641step1 raw20641step1Labels = mixedMoment B raw20641step2 raw20641step2Labels := by
      have hz : ∀ j, raw20641step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20641step2 = (fun i j => raw20641step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20641step2 raw20641step1; decide +kernel
      have hl : raw20641step2Labels = raw20641step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20641step1 raw20641step1Labels permutation14 hz
    mixedMoment B raw20641step2 raw20641step2Labels = mixedMoment B raw20641step3 raw20641step3Labels := by
      have ha : raw20641step3 = (fun i j => raw20641step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20641step3 raw20641step2; decide +kernel
      have hl : raw20641step3Labels = raw20641step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20641step2 raw20641step2Labels permutation2 permutation7
    mixedMoment B raw20641step3 raw20641step3Labels = mixedMoment B raw20641step4 raw20641step4Labels := by
      have ha : raw20641step4 = raw20641step3 := by apply Matrix.ext; unfold raw20641step4 raw20641step3; decide +kernel
      have hl : raw20641step3Labels = labelEmbedding1 ∘ raw20641step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20641step3 raw20641step3Labels raw20641step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1309 node1309Labels := by rfl

def raw20642 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20642Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20642step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20642step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20642step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20642step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![0, -3, 3]]
def raw20642step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20642step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![2, 2, -4]]
def raw20642step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20642 raw20642Labels = mixedMoment B node2289 node2289Labels := by
  calc
    mixedMoment B raw20642 raw20642Labels = mixedMoment B raw20642step0 raw20642step0Labels := by
      have hz : ∀ j, raw20642 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20642step0 = (fun i j => raw20642 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20642step0 raw20642; decide +kernel
      have hl : raw20642step0Labels = raw20642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20642 raw20642Labels permutation434 hz
    mixedMoment B raw20642step0 raw20642step0Labels = mixedMoment B raw20642step1 raw20642step1Labels := by
      have hz : ∀ j, raw20642step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20642step1 = (fun i j => raw20642step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20642step1 raw20642step0; decide +kernel
      have hl : raw20642step1Labels = raw20642step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20642step0 raw20642step0Labels permutation80 hz
    mixedMoment B raw20642step1 raw20642step1Labels = mixedMoment B raw20642step2 raw20642step2Labels := by
      have hz : ∀ j, raw20642step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20642step2 = (fun i j => raw20642step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20642step2 raw20642step1; decide +kernel
      have hl : raw20642step2Labels = raw20642step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20642step1 raw20642step1Labels permutation14 hz
    mixedMoment B raw20642step2 raw20642step2Labels = mixedMoment B raw20642step3 raw20642step3Labels := by
      have ha : raw20642step3 = (fun i j => raw20642step2 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20642step3 raw20642step2; decide +kernel
      have hl : raw20642step3Labels = raw20642step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20642step2 raw20642step2Labels permutation7 permutation4
    _ = mixedMoment B node2289 node2289Labels := by rfl

def raw20643 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20643Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20643step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20643step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20643step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20643step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw20643step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20643step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20643step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20643 raw20643Labels = mixedMoment B node1647 node1647Labels := by
  calc
    mixedMoment B raw20643 raw20643Labels = mixedMoment B raw20643step0 raw20643step0Labels := by
      have hz : ∀ j, raw20643 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20643step0 = (fun i j => raw20643 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20643step0 raw20643; decide +kernel
      have hl : raw20643step0Labels = raw20643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20643 raw20643Labels permutation434 hz
    mixedMoment B raw20643step0 raw20643step0Labels = mixedMoment B raw20643step1 raw20643step1Labels := by
      have hz : ∀ j, raw20643step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20643step1 = (fun i j => raw20643step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20643step1 raw20643step0; decide +kernel
      have hl : raw20643step1Labels = raw20643step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20643step0 raw20643step0Labels permutation80 hz
    mixedMoment B raw20643step1 raw20643step1Labels = mixedMoment B raw20643step2 raw20643step2Labels := by
      have ha : raw20643step2 = (fun i j => raw20643step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20643step2 raw20643step1; decide +kernel
      have hl : raw20643step2Labels = raw20643step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20643step1 raw20643step1Labels permutation10 permutation4
    mixedMoment B raw20643step2 raw20643step2Labels = mixedMoment B raw20643step3 raw20643step3Labels := by
      have ha : raw20643step3 = -raw20643step2 := by apply Matrix.ext; change ∀ i j, raw20643step3 i j = -(raw20643step2 i j); unfold raw20643step3 raw20643step2; decide +kernel
      have hl : raw20643step3Labels = raw20643step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1647 node1647Labels := by rfl

def raw20644 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20644Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20644step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20644step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20644step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw20644step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20644step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20644step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20644 raw20644Labels = mixedMoment B node1647 node1647Labels := by
  calc
    mixedMoment B raw20644 raw20644Labels = mixedMoment B raw20644step0 raw20644step0Labels := by
      have hz : ∀ j, raw20644 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20644step0 = (fun i j => raw20644 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20644step0 raw20644; decide +kernel
      have hl : raw20644step0Labels = raw20644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20644 raw20644Labels permutation434 hz
    mixedMoment B raw20644step0 raw20644step0Labels = mixedMoment B raw20644step1 raw20644step1Labels := by
      have hz : ∀ j, raw20644step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20644step1 = (fun i j => raw20644step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20644step1 raw20644step0; decide +kernel
      have hl : raw20644step1Labels = raw20644step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20644step0 raw20644step0Labels permutation56 hz
    mixedMoment B raw20644step1 raw20644step1Labels = mixedMoment B raw20644step2 raw20644step2Labels := by
      have ha : raw20644step2 = (fun i j => raw20644step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20644step2 raw20644step1; decide +kernel
      have hl : raw20644step2Labels = raw20644step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20644step1 raw20644step1Labels permutation10 permutation4
    mixedMoment B raw20644step2 raw20644step2Labels = mixedMoment B raw20644step3 raw20644step3Labels := by
      have ha : raw20644step3 = -raw20644step2 := by apply Matrix.ext; change ∀ i j, raw20644step3 i j = -(raw20644step2 i j); unfold raw20644step3 raw20644step2; decide +kernel
      have hl : raw20644step3Labels = raw20644step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1647 node1647Labels := by rfl

def raw20645 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20645Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20645step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20645step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20645step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20645step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw20645step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20645step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20645step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20645 raw20645Labels = mixedMoment B node1647 node1647Labels := by
  calc
    mixedMoment B raw20645 raw20645Labels = mixedMoment B raw20645step0 raw20645step0Labels := by
      have hz : ∀ j, raw20645 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20645step0 = (fun i j => raw20645 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20645step0 raw20645; decide +kernel
      have hl : raw20645step0Labels = raw20645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20645 raw20645Labels permutation346 hz
    mixedMoment B raw20645step0 raw20645step0Labels = mixedMoment B raw20645step1 raw20645step1Labels := by
      have hz : ∀ j, raw20645step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20645step1 = (fun i j => raw20645step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20645step1 raw20645step0; decide +kernel
      have hl : raw20645step1Labels = raw20645step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20645step0 raw20645step0Labels permutation56 hz
    mixedMoment B raw20645step1 raw20645step1Labels = mixedMoment B raw20645step2 raw20645step2Labels := by
      have ha : raw20645step2 = (fun i j => raw20645step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20645step2 raw20645step1; decide +kernel
      have hl : raw20645step2Labels = raw20645step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20645step1 raw20645step1Labels permutation10 permutation4
    mixedMoment B raw20645step2 raw20645step2Labels = mixedMoment B raw20645step3 raw20645step3Labels := by
      have ha : raw20645step3 = -raw20645step2 := by apply Matrix.ext; change ∀ i j, raw20645step3 i j = -(raw20645step2 i j); unfold raw20645step3 raw20645step2; decide +kernel
      have hl : raw20645step3Labels = raw20645step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1647 node1647Labels := by rfl

def raw20646 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20646Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20646step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw20646step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20646step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 1, 1], ![1, -4, 3]]
def raw20646step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20646step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw20646step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20646 raw20646Labels = mixedMoment B node1077 node1077Labels := by
  calc
    mixedMoment B raw20646 raw20646Labels = mixedMoment B raw20646step0 raw20646step0Labels := by
      have hz : ∀ j, raw20646 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20646step0 = (fun i j => raw20646 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20646step0 raw20646; decide +kernel
      have hl : raw20646step0Labels = raw20646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20646 raw20646Labels permutation434 hz
    mixedMoment B raw20646step0 raw20646step0Labels = mixedMoment B raw20646step1 raw20646step1Labels := by
      have hz : ∀ j, raw20646step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20646step1 = (fun i j => raw20646step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20646step1 raw20646step0; decide +kernel
      have hl : raw20646step1Labels = raw20646step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20646step0 raw20646step0Labels permutation80 hz
    mixedMoment B raw20646step1 raw20646step1Labels = mixedMoment B raw20646step2 raw20646step2Labels := by
      have hz : ∀ j, raw20646step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20646step2 = (fun i j => raw20646step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20646step2 raw20646step1; decide +kernel
      have hl : raw20646step2Labels = raw20646step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20646step1 raw20646step1Labels permutation14 hz
    mixedMoment B raw20646step2 raw20646step2Labels = mixedMoment B raw20646step3 raw20646step3Labels := by
      have ha : raw20646step3 = (fun i j => raw20646step2 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20646step3 raw20646step2; decide +kernel
      have hl : raw20646step3Labels = raw20646step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20646step2 raw20646step2Labels permutation7 permutation4
    _ = mixedMoment B node1077 node1077Labels := by rfl

def raw20647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 1, -4]]
def raw20647Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![3, 1, -4]]
def raw20647step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20647step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![3, 1, -4]]
def raw20647step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20647step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw20647step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20647step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![3, -1, -2]]
def raw20647step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20647 raw20647Labels = mixedMoment B node1657 node1657Labels := by
  calc
    mixedMoment B raw20647 raw20647Labels = mixedMoment B raw20647step0 raw20647step0Labels := by
      have hz : ∀ j, raw20647 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20647step0 = (fun i j => raw20647 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20647step0 raw20647; decide +kernel
      have hl : raw20647step0Labels = raw20647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20647 raw20647Labels permutation434 hz
    mixedMoment B raw20647step0 raw20647step0Labels = mixedMoment B raw20647step1 raw20647step1Labels := by
      have hz : ∀ j, raw20647step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20647step1 = (fun i j => raw20647step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20647step1 raw20647step0; decide +kernel
      have hl : raw20647step1Labels = raw20647step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20647step0 raw20647step0Labels permutation80 hz
    mixedMoment B raw20647step1 raw20647step1Labels = mixedMoment B raw20647step2 raw20647step2Labels := by
      have ha : raw20647step2 = (fun i j => raw20647step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20647step2 raw20647step1; decide +kernel
      have hl : raw20647step2Labels = raw20647step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20647step1 raw20647step1Labels permutation31 permutation2
    mixedMoment B raw20647step2 raw20647step2Labels = mixedMoment B raw20647step3 raw20647step3Labels := by
      have ha : raw20647step3 = -raw20647step2 := by apply Matrix.ext; change ∀ i j, raw20647step3 i j = -(raw20647step2 i j); unfold raw20647step3 raw20647step2; decide +kernel
      have hl : raw20647step3Labels = raw20647step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1657 node1657Labels := by rfl

def raw20648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![3, 1, -4]]
def raw20648Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 1, -4]]
def raw20648step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20648step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![3, 1, -4]]
def raw20648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20648step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw20648step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20648step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![3, -1, -2]]
def raw20648step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20648 raw20648Labels = mixedMoment B node1657 node1657Labels := by
  calc
    mixedMoment B raw20648 raw20648Labels = mixedMoment B raw20648step0 raw20648step0Labels := by
      have hz : ∀ j, raw20648 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20648step0 = (fun i j => raw20648 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20648step0 raw20648; decide +kernel
      have hl : raw20648step0Labels = raw20648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20648 raw20648Labels permutation434 hz
    mixedMoment B raw20648step0 raw20648step0Labels = mixedMoment B raw20648step1 raw20648step1Labels := by
      have hz : ∀ j, raw20648step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20648step1 = (fun i j => raw20648step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20648step1 raw20648step0; decide +kernel
      have hl : raw20648step1Labels = raw20648step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20648step0 raw20648step0Labels permutation56 hz
    mixedMoment B raw20648step1 raw20648step1Labels = mixedMoment B raw20648step2 raw20648step2Labels := by
      have ha : raw20648step2 = (fun i j => raw20648step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20648step2 raw20648step1; decide +kernel
      have hl : raw20648step2Labels = raw20648step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20648step1 raw20648step1Labels permutation31 permutation2
    mixedMoment B raw20648step2 raw20648step2Labels = mixedMoment B raw20648step3 raw20648step3Labels := by
      have ha : raw20648step3 = -raw20648step2 := by apply Matrix.ext; change ∀ i j, raw20648step3 i j = -(raw20648step2 i j); unfold raw20648step3 raw20648step2; decide +kernel
      have hl : raw20648step3Labels = raw20648step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1657 node1657Labels := by rfl

def raw20649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 1, -4]]
def raw20649Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 1, -4]]
def raw20649step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20649step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![3, 1, -4]]
def raw20649step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20649step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw20649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20649step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![3, -1, -2]]
def raw20649step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20649 raw20649Labels = mixedMoment B node1657 node1657Labels := by
  calc
    mixedMoment B raw20649 raw20649Labels = mixedMoment B raw20649step0 raw20649step0Labels := by
      have hz : ∀ j, raw20649 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20649step0 = (fun i j => raw20649 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20649step0 raw20649; decide +kernel
      have hl : raw20649step0Labels = raw20649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20649 raw20649Labels permutation346 hz
    mixedMoment B raw20649step0 raw20649step0Labels = mixedMoment B raw20649step1 raw20649step1Labels := by
      have hz : ∀ j, raw20649step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20649step1 = (fun i j => raw20649step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20649step1 raw20649step0; decide +kernel
      have hl : raw20649step1Labels = raw20649step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20649step0 raw20649step0Labels permutation56 hz
    mixedMoment B raw20649step1 raw20649step1Labels = mixedMoment B raw20649step2 raw20649step2Labels := by
      have ha : raw20649step2 = (fun i j => raw20649step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20649step2 raw20649step1; decide +kernel
      have hl : raw20649step2Labels = raw20649step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20649step1 raw20649step1Labels permutation31 permutation2
    mixedMoment B raw20649step2 raw20649step2Labels = mixedMoment B raw20649step3 raw20649step3Labels := by
      have ha : raw20649step3 = -raw20649step2 := by apply Matrix.ext; change ∀ i j, raw20649step3 i j = -(raw20649step2 i j); unfold raw20649step3 raw20649step2; decide +kernel
      have hl : raw20649step3Labels = raw20649step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1657 node1657Labels := by rfl

def raw20650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw20650Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw20650step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20650step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw20650step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20650step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![2, 2, -4]]
def raw20650step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20650 raw20650Labels = mixedMoment B node2780 node2780Labels := by
  calc
    mixedMoment B raw20650 raw20650Labels = mixedMoment B raw20650step0 raw20650step0Labels := by
      have hz : ∀ j, raw20650 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20650step0 = (fun i j => raw20650 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20650step0 raw20650; decide +kernel
      have hl : raw20650step0Labels = raw20650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20650 raw20650Labels permutation434 hz
    mixedMoment B raw20650step0 raw20650step0Labels = mixedMoment B raw20650step1 raw20650step1Labels := by
      have hz : ∀ j, raw20650step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20650step1 = (fun i j => raw20650step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20650step1 raw20650step0; decide +kernel
      have hl : raw20650step1Labels = raw20650step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20650step0 raw20650step0Labels permutation80 hz
    mixedMoment B raw20650step1 raw20650step1Labels = mixedMoment B raw20650step2 raw20650step2Labels := by
      have hz : ∀ j, raw20650step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20650step2 = (fun i j => raw20650step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20650step2 raw20650step1; decide +kernel
      have hl : raw20650step2Labels = raw20650step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20650step1 raw20650step1Labels permutation14 hz
    _ = mixedMoment B node2780 node2780Labels := by rfl

def raw20651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20651step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20651step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20651step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20651step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20651 raw20651Labels = mixedMoment B node4153 node4153Labels := by
  calc
    mixedMoment B raw20651 raw20651Labels = mixedMoment B raw20651step0 raw20651step0Labels := by
      have hz : ∀ j, raw20651 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20651step0 = (fun i j => raw20651 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20651step0 raw20651; decide +kernel
      have hl : raw20651step0Labels = raw20651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20651 raw20651Labels permutation346 hz
    mixedMoment B raw20651step0 raw20651step0Labels = mixedMoment B raw20651step1 raw20651step1Labels := by
      have ha : raw20651step1 = (fun i j => raw20651step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20651step1 raw20651step0; decide +kernel
      have hl : raw20651step1Labels = raw20651step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20651step0 raw20651step0Labels permutation40 permutation3
    mixedMoment B raw20651step1 raw20651step1Labels = mixedMoment B raw20651step2 raw20651step2Labels := by
      have ha : raw20651step2 = raw20651step1 := by apply Matrix.ext; unfold raw20651step2 raw20651step1; decide +kernel
      have hl : raw20651step1Labels = labelEmbedding6 ∘ raw20651step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20651step1 raw20651step1Labels raw20651step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4153 node4153Labels := by rfl

def raw20652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20652step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20652step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20652step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20652step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20652 raw20652Labels = mixedMoment B node4528 node4528Labels := by
  calc
    mixedMoment B raw20652 raw20652Labels = mixedMoment B raw20652step0 raw20652step0Labels := by
      have ha : raw20652step0 = (fun i j => raw20652 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20652step0 raw20652; decide +kernel
      have hl : raw20652step0Labels = raw20652Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20652 raw20652Labels permutation184 permutation3
    mixedMoment B raw20652step0 raw20652step0Labels = mixedMoment B raw20652step1 raw20652step1Labels := by
      have ha : raw20652step1 = raw20652step0 := by apply Matrix.ext; unfold raw20652step1 raw20652step0; decide +kernel
      have hl : raw20652step0Labels = labelEmbedding6 ∘ raw20652step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20652step0 raw20652step0Labels raw20652step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4528 node4528Labels := by rfl

def raw20653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20653step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20653step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20653step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20653 raw20653Labels = mixedMoment B node4546 node4546Labels := by
  calc
    mixedMoment B raw20653 raw20653Labels = mixedMoment B raw20653step0 raw20653step0Labels := by
      have hz : ∀ j, raw20653 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20653step0 = (fun i j => raw20653 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20653step0 raw20653; decide +kernel
      have hl : raw20653step0Labels = raw20653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20653 raw20653Labels permutation346 hz
    mixedMoment B raw20653step0 raw20653step0Labels = mixedMoment B raw20653step1 raw20653step1Labels := by
      have ha : raw20653step1 = (fun i j => raw20653step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20653step1 raw20653step0; decide +kernel
      have hl : raw20653step1Labels = raw20653step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20653step0 raw20653step0Labels permutation38 permutation2
    _ = mixedMoment B node4546 node4546Labels := by rfl

def raw20654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20654step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20654step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20654 raw20654Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw20654 raw20654Labels = mixedMoment B raw20654step0 raw20654step0Labels := by
      have hz : ∀ j, raw20654 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20654step0 = (fun i j => raw20654 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20654step0 raw20654; decide +kernel
      have hl : raw20654step0Labels = raw20654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20654 raw20654Labels permutation346 hz
    mixedMoment B raw20654step0 raw20654step0Labels = mixedMoment B raw20654step1 raw20654step1Labels := by
      have ha : raw20654step1 = (fun i j => raw20654step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20654step1 raw20654step0; decide +kernel
      have hl : raw20654step1Labels = raw20654step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20654step0 raw20654step0Labels permutation40 permutation2
    _ = mixedMoment B node4591 node4591Labels := by rfl

def raw20655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20655step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20655step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20655step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20655step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20655step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20655 raw20655Labels = mixedMoment B node4153 node4153Labels := by
  calc
    mixedMoment B raw20655 raw20655Labels = mixedMoment B raw20655step0 raw20655step0Labels := by
      have hz : ∀ j, raw20655 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20655step0 = (fun i j => raw20655 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20655step0 raw20655; decide +kernel
      have hl : raw20655step0Labels = raw20655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20655 raw20655Labels permutation265 hz
    mixedMoment B raw20655step0 raw20655step0Labels = mixedMoment B raw20655step1 raw20655step1Labels := by
      have ha : raw20655step1 = (fun i j => raw20655step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20655step1 raw20655step0; decide +kernel
      have hl : raw20655step1Labels = raw20655step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20655step0 raw20655step0Labels permutation40 permutation3
    mixedMoment B raw20655step1 raw20655step1Labels = mixedMoment B raw20655step2 raw20655step2Labels := by
      have ha : raw20655step2 = raw20655step1 := by apply Matrix.ext; unfold raw20655step2 raw20655step1; decide +kernel
      have hl : raw20655step1Labels = labelEmbedding6 ∘ raw20655step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20655step1 raw20655step1Labels raw20655step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4153 node4153Labels := by rfl

def raw20656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20656step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20656step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20656step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20656 raw20656Labels = mixedMoment B node4528 node4528Labels := by
  calc
    mixedMoment B raw20656 raw20656Labels = mixedMoment B raw20656step0 raw20656step0Labels := by
      have ha : raw20656step0 = (fun i j => raw20656 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20656step0 raw20656; decide +kernel
      have hl : raw20656step0Labels = raw20656Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20656 raw20656Labels permutation160 permutation3
    mixedMoment B raw20656step0 raw20656step0Labels = mixedMoment B raw20656step1 raw20656step1Labels := by
      have ha : raw20656step1 = raw20656step0 := by apply Matrix.ext; unfold raw20656step1 raw20656step0; decide +kernel
      have hl : raw20656step0Labels = labelEmbedding6 ∘ raw20656step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20656step0 raw20656step0Labels raw20656step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4528 node4528Labels := by rfl

def raw20657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20657step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20657step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20657 raw20657Labels = mixedMoment B node4546 node4546Labels := by
  calc
    mixedMoment B raw20657 raw20657Labels = mixedMoment B raw20657step0 raw20657step0Labels := by
      have hz : ∀ j, raw20657 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20657step0 = (fun i j => raw20657 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20657step0 raw20657; decide +kernel
      have hl : raw20657step0Labels = raw20657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20657 raw20657Labels permutation265 hz
    mixedMoment B raw20657step0 raw20657step0Labels = mixedMoment B raw20657step1 raw20657step1Labels := by
      have ha : raw20657step1 = (fun i j => raw20657step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20657step1 raw20657step0; decide +kernel
      have hl : raw20657step1Labels = raw20657step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20657step0 raw20657step0Labels permutation38 permutation2
    _ = mixedMoment B node4546 node4546Labels := by rfl

def raw20658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20658step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20658step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20658 raw20658Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw20658 raw20658Labels = mixedMoment B raw20658step0 raw20658step0Labels := by
      have hz : ∀ j, raw20658 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20658step0 = (fun i j => raw20658 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20658step0 raw20658; decide +kernel
      have hl : raw20658step0Labels = raw20658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20658 raw20658Labels permutation265 hz
    mixedMoment B raw20658step0 raw20658step0Labels = mixedMoment B raw20658step1 raw20658step1Labels := by
      have ha : raw20658step1 = (fun i j => raw20658step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20658step1 raw20658step0; decide +kernel
      have hl : raw20658step1Labels = raw20658step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20658step0 raw20658step0Labels permutation40 permutation2
    _ = mixedMoment B node4591 node4591Labels := by rfl

def raw20659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20659step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20659step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20659step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20659step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20659step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20659step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20659 raw20659Labels = mixedMoment B node4178 node4178Labels := by
  calc
    mixedMoment B raw20659 raw20659Labels = mixedMoment B raw20659step0 raw20659step0Labels := by
      have hz : ∀ j, raw20659 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20659step0 = (fun i j => raw20659 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20659step0 raw20659; decide +kernel
      have hl : raw20659step0Labels = raw20659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20659 raw20659Labels permutation346 hz
    mixedMoment B raw20659step0 raw20659step0Labels = mixedMoment B raw20659step1 raw20659step1Labels := by
      have hz : ∀ j, raw20659step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20659step1 = (fun i j => raw20659step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20659step1 raw20659step0; decide +kernel
      have hl : raw20659step1Labels = raw20659step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20659step0 raw20659step0Labels permutation56 hz
    mixedMoment B raw20659step1 raw20659step1Labels = mixedMoment B raw20659step2 raw20659step2Labels := by
      have ha : raw20659step2 = (fun i j => raw20659step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20659step2 raw20659step1; decide +kernel
      have hl : raw20659step2Labels = raw20659step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20659step1 raw20659step1Labels permutation10 permutation3
    mixedMoment B raw20659step2 raw20659step2Labels = mixedMoment B raw20659step3 raw20659step3Labels := by
      have ha : raw20659step3 = raw20659step2 := by apply Matrix.ext; unfold raw20659step3 raw20659step2; decide +kernel
      have hl : raw20659step2Labels = labelEmbedding6 ∘ raw20659step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20659step2 raw20659step2Labels raw20659step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4178 node4178Labels := by rfl

def raw20660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20660step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20660step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20660step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20660step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20660 raw20660Labels = mixedMoment B node4547 node4547Labels := by
  calc
    mixedMoment B raw20660 raw20660Labels = mixedMoment B raw20660step0 raw20660step0Labels := by
      have hz : ∀ j, raw20660 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20660step0 = (fun i j => raw20660 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20660step0 raw20660; decide +kernel
      have hl : raw20660step0Labels = raw20660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20660 raw20660Labels permutation346 hz
    mixedMoment B raw20660step0 raw20660step0Labels = mixedMoment B raw20660step1 raw20660step1Labels := by
      have ha : raw20660step1 = (fun i j => raw20660step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20660step1 raw20660step0; decide +kernel
      have hl : raw20660step1Labels = raw20660step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20660step0 raw20660step0Labels permutation34 permutation3
    mixedMoment B raw20660step1 raw20660step1Labels = mixedMoment B raw20660step2 raw20660step2Labels := by
      have ha : raw20660step2 = raw20660step1 := by apply Matrix.ext; unfold raw20660step2 raw20660step1; decide +kernel
      have hl : raw20660step1Labels = labelEmbedding6 ∘ raw20660step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20660step1 raw20660step1Labels raw20660step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4547 node4547Labels := by rfl

def raw20661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20661Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20661step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20661step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20661step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20661step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20661 raw20661Labels = mixedMoment B node4547 node4547Labels := by
  calc
    mixedMoment B raw20661 raw20661Labels = mixedMoment B raw20661step0 raw20661step0Labels := by
      have hz : ∀ j, raw20661 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20661step0 = (fun i j => raw20661 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20661step0 raw20661; decide +kernel
      have hl : raw20661step0Labels = raw20661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20661 raw20661Labels permutation265 hz
    mixedMoment B raw20661step0 raw20661step0Labels = mixedMoment B raw20661step1 raw20661step1Labels := by
      have ha : raw20661step1 = (fun i j => raw20661step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20661step1 raw20661step0; decide +kernel
      have hl : raw20661step1Labels = raw20661step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20661step0 raw20661step0Labels permutation34 permutation3
    mixedMoment B raw20661step1 raw20661step1Labels = mixedMoment B raw20661step2 raw20661step2Labels := by
      have ha : raw20661step2 = raw20661step1 := by apply Matrix.ext; unfold raw20661step2 raw20661step1; decide +kernel
      have hl : raw20661step1Labels = labelEmbedding6 ∘ raw20661step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20661step1 raw20661step1Labels raw20661step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4547 node4547Labels := by rfl

def raw20662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20662step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20662step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20662step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20662step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20662step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20662step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20662step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20662 raw20662Labels = mixedMoment B node4609 node4609Labels := by
  calc
    mixedMoment B raw20662 raw20662Labels = mixedMoment B raw20662step0 raw20662step0Labels := by
      have hz : ∀ j, raw20662 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20662step0 = (fun i j => raw20662 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20662step0 raw20662; decide +kernel
      have hl : raw20662step0Labels = raw20662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20662 raw20662Labels permutation346 hz
    mixedMoment B raw20662step0 raw20662step0Labels = mixedMoment B raw20662step1 raw20662step1Labels := by
      have hz : ∀ j, raw20662step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20662step1 = (fun i j => raw20662step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20662step1 raw20662step0; decide +kernel
      have hl : raw20662step1Labels = raw20662step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20662step0 raw20662step0Labels permutation56 hz
    mixedMoment B raw20662step1 raw20662step1Labels = mixedMoment B raw20662step2 raw20662step2Labels := by
      have ha : raw20662step2 = (fun i j => raw20662step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20662step2 raw20662step1; decide +kernel
      have hl : raw20662step2Labels = raw20662step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20662step1 raw20662step1Labels permutation10 permutation3
    mixedMoment B raw20662step2 raw20662step2Labels = mixedMoment B raw20662step3 raw20662step3Labels := by
      have ha : raw20662step3 = raw20662step2 := by apply Matrix.ext; unfold raw20662step3 raw20662step2; decide +kernel
      have hl : raw20662step2Labels = labelEmbedding6 ∘ raw20662step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20662step2 raw20662step2Labels raw20662step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4609 node4609Labels := by rfl

def raw20663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20663step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20663step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20663step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20663step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw20663step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20663step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw20663step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20663 raw20663Labels = mixedMoment B node4161 node4161Labels := by
  calc
    mixedMoment B raw20663 raw20663Labels = mixedMoment B raw20663step0 raw20663step0Labels := by
      have hz : ∀ j, raw20663 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20663step0 = (fun i j => raw20663 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20663step0 raw20663; decide +kernel
      have hl : raw20663step0Labels = raw20663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20663 raw20663Labels permutation346 hz
    mixedMoment B raw20663step0 raw20663step0Labels = mixedMoment B raw20663step1 raw20663step1Labels := by
      have hz : ∀ j, raw20663step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20663step1 = (fun i j => raw20663step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20663step1 raw20663step0; decide +kernel
      have hl : raw20663step1Labels = raw20663step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20663step0 raw20663step0Labels permutation56 hz
    mixedMoment B raw20663step1 raw20663step1Labels = mixedMoment B raw20663step2 raw20663step2Labels := by
      have ha : raw20663step2 = (fun i j => raw20663step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20663step2 raw20663step1; decide +kernel
      have hl : raw20663step2Labels = raw20663step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20663step1 raw20663step1Labels permutation8 permutation3
    mixedMoment B raw20663step2 raw20663step2Labels = mixedMoment B raw20663step3 raw20663step3Labels := by
      have ha : raw20663step3 = raw20663step2 := by apply Matrix.ext; unfold raw20663step3 raw20663step2; decide +kernel
      have hl : raw20663step2Labels = labelEmbedding6 ∘ raw20663step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20663step2 raw20663step2Labels raw20663step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4161 node4161Labels := by rfl

def raw20664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20664step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw20664step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20664step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw20664step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20664 raw20664Labels = mixedMoment B node4535 node4535Labels := by
  calc
    mixedMoment B raw20664 raw20664Labels = mixedMoment B raw20664step0 raw20664step0Labels := by
      have hz : ∀ j, raw20664 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20664step0 = (fun i j => raw20664 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20664step0 raw20664; decide +kernel
      have hl : raw20664step0Labels = raw20664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20664 raw20664Labels permutation346 hz
    mixedMoment B raw20664step0 raw20664step0Labels = mixedMoment B raw20664step1 raw20664step1Labels := by
      have ha : raw20664step1 = (fun i j => raw20664step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20664step1 raw20664step0; decide +kernel
      have hl : raw20664step1Labels = raw20664step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20664step0 raw20664step0Labels permutation32 permutation3
    mixedMoment B raw20664step1 raw20664step1Labels = mixedMoment B raw20664step2 raw20664step2Labels := by
      have ha : raw20664step2 = raw20664step1 := by apply Matrix.ext; unfold raw20664step2 raw20664step1; decide +kernel
      have hl : raw20664step1Labels = labelEmbedding6 ∘ raw20664step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20664step1 raw20664step1Labels raw20664step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4535 node4535Labels := by rfl

def raw20665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw20665step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw20665step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20665 raw20665Labels = mixedMoment B node4535 node4535Labels := by
  calc
    mixedMoment B raw20665 raw20665Labels = mixedMoment B raw20665step0 raw20665step0Labels := by
      have hz : ∀ j, raw20665 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20665step0 = (fun i j => raw20665 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20665step0 raw20665; decide +kernel
      have hl : raw20665step0Labels = raw20665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20665 raw20665Labels permutation265 hz
    mixedMoment B raw20665step0 raw20665step0Labels = mixedMoment B raw20665step1 raw20665step1Labels := by
      have ha : raw20665step1 = (fun i j => raw20665step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20665step1 raw20665step0; decide +kernel
      have hl : raw20665step1Labels = raw20665step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20665step0 raw20665step0Labels permutation32 permutation3
    mixedMoment B raw20665step1 raw20665step1Labels = mixedMoment B raw20665step2 raw20665step2Labels := by
      have ha : raw20665step2 = raw20665step1 := by apply Matrix.ext; unfold raw20665step2 raw20665step1; decide +kernel
      have hl : raw20665step1Labels = labelEmbedding6 ∘ raw20665step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20665step1 raw20665step1Labels raw20665step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4535 node4535Labels := by rfl

def raw20666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20666step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20666step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20666step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20666 raw20666Labels = mixedMoment B node4558 node4558Labels := by
  calc
    mixedMoment B raw20666 raw20666Labels = mixedMoment B raw20666step0 raw20666step0Labels := by
      have hz : ∀ j, raw20666 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20666step0 = (fun i j => raw20666 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20666step0 raw20666; decide +kernel
      have hl : raw20666step0Labels = raw20666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20666 raw20666Labels permutation346 hz
    mixedMoment B raw20666step0 raw20666step0Labels = mixedMoment B raw20666step1 raw20666step1Labels := by
      have hz : ∀ j, raw20666step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20666step1 = (fun i j => raw20666step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20666step1 raw20666step0; decide +kernel
      have hl : raw20666step1Labels = raw20666step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20666step0 raw20666step0Labels permutation56 hz
    _ = mixedMoment B node4558 node4558Labels := by rfl

def raw20667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20667step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20667step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20667step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20667step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20667step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20667step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20667 raw20667Labels = mixedMoment B node4156 node4156Labels := by
  calc
    mixedMoment B raw20667 raw20667Labels = mixedMoment B raw20667step0 raw20667step0Labels := by
      have hz : ∀ j, raw20667 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20667step0 = (fun i j => raw20667 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20667step0 raw20667; decide +kernel
      have hl : raw20667step0Labels = raw20667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20667 raw20667Labels permutation346 hz
    mixedMoment B raw20667step0 raw20667step0Labels = mixedMoment B raw20667step1 raw20667step1Labels := by
      have hz : ∀ j, raw20667step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20667step1 = (fun i j => raw20667step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20667step1 raw20667step0; decide +kernel
      have hl : raw20667step1Labels = raw20667step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20667step0 raw20667step0Labels permutation56 hz
    mixedMoment B raw20667step1 raw20667step1Labels = mixedMoment B raw20667step2 raw20667step2Labels := by
      have ha : raw20667step2 = (fun i j => raw20667step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20667step2 raw20667step1; decide +kernel
      have hl : raw20667step2Labels = raw20667step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20667step1 raw20667step1Labels permutation8 permutation3
    mixedMoment B raw20667step2 raw20667step2Labels = mixedMoment B raw20667step3 raw20667step3Labels := by
      have ha : raw20667step3 = raw20667step2 := by apply Matrix.ext; unfold raw20667step3 raw20667step2; decide +kernel
      have hl : raw20667step2Labels = labelEmbedding6 ∘ raw20667step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20667step2 raw20667step2Labels raw20667step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4156 node4156Labels := by rfl

def raw20668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw20668step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20668step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20668step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20668 raw20668Labels = mixedMoment B node4531 node4531Labels := by
  calc
    mixedMoment B raw20668 raw20668Labels = mixedMoment B raw20668step0 raw20668step0Labels := by
      have hz : ∀ j, raw20668 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20668step0 = (fun i j => raw20668 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20668step0 raw20668; decide +kernel
      have hl : raw20668step0Labels = raw20668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20668 raw20668Labels permutation346 hz
    mixedMoment B raw20668step0 raw20668step0Labels = mixedMoment B raw20668step1 raw20668step1Labels := by
      have ha : raw20668step1 = (fun i j => raw20668step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20668step1 raw20668step0; decide +kernel
      have hl : raw20668step1Labels = raw20668step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20668step0 raw20668step0Labels permutation151 permutation2
    mixedMoment B raw20668step1 raw20668step1Labels = mixedMoment B raw20668step2 raw20668step2Labels := by
      have ha : raw20668step2 = -raw20668step1 := by apply Matrix.ext; change ∀ i j, raw20668step2 i j = -(raw20668step1 i j); unfold raw20668step2 raw20668step1; decide +kernel
      have hl : raw20668step2Labels = raw20668step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4531 node4531Labels := by rfl

def raw20669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw20669step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20669step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20669 raw20669Labels = mixedMoment B node4531 node4531Labels := by
  calc
    mixedMoment B raw20669 raw20669Labels = mixedMoment B raw20669step0 raw20669step0Labels := by
      have hz : ∀ j, raw20669 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20669step0 = (fun i j => raw20669 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20669step0 raw20669; decide +kernel
      have hl : raw20669step0Labels = raw20669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20669 raw20669Labels permutation265 hz
    mixedMoment B raw20669step0 raw20669step0Labels = mixedMoment B raw20669step1 raw20669step1Labels := by
      have ha : raw20669step1 = (fun i j => raw20669step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20669step1 raw20669step0; decide +kernel
      have hl : raw20669step1Labels = raw20669step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20669step0 raw20669step0Labels permutation151 permutation2
    mixedMoment B raw20669step1 raw20669step1Labels = mixedMoment B raw20669step2 raw20669step2Labels := by
      have ha : raw20669step2 = -raw20669step1 := by apply Matrix.ext; change ∀ i j, raw20669step2 i j = -(raw20669step1 i j); unfold raw20669step2 raw20669step1; decide +kernel
      have hl : raw20669step2Labels = raw20669step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4531 node4531Labels := by rfl

def raw20670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20670step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20670step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20670step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20670 raw20670Labels = mixedMoment B node4555 node4555Labels := by
  calc
    mixedMoment B raw20670 raw20670Labels = mixedMoment B raw20670step0 raw20670step0Labels := by
      have hz : ∀ j, raw20670 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20670step0 = (fun i j => raw20670 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20670step0 raw20670; decide +kernel
      have hl : raw20670step0Labels = raw20670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20670 raw20670Labels permutation346 hz
    mixedMoment B raw20670step0 raw20670step0Labels = mixedMoment B raw20670step1 raw20670step1Labels := by
      have hz : ∀ j, raw20670step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20670step1 = (fun i j => raw20670step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20670step1 raw20670step0; decide +kernel
      have hl : raw20670step1Labels = raw20670step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20670step0 raw20670step0Labels permutation56 hz
    _ = mixedMoment B node4555 node4555Labels := by rfl

def raw20671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw20671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw20671step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20671step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw20671step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20671 raw20671Labels = mixedMoment B node4594 node4594Labels := by
  calc
    mixedMoment B raw20671 raw20671Labels = mixedMoment B raw20671step0 raw20671step0Labels := by
      have hz : ∀ j, raw20671 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20671step0 = (fun i j => raw20671 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20671step0 raw20671; decide +kernel
      have hl : raw20671step0Labels = raw20671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20671 raw20671Labels permutation346 hz
    mixedMoment B raw20671step0 raw20671step0Labels = mixedMoment B raw20671step1 raw20671step1Labels := by
      have hz : ∀ j, raw20671step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20671step1 = (fun i j => raw20671step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20671step1 raw20671step0; decide +kernel
      have hl : raw20671step1Labels = raw20671step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20671step0 raw20671step0Labels permutation56 hz
    _ = mixedMoment B node4594 node4594Labels := by rfl

def raw20672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20672Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20672step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20672step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20672step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20672 raw20672Labels = mixedMoment B node2939 node2939Labels := by
  calc
    mixedMoment B raw20672 raw20672Labels = mixedMoment B raw20672step0 raw20672step0Labels := by
      have hz : ∀ j, raw20672 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20672step0 = (fun i j => raw20672 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20672step0 raw20672; decide +kernel
      have hl : raw20672step0Labels = raw20672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20672 raw20672Labels permutation346 hz
    mixedMoment B raw20672step0 raw20672step0Labels = mixedMoment B raw20672step1 raw20672step1Labels := by
      have ha : raw20672step1 = (fun i j => raw20672step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20672step1 raw20672step0; decide +kernel
      have hl : raw20672step1Labels = raw20672step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20672step0 raw20672step0Labels permutation32 permutation3
    _ = mixedMoment B node2939 node2939Labels := by rfl

def raw20673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20673Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20673step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20673step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20673 raw20673Labels = mixedMoment B node2939 node2939Labels := by
  calc
    mixedMoment B raw20673 raw20673Labels = mixedMoment B raw20673step0 raw20673step0Labels := by
      have hz : ∀ j, raw20673 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20673step0 = (fun i j => raw20673 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20673step0 raw20673; decide +kernel
      have hl : raw20673step0Labels = raw20673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20673 raw20673Labels permutation265 hz
    mixedMoment B raw20673step0 raw20673step0Labels = mixedMoment B raw20673step1 raw20673step1Labels := by
      have ha : raw20673step1 = (fun i j => raw20673step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20673step1 raw20673step0; decide +kernel
      have hl : raw20673step1Labels = raw20673step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20673step0 raw20673step0Labels permutation32 permutation3
    _ = mixedMoment B node2939 node2939Labels := by rfl

def raw20674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20674Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20674step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20674step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20674step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20674step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw20674step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20674 raw20674Labels = mixedMoment B node3002 node3002Labels := by
  calc
    mixedMoment B raw20674 raw20674Labels = mixedMoment B raw20674step0 raw20674step0Labels := by
      have hz : ∀ j, raw20674 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20674step0 = (fun i j => raw20674 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20674step0 raw20674; decide +kernel
      have hl : raw20674step0Labels = raw20674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20674 raw20674Labels permutation346 hz
    mixedMoment B raw20674step0 raw20674step0Labels = mixedMoment B raw20674step1 raw20674step1Labels := by
      have hz : ∀ j, raw20674step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20674step1 = (fun i j => raw20674step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20674step1 raw20674step0; decide +kernel
      have hl : raw20674step1Labels = raw20674step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20674step0 raw20674step0Labels permutation56 hz
    mixedMoment B raw20674step1 raw20674step1Labels = mixedMoment B raw20674step2 raw20674step2Labels := by
      have ha : raw20674step2 = (fun i j => raw20674step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20674step2 raw20674step1; decide +kernel
      have hl : raw20674step2Labels = raw20674step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20674step1 raw20674step1Labels permutation8 permutation3
    _ = mixedMoment B node3002 node3002Labels := by rfl

def raw20675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20675Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20675step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20675step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20675step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20675step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw20675step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20675 raw20675Labels = mixedMoment B node3090 node3090Labels := by
  calc
    mixedMoment B raw20675 raw20675Labels = mixedMoment B raw20675step0 raw20675step0Labels := by
      have hz : ∀ j, raw20675 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20675step0 = (fun i j => raw20675 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20675step0 raw20675; decide +kernel
      have hl : raw20675step0Labels = raw20675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20675 raw20675Labels permutation346 hz
    mixedMoment B raw20675step0 raw20675step0Labels = mixedMoment B raw20675step1 raw20675step1Labels := by
      have hz : ∀ j, raw20675step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20675step1 = (fun i j => raw20675step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20675step1 raw20675step0; decide +kernel
      have hl : raw20675step1Labels = raw20675step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20675step0 raw20675step0Labels permutation56 hz
    mixedMoment B raw20675step1 raw20675step1Labels = mixedMoment B raw20675step2 raw20675step2Labels := by
      have ha : raw20675step2 = (fun i j => raw20675step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20675step2 raw20675step1; decide +kernel
      have hl : raw20675step2Labels = raw20675step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20675step1 raw20675step1Labels permutation10 permutation3
    _ = mixedMoment B node3090 node3090Labels := by rfl

def raw20676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20676Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20676step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20676step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20676step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20676step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw20676step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20676 raw20676Labels = mixedMoment B node3112 node3112Labels := by
  calc
    mixedMoment B raw20676 raw20676Labels = mixedMoment B raw20676step0 raw20676step0Labels := by
      have hz : ∀ j, raw20676 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20676step0 = (fun i j => raw20676 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20676step0 raw20676; decide +kernel
      have hl : raw20676step0Labels = raw20676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20676 raw20676Labels permutation346 hz
    mixedMoment B raw20676step0 raw20676step0Labels = mixedMoment B raw20676step1 raw20676step1Labels := by
      have hz : ∀ j, raw20676step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20676step1 = (fun i j => raw20676step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20676step1 raw20676step0; decide +kernel
      have hl : raw20676step1Labels = raw20676step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20676step0 raw20676step0Labels permutation56 hz
    mixedMoment B raw20676step1 raw20676step1Labels = mixedMoment B raw20676step2 raw20676step2Labels := by
      have ha : raw20676step2 = (fun i j => raw20676step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20676step2 raw20676step1; decide +kernel
      have hl : raw20676step2Labels = raw20676step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20676step1 raw20676step1Labels permutation8 permutation3
    _ = mixedMoment B node3112 node3112Labels := by rfl

def raw20677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20677Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20677step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20677step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20677 raw20677Labels = mixedMoment B node581 node581Labels := by
  calc
    mixedMoment B raw20677 raw20677Labels = mixedMoment B raw20677step0 raw20677step0Labels := by
      have hz : ∀ j, raw20677 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20677step0 = (fun i j => raw20677 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20677step0 raw20677; decide +kernel
      have hl : raw20677step0Labels = raw20677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20677 raw20677Labels permutation346 hz
    mixedMoment B raw20677step0 raw20677step0Labels = mixedMoment B raw20677step1 raw20677step1Labels := by
      have ha : raw20677step1 = (fun i j => raw20677step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20677step1 raw20677step0; decide +kernel
      have hl : raw20677step1Labels = raw20677step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20677step0 raw20677step0Labels permutation40 permutation3
    _ = mixedMoment B node581 node581Labels := by rfl

def raw20678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20678Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20678step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20678step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20678 raw20678Labels = mixedMoment B node1112 node1112Labels := by
  calc
    mixedMoment B raw20678 raw20678Labels = mixedMoment B raw20678step0 raw20678step0Labels := by
      have ha : raw20678step0 = (fun i j => raw20678 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20678step0 raw20678; decide +kernel
      have hl : raw20678step0Labels = raw20678Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20678 raw20678Labels permutation184 permutation3
    _ = mixedMoment B node1112 node1112Labels := by rfl

def raw20679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20679Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20679step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20679step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20679step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20679 raw20679Labels = mixedMoment B node1165 node1165Labels := by
  calc
    mixedMoment B raw20679 raw20679Labels = mixedMoment B raw20679step0 raw20679step0Labels := by
      have hz : ∀ j, raw20679 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20679step0 = (fun i j => raw20679 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20679step0 raw20679; decide +kernel
      have hl : raw20679step0Labels = raw20679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20679 raw20679Labels permutation346 hz
    mixedMoment B raw20679step0 raw20679step0Labels = mixedMoment B raw20679step1 raw20679step1Labels := by
      have ha : raw20679step1 = (fun i j => raw20679step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20679step1 raw20679step0; decide +kernel
      have hl : raw20679step1Labels = raw20679step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20679step0 raw20679step0Labels permutation40 permutation3
    _ = mixedMoment B node1165 node1165Labels := by rfl

def raw20680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20680Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20680step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20680step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20680 raw20680Labels = mixedMoment B node1217 node1217Labels := by
  calc
    mixedMoment B raw20680 raw20680Labels = mixedMoment B raw20680step0 raw20680step0Labels := by
      have hz : ∀ j, raw20680 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20680step0 = (fun i j => raw20680 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20680step0 raw20680; decide +kernel
      have hl : raw20680step0Labels = raw20680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20680 raw20680Labels permutation346 hz
    mixedMoment B raw20680step0 raw20680step0Labels = mixedMoment B raw20680step1 raw20680step1Labels := by
      have ha : raw20680step1 = (fun i j => raw20680step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20680step1 raw20680step0; decide +kernel
      have hl : raw20680step1Labels = raw20680step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20680step0 raw20680step0Labels permutation46 permutation3
    _ = mixedMoment B node1217 node1217Labels := by rfl

def raw20681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20681Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20681step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw20681step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20681 raw20681Labels = mixedMoment B node1267 node1267Labels := by
  calc
    mixedMoment B raw20681 raw20681Labels = mixedMoment B raw20681step0 raw20681step0Labels := by
      have hz : ∀ j, raw20681 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20681step0 = (fun i j => raw20681 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20681step0 raw20681; decide +kernel
      have hl : raw20681step0Labels = raw20681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20681 raw20681Labels permutation346 hz
    mixedMoment B raw20681step0 raw20681step0Labels = mixedMoment B raw20681step1 raw20681step1Labels := by
      have ha : raw20681step1 = (fun i j => raw20681step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20681step1 raw20681step0; decide +kernel
      have hl : raw20681step1Labels = raw20681step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20681step0 raw20681step0Labels permutation40 permutation3
    _ = mixedMoment B node1267 node1267Labels := by rfl

def raw20682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20682Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20682step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20682step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20682 raw20682Labels = mixedMoment B node581 node581Labels := by
  calc
    mixedMoment B raw20682 raw20682Labels = mixedMoment B raw20682step0 raw20682step0Labels := by
      have hz : ∀ j, raw20682 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20682step0 = (fun i j => raw20682 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20682step0 raw20682; decide +kernel
      have hl : raw20682step0Labels = raw20682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20682 raw20682Labels permutation265 hz
    mixedMoment B raw20682step0 raw20682step0Labels = mixedMoment B raw20682step1 raw20682step1Labels := by
      have ha : raw20682step1 = (fun i j => raw20682step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20682step1 raw20682step0; decide +kernel
      have hl : raw20682step1Labels = raw20682step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20682step0 raw20682step0Labels permutation40 permutation3
    _ = mixedMoment B node581 node581Labels := by rfl

def raw20683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20683Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20683step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20683step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20683 raw20683Labels = mixedMoment B node1112 node1112Labels := by
  calc
    mixedMoment B raw20683 raw20683Labels = mixedMoment B raw20683step0 raw20683step0Labels := by
      have ha : raw20683step0 = (fun i j => raw20683 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20683step0 raw20683; decide +kernel
      have hl : raw20683step0Labels = raw20683Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20683 raw20683Labels permutation160 permutation3
    _ = mixedMoment B node1112 node1112Labels := by rfl

def raw20684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20684Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20684step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20684step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20684 raw20684Labels = mixedMoment B node1165 node1165Labels := by
  calc
    mixedMoment B raw20684 raw20684Labels = mixedMoment B raw20684step0 raw20684step0Labels := by
      have hz : ∀ j, raw20684 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20684step0 = (fun i j => raw20684 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20684step0 raw20684; decide +kernel
      have hl : raw20684step0Labels = raw20684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20684 raw20684Labels permutation265 hz
    mixedMoment B raw20684step0 raw20684step0Labels = mixedMoment B raw20684step1 raw20684step1Labels := by
      have ha : raw20684step1 = (fun i j => raw20684step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20684step1 raw20684step0; decide +kernel
      have hl : raw20684step1Labels = raw20684step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20684step0 raw20684step0Labels permutation40 permutation3
    _ = mixedMoment B node1165 node1165Labels := by rfl

def raw20685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20685Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20685step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20685step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20685 raw20685Labels = mixedMoment B node1217 node1217Labels := by
  calc
    mixedMoment B raw20685 raw20685Labels = mixedMoment B raw20685step0 raw20685step0Labels := by
      have hz : ∀ j, raw20685 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20685step0 = (fun i j => raw20685 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20685step0 raw20685; decide +kernel
      have hl : raw20685step0Labels = raw20685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20685 raw20685Labels permutation265 hz
    mixedMoment B raw20685step0 raw20685step0Labels = mixedMoment B raw20685step1 raw20685step1Labels := by
      have ha : raw20685step1 = (fun i j => raw20685step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20685step1 raw20685step0; decide +kernel
      have hl : raw20685step1Labels = raw20685step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20685step0 raw20685step0Labels permutation46 permutation3
    _ = mixedMoment B node1217 node1217Labels := by rfl

def raw20686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20686Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20686step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw20686step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20686 raw20686Labels = mixedMoment B node1267 node1267Labels := by
  calc
    mixedMoment B raw20686 raw20686Labels = mixedMoment B raw20686step0 raw20686step0Labels := by
      have hz : ∀ j, raw20686 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20686step0 = (fun i j => raw20686 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20686step0 raw20686; decide +kernel
      have hl : raw20686step0Labels = raw20686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20686 raw20686Labels permutation265 hz
    mixedMoment B raw20686step0 raw20686step0Labels = mixedMoment B raw20686step1 raw20686step1Labels := by
      have ha : raw20686step1 = (fun i j => raw20686step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20686step1 raw20686step0; decide +kernel
      have hl : raw20686step1Labels = raw20686step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20686step0 raw20686step0Labels permutation40 permutation3
    _ = mixedMoment B node1267 node1267Labels := by rfl

def raw20687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20687Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20687step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20687step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20687step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20687step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20687step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20687 raw20687Labels = mixedMoment B node606 node606Labels := by
  calc
    mixedMoment B raw20687 raw20687Labels = mixedMoment B raw20687step0 raw20687step0Labels := by
      have hz : ∀ j, raw20687 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20687step0 = (fun i j => raw20687 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20687step0 raw20687; decide +kernel
      have hl : raw20687step0Labels = raw20687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20687 raw20687Labels permutation346 hz
    mixedMoment B raw20687step0 raw20687step0Labels = mixedMoment B raw20687step1 raw20687step1Labels := by
      have hz : ∀ j, raw20687step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20687step1 = (fun i j => raw20687step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20687step1 raw20687step0; decide +kernel
      have hl : raw20687step1Labels = raw20687step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20687step0 raw20687step0Labels permutation56 hz
    mixedMoment B raw20687step1 raw20687step1Labels = mixedMoment B raw20687step2 raw20687step2Labels := by
      have ha : raw20687step2 = (fun i j => raw20687step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20687step2 raw20687step1; decide +kernel
      have hl : raw20687step2Labels = raw20687step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20687step1 raw20687step1Labels permutation10 permutation3
    _ = mixedMoment B node606 node606Labels := by rfl

def raw20688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20688Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20688step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20688step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20688 raw20688Labels = mixedMoment B node1132 node1132Labels := by
  calc
    mixedMoment B raw20688 raw20688Labels = mixedMoment B raw20688step0 raw20688step0Labels := by
      have hz : ∀ j, raw20688 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20688step0 = (fun i j => raw20688 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20688step0 raw20688; decide +kernel
      have hl : raw20688step0Labels = raw20688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20688 raw20688Labels permutation346 hz
    mixedMoment B raw20688step0 raw20688step0Labels = mixedMoment B raw20688step1 raw20688step1Labels := by
      have ha : raw20688step1 = (fun i j => raw20688step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20688step1 raw20688step0; decide +kernel
      have hl : raw20688step1Labels = raw20688step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20688step0 raw20688step0Labels permutation34 permutation3
    _ = mixedMoment B node1132 node1132Labels := by rfl

def raw20689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20689Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20689step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20689step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20689 raw20689Labels = mixedMoment B node1132 node1132Labels := by
  calc
    mixedMoment B raw20689 raw20689Labels = mixedMoment B raw20689step0 raw20689step0Labels := by
      have hz : ∀ j, raw20689 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20689step0 = (fun i j => raw20689 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20689step0 raw20689; decide +kernel
      have hl : raw20689step0Labels = raw20689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20689 raw20689Labels permutation265 hz
    mixedMoment B raw20689step0 raw20689step0Labels = mixedMoment B raw20689step1 raw20689step1Labels := by
      have ha : raw20689step1 = (fun i j => raw20689step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20689step1 raw20689step0; decide +kernel
      have hl : raw20689step1Labels = raw20689step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20689step0 raw20689step0Labels permutation34 permutation3
    _ = mixedMoment B node1132 node1132Labels := by rfl

def raw20690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20690Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20690step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20690step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20690step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20690step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20690step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20690 raw20690Labels = mixedMoment B node1243 node1243Labels := by
  calc
    mixedMoment B raw20690 raw20690Labels = mixedMoment B raw20690step0 raw20690step0Labels := by
      have hz : ∀ j, raw20690 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20690step0 = (fun i j => raw20690 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20690step0 raw20690; decide +kernel
      have hl : raw20690step0Labels = raw20690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20690 raw20690Labels permutation346 hz
    mixedMoment B raw20690step0 raw20690step0Labels = mixedMoment B raw20690step1 raw20690step1Labels := by
      have hz : ∀ j, raw20690step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20690step1 = (fun i j => raw20690step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20690step1 raw20690step0; decide +kernel
      have hl : raw20690step1Labels = raw20690step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20690step0 raw20690step0Labels permutation56 hz
    mixedMoment B raw20690step1 raw20690step1Labels = mixedMoment B raw20690step2 raw20690step2Labels := by
      have ha : raw20690step2 = (fun i j => raw20690step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20690step2 raw20690step1; decide +kernel
      have hl : raw20690step2Labels = raw20690step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20690step1 raw20690step1Labels permutation10 permutation3
    _ = mixedMoment B node1243 node1243Labels := by rfl

def raw20691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20691Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20691step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20691step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20691step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20691step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw20691step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20691 raw20691Labels = mixedMoment B node1302 node1302Labels := by
  calc
    mixedMoment B raw20691 raw20691Labels = mixedMoment B raw20691step0 raw20691step0Labels := by
      have hz : ∀ j, raw20691 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20691step0 = (fun i j => raw20691 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20691step0 raw20691; decide +kernel
      have hl : raw20691step0Labels = raw20691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20691 raw20691Labels permutation346 hz
    mixedMoment B raw20691step0 raw20691step0Labels = mixedMoment B raw20691step1 raw20691step1Labels := by
      have hz : ∀ j, raw20691step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20691step1 = (fun i j => raw20691step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20691step1 raw20691step0; decide +kernel
      have hl : raw20691step1Labels = raw20691step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20691step0 raw20691step0Labels permutation56 hz
    mixedMoment B raw20691step1 raw20691step1Labels = mixedMoment B raw20691step2 raw20691step2Labels := by
      have ha : raw20691step2 = (fun i j => raw20691step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20691step2 raw20691step1; decide +kernel
      have hl : raw20691step2Labels = raw20691step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20691step1 raw20691step1Labels permutation10 permutation3
    _ = mixedMoment B node1302 node1302Labels := by rfl

def raw20692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20692Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20692step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20692step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20692step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20692step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw20692step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20692 raw20692Labels = mixedMoment B node589 node589Labels := by
  calc
    mixedMoment B raw20692 raw20692Labels = mixedMoment B raw20692step0 raw20692step0Labels := by
      have hz : ∀ j, raw20692 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20692step0 = (fun i j => raw20692 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20692step0 raw20692; decide +kernel
      have hl : raw20692step0Labels = raw20692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20692 raw20692Labels permutation346 hz
    mixedMoment B raw20692step0 raw20692step0Labels = mixedMoment B raw20692step1 raw20692step1Labels := by
      have hz : ∀ j, raw20692step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20692step1 = (fun i j => raw20692step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20692step1 raw20692step0; decide +kernel
      have hl : raw20692step1Labels = raw20692step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20692step0 raw20692step0Labels permutation56 hz
    mixedMoment B raw20692step1 raw20692step1Labels = mixedMoment B raw20692step2 raw20692step2Labels := by
      have ha : raw20692step2 = (fun i j => raw20692step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20692step2 raw20692step1; decide +kernel
      have hl : raw20692step2Labels = raw20692step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20692step1 raw20692step1Labels permutation8 permutation3
    _ = mixedMoment B node589 node589Labels := by rfl

def raw20693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20693Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20693step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw20693step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20693 raw20693Labels = mixedMoment B node1120 node1120Labels := by
  calc
    mixedMoment B raw20693 raw20693Labels = mixedMoment B raw20693step0 raw20693step0Labels := by
      have hz : ∀ j, raw20693 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20693step0 = (fun i j => raw20693 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20693step0 raw20693; decide +kernel
      have hl : raw20693step0Labels = raw20693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20693 raw20693Labels permutation346 hz
    mixedMoment B raw20693step0 raw20693step0Labels = mixedMoment B raw20693step1 raw20693step1Labels := by
      have ha : raw20693step1 = (fun i j => raw20693step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20693step1 raw20693step0; decide +kernel
      have hl : raw20693step1Labels = raw20693step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20693step0 raw20693step0Labels permutation32 permutation3
    _ = mixedMoment B node1120 node1120Labels := by rfl

def raw20694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20694Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20694step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw20694step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20694 raw20694Labels = mixedMoment B node1120 node1120Labels := by
  calc
    mixedMoment B raw20694 raw20694Labels = mixedMoment B raw20694step0 raw20694step0Labels := by
      have hz : ∀ j, raw20694 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20694step0 = (fun i j => raw20694 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20694step0 raw20694; decide +kernel
      have hl : raw20694step0Labels = raw20694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20694 raw20694Labels permutation265 hz
    mixedMoment B raw20694step0 raw20694step0Labels = mixedMoment B raw20694step1 raw20694step1Labels := by
      have ha : raw20694step1 = (fun i j => raw20694step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20694step1 raw20694step0; decide +kernel
      have hl : raw20694step1Labels = raw20694step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20694step0 raw20694step0Labels permutation32 permutation3
    _ = mixedMoment B node1120 node1120Labels := by rfl

def raw20695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20695Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20695step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20695step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20695step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20695step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20695step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20695 raw20695Labels = mixedMoment B node1176 node1176Labels := by
  calc
    mixedMoment B raw20695 raw20695Labels = mixedMoment B raw20695step0 raw20695step0Labels := by
      have hz : ∀ j, raw20695 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20695step0 = (fun i j => raw20695 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20695step0 raw20695; decide +kernel
      have hl : raw20695step0Labels = raw20695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20695 raw20695Labels permutation346 hz
    mixedMoment B raw20695step0 raw20695step0Labels = mixedMoment B raw20695step1 raw20695step1Labels := by
      have hz : ∀ j, raw20695step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20695step1 = (fun i j => raw20695step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20695step1 raw20695step0; decide +kernel
      have hl : raw20695step1Labels = raw20695step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20695step0 raw20695step0Labels permutation56 hz
    mixedMoment B raw20695step1 raw20695step1Labels = mixedMoment B raw20695step2 raw20695step2Labels := by
      have ha : raw20695step2 = (fun i j => raw20695step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20695step2 raw20695step1; decide +kernel
      have hl : raw20695step2Labels = raw20695step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20695step1 raw20695step1Labels permutation8 permutation3
    _ = mixedMoment B node1176 node1176Labels := by rfl

def raw20696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw20696Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw20696step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20696step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw20696step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20696step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw20696step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20696 raw20696Labels = mixedMoment B node1274 node1274Labels := by
  calc
    mixedMoment B raw20696 raw20696Labels = mixedMoment B raw20696step0 raw20696step0Labels := by
      have hz : ∀ j, raw20696 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20696step0 = (fun i j => raw20696 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20696step0 raw20696; decide +kernel
      have hl : raw20696step0Labels = raw20696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20696 raw20696Labels permutation346 hz
    mixedMoment B raw20696step0 raw20696step0Labels = mixedMoment B raw20696step1 raw20696step1Labels := by
      have hz : ∀ j, raw20696step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20696step1 = (fun i j => raw20696step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20696step1 raw20696step0; decide +kernel
      have hl : raw20696step1Labels = raw20696step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20696step0 raw20696step0Labels permutation56 hz
    mixedMoment B raw20696step1 raw20696step1Labels = mixedMoment B raw20696step2 raw20696step2Labels := by
      have ha : raw20696step2 = (fun i j => raw20696step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20696step2 raw20696step1; decide +kernel
      have hl : raw20696step2Labels = raw20696step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20696step1 raw20696step1Labels permutation9 permutation3
    _ = mixedMoment B node1274 node1274Labels := by rfl

def raw20697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20697Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20697step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20697step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20697step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20697step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20697step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20697 raw20697Labels = mixedMoment B node584 node584Labels := by
  calc
    mixedMoment B raw20697 raw20697Labels = mixedMoment B raw20697step0 raw20697step0Labels := by
      have hz : ∀ j, raw20697 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20697step0 = (fun i j => raw20697 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20697step0 raw20697; decide +kernel
      have hl : raw20697step0Labels = raw20697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20697 raw20697Labels permutation346 hz
    mixedMoment B raw20697step0 raw20697step0Labels = mixedMoment B raw20697step1 raw20697step1Labels := by
      have hz : ∀ j, raw20697step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20697step1 = (fun i j => raw20697step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20697step1 raw20697step0; decide +kernel
      have hl : raw20697step1Labels = raw20697step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20697step0 raw20697step0Labels permutation56 hz
    mixedMoment B raw20697step1 raw20697step1Labels = mixedMoment B raw20697step2 raw20697step2Labels := by
      have ha : raw20697step2 = (fun i j => raw20697step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20697step2 raw20697step1; decide +kernel
      have hl : raw20697step2Labels = raw20697step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20697step1 raw20697step1Labels permutation8 permutation3
    _ = mixedMoment B node584 node584Labels := by rfl

def raw20698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20698Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20698step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20698step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20698 raw20698Labels = mixedMoment B node1115 node1115Labels := by
  calc
    mixedMoment B raw20698 raw20698Labels = mixedMoment B raw20698step0 raw20698step0Labels := by
      have hz : ∀ j, raw20698 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20698step0 = (fun i j => raw20698 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20698step0 raw20698; decide +kernel
      have hl : raw20698step0Labels = raw20698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20698 raw20698Labels permutation346 hz
    mixedMoment B raw20698step0 raw20698step0Labels = mixedMoment B raw20698step1 raw20698step1Labels := by
      have ha : raw20698step1 = (fun i j => raw20698step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20698step1 raw20698step0; decide +kernel
      have hl : raw20698step1Labels = raw20698step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20698step0 raw20698step0Labels permutation32 permutation3
    _ = mixedMoment B node1115 node1115Labels := by rfl

def raw20699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20699Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20699step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20699 raw20699Labels = mixedMoment B node1115 node1115Labels := by
  calc
    mixedMoment B raw20699 raw20699Labels = mixedMoment B raw20699step0 raw20699step0Labels := by
      have hz : ∀ j, raw20699 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20699step0 = (fun i j => raw20699 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20699step0 raw20699; decide +kernel
      have hl : raw20699step0Labels = raw20699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20699 raw20699Labels permutation265 hz
    mixedMoment B raw20699step0 raw20699step0Labels = mixedMoment B raw20699step1 raw20699step1Labels := by
      have ha : raw20699step1 = (fun i j => raw20699step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20699step1 raw20699step0; decide +kernel
      have hl : raw20699step1Labels = raw20699step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20699step0 raw20699step0Labels permutation32 permutation3
    _ = mixedMoment B node1115 node1115Labels := by rfl

def raw20700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20700Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20700step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20700step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20700step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20700step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw20700step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20700 raw20700Labels = mixedMoment B node1168 node1168Labels := by
  calc
    mixedMoment B raw20700 raw20700Labels = mixedMoment B raw20700step0 raw20700step0Labels := by
      have hz : ∀ j, raw20700 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20700step0 = (fun i j => raw20700 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20700step0 raw20700; decide +kernel
      have hl : raw20700step0Labels = raw20700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20700 raw20700Labels permutation346 hz
    mixedMoment B raw20700step0 raw20700step0Labels = mixedMoment B raw20700step1 raw20700step1Labels := by
      have hz : ∀ j, raw20700step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20700step1 = (fun i j => raw20700step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20700step1 raw20700step0; decide +kernel
      have hl : raw20700step1Labels = raw20700step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20700step0 raw20700step0Labels permutation56 hz
    mixedMoment B raw20700step1 raw20700step1Labels = mixedMoment B raw20700step2 raw20700step2Labels := by
      have ha : raw20700step2 = (fun i j => raw20700step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20700step2 raw20700step1; decide +kernel
      have hl : raw20700step2Labels = raw20700step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20700step1 raw20700step1Labels permutation8 permutation3
    _ = mixedMoment B node1168 node1168Labels := by rfl

def raw20701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw20701Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw20701step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20701step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw20701step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20701step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw20701step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20701 raw20701Labels = mixedMoment B node1221 node1221Labels := by
  calc
    mixedMoment B raw20701 raw20701Labels = mixedMoment B raw20701step0 raw20701step0Labels := by
      have hz : ∀ j, raw20701 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20701step0 = (fun i j => raw20701 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20701step0 raw20701; decide +kernel
      have hl : raw20701step0Labels = raw20701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20701 raw20701Labels permutation346 hz
    mixedMoment B raw20701step0 raw20701step0Labels = mixedMoment B raw20701step1 raw20701step1Labels := by
      have hz : ∀ j, raw20701step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20701step1 = (fun i j => raw20701step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20701step1 raw20701step0; decide +kernel
      have hl : raw20701step1Labels = raw20701step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20701step0 raw20701step0Labels permutation56 hz
    mixedMoment B raw20701step1 raw20701step1Labels = mixedMoment B raw20701step2 raw20701step2Labels := by
      have ha : raw20701step2 = (fun i j => raw20701step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20701step2 raw20701step1; decide +kernel
      have hl : raw20701step2Labels = raw20701step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20701step1 raw20701step1Labels permutation10 permutation3
    _ = mixedMoment B node1221 node1221Labels := by rfl

def raw20702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20702Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20702step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20702step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20702step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20702step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20702step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20702 raw20702Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw20702 raw20702Labels = mixedMoment B raw20702step0 raw20702step0Labels := by
      have hz : ∀ j, raw20702 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20702step0 = (fun i j => raw20702 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20702step0 raw20702; decide +kernel
      have hl : raw20702step0Labels = raw20702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20702 raw20702Labels permutation346 hz
    mixedMoment B raw20702step0 raw20702step0Labels = mixedMoment B raw20702step1 raw20702step1Labels := by
      have ha : raw20702step1 = (fun i j => raw20702step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20702step1 raw20702step0; decide +kernel
      have hl : raw20702step1Labels = raw20702step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20702step0 raw20702step0Labels permutation149 permutation7
    mixedMoment B raw20702step1 raw20702step1Labels = mixedMoment B raw20702step2 raw20702step2Labels := by
      have ha : raw20702step2 = raw20702step1 := by apply Matrix.ext; unfold raw20702step2 raw20702step1; decide +kernel
      have hl : raw20702step1Labels = labelEmbedding1 ∘ raw20702step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20702step1 raw20702step1Labels raw20702step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3468 node3468Labels := by rfl

def raw20703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20703Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20703step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20703step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20703step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20703step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20703 raw20703Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw20703 raw20703Labels = mixedMoment B raw20703step0 raw20703step0Labels := by
      have hz : ∀ j, raw20703 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20703step0 = (fun i j => raw20703 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20703step0 raw20703; decide +kernel
      have hl : raw20703step0Labels = raw20703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20703 raw20703Labels permutation265 hz
    mixedMoment B raw20703step0 raw20703step0Labels = mixedMoment B raw20703step1 raw20703step1Labels := by
      have ha : raw20703step1 = (fun i j => raw20703step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20703step1 raw20703step0; decide +kernel
      have hl : raw20703step1Labels = raw20703step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20703step0 raw20703step0Labels permutation149 permutation7
    mixedMoment B raw20703step1 raw20703step1Labels = mixedMoment B raw20703step2 raw20703step2Labels := by
      have ha : raw20703step2 = raw20703step1 := by apply Matrix.ext; unfold raw20703step2 raw20703step1; decide +kernel
      have hl : raw20703step1Labels = labelEmbedding1 ∘ raw20703step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20703step1 raw20703step1Labels raw20703step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3468 node3468Labels := by rfl

def raw20704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20704Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20704step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20704step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20704step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20704step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, 1, -3]]
def raw20704step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20704step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, 1, -3]]
def raw20704step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20704 raw20704Labels = mixedMoment B node3484 node3484Labels := by
  calc
    mixedMoment B raw20704 raw20704Labels = mixedMoment B raw20704step0 raw20704step0Labels := by
      have hz : ∀ j, raw20704 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20704step0 = (fun i j => raw20704 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20704step0 raw20704; decide +kernel
      have hl : raw20704step0Labels = raw20704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20704 raw20704Labels permutation346 hz
    mixedMoment B raw20704step0 raw20704step0Labels = mixedMoment B raw20704step1 raw20704step1Labels := by
      have hz : ∀ j, raw20704step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20704step1 = (fun i j => raw20704step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20704step1 raw20704step0; decide +kernel
      have hl : raw20704step1Labels = raw20704step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20704step0 raw20704step0Labels permutation56 hz
    mixedMoment B raw20704step1 raw20704step1Labels = mixedMoment B raw20704step2 raw20704step2Labels := by
      have ha : raw20704step2 = (fun i j => raw20704step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20704step2 raw20704step1; decide +kernel
      have hl : raw20704step2Labels = raw20704step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20704step1 raw20704step1Labels permutation31 permutation7
    mixedMoment B raw20704step2 raw20704step2Labels = mixedMoment B raw20704step3 raw20704step3Labels := by
      have ha : raw20704step3 = raw20704step2 := by apply Matrix.ext; unfold raw20704step3 raw20704step2; decide +kernel
      have hl : raw20704step2Labels = labelEmbedding1 ∘ raw20704step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20704step2 raw20704step2Labels raw20704step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3484 node3484Labels := by rfl

def raw20705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20705Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20705step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20705step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20705step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20705step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw20705step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20705step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw20705step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20705 raw20705Labels = mixedMoment B node3545 node3545Labels := by
  calc
    mixedMoment B raw20705 raw20705Labels = mixedMoment B raw20705step0 raw20705step0Labels := by
      have hz : ∀ j, raw20705 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20705step0 = (fun i j => raw20705 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20705step0 raw20705; decide +kernel
      have hl : raw20705step0Labels = raw20705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20705 raw20705Labels permutation346 hz
    mixedMoment B raw20705step0 raw20705step0Labels = mixedMoment B raw20705step1 raw20705step1Labels := by
      have hz : ∀ j, raw20705step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20705step1 = (fun i j => raw20705step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20705step1 raw20705step0; decide +kernel
      have hl : raw20705step1Labels = raw20705step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20705step0 raw20705step0Labels permutation56 hz
    mixedMoment B raw20705step1 raw20705step1Labels = mixedMoment B raw20705step2 raw20705step2Labels := by
      have ha : raw20705step2 = (fun i j => raw20705step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20705step2 raw20705step1; decide +kernel
      have hl : raw20705step2Labels = raw20705step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20705step1 raw20705step1Labels permutation31 permutation7
    mixedMoment B raw20705step2 raw20705step2Labels = mixedMoment B raw20705step3 raw20705step3Labels := by
      have ha : raw20705step3 = raw20705step2 := by apply Matrix.ext; unfold raw20705step3 raw20705step2; decide +kernel
      have hl : raw20705step2Labels = labelEmbedding1 ∘ raw20705step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20705step2 raw20705step2Labels raw20705step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3545 node3545Labels := by rfl

def raw20706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20706Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20706step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20706step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20706step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20706step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw20706step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20706step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw20706step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20706step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw20706step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20706 raw20706Labels = mixedMoment B node3547 node3547Labels := by
  calc
    mixedMoment B raw20706 raw20706Labels = mixedMoment B raw20706step0 raw20706step0Labels := by
      have hz : ∀ j, raw20706 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20706step0 = (fun i j => raw20706 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20706step0 raw20706; decide +kernel
      have hl : raw20706step0Labels = raw20706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20706 raw20706Labels permutation346 hz
    mixedMoment B raw20706step0 raw20706step0Labels = mixedMoment B raw20706step1 raw20706step1Labels := by
      have hz : ∀ j, raw20706step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20706step1 = (fun i j => raw20706step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20706step1 raw20706step0; decide +kernel
      have hl : raw20706step1Labels = raw20706step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20706step0 raw20706step0Labels permutation56 hz
    mixedMoment B raw20706step1 raw20706step1Labels = mixedMoment B raw20706step2 raw20706step2Labels := by
      have ha : raw20706step2 = (fun i j => raw20706step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20706step2 raw20706step1; decide +kernel
      have hl : raw20706step2Labels = raw20706step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20706step1 raw20706step1Labels permutation8 permutation7
    mixedMoment B raw20706step2 raw20706step2Labels = mixedMoment B raw20706step3 raw20706step3Labels := by
      have ha : raw20706step3 = -raw20706step2 := by apply Matrix.ext; change ∀ i j, raw20706step3 i j = -(raw20706step2 i j); unfold raw20706step3 raw20706step2; decide +kernel
      have hl : raw20706step3Labels = raw20706step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20706step3 raw20706step3Labels = mixedMoment B raw20706step4 raw20706step4Labels := by
      have ha : raw20706step4 = raw20706step3 := by apply Matrix.ext; unfold raw20706step4 raw20706step3; decide +kernel
      have hl : raw20706step3Labels = labelEmbedding1 ∘ raw20706step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20706step3 raw20706step3Labels raw20706step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3547 node3547Labels := by rfl

def raw20707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20707Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20707step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20707step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20707step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20707step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20707step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20707 raw20707Labels = mixedMoment B node1514 node1514Labels := by
  calc
    mixedMoment B raw20707 raw20707Labels = mixedMoment B raw20707step0 raw20707step0Labels := by
      have hz : ∀ j, raw20707 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20707step0 = (fun i j => raw20707 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20707step0 raw20707; decide +kernel
      have hl : raw20707step0Labels = raw20707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20707 raw20707Labels permutation346 hz
    mixedMoment B raw20707step0 raw20707step0Labels = mixedMoment B raw20707step1 raw20707step1Labels := by
      have ha : raw20707step1 = (fun i j => raw20707step0 (permutation46 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20707step1 raw20707step0; decide +kernel
      have hl : raw20707step1Labels = raw20707step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20707step0 raw20707step0Labels permutation46 permutation5
    mixedMoment B raw20707step1 raw20707step1Labels = mixedMoment B raw20707step2 raw20707step2Labels := by
      have ha : raw20707step2 = -raw20707step1 := by apply Matrix.ext; change ∀ i j, raw20707step2 i j = -(raw20707step1 i j); unfold raw20707step2 raw20707step1; decide +kernel
      have hl : raw20707step2Labels = raw20707step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20707step2 raw20707step2Labels = mixedMoment B raw20707step3 raw20707step3Labels := by
      have ha : raw20707step3 = raw20707step2 := by apply Matrix.ext; unfold raw20707step3 raw20707step2; decide +kernel
      have hl : raw20707step2Labels = labelEmbedding1 ∘ raw20707step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20707step2 raw20707step2Labels raw20707step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1514 node1514Labels := by rfl

def raw20708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20708Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20708step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20708step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20708step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20708step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20708step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20708step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20708 raw20708Labels = mixedMoment B node3260 node3260Labels := by
  calc
    mixedMoment B raw20708 raw20708Labels = mixedMoment B raw20708step0 raw20708step0Labels := by
      have ha : raw20708step0 = (fun i j => raw20708 (permutation190 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20708step0 raw20708; decide +kernel
      have hl : raw20708step0Labels = raw20708Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20708 raw20708Labels permutation190 permutation5
    mixedMoment B raw20708step0 raw20708step0Labels = mixedMoment B raw20708step1 raw20708step1Labels := by
      have ha : raw20708step1 = -raw20708step0 := by apply Matrix.ext; change ∀ i j, raw20708step1 i j = -(raw20708step0 i j); unfold raw20708step1 raw20708step0; decide +kernel
      have hl : raw20708step1Labels = raw20708step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20708step1 raw20708step1Labels = mixedMoment B raw20708step2 raw20708step2Labels := by
      have ha : raw20708step2 = raw20708step1 := by apply Matrix.ext; unfold raw20708step2 raw20708step1; decide +kernel
      have hl : raw20708step1Labels = labelEmbedding1 ∘ raw20708step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20708step1 raw20708step1Labels raw20708step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3260 node3260Labels := by rfl

def raw20709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20709Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20709step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw20709step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20709step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw20709step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20709step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw20709step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20709 raw20709Labels = mixedMoment B node3264 node3264Labels := by
  calc
    mixedMoment B raw20709 raw20709Labels = mixedMoment B raw20709step0 raw20709step0Labels := by
      have hz : ∀ j, raw20709 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20709step0 = (fun i j => raw20709 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20709step0 raw20709; decide +kernel
      have hl : raw20709step0Labels = raw20709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20709 raw20709Labels permutation346 hz
    mixedMoment B raw20709step0 raw20709step0Labels = mixedMoment B raw20709step1 raw20709step1Labels := by
      have ha : raw20709step1 = (fun i j => raw20709step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20709step1 raw20709step0; decide +kernel
      have hl : raw20709step1Labels = raw20709step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20709step0 raw20709step0Labels permutation38 permutation7
    mixedMoment B raw20709step1 raw20709step1Labels = mixedMoment B raw20709step2 raw20709step2Labels := by
      have ha : raw20709step2 = -raw20709step1 := by apply Matrix.ext; change ∀ i j, raw20709step2 i j = -(raw20709step1 i j); unfold raw20709step2 raw20709step1; decide +kernel
      have hl : raw20709step2Labels = raw20709step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20709step2 raw20709step2Labels = mixedMoment B raw20709step3 raw20709step3Labels := by
      have ha : raw20709step3 = raw20709step2 := by apply Matrix.ext; unfold raw20709step3 raw20709step2; decide +kernel
      have hl : raw20709step2Labels = labelEmbedding1 ∘ raw20709step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20709step2 raw20709step2Labels raw20709step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3264 node3264Labels := by rfl

def raw20710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20710Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20710step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw20710step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20710step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20710step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20710step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20710step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20710 raw20710Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw20710 raw20710Labels = mixedMoment B raw20710step0 raw20710step0Labels := by
      have hz : ∀ j, raw20710 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20710step0 = (fun i j => raw20710 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20710step0 raw20710; decide +kernel
      have hl : raw20710step0Labels = raw20710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20710 raw20710Labels permutation346 hz
    mixedMoment B raw20710step0 raw20710step0Labels = mixedMoment B raw20710step1 raw20710step1Labels := by
      have ha : raw20710step1 = (fun i j => raw20710step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20710step1 raw20710step0; decide +kernel
      have hl : raw20710step1Labels = raw20710step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20710step0 raw20710step0Labels permutation38 permutation7
    mixedMoment B raw20710step1 raw20710step1Labels = mixedMoment B raw20710step2 raw20710step2Labels := by
      have ha : raw20710step2 = -raw20710step1 := by apply Matrix.ext; change ∀ i j, raw20710step2 i j = -(raw20710step1 i j); unfold raw20710step2 raw20710step1; decide +kernel
      have hl : raw20710step2Labels = raw20710step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20710step2 raw20710step2Labels = mixedMoment B raw20710step3 raw20710step3Labels := by
      have ha : raw20710step3 = raw20710step2 := by apply Matrix.ext; unfold raw20710step3 raw20710step2; decide +kernel
      have hl : raw20710step2Labels = labelEmbedding1 ∘ raw20710step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20710step2 raw20710step2Labels raw20710step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

def raw20711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20711Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20711step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20711step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw20711step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20711step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw20711step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20711step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw20711step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20711 raw20711Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw20711 raw20711Labels = mixedMoment B raw20711step0 raw20711step0Labels := by
      have hz : ∀ j, raw20711 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20711step0 = (fun i j => raw20711 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20711step0 raw20711; decide +kernel
      have hl : raw20711step0Labels = raw20711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20711 raw20711Labels permutation346 hz
    mixedMoment B raw20711step0 raw20711step0Labels = mixedMoment B raw20711step1 raw20711step1Labels := by
      have ha : raw20711step1 = (fun i j => raw20711step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20711step1 raw20711step0; decide +kernel
      have hl : raw20711step1Labels = raw20711step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20711step0 raw20711step0Labels permutation38 permutation7
    mixedMoment B raw20711step1 raw20711step1Labels = mixedMoment B raw20711step2 raw20711step2Labels := by
      have ha : raw20711step2 = -raw20711step1 := by apply Matrix.ext; change ∀ i j, raw20711step2 i j = -(raw20711step1 i j); unfold raw20711step2 raw20711step1; decide +kernel
      have hl : raw20711step2Labels = raw20711step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20711step2 raw20711step2Labels = mixedMoment B raw20711step3 raw20711step3Labels := by
      have ha : raw20711step3 = raw20711step2 := by apply Matrix.ext; unfold raw20711step3 raw20711step2; decide +kernel
      have hl : raw20711step2Labels = labelEmbedding1 ∘ raw20711step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20711step2 raw20711step2Labels raw20711step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3293 node3293Labels := by rfl

def raw20712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20712Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20712step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20712step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20712step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20712step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20712step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20712step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20712 raw20712Labels = mixedMoment B node1514 node1514Labels := by
  calc
    mixedMoment B raw20712 raw20712Labels = mixedMoment B raw20712step0 raw20712step0Labels := by
      have hz : ∀ j, raw20712 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20712step0 = (fun i j => raw20712 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20712step0 raw20712; decide +kernel
      have hl : raw20712step0Labels = raw20712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20712 raw20712Labels permutation265 hz
    mixedMoment B raw20712step0 raw20712step0Labels = mixedMoment B raw20712step1 raw20712step1Labels := by
      have ha : raw20712step1 = (fun i j => raw20712step0 (permutation46 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20712step1 raw20712step0; decide +kernel
      have hl : raw20712step1Labels = raw20712step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20712step0 raw20712step0Labels permutation46 permutation5
    mixedMoment B raw20712step1 raw20712step1Labels = mixedMoment B raw20712step2 raw20712step2Labels := by
      have ha : raw20712step2 = -raw20712step1 := by apply Matrix.ext; change ∀ i j, raw20712step2 i j = -(raw20712step1 i j); unfold raw20712step2 raw20712step1; decide +kernel
      have hl : raw20712step2Labels = raw20712step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20712step2 raw20712step2Labels = mixedMoment B raw20712step3 raw20712step3Labels := by
      have ha : raw20712step3 = raw20712step2 := by apply Matrix.ext; unfold raw20712step3 raw20712step2; decide +kernel
      have hl : raw20712step2Labels = labelEmbedding1 ∘ raw20712step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20712step2 raw20712step2Labels raw20712step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1514 node1514Labels := by rfl

def raw20713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20713Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20713step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20713step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20713step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20713step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20713step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20713 raw20713Labels = mixedMoment B node3260 node3260Labels := by
  calc
    mixedMoment B raw20713 raw20713Labels = mixedMoment B raw20713step0 raw20713step0Labels := by
      have ha : raw20713step0 = (fun i j => raw20713 (permutation166 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20713step0 raw20713; decide +kernel
      have hl : raw20713step0Labels = raw20713Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20713 raw20713Labels permutation166 permutation5
    mixedMoment B raw20713step0 raw20713step0Labels = mixedMoment B raw20713step1 raw20713step1Labels := by
      have ha : raw20713step1 = -raw20713step0 := by apply Matrix.ext; change ∀ i j, raw20713step1 i j = -(raw20713step0 i j); unfold raw20713step1 raw20713step0; decide +kernel
      have hl : raw20713step1Labels = raw20713step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20713step1 raw20713step1Labels = mixedMoment B raw20713step2 raw20713step2Labels := by
      have ha : raw20713step2 = raw20713step1 := by apply Matrix.ext; unfold raw20713step2 raw20713step1; decide +kernel
      have hl : raw20713step1Labels = labelEmbedding1 ∘ raw20713step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20713step1 raw20713step1Labels raw20713step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3260 node3260Labels := by rfl

def raw20714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20714Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20714step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw20714step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20714step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw20714step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20714step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw20714step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20714 raw20714Labels = mixedMoment B node3264 node3264Labels := by
  calc
    mixedMoment B raw20714 raw20714Labels = mixedMoment B raw20714step0 raw20714step0Labels := by
      have hz : ∀ j, raw20714 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20714step0 = (fun i j => raw20714 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20714step0 raw20714; decide +kernel
      have hl : raw20714step0Labels = raw20714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20714 raw20714Labels permutation265 hz
    mixedMoment B raw20714step0 raw20714step0Labels = mixedMoment B raw20714step1 raw20714step1Labels := by
      have ha : raw20714step1 = (fun i j => raw20714step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20714step1 raw20714step0; decide +kernel
      have hl : raw20714step1Labels = raw20714step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20714step0 raw20714step0Labels permutation38 permutation7
    mixedMoment B raw20714step1 raw20714step1Labels = mixedMoment B raw20714step2 raw20714step2Labels := by
      have ha : raw20714step2 = -raw20714step1 := by apply Matrix.ext; change ∀ i j, raw20714step2 i j = -(raw20714step1 i j); unfold raw20714step2 raw20714step1; decide +kernel
      have hl : raw20714step2Labels = raw20714step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20714step2 raw20714step2Labels = mixedMoment B raw20714step3 raw20714step3Labels := by
      have ha : raw20714step3 = raw20714step2 := by apply Matrix.ext; unfold raw20714step3 raw20714step2; decide +kernel
      have hl : raw20714step2Labels = labelEmbedding1 ∘ raw20714step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20714step2 raw20714step2Labels raw20714step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3264 node3264Labels := by rfl

def raw20715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20715Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20715step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw20715step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20715step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20715step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20715step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20715step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20715 raw20715Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw20715 raw20715Labels = mixedMoment B raw20715step0 raw20715step0Labels := by
      have hz : ∀ j, raw20715 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20715step0 = (fun i j => raw20715 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20715step0 raw20715; decide +kernel
      have hl : raw20715step0Labels = raw20715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20715 raw20715Labels permutation265 hz
    mixedMoment B raw20715step0 raw20715step0Labels = mixedMoment B raw20715step1 raw20715step1Labels := by
      have ha : raw20715step1 = (fun i j => raw20715step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20715step1 raw20715step0; decide +kernel
      have hl : raw20715step1Labels = raw20715step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20715step0 raw20715step0Labels permutation38 permutation7
    mixedMoment B raw20715step1 raw20715step1Labels = mixedMoment B raw20715step2 raw20715step2Labels := by
      have ha : raw20715step2 = -raw20715step1 := by apply Matrix.ext; change ∀ i j, raw20715step2 i j = -(raw20715step1 i j); unfold raw20715step2 raw20715step1; decide +kernel
      have hl : raw20715step2Labels = raw20715step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20715step2 raw20715step2Labels = mixedMoment B raw20715step3 raw20715step3Labels := by
      have ha : raw20715step3 = raw20715step2 := by apply Matrix.ext; unfold raw20715step3 raw20715step2; decide +kernel
      have hl : raw20715step2Labels = labelEmbedding1 ∘ raw20715step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20715step2 raw20715step2Labels raw20715step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

def raw20716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20716Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20716step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw20716step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20716step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw20716step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20716step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw20716step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20716 raw20716Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw20716 raw20716Labels = mixedMoment B raw20716step0 raw20716step0Labels := by
      have hz : ∀ j, raw20716 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20716step0 = (fun i j => raw20716 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20716step0 raw20716; decide +kernel
      have hl : raw20716step0Labels = raw20716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20716 raw20716Labels permutation265 hz
    mixedMoment B raw20716step0 raw20716step0Labels = mixedMoment B raw20716step1 raw20716step1Labels := by
      have ha : raw20716step1 = (fun i j => raw20716step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20716step1 raw20716step0; decide +kernel
      have hl : raw20716step1Labels = raw20716step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20716step0 raw20716step0Labels permutation38 permutation7
    mixedMoment B raw20716step1 raw20716step1Labels = mixedMoment B raw20716step2 raw20716step2Labels := by
      have ha : raw20716step2 = -raw20716step1 := by apply Matrix.ext; change ∀ i j, raw20716step2 i j = -(raw20716step1 i j); unfold raw20716step2 raw20716step1; decide +kernel
      have hl : raw20716step2Labels = raw20716step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20716step2 raw20716step2Labels = mixedMoment B raw20716step3 raw20716step3Labels := by
      have ha : raw20716step3 = raw20716step2 := by apply Matrix.ext; unfold raw20716step3 raw20716step2; decide +kernel
      have hl : raw20716step2Labels = labelEmbedding1 ∘ raw20716step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20716step2 raw20716step2Labels raw20716step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3293 node3293Labels := by rfl

def raw20717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20717Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20717step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20717step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20717step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20717step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw20717step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20717step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw20717step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20717step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw20717step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20717 raw20717Labels = mixedMoment B node1520 node1520Labels := by
  calc
    mixedMoment B raw20717 raw20717Labels = mixedMoment B raw20717step0 raw20717step0Labels := by
      have hz : ∀ j, raw20717 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20717step0 = (fun i j => raw20717 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20717step0 raw20717; decide +kernel
      have hl : raw20717step0Labels = raw20717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20717 raw20717Labels permutation346 hz
    mixedMoment B raw20717step0 raw20717step0Labels = mixedMoment B raw20717step1 raw20717step1Labels := by
      have hz : ∀ j, raw20717step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20717step1 = (fun i j => raw20717step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20717step1 raw20717step0; decide +kernel
      have hl : raw20717step1Labels = raw20717step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20717step0 raw20717step0Labels permutation56 hz
    mixedMoment B raw20717step1 raw20717step1Labels = mixedMoment B raw20717step2 raw20717step2Labels := by
      have ha : raw20717step2 = (fun i j => raw20717step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20717step2 raw20717step1; decide +kernel
      have hl : raw20717step2Labels = raw20717step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20717step1 raw20717step1Labels permutation11 permutation5
    mixedMoment B raw20717step2 raw20717step2Labels = mixedMoment B raw20717step3 raw20717step3Labels := by
      have ha : raw20717step3 = -raw20717step2 := by apply Matrix.ext; change ∀ i j, raw20717step3 i j = -(raw20717step2 i j); unfold raw20717step3 raw20717step2; decide +kernel
      have hl : raw20717step3Labels = raw20717step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20717step3 raw20717step3Labels = mixedMoment B raw20717step4 raw20717step4Labels := by
      have ha : raw20717step4 = raw20717step3 := by apply Matrix.ext; unfold raw20717step4 raw20717step3; decide +kernel
      have hl : raw20717step3Labels = labelEmbedding1 ∘ raw20717step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20717step3 raw20717step3Labels raw20717step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1520 node1520Labels := by rfl

def raw20718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20718Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20718step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw20718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw20718step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20718step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw20718step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20718 raw20718Labels = mixedMoment B node3266 node3266Labels := by
  calc
    mixedMoment B raw20718 raw20718Labels = mixedMoment B raw20718step0 raw20718step0Labels := by
      have hz : ∀ j, raw20718 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20718step0 = (fun i j => raw20718 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20718step0 raw20718; decide +kernel
      have hl : raw20718step0Labels = raw20718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20718 raw20718Labels permutation346 hz
    mixedMoment B raw20718step0 raw20718step0Labels = mixedMoment B raw20718step1 raw20718step1Labels := by
      have ha : raw20718step1 = (fun i j => raw20718step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20718step1 raw20718step0; decide +kernel
      have hl : raw20718step1Labels = raw20718step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20718step0 raw20718step0Labels permutation35 permutation5
    mixedMoment B raw20718step1 raw20718step1Labels = mixedMoment B raw20718step2 raw20718step2Labels := by
      have ha : raw20718step2 = -raw20718step1 := by apply Matrix.ext; change ∀ i j, raw20718step2 i j = -(raw20718step1 i j); unfold raw20718step2 raw20718step1; decide +kernel
      have hl : raw20718step2Labels = raw20718step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20718step2 raw20718step2Labels = mixedMoment B raw20718step3 raw20718step3Labels := by
      have ha : raw20718step3 = raw20718step2 := by apply Matrix.ext; unfold raw20718step3 raw20718step2; decide +kernel
      have hl : raw20718step2Labels = labelEmbedding1 ∘ raw20718step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20718step2 raw20718step2Labels raw20718step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3266 node3266Labels := by rfl

def raw20719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20719Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20719step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw20719step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20719step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw20719step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20719step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw20719step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20719 raw20719Labels = mixedMoment B node3266 node3266Labels := by
  calc
    mixedMoment B raw20719 raw20719Labels = mixedMoment B raw20719step0 raw20719step0Labels := by
      have hz : ∀ j, raw20719 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20719step0 = (fun i j => raw20719 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20719step0 raw20719; decide +kernel
      have hl : raw20719step0Labels = raw20719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20719 raw20719Labels permutation265 hz
    mixedMoment B raw20719step0 raw20719step0Labels = mixedMoment B raw20719step1 raw20719step1Labels := by
      have ha : raw20719step1 = (fun i j => raw20719step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20719step1 raw20719step0; decide +kernel
      have hl : raw20719step1Labels = raw20719step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20719step0 raw20719step0Labels permutation35 permutation5
    mixedMoment B raw20719step1 raw20719step1Labels = mixedMoment B raw20719step2 raw20719step2Labels := by
      have ha : raw20719step2 = -raw20719step1 := by apply Matrix.ext; change ∀ i j, raw20719step2 i j = -(raw20719step1 i j); unfold raw20719step2 raw20719step1; decide +kernel
      have hl : raw20719step2Labels = raw20719step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20719step2 raw20719step2Labels = mixedMoment B raw20719step3 raw20719step3Labels := by
      have ha : raw20719step3 = raw20719step2 := by apply Matrix.ext; unfold raw20719step3 raw20719step2; decide +kernel
      have hl : raw20719step2Labels = labelEmbedding1 ∘ raw20719step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20719step2 raw20719step2Labels raw20719step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3266 node3266Labels := by rfl

def raw20720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20720step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20720step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20720step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20720step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw20720step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20720step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw20720step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20720step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw20720step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20720 raw20720Labels = mixedMoment B node3302 node3302Labels := by
  calc
    mixedMoment B raw20720 raw20720Labels = mixedMoment B raw20720step0 raw20720step0Labels := by
      have hz : ∀ j, raw20720 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20720step0 = (fun i j => raw20720 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20720step0 raw20720; decide +kernel
      have hl : raw20720step0Labels = raw20720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20720 raw20720Labels permutation346 hz
    mixedMoment B raw20720step0 raw20720step0Labels = mixedMoment B raw20720step1 raw20720step1Labels := by
      have hz : ∀ j, raw20720step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20720step1 = (fun i j => raw20720step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20720step1 raw20720step0; decide +kernel
      have hl : raw20720step1Labels = raw20720step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20720step0 raw20720step0Labels permutation56 hz
    mixedMoment B raw20720step1 raw20720step1Labels = mixedMoment B raw20720step2 raw20720step2Labels := by
      have ha : raw20720step2 = (fun i j => raw20720step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20720step2 raw20720step1; decide +kernel
      have hl : raw20720step2Labels = raw20720step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20720step1 raw20720step1Labels permutation11 permutation5
    mixedMoment B raw20720step2 raw20720step2Labels = mixedMoment B raw20720step3 raw20720step3Labels := by
      have ha : raw20720step3 = -raw20720step2 := by apply Matrix.ext; change ∀ i j, raw20720step3 i j = -(raw20720step2 i j); unfold raw20720step3 raw20720step2; decide +kernel
      have hl : raw20720step3Labels = raw20720step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20720step3 raw20720step3Labels = mixedMoment B raw20720step4 raw20720step4Labels := by
      have ha : raw20720step4 = raw20720step3 := by apply Matrix.ext; unfold raw20720step4 raw20720step3; decide +kernel
      have hl : raw20720step3Labels = labelEmbedding1 ∘ raw20720step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20720step3 raw20720step3Labels raw20720step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3302 node3302Labels := by rfl

def raw20721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20721Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20721step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20721step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20721step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20721step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw20721step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20721step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw20721step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20721step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw20721step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20721 raw20721Labels = mixedMoment B node3305 node3305Labels := by
  calc
    mixedMoment B raw20721 raw20721Labels = mixedMoment B raw20721step0 raw20721step0Labels := by
      have hz : ∀ j, raw20721 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20721step0 = (fun i j => raw20721 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20721step0 raw20721; decide +kernel
      have hl : raw20721step0Labels = raw20721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20721 raw20721Labels permutation346 hz
    mixedMoment B raw20721step0 raw20721step0Labels = mixedMoment B raw20721step1 raw20721step1Labels := by
      have hz : ∀ j, raw20721step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20721step1 = (fun i j => raw20721step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20721step1 raw20721step0; decide +kernel
      have hl : raw20721step1Labels = raw20721step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20721step0 raw20721step0Labels permutation56 hz
    mixedMoment B raw20721step1 raw20721step1Labels = mixedMoment B raw20721step2 raw20721step2Labels := by
      have ha : raw20721step2 = (fun i j => raw20721step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20721step2 raw20721step1; decide +kernel
      have hl : raw20721step2Labels = raw20721step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20721step1 raw20721step1Labels permutation8 permutation7
    mixedMoment B raw20721step2 raw20721step2Labels = mixedMoment B raw20721step3 raw20721step3Labels := by
      have ha : raw20721step3 = -raw20721step2 := by apply Matrix.ext; change ∀ i j, raw20721step3 i j = -(raw20721step2 i j); unfold raw20721step3 raw20721step2; decide +kernel
      have hl : raw20721step3Labels = raw20721step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20721step3 raw20721step3Labels = mixedMoment B raw20721step4 raw20721step4Labels := by
      have ha : raw20721step4 = raw20721step3 := by apply Matrix.ext; unfold raw20721step4 raw20721step3; decide +kernel
      have hl : raw20721step3Labels = labelEmbedding1 ∘ raw20721step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20721step3 raw20721step3Labels raw20721step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3305 node3305Labels := by rfl

def raw20722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20722Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20722step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20722step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20722step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20722step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw20722step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20722step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw20722step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20722step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw20722step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20722 raw20722Labels = mixedMoment B node1533 node1533Labels := by
  calc
    mixedMoment B raw20722 raw20722Labels = mixedMoment B raw20722step0 raw20722step0Labels := by
      have hz : ∀ j, raw20722 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20722step0 = (fun i j => raw20722 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20722step0 raw20722; decide +kernel
      have hl : raw20722step0Labels = raw20722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20722 raw20722Labels permutation346 hz
    mixedMoment B raw20722step0 raw20722step0Labels = mixedMoment B raw20722step1 raw20722step1Labels := by
      have hz : ∀ j, raw20722step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20722step1 = (fun i j => raw20722step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20722step1 raw20722step0; decide +kernel
      have hl : raw20722step1Labels = raw20722step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20722step0 raw20722step0Labels permutation56 hz
    mixedMoment B raw20722step1 raw20722step1Labels = mixedMoment B raw20722step2 raw20722step2Labels := by
      have ha : raw20722step2 = (fun i j => raw20722step1 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20722step2 raw20722step1; decide +kernel
      have hl : raw20722step2Labels = raw20722step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20722step1 raw20722step1Labels permutation8 permutation5
    mixedMoment B raw20722step2 raw20722step2Labels = mixedMoment B raw20722step3 raw20722step3Labels := by
      have ha : raw20722step3 = -raw20722step2 := by apply Matrix.ext; change ∀ i j, raw20722step3 i j = -(raw20722step2 i j); unfold raw20722step3 raw20722step2; decide +kernel
      have hl : raw20722step3Labels = raw20722step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20722step3 raw20722step3Labels = mixedMoment B raw20722step4 raw20722step4Labels := by
      have ha : raw20722step4 = raw20722step3 := by apply Matrix.ext; unfold raw20722step4 raw20722step3; decide +kernel
      have hl : raw20722step3Labels = labelEmbedding1 ∘ raw20722step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20722step3 raw20722step3Labels raw20722step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1533 node1533Labels := by rfl

def raw20723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20723Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20723step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw20723step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20723step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw20723step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20723step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw20723step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20723 raw20723Labels = mixedMoment B node3272 node3272Labels := by
  calc
    mixedMoment B raw20723 raw20723Labels = mixedMoment B raw20723step0 raw20723step0Labels := by
      have hz : ∀ j, raw20723 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20723step0 = (fun i j => raw20723 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20723step0 raw20723; decide +kernel
      have hl : raw20723step0Labels = raw20723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20723 raw20723Labels permutation346 hz
    mixedMoment B raw20723step0 raw20723step0Labels = mixedMoment B raw20723step1 raw20723step1Labels := by
      have ha : raw20723step1 = (fun i j => raw20723step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20723step1 raw20723step0; decide +kernel
      have hl : raw20723step1Labels = raw20723step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20723step0 raw20723step0Labels permutation32 permutation5
    mixedMoment B raw20723step1 raw20723step1Labels = mixedMoment B raw20723step2 raw20723step2Labels := by
      have ha : raw20723step2 = -raw20723step1 := by apply Matrix.ext; change ∀ i j, raw20723step2 i j = -(raw20723step1 i j); unfold raw20723step2 raw20723step1; decide +kernel
      have hl : raw20723step2Labels = raw20723step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20723step2 raw20723step2Labels = mixedMoment B raw20723step3 raw20723step3Labels := by
      have ha : raw20723step3 = raw20723step2 := by apply Matrix.ext; unfold raw20723step3 raw20723step2; decide +kernel
      have hl : raw20723step2Labels = labelEmbedding1 ∘ raw20723step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20723step2 raw20723step2Labels raw20723step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3272 node3272Labels := by rfl

def raw20724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20724Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20724step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw20724step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw20724step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20724step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw20724step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20724 raw20724Labels = mixedMoment B node3272 node3272Labels := by
  calc
    mixedMoment B raw20724 raw20724Labels = mixedMoment B raw20724step0 raw20724step0Labels := by
      have hz : ∀ j, raw20724 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20724step0 = (fun i j => raw20724 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20724step0 raw20724; decide +kernel
      have hl : raw20724step0Labels = raw20724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20724 raw20724Labels permutation265 hz
    mixedMoment B raw20724step0 raw20724step0Labels = mixedMoment B raw20724step1 raw20724step1Labels := by
      have ha : raw20724step1 = (fun i j => raw20724step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20724step1 raw20724step0; decide +kernel
      have hl : raw20724step1Labels = raw20724step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20724step0 raw20724step0Labels permutation32 permutation5
    mixedMoment B raw20724step1 raw20724step1Labels = mixedMoment B raw20724step2 raw20724step2Labels := by
      have ha : raw20724step2 = -raw20724step1 := by apply Matrix.ext; change ∀ i j, raw20724step2 i j = -(raw20724step1 i j); unfold raw20724step2 raw20724step1; decide +kernel
      have hl : raw20724step2Labels = raw20724step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20724step2 raw20724step2Labels = mixedMoment B raw20724step3 raw20724step3Labels := by
      have ha : raw20724step3 = raw20724step2 := by apply Matrix.ext; unfold raw20724step3 raw20724step2; decide +kernel
      have hl : raw20724step2Labels = labelEmbedding1 ∘ raw20724step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20724step2 raw20724step2Labels raw20724step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3272 node3272Labels := by rfl

def raw20725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20725Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20725step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20725step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20725step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20725step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw20725step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20725step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 1, -2], ![2, 1, -3]]
def raw20725step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20725step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 1, -2], ![2, 1, -3]]
def raw20725step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20725 raw20725Labels = mixedMoment B node3276 node3276Labels := by
  calc
    mixedMoment B raw20725 raw20725Labels = mixedMoment B raw20725step0 raw20725step0Labels := by
      have hz : ∀ j, raw20725 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20725step0 = (fun i j => raw20725 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20725step0 raw20725; decide +kernel
      have hl : raw20725step0Labels = raw20725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20725 raw20725Labels permutation346 hz
    mixedMoment B raw20725step0 raw20725step0Labels = mixedMoment B raw20725step1 raw20725step1Labels := by
      have hz : ∀ j, raw20725step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20725step1 = (fun i j => raw20725step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20725step1 raw20725step0; decide +kernel
      have hl : raw20725step1Labels = raw20725step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20725step0 raw20725step0Labels permutation56 hz
    mixedMoment B raw20725step1 raw20725step1Labels = mixedMoment B raw20725step2 raw20725step2Labels := by
      have ha : raw20725step2 = (fun i j => raw20725step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20725step2 raw20725step1; decide +kernel
      have hl : raw20725step2Labels = raw20725step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20725step1 raw20725step1Labels permutation8 permutation7
    mixedMoment B raw20725step2 raw20725step2Labels = mixedMoment B raw20725step3 raw20725step3Labels := by
      have ha : raw20725step3 = -raw20725step2 := by apply Matrix.ext; change ∀ i j, raw20725step3 i j = -(raw20725step2 i j); unfold raw20725step3 raw20725step2; decide +kernel
      have hl : raw20725step3Labels = raw20725step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20725step3 raw20725step3Labels = mixedMoment B raw20725step4 raw20725step4Labels := by
      have ha : raw20725step4 = raw20725step3 := by apply Matrix.ext; unfold raw20725step4 raw20725step3; decide +kernel
      have hl : raw20725step3Labels = labelEmbedding1 ∘ raw20725step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20725step3 raw20725step3Labels raw20725step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3276 node3276Labels := by rfl

def raw20726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw20726Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw20726step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20726step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw20726step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20726step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw20726step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20726step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw20726step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20726step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw20726step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20726 raw20726Labels = mixedMoment B node3301 node3301Labels := by
  calc
    mixedMoment B raw20726 raw20726Labels = mixedMoment B raw20726step0 raw20726step0Labels := by
      have hz : ∀ j, raw20726 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20726step0 = (fun i j => raw20726 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20726step0 raw20726; decide +kernel
      have hl : raw20726step0Labels = raw20726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20726 raw20726Labels permutation346 hz
    mixedMoment B raw20726step0 raw20726step0Labels = mixedMoment B raw20726step1 raw20726step1Labels := by
      have hz : ∀ j, raw20726step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20726step1 = (fun i j => raw20726step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20726step1 raw20726step0; decide +kernel
      have hl : raw20726step1Labels = raw20726step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20726step0 raw20726step0Labels permutation56 hz
    mixedMoment B raw20726step1 raw20726step1Labels = mixedMoment B raw20726step2 raw20726step2Labels := by
      have ha : raw20726step2 = (fun i j => raw20726step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20726step2 raw20726step1; decide +kernel
      have hl : raw20726step2Labels = raw20726step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20726step1 raw20726step1Labels permutation8 permutation7
    mixedMoment B raw20726step2 raw20726step2Labels = mixedMoment B raw20726step3 raw20726step3Labels := by
      have ha : raw20726step3 = -raw20726step2 := by apply Matrix.ext; change ∀ i j, raw20726step3 i j = -(raw20726step2 i j); unfold raw20726step3 raw20726step2; decide +kernel
      have hl : raw20726step3Labels = raw20726step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20726step3 raw20726step3Labels = mixedMoment B raw20726step4 raw20726step4Labels := by
      have ha : raw20726step4 = raw20726step3 := by apply Matrix.ext; unfold raw20726step4 raw20726step3; decide +kernel
      have hl : raw20726step3Labels = labelEmbedding1 ∘ raw20726step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20726step3 raw20726step3Labels raw20726step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3301 node3301Labels := by rfl

def raw20727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20727Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20727step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20727step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20727step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20727step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-2, -2, 4]]
def raw20727step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20727step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20727step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20727step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20727step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20727 raw20727Labels = mixedMoment B node1516 node1516Labels := by
  calc
    mixedMoment B raw20727 raw20727Labels = mixedMoment B raw20727step0 raw20727step0Labels := by
      have hz : ∀ j, raw20727 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20727step0 = (fun i j => raw20727 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20727step0 raw20727; decide +kernel
      have hl : raw20727step0Labels = raw20727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20727 raw20727Labels permutation346 hz
    mixedMoment B raw20727step0 raw20727step0Labels = mixedMoment B raw20727step1 raw20727step1Labels := by
      have hz : ∀ j, raw20727step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20727step1 = (fun i j => raw20727step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20727step1 raw20727step0; decide +kernel
      have hl : raw20727step1Labels = raw20727step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20727step0 raw20727step0Labels permutation56 hz
    mixedMoment B raw20727step1 raw20727step1Labels = mixedMoment B raw20727step2 raw20727step2Labels := by
      have ha : raw20727step2 = (fun i j => raw20727step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20727step2 raw20727step1; decide +kernel
      have hl : raw20727step2Labels = raw20727step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20727step1 raw20727step1Labels permutation10 permutation5
    mixedMoment B raw20727step2 raw20727step2Labels = mixedMoment B raw20727step3 raw20727step3Labels := by
      have ha : raw20727step3 = -raw20727step2 := by apply Matrix.ext; change ∀ i j, raw20727step3 i j = -(raw20727step2 i j); unfold raw20727step3 raw20727step2; decide +kernel
      have hl : raw20727step3Labels = raw20727step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20727step3 raw20727step3Labels = mixedMoment B raw20727step4 raw20727step4Labels := by
      have ha : raw20727step4 = raw20727step3 := by apply Matrix.ext; unfold raw20727step4 raw20727step3; decide +kernel
      have hl : raw20727step3Labels = labelEmbedding1 ∘ raw20727step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20727step3 raw20727step3Labels raw20727step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1516 node1516Labels := by rfl

def raw20728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20728Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20728step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -2, 4]]
def raw20728step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20728step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20728step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20728step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20728step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20728 raw20728Labels = mixedMoment B node3262 node3262Labels := by
  calc
    mixedMoment B raw20728 raw20728Labels = mixedMoment B raw20728step0 raw20728step0Labels := by
      have hz : ∀ j, raw20728 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20728step0 = (fun i j => raw20728 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20728step0 raw20728; decide +kernel
      have hl : raw20728step0Labels = raw20728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20728 raw20728Labels permutation346 hz
    mixedMoment B raw20728step0 raw20728step0Labels = mixedMoment B raw20728step1 raw20728step1Labels := by
      have ha : raw20728step1 = (fun i j => raw20728step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20728step1 raw20728step0; decide +kernel
      have hl : raw20728step1Labels = raw20728step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20728step0 raw20728step0Labels permutation34 permutation5
    mixedMoment B raw20728step1 raw20728step1Labels = mixedMoment B raw20728step2 raw20728step2Labels := by
      have ha : raw20728step2 = -raw20728step1 := by apply Matrix.ext; change ∀ i j, raw20728step2 i j = -(raw20728step1 i j); unfold raw20728step2 raw20728step1; decide +kernel
      have hl : raw20728step2Labels = raw20728step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20728step2 raw20728step2Labels = mixedMoment B raw20728step3 raw20728step3Labels := by
      have ha : raw20728step3 = raw20728step2 := by apply Matrix.ext; unfold raw20728step3 raw20728step2; decide +kernel
      have hl : raw20728step2Labels = labelEmbedding1 ∘ raw20728step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20728step2 raw20728step2Labels raw20728step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3262 node3262Labels := by rfl

def raw20729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20729Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20729step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -2, 4]]
def raw20729step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20729step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20729step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20729step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20729 raw20729Labels = mixedMoment B node3262 node3262Labels := by
  calc
    mixedMoment B raw20729 raw20729Labels = mixedMoment B raw20729step0 raw20729step0Labels := by
      have hz : ∀ j, raw20729 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20729step0 = (fun i j => raw20729 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20729step0 raw20729; decide +kernel
      have hl : raw20729step0Labels = raw20729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20729 raw20729Labels permutation265 hz
    mixedMoment B raw20729step0 raw20729step0Labels = mixedMoment B raw20729step1 raw20729step1Labels := by
      have ha : raw20729step1 = (fun i j => raw20729step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20729step1 raw20729step0; decide +kernel
      have hl : raw20729step1Labels = raw20729step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20729step0 raw20729step0Labels permutation34 permutation5
    mixedMoment B raw20729step1 raw20729step1Labels = mixedMoment B raw20729step2 raw20729step2Labels := by
      have ha : raw20729step2 = -raw20729step1 := by apply Matrix.ext; change ∀ i j, raw20729step2 i j = -(raw20729step1 i j); unfold raw20729step2 raw20729step1; decide +kernel
      have hl : raw20729step2Labels = raw20729step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20729step2 raw20729step2Labels = mixedMoment B raw20729step3 raw20729step3Labels := by
      have ha : raw20729step3 = raw20729step2 := by apply Matrix.ext; unfold raw20729step3 raw20729step2; decide +kernel
      have hl : raw20729step2Labels = labelEmbedding1 ∘ raw20729step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20729step2 raw20729step2Labels raw20729step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3262 node3262Labels := by rfl

def raw20730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20730Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20730step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20730step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20730step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20730step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![2, 2, -4]]
def raw20730step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20730step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![2, 2, -4]]
def raw20730step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20730 raw20730Labels = mixedMoment B node3275 node3275Labels := by
  calc
    mixedMoment B raw20730 raw20730Labels = mixedMoment B raw20730step0 raw20730step0Labels := by
      have hz : ∀ j, raw20730 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20730step0 = (fun i j => raw20730 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20730step0 raw20730; decide +kernel
      have hl : raw20730step0Labels = raw20730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20730 raw20730Labels permutation346 hz
    mixedMoment B raw20730step0 raw20730step0Labels = mixedMoment B raw20730step1 raw20730step1Labels := by
      have hz : ∀ j, raw20730step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20730step1 = (fun i j => raw20730step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20730step1 raw20730step0; decide +kernel
      have hl : raw20730step1Labels = raw20730step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20730step0 raw20730step0Labels permutation56 hz
    mixedMoment B raw20730step1 raw20730step1Labels = mixedMoment B raw20730step2 raw20730step2Labels := by
      have ha : raw20730step2 = (fun i j => raw20730step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20730step2 raw20730step1; decide +kernel
      have hl : raw20730step2Labels = raw20730step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20730step1 raw20730step1Labels permutation31 permutation7
    mixedMoment B raw20730step2 raw20730step2Labels = mixedMoment B raw20730step3 raw20730step3Labels := by
      have ha : raw20730step3 = raw20730step2 := by apply Matrix.ext; unfold raw20730step3 raw20730step2; decide +kernel
      have hl : raw20730step2Labels = labelEmbedding1 ∘ raw20730step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20730step2 raw20730step2Labels raw20730step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3275 node3275Labels := by rfl

def raw20731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw20731Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw20731step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20731step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw20731step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20731step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw20731step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20731step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw20731step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20731 raw20731Labels = mixedMoment B node3298 node3298Labels := by
  calc
    mixedMoment B raw20731 raw20731Labels = mixedMoment B raw20731step0 raw20731step0Labels := by
      have hz : ∀ j, raw20731 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20731step0 = (fun i j => raw20731 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20731step0 raw20731; decide +kernel
      have hl : raw20731step0Labels = raw20731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20731 raw20731Labels permutation346 hz
    mixedMoment B raw20731step0 raw20731step0Labels = mixedMoment B raw20731step1 raw20731step1Labels := by
      have hz : ∀ j, raw20731step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20731step1 = (fun i j => raw20731step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20731step1 raw20731step0; decide +kernel
      have hl : raw20731step1Labels = raw20731step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20731step0 raw20731step0Labels permutation56 hz
    mixedMoment B raw20731step1 raw20731step1Labels = mixedMoment B raw20731step2 raw20731step2Labels := by
      have ha : raw20731step2 = (fun i j => raw20731step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20731step2 raw20731step1; decide +kernel
      have hl : raw20731step2Labels = raw20731step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20731step1 raw20731step1Labels permutation29 permutation5
    mixedMoment B raw20731step2 raw20731step2Labels = mixedMoment B raw20731step3 raw20731step3Labels := by
      have ha : raw20731step3 = raw20731step2 := by apply Matrix.ext; unfold raw20731step3 raw20731step2; decide +kernel
      have hl : raw20731step2Labels = labelEmbedding1 ∘ raw20731step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20731step2 raw20731step2Labels raw20731step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3298 node3298Labels := by rfl

def raw20732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20732Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20732step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20732step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20732step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20732 raw20732Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw20732 raw20732Labels = mixedMoment B raw20732step0 raw20732step0Labels := by
      have hz : ∀ j, raw20732 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20732step0 = (fun i j => raw20732 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20732step0 raw20732; decide +kernel
      have hl : raw20732step0Labels = raw20732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20732 raw20732Labels permutation346 hz
    mixedMoment B raw20732step0 raw20732step0Labels = mixedMoment B raw20732step1 raw20732step1Labels := by
      have hz : ∀ j, raw20732step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20732step1 = (fun i j => raw20732step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20732step1 raw20732step0; decide +kernel
      have hl : raw20732step1Labels = raw20732step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20732step0 raw20732step0Labels permutation56 hz
    _ = mixedMoment B node1242 node1242Labels := by rfl

def raw20733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20733Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20733step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20733step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20733 raw20733Labels = mixedMoment B node626 node626Labels := by
  calc
    mixedMoment B raw20733 raw20733Labels = mixedMoment B raw20733step0 raw20733step0Labels := by
      have hz : ∀ j, raw20733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20733step0 = (fun i j => raw20733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20733step0 raw20733; decide +kernel
      have hl : raw20733step0Labels = raw20733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20733 raw20733Labels permutation346 hz
    mixedMoment B raw20733step0 raw20733step0Labels = mixedMoment B raw20733step1 raw20733step1Labels := by
      have ha : raw20733step1 = (fun i j => raw20733step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20733step1 raw20733step0; decide +kernel
      have hl : raw20733step1Labels = raw20733step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20733step0 raw20733step0Labels permutation38 permutation2
    _ = mixedMoment B node626 node626Labels := by rfl

def raw20734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20734Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20734step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20734step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20734 raw20734Labels = mixedMoment B node626 node626Labels := by
  calc
    mixedMoment B raw20734 raw20734Labels = mixedMoment B raw20734step0 raw20734step0Labels := by
      have hz : ∀ j, raw20734 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20734step0 = (fun i j => raw20734 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20734step0 raw20734; decide +kernel
      have hl : raw20734step0Labels = raw20734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20734 raw20734Labels permutation265 hz
    mixedMoment B raw20734step0 raw20734step0Labels = mixedMoment B raw20734step1 raw20734step1Labels := by
      have ha : raw20734step1 = (fun i j => raw20734step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20734step1 raw20734step0; decide +kernel
      have hl : raw20734step1Labels = raw20734step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20734step0 raw20734step0Labels permutation38 permutation2
    _ = mixedMoment B node626 node626Labels := by rfl

def raw20735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20735Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20735step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20735step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20735step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20735 raw20735Labels = mixedMoment B node641 node641Labels := by
  calc
    mixedMoment B raw20735 raw20735Labels = mixedMoment B raw20735step0 raw20735step0Labels := by
      have hz : ∀ j, raw20735 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20735step0 = (fun i j => raw20735 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20735step0 raw20735; decide +kernel
      have hl : raw20735step0Labels = raw20735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20735 raw20735Labels permutation346 hz
    mixedMoment B raw20735step0 raw20735step0Labels = mixedMoment B raw20735step1 raw20735step1Labels := by
      have hz : ∀ j, raw20735step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20735step1 = (fun i j => raw20735step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20735step1 raw20735step0; decide +kernel
      have hl : raw20735step1Labels = raw20735step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20735step0 raw20735step0Labels permutation56 hz
    _ = mixedMoment B node641 node641Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
