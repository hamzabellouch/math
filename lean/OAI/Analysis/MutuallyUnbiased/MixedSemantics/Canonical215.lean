import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw27520 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27520Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw27520step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27520 raw27520Labels = mixedMoment B node3368 node3368Labels := by
  calc
    mixedMoment B raw27520 raw27520Labels = mixedMoment B raw27520step0 raw27520step0Labels := by
      have ha : raw27520step0 = (fun i j => raw27520 (permutation664 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27520step0 raw27520; decide +kernel
      have hl : raw27520step0Labels = raw27520Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27520 raw27520Labels permutation664 permutation4
    _ = mixedMoment B node3368 node3368Labels := by rfl

def raw27521 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw27521Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27521step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw27521step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27521 raw27521Labels = mixedMoment B node3432 node3432Labels := by
  calc
    mixedMoment B raw27521 raw27521Labels = mixedMoment B raw27521step0 raw27521step0Labels := by
      have ha : raw27521step0 = (fun i j => raw27521 (permutation688 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27521step0 raw27521; decide +kernel
      have hl : raw27521step0Labels = raw27521Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27521 raw27521Labels permutation688 permutation4
    _ = mixedMoment B node3432 node3432Labels := by rfl

def raw27522 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw27522Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw27522step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27522 raw27522Labels = mixedMoment B node1996 node1996Labels := by
  calc
    mixedMoment B raw27522 raw27522Labels = mixedMoment B raw27522step0 raw27522step0Labels := by
      have ha : raw27522step0 = (fun i j => raw27522 (permutation664 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27522step0 raw27522; decide +kernel
      have hl : raw27522step0Labels = raw27522Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27522 raw27522Labels permutation664 permutation4
    _ = mixedMoment B node1996 node1996Labels := by rfl

def raw27523 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27523Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27523step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27523step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw27523step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27523step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]
def raw27523step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27523 raw27523Labels = mixedMoment B node3608 node3608Labels := by
  calc
    mixedMoment B raw27523 raw27523Labels = mixedMoment B raw27523step0 raw27523step0Labels := by
      have hz : ∀ j, raw27523 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27523step0 = (fun i j => raw27523 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27523step0 raw27523; decide +kernel
      have hl : raw27523step0Labels = raw27523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27523 raw27523Labels permutation434 hz
    mixedMoment B raw27523step0 raw27523step0Labels = mixedMoment B raw27523step1 raw27523step1Labels := by
      have hz : ∀ j, raw27523step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27523step1 = (fun i j => raw27523step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27523step1 raw27523step0; decide +kernel
      have hl : raw27523step1Labels = raw27523step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27523step0 raw27523step0Labels permutation80 hz
    mixedMoment B raw27523step1 raw27523step1Labels = mixedMoment B raw27523step2 raw27523step2Labels := by
      have ha : raw27523step2 = (fun i j => raw27523step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27523step2 raw27523step1; decide +kernel
      have hl : raw27523step2Labels = raw27523step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27523step1 raw27523step1Labels permutation31 permutation4
    _ = mixedMoment B node3608 node3608Labels := by rfl

def raw27524 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw27524Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw27524step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27524step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw27524step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27524 raw27524Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw27524 raw27524Labels = mixedMoment B raw27524step0 raw27524step0Labels := by
      have hz : ∀ j, raw27524 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27524step0 = (fun i j => raw27524 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27524step0 raw27524; decide +kernel
      have hl : raw27524step0Labels = raw27524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27524 raw27524Labels permutation346 hz
    mixedMoment B raw27524step0 raw27524step0Labels = mixedMoment B raw27524step1 raw27524step1Labels := by
      have ha : raw27524step1 = (fun i j => raw27524step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27524step1 raw27524step0; decide +kernel
      have hl : raw27524step1Labels = raw27524step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27524step0 raw27524step0Labels permutation143 permutation4
    _ = mixedMoment B node3530 node3530Labels := by rfl

def raw27525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27525Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27525step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw27525step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27525step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw27525step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27525 raw27525Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw27525 raw27525Labels = mixedMoment B raw27525step0 raw27525step0Labels := by
      have ha : raw27525step0 = (fun i j => raw27525 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27525step0 raw27525; decide +kernel
      have hl : raw27525step0Labels = raw27525Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27525 raw27525Labels permutation686 permutation2
    mixedMoment B raw27525step0 raw27525step0Labels = mixedMoment B raw27525step1 raw27525step1Labels := by
      have ha : raw27525step1 = -raw27525step0 := by apply Matrix.ext; change ∀ i j, raw27525step1 i j = -(raw27525step0 i j); unfold raw27525step1 raw27525step0; decide +kernel
      have hl : raw27525step1Labels = raw27525step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2924 node2924Labels := by rfl

def raw27526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27526Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27526step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27526 raw27526Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw27526 raw27526Labels = mixedMoment B raw27526step0 raw27526step0Labels := by
      have hz : ∀ j, raw27526 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27526step0 = (fun i j => raw27526 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27526step0 raw27526; decide +kernel
      have hl : raw27526step0Labels = raw27526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27526 raw27526Labels permutation265 hz
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw27527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27527Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27527 raw27527Labels = mixedMoment B node2543 node2543Labels := by
  calc
    _ = mixedMoment B node2543 node2543Labels := by rfl

def raw27528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27528Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27528step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27528step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27528 raw27528Labels = mixedMoment B node2429 node2429Labels := by
  calc
    mixedMoment B raw27528 raw27528Labels = mixedMoment B raw27528step0 raw27528step0Labels := by
      have ha : raw27528step0 = (fun i j => raw27528 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27528step0 raw27528; decide +kernel
      have hl : raw27528step0Labels = raw27528Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27528 raw27528Labels permutation176 permutation2
    _ = mixedMoment B node2429 node2429Labels := by rfl

def raw27529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27529Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27529step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27529step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27529 raw27529Labels = mixedMoment B node2422 node2422Labels := by
  calc
    mixedMoment B raw27529 raw27529Labels = mixedMoment B raw27529step0 raw27529step0Labels := by
      have ha : raw27529step0 = (fun i j => raw27529 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27529step0 raw27529; decide +kernel
      have hl : raw27529step0Labels = raw27529Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27529 raw27529Labels permutation176 permutation2
    _ = mixedMoment B node2422 node2422Labels := by rfl

def raw27530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw27530Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27530step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -3, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw27530step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27530step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27530step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27530 raw27530Labels = mixedMoment B node1327 node1327Labels := by
  calc
    mixedMoment B raw27530 raw27530Labels = mixedMoment B raw27530step0 raw27530step0Labels := by
      have ha : raw27530step0 = (fun i j => raw27530 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27530step0 raw27530; decide +kernel
      have hl : raw27530step0Labels = raw27530Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27530 raw27530Labels permutation686 permutation2
    mixedMoment B raw27530step0 raw27530step0Labels = mixedMoment B raw27530step1 raw27530step1Labels := by
      have ha : raw27530step1 = -raw27530step0 := by apply Matrix.ext; change ∀ i j, raw27530step1 i j = -(raw27530step0 i j); unfold raw27530step1 raw27530step0; decide +kernel
      have hl : raw27530step1Labels = raw27530step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1327 node1327Labels := by rfl

def raw27531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27531Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27531 raw27531Labels = mixedMoment B node2349 node2349Labels := by
  calc
    _ = mixedMoment B node2349 node2349Labels := by rfl

def raw27532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw27532Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27532step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27532step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27532 raw27532Labels = mixedMoment B node2543 node2543Labels := by
  calc
    mixedMoment B raw27532 raw27532Labels = mixedMoment B raw27532step0 raw27532step0Labels := by
      have ha : raw27532step0 = (fun i j => raw27532 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27532step0 raw27532; decide +kernel
      have hl : raw27532step0Labels = raw27532Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27532 raw27532Labels permutation154 permutation2
    _ = mixedMoment B node2543 node2543Labels := by rfl

def raw27533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27533Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27533step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27533step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27533step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27533 raw27533Labels = mixedMoment B node2071 node2071Labels := by
  calc
    mixedMoment B raw27533 raw27533Labels = mixedMoment B raw27533step0 raw27533step0Labels := by
      have ha : raw27533step0 = (fun i j => raw27533 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27533step0 raw27533; decide +kernel
      have hl : raw27533step0Labels = raw27533Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27533 raw27533Labels permutation682 permutation2
    mixedMoment B raw27533step0 raw27533step0Labels = mixedMoment B raw27533step1 raw27533step1Labels := by
      have ha : raw27533step1 = -raw27533step0 := by apply Matrix.ext; change ∀ i j, raw27533step1 i j = -(raw27533step0 i j); unfold raw27533step1 raw27533step0; decide +kernel
      have hl : raw27533step1Labels = raw27533step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2071 node2071Labels := by rfl

def raw27534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27534Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27534step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw27534step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27534step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw27534step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27534 raw27534Labels = mixedMoment B node2073 node2073Labels := by
  calc
    mixedMoment B raw27534 raw27534Labels = mixedMoment B raw27534step0 raw27534step0Labels := by
      have ha : raw27534step0 = (fun i j => raw27534 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27534step0 raw27534; decide +kernel
      have hl : raw27534step0Labels = raw27534Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27534 raw27534Labels permutation681 permutation2
    mixedMoment B raw27534step0 raw27534step0Labels = mixedMoment B raw27534step1 raw27534step1Labels := by
      have ha : raw27534step1 = -raw27534step0 := by apply Matrix.ext; change ∀ i j, raw27534step1 i j = -(raw27534step0 i j); unfold raw27534step1 raw27534step0; decide +kernel
      have hl : raw27534step1Labels = raw27534step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2073 node2073Labels := by rfl

def raw27535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27535Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27535step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27535step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27535step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw27535step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27535 raw27535Labels = mixedMoment B node2086 node2086Labels := by
  calc
    mixedMoment B raw27535 raw27535Labels = mixedMoment B raw27535step0 raw27535step0Labels := by
      have ha : raw27535step0 = (fun i j => raw27535 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27535step0 raw27535; decide +kernel
      have hl : raw27535step0Labels = raw27535Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27535 raw27535Labels permutation688 permutation2
    mixedMoment B raw27535step0 raw27535step0Labels = mixedMoment B raw27535step1 raw27535step1Labels := by
      have ha : raw27535step1 = -raw27535step0 := by apply Matrix.ext; change ∀ i j, raw27535step1 i j = -(raw27535step0 i j); unfold raw27535step1 raw27535step0; decide +kernel
      have hl : raw27535step1Labels = raw27535step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2086 node2086Labels := by rfl

def raw27536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27536Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27536step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27536step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27536step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27536 raw27536Labels = mixedMoment B node2077 node2077Labels := by
  calc
    mixedMoment B raw27536 raw27536Labels = mixedMoment B raw27536step0 raw27536step0Labels := by
      have ha : raw27536step0 = (fun i j => raw27536 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27536step0 raw27536; decide +kernel
      have hl : raw27536step0Labels = raw27536Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27536 raw27536Labels permutation680 permutation2
    mixedMoment B raw27536step0 raw27536step0Labels = mixedMoment B raw27536step1 raw27536step1Labels := by
      have ha : raw27536step1 = -raw27536step0 := by apply Matrix.ext; change ∀ i j, raw27536step1 i j = -(raw27536step0 i j); unfold raw27536step1 raw27536step0; decide +kernel
      have hl : raw27536step1Labels = raw27536step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2077 node2077Labels := by rfl

def raw27537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw27537Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27537step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27537step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27537step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27537 raw27537Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw27537 raw27537Labels = mixedMoment B raw27537step0 raw27537step0Labels := by
      have ha : raw27537step0 = (fun i j => raw27537 (permutation640 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27537step0 raw27537; decide +kernel
      have hl : raw27537step0Labels = raw27537Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27537 raw27537Labels permutation640 permutation2
    mixedMoment B raw27537step0 raw27537step0Labels = mixedMoment B raw27537step1 raw27537step1Labels := by
      have ha : raw27537step1 = -raw27537step0 := by apply Matrix.ext; change ∀ i j, raw27537step1 i j = -(raw27537step0 i j); unfold raw27537step1 raw27537step0; decide +kernel
      have hl : raw27537step1Labels = raw27537step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2191 node2191Labels := by rfl

def raw27538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw27538Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27538step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27538step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27538step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27538step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27538 raw27538Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw27538 raw27538Labels = mixedMoment B raw27538step0 raw27538step0Labels := by
      have ha : raw27538step0 = (fun i j => raw27538 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27538step0 raw27538; decide +kernel
      have hl : raw27538step0Labels = raw27538Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27538 raw27538Labels permutation682 permutation2
    mixedMoment B raw27538step0 raw27538step0Labels = mixedMoment B raw27538step1 raw27538step1Labels := by
      have ha : raw27538step1 = -raw27538step0 := by apply Matrix.ext; change ∀ i j, raw27538step1 i j = -(raw27538step0 i j); unfold raw27538step1 raw27538step0; decide +kernel
      have hl : raw27538step1Labels = raw27538step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3558 node3558Labels := by rfl

def raw27539 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw27539Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27539step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw27539step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27539step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw27539step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27539 raw27539Labels = mixedMoment B node4079 node4079Labels := by
  calc
    mixedMoment B raw27539 raw27539Labels = mixedMoment B raw27539step0 raw27539step0Labels := by
      have ha : raw27539step0 = (fun i j => raw27539 (permutation623 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27539step0 raw27539; decide +kernel
      have hl : raw27539step0Labels = raw27539Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27539 raw27539Labels permutation623 permutation0
    mixedMoment B raw27539step0 raw27539step0Labels = mixedMoment B raw27539step1 raw27539step1Labels := by
      have ha : raw27539step1 = -raw27539step0 := by apply Matrix.ext; change ∀ i j, raw27539step1 i j = -(raw27539step0 i j); unfold raw27539step1 raw27539step0; decide +kernel
      have hl : raw27539step1Labels = raw27539step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4079 node4079Labels := by rfl

def raw27540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw27540Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw27540step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27540step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw27540step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27540 raw27540Labels = mixedMoment B node2454 node2454Labels := by
  calc
    mixedMoment B raw27540 raw27540Labels = mixedMoment B raw27540step0 raw27540step0Labels := by
      have ha : raw27540step0 = (fun i j => raw27540 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27540step0 raw27540; decide +kernel
      have hl : raw27540step0Labels = raw27540Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27540 raw27540Labels permutation682 permutation2
    mixedMoment B raw27540step0 raw27540step0Labels = mixedMoment B raw27540step1 raw27540step1Labels := by
      have ha : raw27540step1 = -raw27540step0 := by apply Matrix.ext; change ∀ i j, raw27540step1 i j = -(raw27540step0 i j); unfold raw27540step1 raw27540step0; decide +kernel
      have hl : raw27540step1Labels = raw27540step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2454 node2454Labels := by rfl

def raw27541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw27541Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27541step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw27541step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27541step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw27541step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27541 raw27541Labels = mixedMoment B node2456 node2456Labels := by
  calc
    mixedMoment B raw27541 raw27541Labels = mixedMoment B raw27541step0 raw27541step0Labels := by
      have ha : raw27541step0 = (fun i j => raw27541 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27541step0 raw27541; decide +kernel
      have hl : raw27541step0Labels = raw27541Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27541 raw27541Labels permutation681 permutation2
    mixedMoment B raw27541step0 raw27541step0Labels = mixedMoment B raw27541step1 raw27541step1Labels := by
      have ha : raw27541step1 = -raw27541step0 := by apply Matrix.ext; change ∀ i j, raw27541step1 i j = -(raw27541step0 i j); unfold raw27541step1 raw27541step0; decide +kernel
      have hl : raw27541step1Labels = raw27541step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2456 node2456Labels := by rfl

def raw27542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw27542Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27542step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27542step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27542step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw27542step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27542 raw27542Labels = mixedMoment B node2491 node2491Labels := by
  calc
    mixedMoment B raw27542 raw27542Labels = mixedMoment B raw27542step0 raw27542step0Labels := by
      have ha : raw27542step0 = (fun i j => raw27542 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27542step0 raw27542; decide +kernel
      have hl : raw27542step0Labels = raw27542Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27542 raw27542Labels permutation688 permutation2
    mixedMoment B raw27542step0 raw27542step0Labels = mixedMoment B raw27542step1 raw27542step1Labels := by
      have ha : raw27542step1 = -raw27542step0 := by apply Matrix.ext; change ∀ i j, raw27542step1 i j = -(raw27542step0 i j); unfold raw27542step1 raw27542step0; decide +kernel
      have hl : raw27542step1Labels = raw27542step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2491 node2491Labels := by rfl

def raw27543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw27543Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27543step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw27543step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27543step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw27543step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27543 raw27543Labels = mixedMoment B node2462 node2462Labels := by
  calc
    mixedMoment B raw27543 raw27543Labels = mixedMoment B raw27543step0 raw27543step0Labels := by
      have ha : raw27543step0 = (fun i j => raw27543 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27543step0 raw27543; decide +kernel
      have hl : raw27543step0Labels = raw27543Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27543 raw27543Labels permutation680 permutation2
    mixedMoment B raw27543step0 raw27543step0Labels = mixedMoment B raw27543step1 raw27543step1Labels := by
      have ha : raw27543step1 = -raw27543step0 := by apply Matrix.ext; change ∀ i j, raw27543step1 i j = -(raw27543step0 i j); unfold raw27543step1 raw27543step0; decide +kernel
      have hl : raw27543step1Labels = raw27543step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2462 node2462Labels := by rfl

def raw27544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw27544Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw27544step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27544step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27544step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27544 raw27544Labels = mixedMoment B node2698 node2698Labels := by
  calc
    mixedMoment B raw27544 raw27544Labels = mixedMoment B raw27544step0 raw27544step0Labels := by
      have ha : raw27544step0 = (fun i j => raw27544 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27544step0 raw27544; decide +kernel
      have hl : raw27544step0Labels = raw27544Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27544 raw27544Labels permutation646 permutation2
    mixedMoment B raw27544step0 raw27544step0Labels = mixedMoment B raw27544step1 raw27544step1Labels := by
      have ha : raw27544step1 = -raw27544step0 := by apply Matrix.ext; change ∀ i j, raw27544step1 i j = -(raw27544step0 i j); unfold raw27544step1 raw27544step0; decide +kernel
      have hl : raw27544step1Labels = raw27544step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2698 node2698Labels := by rfl

def raw27545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw27545Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw27545step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27545step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27545step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27545 raw27545Labels = mixedMoment B node3796 node3796Labels := by
  calc
    mixedMoment B raw27545 raw27545Labels = mixedMoment B raw27545step0 raw27545step0Labels := by
      have ha : raw27545step0 = (fun i j => raw27545 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27545step0 raw27545; decide +kernel
      have hl : raw27545step0Labels = raw27545Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27545 raw27545Labels permutation682 permutation2
    mixedMoment B raw27545step0 raw27545step0Labels = mixedMoment B raw27545step1 raw27545step1Labels := by
      have ha : raw27545step1 = -raw27545step0 := by apply Matrix.ext; change ∀ i j, raw27545step1 i j = -(raw27545step0 i j); unfold raw27545step1 raw27545step0; decide +kernel
      have hl : raw27545step1Labels = raw27545step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3796 node3796Labels := by rfl

def raw27546 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-2, 2], ![1, -1], ![2, -2]]
def raw27546Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27546step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw27546step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27546 raw27546Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw27546 raw27546Labels = mixedMoment B raw27546step0 raw27546step0Labels := by
      have ha : raw27546step0 = (fun i j => raw27546 (permutation434 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27546step0 raw27546; decide +kernel
      have hl : raw27546step0Labels = raw27546Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27546 raw27546Labels permutation434 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

def raw27547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw27547Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw27547step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27547 raw27547Labels = mixedMoment B node3016 node3016Labels := by
  calc
    mixedMoment B raw27547 raw27547Labels = mixedMoment B raw27547step0 raw27547step0Labels := by
      have ha : raw27547step0 = (fun i j => raw27547 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27547step0 raw27547; decide +kernel
      have hl : raw27547step0Labels = raw27547Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27547 raw27547Labels permutation200 permutation2
    _ = mixedMoment B node3016 node3016Labels := by rfl

def raw27548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw27548Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw27548step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27548 raw27548Labels = mixedMoment B node2908 node2908Labels := by
  calc
    mixedMoment B raw27548 raw27548Labels = mixedMoment B raw27548step0 raw27548step0Labels := by
      have ha : raw27548step0 = (fun i j => raw27548 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27548step0 raw27548; decide +kernel
      have hl : raw27548step0Labels = raw27548Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27548 raw27548Labels permutation158 permutation2
    _ = mixedMoment B node2908 node2908Labels := by rfl

def raw27549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw27549Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27549step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw27549step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27549 raw27549Labels = mixedMoment B node2715 node2715Labels := by
  calc
    mixedMoment B raw27549 raw27549Labels = mixedMoment B raw27549step0 raw27549step0Labels := by
      have ha : raw27549step0 = (fun i j => raw27549 (permutation463 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27549step0 raw27549; decide +kernel
      have hl : raw27549step0Labels = raw27549Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27549 raw27549Labels permutation463 permutation4
    _ = mixedMoment B node2715 node2715Labels := by rfl

def raw27550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw27550Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27550step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw27550step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27550 raw27550Labels = mixedMoment B node2905 node2905Labels := by
  calc
    mixedMoment B raw27550 raw27550Labels = mixedMoment B raw27550step0 raw27550step0Labels := by
      have ha : raw27550step0 = (fun i j => raw27550 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27550step0 raw27550; decide +kernel
      have hl : raw27550step0Labels = raw27550Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27550 raw27550Labels permutation158 permutation2
    _ = mixedMoment B node2905 node2905Labels := by rfl

def raw27551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw27551Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw27551step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27551step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw27551step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27551 raw27551Labels = mixedMoment B node1992 node1992Labels := by
  calc
    mixedMoment B raw27551 raw27551Labels = mixedMoment B raw27551step0 raw27551step0Labels := by
      have ha : raw27551step0 = (fun i j => raw27551 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27551step0 raw27551; decide +kernel
      have hl : raw27551step0Labels = raw27551Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27551 raw27551Labels permutation682 permutation2
    mixedMoment B raw27551step0 raw27551step0Labels = mixedMoment B raw27551step1 raw27551step1Labels := by
      have ha : raw27551step1 = -raw27551step0 := by apply Matrix.ext; change ∀ i j, raw27551step1 i j = -(raw27551step0 i j); unfold raw27551step1 raw27551step0; decide +kernel
      have hl : raw27551step1Labels = raw27551step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1992 node1992Labels := by rfl

def raw27552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw27552Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27552step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw27552step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27552step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw27552step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27552 raw27552Labels = mixedMoment B node1994 node1994Labels := by
  calc
    mixedMoment B raw27552 raw27552Labels = mixedMoment B raw27552step0 raw27552step0Labels := by
      have ha : raw27552step0 = (fun i j => raw27552 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27552step0 raw27552; decide +kernel
      have hl : raw27552step0Labels = raw27552Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27552 raw27552Labels permutation681 permutation2
    mixedMoment B raw27552step0 raw27552step0Labels = mixedMoment B raw27552step1 raw27552step1Labels := by
      have ha : raw27552step1 = -raw27552step0 := by apply Matrix.ext; change ∀ i j, raw27552step1 i j = -(raw27552step0 i j); unfold raw27552step1 raw27552step0; decide +kernel
      have hl : raw27552step1Labels = raw27552step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1994 node1994Labels := by rfl

def raw27553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw27553Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27553step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27553step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27553step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw27553step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27553 raw27553Labels = mixedMoment B node2031 node2031Labels := by
  calc
    mixedMoment B raw27553 raw27553Labels = mixedMoment B raw27553step0 raw27553step0Labels := by
      have ha : raw27553step0 = (fun i j => raw27553 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27553step0 raw27553; decide +kernel
      have hl : raw27553step0Labels = raw27553Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27553 raw27553Labels permutation688 permutation2
    mixedMoment B raw27553step0 raw27553step0Labels = mixedMoment B raw27553step1 raw27553step1Labels := by
      have ha : raw27553step1 = -raw27553step0 := by apply Matrix.ext; change ∀ i j, raw27553step1 i j = -(raw27553step0 i j); unfold raw27553step1 raw27553step0; decide +kernel
      have hl : raw27553step1Labels = raw27553step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2031 node2031Labels := by rfl

def raw27554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw27554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27554step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw27554step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27554step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw27554step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27554 raw27554Labels = mixedMoment B node2000 node2000Labels := by
  calc
    mixedMoment B raw27554 raw27554Labels = mixedMoment B raw27554step0 raw27554step0Labels := by
      have ha : raw27554step0 = (fun i j => raw27554 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27554step0 raw27554; decide +kernel
      have hl : raw27554step0Labels = raw27554Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27554 raw27554Labels permutation680 permutation2
    mixedMoment B raw27554step0 raw27554step0Labels = mixedMoment B raw27554step1 raw27554step1Labels := by
      have ha : raw27554step1 = -raw27554step0 := by apply Matrix.ext; change ∀ i j, raw27554step1 i j = -(raw27554step0 i j); unfold raw27554step1 raw27554step0; decide +kernel
      have hl : raw27554step1Labels = raw27554step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2000 node2000Labels := by rfl

def raw27555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![0, 0, 0], ![3, 0, -3]]
def raw27555Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![3, 0, -3]]
def raw27555step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27555step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw27555step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27555step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27555step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27555 raw27555Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw27555 raw27555Labels = mixedMoment B raw27555step0 raw27555step0Labels := by
      have hz : ∀ j, raw27555 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27555step0 = (fun i j => raw27555 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27555step0 raw27555; decide +kernel
      have hl : raw27555step0Labels = raw27555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27555 raw27555Labels permutation520 hz
    mixedMoment B raw27555step0 raw27555step0Labels = mixedMoment B raw27555step1 raw27555step1Labels := by
      have ha : raw27555step1 = (fun i j => raw27555step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27555step1 raw27555step0; decide +kernel
      have hl : raw27555step1Labels = raw27555step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27555step0 raw27555step0Labels permutation145 permutation2
    mixedMoment B raw27555step1 raw27555step1Labels = mixedMoment B raw27555step2 raw27555step2Labels := by
      have ha : raw27555step2 = -raw27555step1 := by apply Matrix.ext; change ∀ i j, raw27555step2 i j = -(raw27555step1 i j); unfold raw27555step2 raw27555step1; decide +kernel
      have hl : raw27555step2Labels = raw27555step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2216 node2216Labels := by rfl

def raw27556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw27556Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27556step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw27556step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27556step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27556step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27556 raw27556Labels = mixedMoment B node3517 node3517Labels := by
  calc
    mixedMoment B raw27556 raw27556Labels = mixedMoment B raw27556step0 raw27556step0Labels := by
      have ha : raw27556step0 = (fun i j => raw27556 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27556step0 raw27556; decide +kernel
      have hl : raw27556step0Labels = raw27556Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27556 raw27556Labels permutation682 permutation2
    mixedMoment B raw27556step0 raw27556step0Labels = mixedMoment B raw27556step1 raw27556step1Labels := by
      have ha : raw27556step1 = -raw27556step0 := by apply Matrix.ext; change ∀ i j, raw27556step1 i j = -(raw27556step0 i j); unfold raw27556step1 raw27556step0; decide +kernel
      have hl : raw27556step1Labels = raw27556step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3517 node3517Labels := by rfl

def raw27557 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-2, 2], ![0, 0], ![3, -3]]
def raw27557Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27557step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-2, 2], ![3, -3]]
def raw27557step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27557step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw27557step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27557step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw27557step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27557 raw27557Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw27557 raw27557Labels = mixedMoment B raw27557step0 raw27557step0Labels := by
      have hz : ∀ j, raw27557 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27557step0 = (fun i j => raw27557 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27557step0 raw27557; decide +kernel
      have hl : raw27557step0Labels = raw27557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27557 raw27557Labels permutation520 hz
    mixedMoment B raw27557step0 raw27557step0Labels = mixedMoment B raw27557step1 raw27557step1Labels := by
      have ha : raw27557step1 = (fun i j => raw27557step0 (permutation140 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27557step1 raw27557step0; decide +kernel
      have hl : raw27557step1Labels = raw27557step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27557step0 raw27557step0Labels permutation140 permutation0
    mixedMoment B raw27557step1 raw27557step1Labels = mixedMoment B raw27557step2 raw27557step2Labels := by
      have ha : raw27557step2 = -raw27557step1 := by apply Matrix.ext; change ∀ i j, raw27557step2 i j = -(raw27557step1 i j); unfold raw27557step2 raw27557step1; decide +kernel
      have hl : raw27557step2Labels = raw27557step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw27558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27558Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27558step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27558 raw27558Labels = mixedMoment B node4970 node4970Labels := by
  calc
    mixedMoment B raw27558 raw27558Labels = mixedMoment B raw27558step0 raw27558step0Labels := by
      have hz : ∀ j, raw27558 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27558step0 = (fun i j => raw27558 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27558step0 raw27558; decide +kernel
      have hl : raw27558step0Labels = raw27558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27558 raw27558Labels permutation434 hz
    _ = mixedMoment B node4970 node4970Labels := by rfl

def raw27559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27559Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27559step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27559step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27559 raw27559Labels = mixedMoment B node5113 node5113Labels := by
  calc
    mixedMoment B raw27559 raw27559Labels = mixedMoment B raw27559step0 raw27559step0Labels := by
      have ha : raw27559step0 = (fun i j => raw27559 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27559step0 raw27559; decide +kernel
      have hl : raw27559step0Labels = raw27559Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27559 raw27559Labels permutation158 permutation2
    _ = mixedMoment B node5113 node5113Labels := by rfl

def raw27560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27560step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27560 raw27560Labels = mixedMoment B node4970 node4970Labels := by
  calc
    mixedMoment B raw27560 raw27560Labels = mixedMoment B raw27560step0 raw27560step0Labels := by
      have hz : ∀ j, raw27560 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27560step0 = (fun i j => raw27560 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27560step0 raw27560; decide +kernel
      have hl : raw27560step0Labels = raw27560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27560 raw27560Labels permutation346 hz
    _ = mixedMoment B node4970 node4970Labels := by rfl

def raw27561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27561Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27561 raw27561Labels = mixedMoment B node5113 node5113Labels := by
  calc
    _ = mixedMoment B node5113 node5113Labels := by rfl

def raw27562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw27562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw27562step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27562step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![3, -1, -2]]
def raw27562step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27562 raw27562Labels = mixedMoment B node4979 node4979Labels := by
  calc
    mixedMoment B raw27562 raw27562Labels = mixedMoment B raw27562step0 raw27562step0Labels := by
      have hz : ∀ j, raw27562 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27562step0 = (fun i j => raw27562 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27562step0 raw27562; decide +kernel
      have hl : raw27562step0Labels = raw27562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27562 raw27562Labels permutation434 hz
    mixedMoment B raw27562step0 raw27562step0Labels = mixedMoment B raw27562step1 raw27562step1Labels := by
      have hz : ∀ j, raw27562step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27562step1 = (fun i j => raw27562step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27562step1 raw27562step0; decide +kernel
      have hl : raw27562step1Labels = raw27562step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27562step0 raw27562step0Labels permutation80 hz
    _ = mixedMoment B node4979 node4979Labels := by rfl

def raw27563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw27563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw27563step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27563step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw27563step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27563step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27563step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27563 raw27563Labels = mixedMoment B node4970 node4970Labels := by
  calc
    mixedMoment B raw27563 raw27563Labels = mixedMoment B raw27563step0 raw27563step0Labels := by
      have hz : ∀ j, raw27563 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27563step0 = (fun i j => raw27563 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27563step0 raw27563; decide +kernel
      have hl : raw27563step0Labels = raw27563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27563 raw27563Labels permutation434 hz
    mixedMoment B raw27563step0 raw27563step0Labels = mixedMoment B raw27563step1 raw27563step1Labels := by
      have ha : raw27563step1 = (fun i j => raw27563step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27563step1 raw27563step0; decide +kernel
      have hl : raw27563step1Labels = raw27563step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27563step0 raw27563step0Labels permutation149 permutation2
    mixedMoment B raw27563step1 raw27563step1Labels = mixedMoment B raw27563step2 raw27563step2Labels := by
      have ha : raw27563step2 = -raw27563step1 := by apply Matrix.ext; change ∀ i j, raw27563step2 i j = -(raw27563step1 i j); unfold raw27563step2 raw27563step1; decide +kernel
      have hl : raw27563step2Labels = raw27563step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4970 node4970Labels := by rfl

def raw27564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw27564Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw27564step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw27564step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27564step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27564step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27564 raw27564Labels = mixedMoment B node4970 node4970Labels := by
  calc
    mixedMoment B raw27564 raw27564Labels = mixedMoment B raw27564step0 raw27564step0Labels := by
      have hz : ∀ j, raw27564 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27564step0 = (fun i j => raw27564 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27564step0 raw27564; decide +kernel
      have hl : raw27564step0Labels = raw27564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27564 raw27564Labels permutation346 hz
    mixedMoment B raw27564step0 raw27564step0Labels = mixedMoment B raw27564step1 raw27564step1Labels := by
      have ha : raw27564step1 = (fun i j => raw27564step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27564step1 raw27564step0; decide +kernel
      have hl : raw27564step1Labels = raw27564step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27564step0 raw27564step0Labels permutation149 permutation2
    mixedMoment B raw27564step1 raw27564step1Labels = mixedMoment B raw27564step2 raw27564step2Labels := by
      have ha : raw27564step2 = -raw27564step1 := by apply Matrix.ext; change ∀ i j, raw27564step2 i j = -(raw27564step1 i j); unfold raw27564step2 raw27564step1; decide +kernel
      have hl : raw27564step2Labels = raw27564step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4970 node4970Labels := by rfl

def raw27565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw27565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw27565step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27565step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![4, -2, -2]]
def raw27565step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27565step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw27565step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27565step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27565step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27565step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27565step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27565 raw27565Labels = mixedMoment B node4559 node4559Labels := by
  calc
    mixedMoment B raw27565 raw27565Labels = mixedMoment B raw27565step0 raw27565step0Labels := by
      have hz : ∀ j, raw27565 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27565step0 = (fun i j => raw27565 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27565step0 raw27565; decide +kernel
      have hl : raw27565step0Labels = raw27565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27565 raw27565Labels permutation434 hz
    mixedMoment B raw27565step0 raw27565step0Labels = mixedMoment B raw27565step1 raw27565step1Labels := by
      have hz : ∀ j, raw27565step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27565step1 = (fun i j => raw27565step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27565step1 raw27565step0; decide +kernel
      have hl : raw27565step1Labels = raw27565step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27565step0 raw27565step0Labels permutation80 hz
    mixedMoment B raw27565step1 raw27565step1Labels = mixedMoment B raw27565step2 raw27565step2Labels := by
      have ha : raw27565step2 = (fun i j => raw27565step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27565step2 raw27565step1; decide +kernel
      have hl : raw27565step2Labels = raw27565step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27565step1 raw27565step1Labels permutation31 permutation3
    mixedMoment B raw27565step2 raw27565step2Labels = mixedMoment B raw27565step3 raw27565step3Labels := by
      have ha : raw27565step3 = -raw27565step2 := by apply Matrix.ext; change ∀ i j, raw27565step3 i j = -(raw27565step2 i j); unfold raw27565step3 raw27565step2; decide +kernel
      have hl : raw27565step3Labels = raw27565step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27565step3 raw27565step3Labels = mixedMoment B raw27565step4 raw27565step4Labels := by
      have ha : raw27565step4 = raw27565step3 := by apply Matrix.ext; unfold raw27565step4 raw27565step3; decide +kernel
      have hl : raw27565step3Labels = labelEmbedding6 ∘ raw27565step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27565step3 raw27565step3Labels raw27565step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4559 node4559Labels := by rfl

def raw27566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw27566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw27566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27566step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27566step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27566step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27566step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27566step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27566 raw27566Labels = mixedMoment B node4551 node4551Labels := by
  calc
    mixedMoment B raw27566 raw27566Labels = mixedMoment B raw27566step0 raw27566step0Labels := by
      have hz : ∀ j, raw27566 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27566step0 = (fun i j => raw27566 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27566step0 raw27566; decide +kernel
      have hl : raw27566step0Labels = raw27566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27566 raw27566Labels permutation434 hz
    mixedMoment B raw27566step0 raw27566step0Labels = mixedMoment B raw27566step1 raw27566step1Labels := by
      have ha : raw27566step1 = (fun i j => raw27566step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27566step1 raw27566step0; decide +kernel
      have hl : raw27566step1Labels = raw27566step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27566step0 raw27566step0Labels permutation149 permutation3
    mixedMoment B raw27566step1 raw27566step1Labels = mixedMoment B raw27566step2 raw27566step2Labels := by
      have ha : raw27566step2 = -raw27566step1 := by apply Matrix.ext; change ∀ i j, raw27566step2 i j = -(raw27566step1 i j); unfold raw27566step2 raw27566step1; decide +kernel
      have hl : raw27566step2Labels = raw27566step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27566step2 raw27566step2Labels = mixedMoment B raw27566step3 raw27566step3Labels := by
      have ha : raw27566step3 = raw27566step2 := by apply Matrix.ext; unfold raw27566step3 raw27566step2; decide +kernel
      have hl : raw27566step2Labels = labelEmbedding6 ∘ raw27566step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27566step2 raw27566step2Labels raw27566step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4551 node4551Labels := by rfl

def raw27567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw27567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw27567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27567step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27567step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27567step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27567step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27567step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27567 raw27567Labels = mixedMoment B node4551 node4551Labels := by
  calc
    mixedMoment B raw27567 raw27567Labels = mixedMoment B raw27567step0 raw27567step0Labels := by
      have hz : ∀ j, raw27567 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27567step0 = (fun i j => raw27567 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27567step0 raw27567; decide +kernel
      have hl : raw27567step0Labels = raw27567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27567 raw27567Labels permutation346 hz
    mixedMoment B raw27567step0 raw27567step0Labels = mixedMoment B raw27567step1 raw27567step1Labels := by
      have ha : raw27567step1 = (fun i j => raw27567step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27567step1 raw27567step0; decide +kernel
      have hl : raw27567step1Labels = raw27567step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27567step0 raw27567step0Labels permutation149 permutation3
    mixedMoment B raw27567step1 raw27567step1Labels = mixedMoment B raw27567step2 raw27567step2Labels := by
      have ha : raw27567step2 = -raw27567step1 := by apply Matrix.ext; change ∀ i j, raw27567step2 i j = -(raw27567step1 i j); unfold raw27567step2 raw27567step1; decide +kernel
      have hl : raw27567step2Labels = raw27567step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27567step2 raw27567step2Labels = mixedMoment B raw27567step3 raw27567step3Labels := by
      have ha : raw27567step3 = raw27567step2 := by apply Matrix.ext; unfold raw27567step3 raw27567step2; decide +kernel
      have hl : raw27567step2Labels = labelEmbedding6 ∘ raw27567step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27567step2 raw27567step2Labels raw27567step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4551 node4551Labels := by rfl

def raw27568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27568Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27568step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27568step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27568step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27568step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw27568step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27568step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw27568step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27568 raw27568Labels = mixedMoment B node2968 node2968Labels := by
  calc
    mixedMoment B raw27568 raw27568Labels = mixedMoment B raw27568step0 raw27568step0Labels := by
      have hz : ∀ j, raw27568 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27568step0 = (fun i j => raw27568 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27568step0 raw27568; decide +kernel
      have hl : raw27568step0Labels = raw27568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27568 raw27568Labels permutation434 hz
    mixedMoment B raw27568step0 raw27568step0Labels = mixedMoment B raw27568step1 raw27568step1Labels := by
      have hz : ∀ j, raw27568step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27568step1 = (fun i j => raw27568step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27568step1 raw27568step0; decide +kernel
      have hl : raw27568step1Labels = raw27568step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27568step0 raw27568step0Labels permutation80 hz
    mixedMoment B raw27568step1 raw27568step1Labels = mixedMoment B raw27568step2 raw27568step2Labels := by
      have ha : raw27568step2 = (fun i j => raw27568step1 (permutation30 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27568step2 raw27568step1; decide +kernel
      have hl : raw27568step2Labels = raw27568step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27568step1 raw27568step1Labels permutation30 permutation3
    mixedMoment B raw27568step2 raw27568step2Labels = mixedMoment B raw27568step3 raw27568step3Labels := by
      have ha : raw27568step3 = -raw27568step2 := by apply Matrix.ext; change ∀ i j, raw27568step3 i j = -(raw27568step2 i j); unfold raw27568step3 raw27568step2; decide +kernel
      have hl : raw27568step3Labels = raw27568step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2968 node2968Labels := by rfl

def raw27569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27569Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27569step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27569step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw27569step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27569step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27569step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27569 raw27569Labels = mixedMoment B node2963 node2963Labels := by
  calc
    mixedMoment B raw27569 raw27569Labels = mixedMoment B raw27569step0 raw27569step0Labels := by
      have hz : ∀ j, raw27569 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27569step0 = (fun i j => raw27569 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27569step0 raw27569; decide +kernel
      have hl : raw27569step0Labels = raw27569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27569 raw27569Labels permutation434 hz
    mixedMoment B raw27569step0 raw27569step0Labels = mixedMoment B raw27569step1 raw27569step1Labels := by
      have ha : raw27569step1 = (fun i j => raw27569step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27569step1 raw27569step0; decide +kernel
      have hl : raw27569step1Labels = raw27569step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27569step0 raw27569step0Labels permutation149 permutation3
    mixedMoment B raw27569step1 raw27569step1Labels = mixedMoment B raw27569step2 raw27569step2Labels := by
      have ha : raw27569step2 = -raw27569step1 := by apply Matrix.ext; change ∀ i j, raw27569step2 i j = -(raw27569step1 i j); unfold raw27569step2 raw27569step1; decide +kernel
      have hl : raw27569step2Labels = raw27569step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2963 node2963Labels := by rfl

def raw27570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27570Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27570step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw27570step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27570step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27570step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27570 raw27570Labels = mixedMoment B node2963 node2963Labels := by
  calc
    mixedMoment B raw27570 raw27570Labels = mixedMoment B raw27570step0 raw27570step0Labels := by
      have hz : ∀ j, raw27570 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27570step0 = (fun i j => raw27570 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27570step0 raw27570; decide +kernel
      have hl : raw27570step0Labels = raw27570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27570 raw27570Labels permutation346 hz
    mixedMoment B raw27570step0 raw27570step0Labels = mixedMoment B raw27570step1 raw27570step1Labels := by
      have ha : raw27570step1 = (fun i j => raw27570step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27570step1 raw27570step0; decide +kernel
      have hl : raw27570step1Labels = raw27570step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27570step0 raw27570step0Labels permutation149 permutation3
    mixedMoment B raw27570step1 raw27570step1Labels = mixedMoment B raw27570step2 raw27570step2Labels := by
      have ha : raw27570step2 = -raw27570step1 := by apply Matrix.ext; change ∀ i j, raw27570step2 i j = -(raw27570step1 i j); unfold raw27570step2 raw27570step1; decide +kernel
      have hl : raw27570step2Labels = raw27570step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2963 node2963Labels := by rfl

def raw27571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw27571Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw27571step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27571step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw27571step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27571step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![3, -1, -2]]
def raw27571step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27571step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -2, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw27571step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27571step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw27571step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27571 raw27571Labels = mixedMoment B node3124 node3124Labels := by
  calc
    mixedMoment B raw27571 raw27571Labels = mixedMoment B raw27571step0 raw27571step0Labels := by
      have hz : ∀ j, raw27571 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27571step0 = (fun i j => raw27571 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27571step0 raw27571; decide +kernel
      have hl : raw27571step0Labels = raw27571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27571 raw27571Labels permutation520 hz
    mixedMoment B raw27571step0 raw27571step0Labels = mixedMoment B raw27571step1 raw27571step1Labels := by
      have hz : ∀ j, raw27571step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw27571step1 = (fun i j => raw27571step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw27571step1 raw27571step0; decide +kernel
      have hl : raw27571step1Labels = raw27571step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27571step0 raw27571step0Labels permutation104 hz
    mixedMoment B raw27571step1 raw27571step1Labels = mixedMoment B raw27571step2 raw27571step2Labels := by
      have hz : ∀ j, raw27571step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw27571step2 = (fun i j => raw27571step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw27571step2 raw27571step1; decide +kernel
      have hl : raw27571step2Labels = raw27571step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27571step1 raw27571step1Labels permutation20 hz
    mixedMoment B raw27571step2 raw27571step2Labels = mixedMoment B raw27571step3 raw27571step3Labels := by
      have ha : raw27571step3 = (fun i j => raw27571step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27571step3 raw27571step2; decide +kernel
      have hl : raw27571step3Labels = raw27571step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27571step2 raw27571step2Labels permutation7 permutation3
    mixedMoment B raw27571step3 raw27571step3Labels = mixedMoment B raw27571step4 raw27571step4Labels := by
      have ha : raw27571step4 = -raw27571step3 := by apply Matrix.ext; change ∀ i j, raw27571step4 i j = -(raw27571step3 i j); unfold raw27571step4 raw27571step3; decide +kernel
      have hl : raw27571step4Labels = raw27571step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3124 node3124Labels := by rfl

def raw27572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw27572Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw27572step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27572step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw27572step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27572step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0]]
def raw27572step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27572 raw27572Labels = mixedMoment B node4037 node4037Labels := by
  calc
    mixedMoment B raw27572 raw27572Labels = mixedMoment B raw27572step0 raw27572step0Labels := by
      have hz : ∀ j, raw27572 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27572step0 = (fun i j => raw27572 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27572step0 raw27572; decide +kernel
      have hl : raw27572step0Labels = raw27572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27572 raw27572Labels permutation434 hz
    mixedMoment B raw27572step0 raw27572step0Labels = mixedMoment B raw27572step1 raw27572step1Labels := by
      have hz : ∀ j, raw27572step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27572step1 = (fun i j => raw27572step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27572step1 raw27572step0; decide +kernel
      have hl : raw27572step1Labels = raw27572step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27572step0 raw27572step0Labels permutation80 hz
    mixedMoment B raw27572step1 raw27572step1Labels = mixedMoment B raw27572step2 raw27572step2Labels := by
      have ha : raw27572step2 = (fun i j => raw27572step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27572step2 raw27572step1; decide +kernel
      have hl : raw27572step2Labels = raw27572step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27572step1 raw27572step1Labels permutation8 permutation3
    _ = mixedMoment B node4037 node4037Labels := by rfl

def raw27573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27573Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27573step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27573step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27573step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27573 raw27573Labels = mixedMoment B node2815 node2815Labels := by
  calc
    mixedMoment B raw27573 raw27573Labels = mixedMoment B raw27573step0 raw27573step0Labels := by
      have hz : ∀ j, raw27573 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27573step0 = (fun i j => raw27573 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27573step0 raw27573; decide +kernel
      have hl : raw27573step0Labels = raw27573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27573 raw27573Labels permutation434 hz
    mixedMoment B raw27573step0 raw27573step0Labels = mixedMoment B raw27573step1 raw27573step1Labels := by
      have ha : raw27573step1 = (fun i j => raw27573step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27573step1 raw27573step0; decide +kernel
      have hl : raw27573step1Labels = raw27573step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27573step0 raw27573step0Labels permutation32 permutation3
    _ = mixedMoment B node2815 node2815Labels := by rfl

def raw27574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27574Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27574step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27574step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27574 raw27574Labels = mixedMoment B node2894 node2894Labels := by
  calc
    mixedMoment B raw27574 raw27574Labels = mixedMoment B raw27574step0 raw27574step0Labels := by
      have ha : raw27574step0 = (fun i j => raw27574 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27574step0 raw27574; decide +kernel
      have hl : raw27574step0Labels = raw27574Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27574 raw27574Labels permutation158 permutation3
    _ = mixedMoment B node2894 node2894Labels := by rfl

def raw27575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw27575Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw27575step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27575step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27575step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27575step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw27575step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27575 raw27575Labels = mixedMoment B node2965 node2965Labels := by
  calc
    mixedMoment B raw27575 raw27575Labels = mixedMoment B raw27575step0 raw27575step0Labels := by
      have hz : ∀ j, raw27575 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27575step0 = (fun i j => raw27575 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27575step0 raw27575; decide +kernel
      have hl : raw27575step0Labels = raw27575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27575 raw27575Labels permutation520 hz
    mixedMoment B raw27575step0 raw27575step0Labels = mixedMoment B raw27575step1 raw27575step1Labels := by
      have hz : ∀ j, raw27575step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw27575step1 = (fun i j => raw27575step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw27575step1 raw27575step0; decide +kernel
      have hl : raw27575step1Labels = raw27575step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27575step0 raw27575step0Labels permutation104 hz
    mixedMoment B raw27575step1 raw27575step1Labels = mixedMoment B raw27575step2 raw27575step2Labels := by
      have ha : raw27575step2 = (fun i j => raw27575step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27575step2 raw27575step1; decide +kernel
      have hl : raw27575step2Labels = raw27575step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27575step1 raw27575step1Labels permutation8 permutation3
    _ = mixedMoment B node2965 node2965Labels := by rfl

def raw27576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw27576Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw27576step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27576step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27576 raw27576Labels = mixedMoment B node2963 node2963Labels := by
  calc
    mixedMoment B raw27576 raw27576Labels = mixedMoment B raw27576step0 raw27576step0Labels := by
      have hz : ∀ j, raw27576 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27576step0 = (fun i j => raw27576 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27576step0 raw27576; decide +kernel
      have hl : raw27576step0Labels = raw27576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27576 raw27576Labels permutation434 hz
    mixedMoment B raw27576step0 raw27576step0Labels = mixedMoment B raw27576step1 raw27576step1Labels := by
      have ha : raw27576step1 = (fun i j => raw27576step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27576step1 raw27576step0; decide +kernel
      have hl : raw27576step1Labels = raw27576step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27576step0 raw27576step0Labels permutation32 permutation3
    _ = mixedMoment B node2963 node2963Labels := by rfl

def raw27577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27577Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27577step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27577step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27577 raw27577Labels = mixedMoment B node2815 node2815Labels := by
  calc
    mixedMoment B raw27577 raw27577Labels = mixedMoment B raw27577step0 raw27577step0Labels := by
      have hz : ∀ j, raw27577 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27577step0 = (fun i j => raw27577 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27577step0 raw27577; decide +kernel
      have hl : raw27577step0Labels = raw27577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27577 raw27577Labels permutation346 hz
    mixedMoment B raw27577step0 raw27577step0Labels = mixedMoment B raw27577step1 raw27577step1Labels := by
      have ha : raw27577step1 = (fun i j => raw27577step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27577step1 raw27577step0; decide +kernel
      have hl : raw27577step1Labels = raw27577step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27577step0 raw27577step0Labels permutation32 permutation3
    _ = mixedMoment B node2815 node2815Labels := by rfl

def raw27578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27578Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27578step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27578step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27578 raw27578Labels = mixedMoment B node2894 node2894Labels := by
  calc
    mixedMoment B raw27578 raw27578Labels = mixedMoment B raw27578step0 raw27578step0Labels := by
      have ha : raw27578step0 = (fun i j => raw27578 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27578step0 raw27578; decide +kernel
      have hl : raw27578step0Labels = raw27578Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27578 raw27578Labels permutation152 permutation3
    _ = mixedMoment B node2894 node2894Labels := by rfl

def raw27579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw27579Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27579step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27579step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27579step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27579step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw27579step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27579 raw27579Labels = mixedMoment B node2965 node2965Labels := by
  calc
    mixedMoment B raw27579 raw27579Labels = mixedMoment B raw27579step0 raw27579step0Labels := by
      have hz : ∀ j, raw27579 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27579step0 = (fun i j => raw27579 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27579step0 raw27579; decide +kernel
      have hl : raw27579step0Labels = raw27579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27579 raw27579Labels permutation520 hz
    mixedMoment B raw27579step0 raw27579step0Labels = mixedMoment B raw27579step1 raw27579step1Labels := by
      have hz : ∀ j, raw27579step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27579step1 = (fun i j => raw27579step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27579step1 raw27579step0; decide +kernel
      have hl : raw27579step1Labels = raw27579step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27579step0 raw27579step0Labels permutation80 hz
    mixedMoment B raw27579step1 raw27579step1Labels = mixedMoment B raw27579step2 raw27579step2Labels := by
      have ha : raw27579step2 = (fun i j => raw27579step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27579step2 raw27579step1; decide +kernel
      have hl : raw27579step2Labels = raw27579step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27579step1 raw27579step1Labels permutation8 permutation3
    _ = mixedMoment B node2965 node2965Labels := by rfl

def raw27580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw27580Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw27580step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27580step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![3, -1, -2]]
def raw27580step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27580step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 0, -2], ![3, -2, -1]]
def raw27580step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27580 raw27580Labels = mixedMoment B node2820 node2820Labels := by
  calc
    mixedMoment B raw27580 raw27580Labels = mixedMoment B raw27580step0 raw27580step0Labels := by
      have hz : ∀ j, raw27580 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27580step0 = (fun i j => raw27580 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27580step0 raw27580; decide +kernel
      have hl : raw27580step0Labels = raw27580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27580 raw27580Labels permutation434 hz
    mixedMoment B raw27580step0 raw27580step0Labels = mixedMoment B raw27580step1 raw27580step1Labels := by
      have hz : ∀ j, raw27580step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27580step1 = (fun i j => raw27580step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27580step1 raw27580step0; decide +kernel
      have hl : raw27580step1Labels = raw27580step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27580step0 raw27580step0Labels permutation80 hz
    mixedMoment B raw27580step1 raw27580step1Labels = mixedMoment B raw27580step2 raw27580step2Labels := by
      have ha : raw27580step2 = (fun i j => raw27580step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27580step2 raw27580step1; decide +kernel
      have hl : raw27580step2Labels = raw27580step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27580step1 raw27580step1Labels permutation8 permutation3
    _ = mixedMoment B node2820 node2820Labels := by rfl

def raw27581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw27581Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw27581step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27581step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27581step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27581step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27581step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27581 raw27581Labels = mixedMoment B node2815 node2815Labels := by
  calc
    mixedMoment B raw27581 raw27581Labels = mixedMoment B raw27581step0 raw27581step0Labels := by
      have hz : ∀ j, raw27581 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27581step0 = (fun i j => raw27581 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27581step0 raw27581; decide +kernel
      have hl : raw27581step0Labels = raw27581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27581 raw27581Labels permutation434 hz
    mixedMoment B raw27581step0 raw27581step0Labels = mixedMoment B raw27581step1 raw27581step1Labels := by
      have ha : raw27581step1 = (fun i j => raw27581step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27581step1 raw27581step0; decide +kernel
      have hl : raw27581step1Labels = raw27581step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27581step0 raw27581step0Labels permutation149 permutation3
    mixedMoment B raw27581step1 raw27581step1Labels = mixedMoment B raw27581step2 raw27581step2Labels := by
      have ha : raw27581step2 = -raw27581step1 := by apply Matrix.ext; change ∀ i j, raw27581step2 i j = -(raw27581step1 i j); unfold raw27581step2 raw27581step1; decide +kernel
      have hl : raw27581step2Labels = raw27581step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2815 node2815Labels := by rfl

def raw27582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw27582Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw27582step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27582step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27582step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27582step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27582step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27582 raw27582Labels = mixedMoment B node2815 node2815Labels := by
  calc
    mixedMoment B raw27582 raw27582Labels = mixedMoment B raw27582step0 raw27582step0Labels := by
      have hz : ∀ j, raw27582 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27582step0 = (fun i j => raw27582 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27582step0 raw27582; decide +kernel
      have hl : raw27582step0Labels = raw27582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27582 raw27582Labels permutation346 hz
    mixedMoment B raw27582step0 raw27582step0Labels = mixedMoment B raw27582step1 raw27582step1Labels := by
      have ha : raw27582step1 = (fun i j => raw27582step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27582step1 raw27582step0; decide +kernel
      have hl : raw27582step1Labels = raw27582step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27582step0 raw27582step0Labels permutation149 permutation3
    mixedMoment B raw27582step1 raw27582step1Labels = mixedMoment B raw27582step2 raw27582step2Labels := by
      have ha : raw27582step2 = -raw27582step1 := by apply Matrix.ext; change ∀ i j, raw27582step2 i j = -(raw27582step1 i j); unfold raw27582step2 raw27582step1; decide +kernel
      have hl : raw27582step2Labels = raw27582step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2815 node2815Labels := by rfl

def raw27583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw27583Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw27583step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27583step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![4, -2, -2]]
def raw27583step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27583step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw27583step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27583step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27583step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27583 raw27583Labels = mixedMoment B node1145 node1145Labels := by
  calc
    mixedMoment B raw27583 raw27583Labels = mixedMoment B raw27583step0 raw27583step0Labels := by
      have hz : ∀ j, raw27583 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27583step0 = (fun i j => raw27583 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27583step0 raw27583; decide +kernel
      have hl : raw27583step0Labels = raw27583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27583 raw27583Labels permutation434 hz
    mixedMoment B raw27583step0 raw27583step0Labels = mixedMoment B raw27583step1 raw27583step1Labels := by
      have hz : ∀ j, raw27583step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27583step1 = (fun i j => raw27583step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27583step1 raw27583step0; decide +kernel
      have hl : raw27583step1Labels = raw27583step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27583step0 raw27583step0Labels permutation80 hz
    mixedMoment B raw27583step1 raw27583step1Labels = mixedMoment B raw27583step2 raw27583step2Labels := by
      have ha : raw27583step2 = (fun i j => raw27583step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27583step2 raw27583step1; decide +kernel
      have hl : raw27583step2Labels = raw27583step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27583step1 raw27583step1Labels permutation31 permutation3
    mixedMoment B raw27583step2 raw27583step2Labels = mixedMoment B raw27583step3 raw27583step3Labels := by
      have ha : raw27583step3 = -raw27583step2 := by apply Matrix.ext; change ∀ i j, raw27583step3 i j = -(raw27583step2 i j); unfold raw27583step3 raw27583step2; decide +kernel
      have hl : raw27583step3Labels = raw27583step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1145 node1145Labels := by rfl

def raw27584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw27584Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw27584step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27584step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27584step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27584step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27584step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27584 raw27584Labels = mixedMoment B node1136 node1136Labels := by
  calc
    mixedMoment B raw27584 raw27584Labels = mixedMoment B raw27584step0 raw27584step0Labels := by
      have hz : ∀ j, raw27584 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27584step0 = (fun i j => raw27584 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27584step0 raw27584; decide +kernel
      have hl : raw27584step0Labels = raw27584Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27584 raw27584Labels permutation434 hz
    mixedMoment B raw27584step0 raw27584step0Labels = mixedMoment B raw27584step1 raw27584step1Labels := by
      have ha : raw27584step1 = (fun i j => raw27584step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27584step1 raw27584step0; decide +kernel
      have hl : raw27584step1Labels = raw27584step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27584step0 raw27584step0Labels permutation149 permutation3
    mixedMoment B raw27584step1 raw27584step1Labels = mixedMoment B raw27584step2 raw27584step2Labels := by
      have ha : raw27584step2 = -raw27584step1 := by apply Matrix.ext; change ∀ i j, raw27584step2 i j = -(raw27584step1 i j); unfold raw27584step2 raw27584step1; decide +kernel
      have hl : raw27584step2Labels = raw27584step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1136 node1136Labels := by rfl

def raw27585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw27585Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw27585step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27585step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27585step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27585step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27585step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27585 raw27585Labels = mixedMoment B node1136 node1136Labels := by
  calc
    mixedMoment B raw27585 raw27585Labels = mixedMoment B raw27585step0 raw27585step0Labels := by
      have hz : ∀ j, raw27585 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27585step0 = (fun i j => raw27585 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27585step0 raw27585; decide +kernel
      have hl : raw27585step0Labels = raw27585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27585 raw27585Labels permutation346 hz
    mixedMoment B raw27585step0 raw27585step0Labels = mixedMoment B raw27585step1 raw27585step1Labels := by
      have ha : raw27585step1 = (fun i j => raw27585step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27585step1 raw27585step0; decide +kernel
      have hl : raw27585step1Labels = raw27585step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27585step0 raw27585step0Labels permutation149 permutation3
    mixedMoment B raw27585step1 raw27585step1Labels = mixedMoment B raw27585step2 raw27585step2Labels := by
      have ha : raw27585step2 = -raw27585step1 := by apply Matrix.ext; change ∀ i j, raw27585step2 i j = -(raw27585step1 i j); unfold raw27585step2 raw27585step1; decide +kernel
      have hl : raw27585step2Labels = raw27585step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1136 node1136Labels := by rfl

def raw27586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27586step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27586step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27586step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27586step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27586 raw27586Labels = mixedMoment B node4943 node4943Labels := by
  calc
    mixedMoment B raw27586 raw27586Labels = mixedMoment B raw27586step0 raw27586step0Labels := by
      have hz : ∀ j, raw27586 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27586step0 = (fun i j => raw27586 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27586step0 raw27586; decide +kernel
      have hl : raw27586step0Labels = raw27586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27586 raw27586Labels permutation434 hz
    mixedMoment B raw27586step0 raw27586step0Labels = mixedMoment B raw27586step1 raw27586step1Labels := by
      have ha : raw27586step1 = (fun i j => raw27586step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27586step1 raw27586step0; decide +kernel
      have hl : raw27586step1Labels = raw27586step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27586step0 raw27586step0Labels permutation34 permutation3
    mixedMoment B raw27586step1 raw27586step1Labels = mixedMoment B raw27586step2 raw27586step2Labels := by
      have ha : raw27586step2 = raw27586step1 := by apply Matrix.ext; unfold raw27586step2 raw27586step1; decide +kernel
      have hl : raw27586step1Labels = labelEmbedding6 ∘ raw27586step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27586step1 raw27586step1Labels raw27586step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4943 node4943Labels := by rfl

def raw27587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27587step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27587step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27587step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27587step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27587 raw27587Labels = mixedMoment B node5033 node5033Labels := by
  calc
    mixedMoment B raw27587 raw27587Labels = mixedMoment B raw27587step0 raw27587step0Labels := by
      have ha : raw27587step0 = (fun i j => raw27587 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27587step0 raw27587; decide +kernel
      have hl : raw27587step0Labels = raw27587Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27587 raw27587Labels permutation202 permutation3
    mixedMoment B raw27587step0 raw27587step0Labels = mixedMoment B raw27587step1 raw27587step1Labels := by
      have ha : raw27587step1 = raw27587step0 := by apply Matrix.ext; unfold raw27587step1 raw27587step0; decide +kernel
      have hl : raw27587step0Labels = labelEmbedding6 ∘ raw27587step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27587step0 raw27587step0Labels raw27587step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5033 node5033Labels := by rfl

def raw27588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27588Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27588step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27588step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27588step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27588step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27588 raw27588Labels = mixedMoment B node4943 node4943Labels := by
  calc
    mixedMoment B raw27588 raw27588Labels = mixedMoment B raw27588step0 raw27588step0Labels := by
      have hz : ∀ j, raw27588 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27588step0 = (fun i j => raw27588 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27588step0 raw27588; decide +kernel
      have hl : raw27588step0Labels = raw27588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27588 raw27588Labels permutation346 hz
    mixedMoment B raw27588step0 raw27588step0Labels = mixedMoment B raw27588step1 raw27588step1Labels := by
      have ha : raw27588step1 = (fun i j => raw27588step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27588step1 raw27588step0; decide +kernel
      have hl : raw27588step1Labels = raw27588step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27588step0 raw27588step0Labels permutation34 permutation3
    mixedMoment B raw27588step1 raw27588step1Labels = mixedMoment B raw27588step2 raw27588step2Labels := by
      have ha : raw27588step2 = raw27588step1 := by apply Matrix.ext; unfold raw27588step2 raw27588step1; decide +kernel
      have hl : raw27588step1Labels = labelEmbedding6 ∘ raw27588step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27588step1 raw27588step1Labels raw27588step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4943 node4943Labels := by rfl

def raw27589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27589step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27589step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27589step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27589 raw27589Labels = mixedMoment B node5033 node5033Labels := by
  calc
    mixedMoment B raw27589 raw27589Labels = mixedMoment B raw27589step0 raw27589step0Labels := by
      have ha : raw27589step0 = (fun i j => raw27589 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27589step0 raw27589; decide +kernel
      have hl : raw27589step0Labels = raw27589Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27589 raw27589Labels permutation178 permutation3
    mixedMoment B raw27589step0 raw27589step0Labels = mixedMoment B raw27589step1 raw27589step1Labels := by
      have ha : raw27589step1 = raw27589step0 := by apply Matrix.ext; unfold raw27589step1 raw27589step0; decide +kernel
      have hl : raw27589step0Labels = labelEmbedding6 ∘ raw27589step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27589step0 raw27589step0Labels raw27589step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5033 node5033Labels := by rfl

def raw27590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27590Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27590step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27590step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -1, -1], ![3, -2, -1]]
def raw27590step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27590step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27590step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27590step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27590step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27590 raw27590Labels = mixedMoment B node4952 node4952Labels := by
  calc
    mixedMoment B raw27590 raw27590Labels = mixedMoment B raw27590step0 raw27590step0Labels := by
      have hz : ∀ j, raw27590 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27590step0 = (fun i j => raw27590 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27590step0 raw27590; decide +kernel
      have hl : raw27590step0Labels = raw27590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27590 raw27590Labels permutation434 hz
    mixedMoment B raw27590step0 raw27590step0Labels = mixedMoment B raw27590step1 raw27590step1Labels := by
      have hz : ∀ j, raw27590step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27590step1 = (fun i j => raw27590step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27590step1 raw27590step0; decide +kernel
      have hl : raw27590step1Labels = raw27590step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27590step0 raw27590step0Labels permutation80 hz
    mixedMoment B raw27590step1 raw27590step1Labels = mixedMoment B raw27590step2 raw27590step2Labels := by
      have ha : raw27590step2 = (fun i j => raw27590step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27590step2 raw27590step1; decide +kernel
      have hl : raw27590step2Labels = raw27590step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27590step1 raw27590step1Labels permutation8 permutation3
    mixedMoment B raw27590step2 raw27590step2Labels = mixedMoment B raw27590step3 raw27590step3Labels := by
      have ha : raw27590step3 = raw27590step2 := by apply Matrix.ext; unfold raw27590step3 raw27590step2; decide +kernel
      have hl : raw27590step2Labels = labelEmbedding6 ∘ raw27590step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27590step2 raw27590step2Labels raw27590step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4952 node4952Labels := by rfl

def raw27591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27591Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27591step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw27591step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27591step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27591step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27591step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27591step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27591 raw27591Labels = mixedMoment B node4943 node4943Labels := by
  calc
    mixedMoment B raw27591 raw27591Labels = mixedMoment B raw27591step0 raw27591step0Labels := by
      have hz : ∀ j, raw27591 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27591step0 = (fun i j => raw27591 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27591step0 raw27591; decide +kernel
      have hl : raw27591step0Labels = raw27591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27591 raw27591Labels permutation434 hz
    mixedMoment B raw27591step0 raw27591step0Labels = mixedMoment B raw27591step1 raw27591step1Labels := by
      have ha : raw27591step1 = (fun i j => raw27591step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27591step1 raw27591step0; decide +kernel
      have hl : raw27591step1Labels = raw27591step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27591step0 raw27591step0Labels permutation149 permutation3
    mixedMoment B raw27591step1 raw27591step1Labels = mixedMoment B raw27591step2 raw27591step2Labels := by
      have ha : raw27591step2 = -raw27591step1 := by apply Matrix.ext; change ∀ i j, raw27591step2 i j = -(raw27591step1 i j); unfold raw27591step2 raw27591step1; decide +kernel
      have hl : raw27591step2Labels = raw27591step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27591step2 raw27591step2Labels = mixedMoment B raw27591step3 raw27591step3Labels := by
      have ha : raw27591step3 = raw27591step2 := by apply Matrix.ext; unfold raw27591step3 raw27591step2; decide +kernel
      have hl : raw27591step2Labels = labelEmbedding6 ∘ raw27591step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27591step2 raw27591step2Labels raw27591step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4943 node4943Labels := by rfl

def raw27592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27592Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27592step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw27592step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27592step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27592step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27592step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27592step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27592 raw27592Labels = mixedMoment B node4943 node4943Labels := by
  calc
    mixedMoment B raw27592 raw27592Labels = mixedMoment B raw27592step0 raw27592step0Labels := by
      have hz : ∀ j, raw27592 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27592step0 = (fun i j => raw27592 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27592step0 raw27592; decide +kernel
      have hl : raw27592step0Labels = raw27592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27592 raw27592Labels permutation346 hz
    mixedMoment B raw27592step0 raw27592step0Labels = mixedMoment B raw27592step1 raw27592step1Labels := by
      have ha : raw27592step1 = (fun i j => raw27592step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27592step1 raw27592step0; decide +kernel
      have hl : raw27592step1Labels = raw27592step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27592step0 raw27592step0Labels permutation149 permutation3
    mixedMoment B raw27592step1 raw27592step1Labels = mixedMoment B raw27592step2 raw27592step2Labels := by
      have ha : raw27592step2 = -raw27592step1 := by apply Matrix.ext; change ∀ i j, raw27592step2 i j = -(raw27592step1 i j); unfold raw27592step2 raw27592step1; decide +kernel
      have hl : raw27592step2Labels = raw27592step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27592step2 raw27592step2Labels = mixedMoment B raw27592step3 raw27592step3Labels := by
      have ha : raw27592step3 = raw27592step2 := by apply Matrix.ext; unfold raw27592step3 raw27592step2; decide +kernel
      have hl : raw27592step2Labels = labelEmbedding6 ∘ raw27592step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27592step2 raw27592step2Labels raw27592step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4943 node4943Labels := by rfl

def raw27593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27593Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27593step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27593step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![4, -3, -1]]
def raw27593step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27593step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw27593step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27593step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw27593step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27593step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw27593step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27593 raw27593Labels = mixedMoment B node4360 node4360Labels := by
  calc
    mixedMoment B raw27593 raw27593Labels = mixedMoment B raw27593step0 raw27593step0Labels := by
      have hz : ∀ j, raw27593 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27593step0 = (fun i j => raw27593 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27593step0 raw27593; decide +kernel
      have hl : raw27593step0Labels = raw27593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27593 raw27593Labels permutation434 hz
    mixedMoment B raw27593step0 raw27593step0Labels = mixedMoment B raw27593step1 raw27593step1Labels := by
      have hz : ∀ j, raw27593step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27593step1 = (fun i j => raw27593step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27593step1 raw27593step0; decide +kernel
      have hl : raw27593step1Labels = raw27593step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27593step0 raw27593step0Labels permutation80 hz
    mixedMoment B raw27593step1 raw27593step1Labels = mixedMoment B raw27593step2 raw27593step2Labels := by
      have ha : raw27593step2 = (fun i j => raw27593step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27593step2 raw27593step1; decide +kernel
      have hl : raw27593step2Labels = raw27593step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27593step1 raw27593step1Labels permutation31 permutation3
    mixedMoment B raw27593step2 raw27593step2Labels = mixedMoment B raw27593step3 raw27593step3Labels := by
      have ha : raw27593step3 = -raw27593step2 := by apply Matrix.ext; change ∀ i j, raw27593step3 i j = -(raw27593step2 i j); unfold raw27593step3 raw27593step2; decide +kernel
      have hl : raw27593step3Labels = raw27593step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27593step3 raw27593step3Labels = mixedMoment B raw27593step4 raw27593step4Labels := by
      have ha : raw27593step4 = raw27593step3 := by apply Matrix.ext; unfold raw27593step4 raw27593step3; decide +kernel
      have hl : raw27593step3Labels = labelEmbedding6 ∘ raw27593step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27593step3 raw27593step3Labels raw27593step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4360 node4360Labels := by rfl

def raw27594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27594Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27594step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw27594step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27594step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27594step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27594step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27594step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27594 raw27594Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw27594 raw27594Labels = mixedMoment B raw27594step0 raw27594step0Labels := by
      have hz : ∀ j, raw27594 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27594step0 = (fun i j => raw27594 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27594step0 raw27594; decide +kernel
      have hl : raw27594step0Labels = raw27594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27594 raw27594Labels permutation434 hz
    mixedMoment B raw27594step0 raw27594step0Labels = mixedMoment B raw27594step1 raw27594step1Labels := by
      have ha : raw27594step1 = (fun i j => raw27594step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27594step1 raw27594step0; decide +kernel
      have hl : raw27594step1Labels = raw27594step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27594step0 raw27594step0Labels permutation149 permutation3
    mixedMoment B raw27594step1 raw27594step1Labels = mixedMoment B raw27594step2 raw27594step2Labels := by
      have ha : raw27594step2 = -raw27594step1 := by apply Matrix.ext; change ∀ i j, raw27594step2 i j = -(raw27594step1 i j); unfold raw27594step2 raw27594step1; decide +kernel
      have hl : raw27594step2Labels = raw27594step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27594step2 raw27594step2Labels = mixedMoment B raw27594step3 raw27594step3Labels := by
      have ha : raw27594step3 = raw27594step2 := by apply Matrix.ext; unfold raw27594step3 raw27594step2; decide +kernel
      have hl : raw27594step2Labels = labelEmbedding6 ∘ raw27594step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27594step2 raw27594step2Labels raw27594step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4346 node4346Labels := by rfl

def raw27595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27595Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27595step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27595step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw27595step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27595step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27595step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27595step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27595step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27595 raw27595Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw27595 raw27595Labels = mixedMoment B raw27595step0 raw27595step0Labels := by
      have hz : ∀ j, raw27595 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27595step0 = (fun i j => raw27595 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27595step0 raw27595; decide +kernel
      have hl : raw27595step0Labels = raw27595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27595 raw27595Labels permutation346 hz
    mixedMoment B raw27595step0 raw27595step0Labels = mixedMoment B raw27595step1 raw27595step1Labels := by
      have ha : raw27595step1 = (fun i j => raw27595step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27595step1 raw27595step0; decide +kernel
      have hl : raw27595step1Labels = raw27595step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27595step0 raw27595step0Labels permutation149 permutation3
    mixedMoment B raw27595step1 raw27595step1Labels = mixedMoment B raw27595step2 raw27595step2Labels := by
      have ha : raw27595step2 = -raw27595step1 := by apply Matrix.ext; change ∀ i j, raw27595step2 i j = -(raw27595step1 i j); unfold raw27595step2 raw27595step1; decide +kernel
      have hl : raw27595step2Labels = raw27595step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27595step2 raw27595step2Labels = mixedMoment B raw27595step3 raw27595step3Labels := by
      have ha : raw27595step3 = raw27595step2 := by apply Matrix.ext; unfold raw27595step3 raw27595step2; decide +kernel
      have hl : raw27595step2Labels = labelEmbedding6 ∘ raw27595step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27595step2 raw27595step2Labels raw27595step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4346 node4346Labels := by rfl

def raw27596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27596Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27596step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27596step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw27596step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27596step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw27596step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27596step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw27596step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27596 raw27596Labels = mixedMoment B node2605 node2605Labels := by
  calc
    mixedMoment B raw27596 raw27596Labels = mixedMoment B raw27596step0 raw27596step0Labels := by
      have hz : ∀ j, raw27596 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27596step0 = (fun i j => raw27596 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27596step0 raw27596; decide +kernel
      have hl : raw27596step0Labels = raw27596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27596 raw27596Labels permutation434 hz
    mixedMoment B raw27596step0 raw27596step0Labels = mixedMoment B raw27596step1 raw27596step1Labels := by
      have hz : ∀ j, raw27596step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27596step1 = (fun i j => raw27596step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27596step1 raw27596step0; decide +kernel
      have hl : raw27596step1Labels = raw27596step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27596step0 raw27596step0Labels permutation80 hz
    mixedMoment B raw27596step1 raw27596step1Labels = mixedMoment B raw27596step2 raw27596step2Labels := by
      have ha : raw27596step2 = (fun i j => raw27596step1 (permutation30 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27596step2 raw27596step1; decide +kernel
      have hl : raw27596step2Labels = raw27596step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27596step1 raw27596step1Labels permutation30 permutation3
    mixedMoment B raw27596step2 raw27596step2Labels = mixedMoment B raw27596step3 raw27596step3Labels := by
      have ha : raw27596step3 = -raw27596step2 := by apply Matrix.ext; change ∀ i j, raw27596step3 i j = -(raw27596step2 i j); unfold raw27596step3 raw27596step2; decide +kernel
      have hl : raw27596step3Labels = raw27596step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2605 node2605Labels := by rfl

def raw27597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27597Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27597step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27597step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw27597step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27597step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27597step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27597 raw27597Labels = mixedMoment B node2595 node2595Labels := by
  calc
    mixedMoment B raw27597 raw27597Labels = mixedMoment B raw27597step0 raw27597step0Labels := by
      have hz : ∀ j, raw27597 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27597step0 = (fun i j => raw27597 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27597step0 raw27597; decide +kernel
      have hl : raw27597step0Labels = raw27597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27597 raw27597Labels permutation434 hz
    mixedMoment B raw27597step0 raw27597step0Labels = mixedMoment B raw27597step1 raw27597step1Labels := by
      have ha : raw27597step1 = (fun i j => raw27597step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27597step1 raw27597step0; decide +kernel
      have hl : raw27597step1Labels = raw27597step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27597step0 raw27597step0Labels permutation149 permutation3
    mixedMoment B raw27597step1 raw27597step1Labels = mixedMoment B raw27597step2 raw27597step2Labels := by
      have ha : raw27597step2 = -raw27597step1 := by apply Matrix.ext; change ∀ i j, raw27597step2 i j = -(raw27597step1 i j); unfold raw27597step2 raw27597step1; decide +kernel
      have hl : raw27597step2Labels = raw27597step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2595 node2595Labels := by rfl

def raw27598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27598Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27598step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27598step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw27598step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27598step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27598step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27598 raw27598Labels = mixedMoment B node2595 node2595Labels := by
  calc
    mixedMoment B raw27598 raw27598Labels = mixedMoment B raw27598step0 raw27598step0Labels := by
      have hz : ∀ j, raw27598 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27598step0 = (fun i j => raw27598 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27598step0 raw27598; decide +kernel
      have hl : raw27598step0Labels = raw27598Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27598 raw27598Labels permutation346 hz
    mixedMoment B raw27598step0 raw27598step0Labels = mixedMoment B raw27598step1 raw27598step1Labels := by
      have ha : raw27598step1 = (fun i j => raw27598step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27598step1 raw27598step0; decide +kernel
      have hl : raw27598step1Labels = raw27598step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27598step0 raw27598step0Labels permutation149 permutation3
    mixedMoment B raw27598step1 raw27598step1Labels = mixedMoment B raw27598step2 raw27598step2Labels := by
      have ha : raw27598step2 = -raw27598step1 := by apply Matrix.ext; change ∀ i j, raw27598step2 i j = -(raw27598step1 i j); unfold raw27598step2 raw27598step1; decide +kernel
      have hl : raw27598step2Labels = raw27598step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2595 node2595Labels := by rfl

def raw27599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27599Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27599step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27599step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27599 raw27599Labels = mixedMoment B node2334 node2334Labels := by
  calc
    mixedMoment B raw27599 raw27599Labels = mixedMoment B raw27599step0 raw27599step0Labels := by
      have hz : ∀ j, raw27599 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27599step0 = (fun i j => raw27599 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27599step0 raw27599; decide +kernel
      have hl : raw27599step0Labels = raw27599Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27599 raw27599Labels permutation434 hz
    mixedMoment B raw27599step0 raw27599step0Labels = mixedMoment B raw27599step1 raw27599step1Labels := by
      have ha : raw27599step1 = (fun i j => raw27599step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27599step1 raw27599step0; decide +kernel
      have hl : raw27599step1Labels = raw27599step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27599step0 raw27599step0Labels permutation34 permutation3
    _ = mixedMoment B node2334 node2334Labels := by rfl

def raw27600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27600Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27600step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27600 raw27600Labels = mixedMoment B node2425 node2425Labels := by
  calc
    mixedMoment B raw27600 raw27600Labels = mixedMoment B raw27600step0 raw27600step0Labels := by
      have ha : raw27600step0 = (fun i j => raw27600 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27600step0 raw27600; decide +kernel
      have hl : raw27600step0Labels = raw27600Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27600 raw27600Labels permutation202 permutation3
    _ = mixedMoment B node2425 node2425Labels := by rfl

def raw27601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27601Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27601step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27601step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27601step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27601 raw27601Labels = mixedMoment B node2595 node2595Labels := by
  calc
    mixedMoment B raw27601 raw27601Labels = mixedMoment B raw27601step0 raw27601step0Labels := by
      have hz : ∀ j, raw27601 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27601step0 = (fun i j => raw27601 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27601step0 raw27601; decide +kernel
      have hl : raw27601step0Labels = raw27601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27601 raw27601Labels permutation434 hz
    mixedMoment B raw27601step0 raw27601step0Labels = mixedMoment B raw27601step1 raw27601step1Labels := by
      have ha : raw27601step1 = (fun i j => raw27601step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27601step1 raw27601step0; decide +kernel
      have hl : raw27601step1Labels = raw27601step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27601step0 raw27601step0Labels permutation34 permutation3
    _ = mixedMoment B node2595 node2595Labels := by rfl

def raw27602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27602Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27602step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27602step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27602 raw27602Labels = mixedMoment B node2334 node2334Labels := by
  calc
    mixedMoment B raw27602 raw27602Labels = mixedMoment B raw27602step0 raw27602step0Labels := by
      have hz : ∀ j, raw27602 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27602step0 = (fun i j => raw27602 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27602step0 raw27602; decide +kernel
      have hl : raw27602step0Labels = raw27602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27602 raw27602Labels permutation346 hz
    mixedMoment B raw27602step0 raw27602step0Labels = mixedMoment B raw27602step1 raw27602step1Labels := by
      have ha : raw27602step1 = (fun i j => raw27602step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27602step1 raw27602step0; decide +kernel
      have hl : raw27602step1Labels = raw27602step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27602step0 raw27602step0Labels permutation34 permutation3
    _ = mixedMoment B node2334 node2334Labels := by rfl

def raw27603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27603Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27603step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27603 raw27603Labels = mixedMoment B node2425 node2425Labels := by
  calc
    mixedMoment B raw27603 raw27603Labels = mixedMoment B raw27603step0 raw27603step0Labels := by
      have ha : raw27603step0 = (fun i j => raw27603 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27603step0 raw27603; decide +kernel
      have hl : raw27603step0Labels = raw27603Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27603 raw27603Labels permutation178 permutation3
    _ = mixedMoment B node2425 node2425Labels := by rfl

def raw27604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27604Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27604step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27604step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -1, -1], ![3, -2, -1]]
def raw27604step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27604step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27604step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27604 raw27604Labels = mixedMoment B node2344 node2344Labels := by
  calc
    mixedMoment B raw27604 raw27604Labels = mixedMoment B raw27604step0 raw27604step0Labels := by
      have hz : ∀ j, raw27604 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27604step0 = (fun i j => raw27604 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27604step0 raw27604; decide +kernel
      have hl : raw27604step0Labels = raw27604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27604 raw27604Labels permutation434 hz
    mixedMoment B raw27604step0 raw27604step0Labels = mixedMoment B raw27604step1 raw27604step1Labels := by
      have hz : ∀ j, raw27604step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27604step1 = (fun i j => raw27604step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27604step1 raw27604step0; decide +kernel
      have hl : raw27604step1Labels = raw27604step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27604step0 raw27604step0Labels permutation80 hz
    mixedMoment B raw27604step1 raw27604step1Labels = mixedMoment B raw27604step2 raw27604step2Labels := by
      have ha : raw27604step2 = (fun i j => raw27604step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27604step2 raw27604step1; decide +kernel
      have hl : raw27604step2Labels = raw27604step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27604step1 raw27604step1Labels permutation8 permutation3
    _ = mixedMoment B node2344 node2344Labels := by rfl

def raw27605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27605Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27605step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27605step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw27605step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27605step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27605step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27605 raw27605Labels = mixedMoment B node2334 node2334Labels := by
  calc
    mixedMoment B raw27605 raw27605Labels = mixedMoment B raw27605step0 raw27605step0Labels := by
      have hz : ∀ j, raw27605 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27605step0 = (fun i j => raw27605 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27605step0 raw27605; decide +kernel
      have hl : raw27605step0Labels = raw27605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27605 raw27605Labels permutation434 hz
    mixedMoment B raw27605step0 raw27605step0Labels = mixedMoment B raw27605step1 raw27605step1Labels := by
      have ha : raw27605step1 = (fun i j => raw27605step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27605step1 raw27605step0; decide +kernel
      have hl : raw27605step1Labels = raw27605step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27605step0 raw27605step0Labels permutation149 permutation3
    mixedMoment B raw27605step1 raw27605step1Labels = mixedMoment B raw27605step2 raw27605step2Labels := by
      have ha : raw27605step2 = -raw27605step1 := by apply Matrix.ext; change ∀ i j, raw27605step2 i j = -(raw27605step1 i j); unfold raw27605step2 raw27605step1; decide +kernel
      have hl : raw27605step2Labels = raw27605step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2334 node2334Labels := by rfl

def raw27606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27606Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27606step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw27606step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27606step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27606step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27606 raw27606Labels = mixedMoment B node2334 node2334Labels := by
  calc
    mixedMoment B raw27606 raw27606Labels = mixedMoment B raw27606step0 raw27606step0Labels := by
      have hz : ∀ j, raw27606 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27606step0 = (fun i j => raw27606 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27606step0 raw27606; decide +kernel
      have hl : raw27606step0Labels = raw27606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27606 raw27606Labels permutation346 hz
    mixedMoment B raw27606step0 raw27606step0Labels = mixedMoment B raw27606step1 raw27606step1Labels := by
      have ha : raw27606step1 = (fun i j => raw27606step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27606step1 raw27606step0; decide +kernel
      have hl : raw27606step1Labels = raw27606step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27606step0 raw27606step0Labels permutation149 permutation3
    mixedMoment B raw27606step1 raw27606step1Labels = mixedMoment B raw27606step2 raw27606step2Labels := by
      have ha : raw27606step2 = -raw27606step1 := by apply Matrix.ext; change ∀ i j, raw27606step2 i j = -(raw27606step1 i j); unfold raw27606step2 raw27606step1; decide +kernel
      have hl : raw27606step2Labels = raw27606step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2334 node2334Labels := by rfl

def raw27607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27607Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27607step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27607step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![4, -3, -1]]
def raw27607step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27607step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw27607step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27607step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw27607step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27607 raw27607Labels = mixedMoment B node938 node938Labels := by
  calc
    mixedMoment B raw27607 raw27607Labels = mixedMoment B raw27607step0 raw27607step0Labels := by
      have hz : ∀ j, raw27607 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27607step0 = (fun i j => raw27607 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27607step0 raw27607; decide +kernel
      have hl : raw27607step0Labels = raw27607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27607 raw27607Labels permutation434 hz
    mixedMoment B raw27607step0 raw27607step0Labels = mixedMoment B raw27607step1 raw27607step1Labels := by
      have hz : ∀ j, raw27607step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27607step1 = (fun i j => raw27607step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27607step1 raw27607step0; decide +kernel
      have hl : raw27607step1Labels = raw27607step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27607step0 raw27607step0Labels permutation80 hz
    mixedMoment B raw27607step1 raw27607step1Labels = mixedMoment B raw27607step2 raw27607step2Labels := by
      have ha : raw27607step2 = (fun i j => raw27607step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27607step2 raw27607step1; decide +kernel
      have hl : raw27607step2Labels = raw27607step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27607step1 raw27607step1Labels permutation31 permutation3
    mixedMoment B raw27607step2 raw27607step2Labels = mixedMoment B raw27607step3 raw27607step3Labels := by
      have ha : raw27607step3 = -raw27607step2 := by apply Matrix.ext; change ∀ i j, raw27607step3 i j = -(raw27607step2 i j); unfold raw27607step3 raw27607step2; decide +kernel
      have hl : raw27607step3Labels = raw27607step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node938 node938Labels := by rfl

def raw27608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27608Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27608step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw27608step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27608step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27608step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27608 raw27608Labels = mixedMoment B node924 node924Labels := by
  calc
    mixedMoment B raw27608 raw27608Labels = mixedMoment B raw27608step0 raw27608step0Labels := by
      have hz : ∀ j, raw27608 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27608step0 = (fun i j => raw27608 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27608step0 raw27608; decide +kernel
      have hl : raw27608step0Labels = raw27608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27608 raw27608Labels permutation434 hz
    mixedMoment B raw27608step0 raw27608step0Labels = mixedMoment B raw27608step1 raw27608step1Labels := by
      have ha : raw27608step1 = (fun i j => raw27608step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27608step1 raw27608step0; decide +kernel
      have hl : raw27608step1Labels = raw27608step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27608step0 raw27608step0Labels permutation149 permutation3
    mixedMoment B raw27608step1 raw27608step1Labels = mixedMoment B raw27608step2 raw27608step2Labels := by
      have ha : raw27608step2 = -raw27608step1 := by apply Matrix.ext; change ∀ i j, raw27608step2 i j = -(raw27608step1 i j); unfold raw27608step2 raw27608step1; decide +kernel
      have hl : raw27608step2Labels = raw27608step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node924 node924Labels := by rfl

def raw27609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27609Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27609step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27609step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw27609step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27609step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27609step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27609 raw27609Labels = mixedMoment B node924 node924Labels := by
  calc
    mixedMoment B raw27609 raw27609Labels = mixedMoment B raw27609step0 raw27609step0Labels := by
      have hz : ∀ j, raw27609 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27609step0 = (fun i j => raw27609 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27609step0 raw27609; decide +kernel
      have hl : raw27609step0Labels = raw27609Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27609 raw27609Labels permutation346 hz
    mixedMoment B raw27609step0 raw27609step0Labels = mixedMoment B raw27609step1 raw27609step1Labels := by
      have ha : raw27609step1 = (fun i j => raw27609step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27609step1 raw27609step0; decide +kernel
      have hl : raw27609step1Labels = raw27609step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27609step0 raw27609step0Labels permutation149 permutation3
    mixedMoment B raw27609step1 raw27609step1Labels = mixedMoment B raw27609step2 raw27609step2Labels := by
      have ha : raw27609step2 = -raw27609step1 := by apply Matrix.ext; change ∀ i j, raw27609step2 i j = -(raw27609step1 i j); unfold raw27609step2 raw27609step1; decide +kernel
      have hl : raw27609step2Labels = raw27609step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node924 node924Labels := by rfl

def raw27610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27610step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27610step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27610step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27610step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw27610step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27610step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw27610step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27610step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw27610step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27610 raw27610Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw27610 raw27610Labels = mixedMoment B raw27610step0 raw27610step0Labels := by
      have hz : ∀ j, raw27610 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27610step0 = (fun i j => raw27610 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27610step0 raw27610; decide +kernel
      have hl : raw27610step0Labels = raw27610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27610 raw27610Labels permutation434 hz
    mixedMoment B raw27610step0 raw27610step0Labels = mixedMoment B raw27610step1 raw27610step1Labels := by
      have hz : ∀ j, raw27610step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27610step1 = (fun i j => raw27610step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27610step1 raw27610step0; decide +kernel
      have hl : raw27610step1Labels = raw27610step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27610step0 raw27610step0Labels permutation80 hz
    mixedMoment B raw27610step1 raw27610step1Labels = mixedMoment B raw27610step2 raw27610step2Labels := by
      have ha : raw27610step2 = (fun i j => raw27610step1 (permutation30 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27610step2 raw27610step1; decide +kernel
      have hl : raw27610step2Labels = raw27610step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27610step1 raw27610step1Labels permutation30 permutation3
    mixedMoment B raw27610step2 raw27610step2Labels = mixedMoment B raw27610step3 raw27610step3Labels := by
      have ha : raw27610step3 = -raw27610step2 := by apply Matrix.ext; change ∀ i j, raw27610step3 i j = -(raw27610step2 i j); unfold raw27610step3 raw27610step2; decide +kernel
      have hl : raw27610step3Labels = raw27610step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27610step3 raw27610step3Labels = mixedMoment B raw27610step4 raw27610step4Labels := by
      have ha : raw27610step4 = raw27610step3 := by apply Matrix.ext; unfold raw27610step4 raw27610step3; decide +kernel
      have hl : raw27610step3Labels = labelEmbedding6 ∘ raw27610step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27610step3 raw27610step3Labels raw27610step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5176 node5176Labels := by rfl

def raw27611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27611step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw27611step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27611step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27611step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27611step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27611step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27611 raw27611Labels = mixedMoment B node5172 node5172Labels := by
  calc
    mixedMoment B raw27611 raw27611Labels = mixedMoment B raw27611step0 raw27611step0Labels := by
      have hz : ∀ j, raw27611 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27611step0 = (fun i j => raw27611 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27611step0 raw27611; decide +kernel
      have hl : raw27611step0Labels = raw27611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27611 raw27611Labels permutation434 hz
    mixedMoment B raw27611step0 raw27611step0Labels = mixedMoment B raw27611step1 raw27611step1Labels := by
      have ha : raw27611step1 = (fun i j => raw27611step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27611step1 raw27611step0; decide +kernel
      have hl : raw27611step1Labels = raw27611step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27611step0 raw27611step0Labels permutation149 permutation3
    mixedMoment B raw27611step1 raw27611step1Labels = mixedMoment B raw27611step2 raw27611step2Labels := by
      have ha : raw27611step2 = -raw27611step1 := by apply Matrix.ext; change ∀ i j, raw27611step2 i j = -(raw27611step1 i j); unfold raw27611step2 raw27611step1; decide +kernel
      have hl : raw27611step2Labels = raw27611step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27611step2 raw27611step2Labels = mixedMoment B raw27611step3 raw27611step3Labels := by
      have ha : raw27611step3 = raw27611step2 := by apply Matrix.ext; unfold raw27611step3 raw27611step2; decide +kernel
      have hl : raw27611step2Labels = labelEmbedding6 ∘ raw27611step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27611step2 raw27611step2Labels raw27611step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5172 node5172Labels := by rfl

def raw27612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27612Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27612step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw27612step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27612step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27612step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27612step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27612step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27612 raw27612Labels = mixedMoment B node5172 node5172Labels := by
  calc
    mixedMoment B raw27612 raw27612Labels = mixedMoment B raw27612step0 raw27612step0Labels := by
      have hz : ∀ j, raw27612 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27612step0 = (fun i j => raw27612 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27612step0 raw27612; decide +kernel
      have hl : raw27612step0Labels = raw27612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27612 raw27612Labels permutation346 hz
    mixedMoment B raw27612step0 raw27612step0Labels = mixedMoment B raw27612step1 raw27612step1Labels := by
      have ha : raw27612step1 = (fun i j => raw27612step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27612step1 raw27612step0; decide +kernel
      have hl : raw27612step1Labels = raw27612step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27612step0 raw27612step0Labels permutation149 permutation3
    mixedMoment B raw27612step1 raw27612step1Labels = mixedMoment B raw27612step2 raw27612step2Labels := by
      have ha : raw27612step2 = -raw27612step1 := by apply Matrix.ext; change ∀ i j, raw27612step2 i j = -(raw27612step1 i j); unfold raw27612step2 raw27612step1; decide +kernel
      have hl : raw27612step2Labels = raw27612step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27612step2 raw27612step2Labels = mixedMoment B raw27612step3 raw27612step3Labels := by
      have ha : raw27612step3 = raw27612step2 := by apply Matrix.ext; unfold raw27612step3 raw27612step2; decide +kernel
      have hl : raw27612step2Labels = labelEmbedding6 ∘ raw27612step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27612step2 raw27612step2Labels raw27612step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5172 node5172Labels := by rfl

def raw27613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27613step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27613 raw27613Labels = mixedMoment B node4972 node4972Labels := by
  calc
    mixedMoment B raw27613 raw27613Labels = mixedMoment B raw27613step0 raw27613step0Labels := by
      have hz : ∀ j, raw27613 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27613step0 = (fun i j => raw27613 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27613step0 raw27613; decide +kernel
      have hl : raw27613step0Labels = raw27613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27613 raw27613Labels permutation434 hz
    _ = mixedMoment B node4972 node4972Labels := by rfl

def raw27614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27614Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27614step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27614step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27614step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27614step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27614step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27614step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27614 raw27614Labels = mixedMoment B node5037 node5037Labels := by
  calc
    mixedMoment B raw27614 raw27614Labels = mixedMoment B raw27614step0 raw27614step0Labels := by
      have ha : raw27614step0 = (fun i j => raw27614 (permutation644 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27614step0 raw27614; decide +kernel
      have hl : raw27614step0Labels = raw27614Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27614 raw27614Labels permutation644 permutation3
    mixedMoment B raw27614step0 raw27614step0Labels = mixedMoment B raw27614step1 raw27614step1Labels := by
      have ha : raw27614step1 = -raw27614step0 := by apply Matrix.ext; change ∀ i j, raw27614step1 i j = -(raw27614step0 i j); unfold raw27614step1 raw27614step0; decide +kernel
      have hl : raw27614step1Labels = raw27614step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27614step1 raw27614step1Labels = mixedMoment B raw27614step2 raw27614step2Labels := by
      have ha : raw27614step2 = raw27614step1 := by apply Matrix.ext; unfold raw27614step2 raw27614step1; decide +kernel
      have hl : raw27614step1Labels = labelEmbedding6 ∘ raw27614step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27614step1 raw27614step1Labels raw27614step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5037 node5037Labels := by rfl

def raw27615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27615Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27615step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27615 raw27615Labels = mixedMoment B node4972 node4972Labels := by
  calc
    mixedMoment B raw27615 raw27615Labels = mixedMoment B raw27615step0 raw27615step0Labels := by
      have hz : ∀ j, raw27615 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27615step0 = (fun i j => raw27615 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27615step0 raw27615; decide +kernel
      have hl : raw27615step0Labels = raw27615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27615 raw27615Labels permutation346 hz
    _ = mixedMoment B node4972 node4972Labels := by rfl

def raw27616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27616step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27616step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27616step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27616step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27616step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27616step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27616 raw27616Labels = mixedMoment B node5037 node5037Labels := by
  calc
    mixedMoment B raw27616 raw27616Labels = mixedMoment B raw27616step0 raw27616step0Labels := by
      have ha : raw27616step0 = (fun i j => raw27616 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27616step0 raw27616; decide +kernel
      have hl : raw27616step0Labels = raw27616Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27616 raw27616Labels permutation662 permutation3
    mixedMoment B raw27616step0 raw27616step0Labels = mixedMoment B raw27616step1 raw27616step1Labels := by
      have ha : raw27616step1 = -raw27616step0 := by apply Matrix.ext; change ∀ i j, raw27616step1 i j = -(raw27616step0 i j); unfold raw27616step1 raw27616step0; decide +kernel
      have hl : raw27616step1Labels = raw27616step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27616step1 raw27616step1Labels = mixedMoment B raw27616step2 raw27616step2Labels := by
      have ha : raw27616step2 = raw27616step1 := by apply Matrix.ext; unfold raw27616step2 raw27616step1; decide +kernel
      have hl : raw27616step1Labels = labelEmbedding6 ∘ raw27616step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27616step1 raw27616step1Labels raw27616step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5037 node5037Labels := by rfl

def raw27617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27617step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27617step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27617step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27617step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw27617step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27617step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27617step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27617step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27617step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27617 raw27617Labels = mixedMoment B node4953 node4953Labels := by
  calc
    mixedMoment B raw27617 raw27617Labels = mixedMoment B raw27617step0 raw27617step0Labels := by
      have hz : ∀ j, raw27617 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27617step0 = (fun i j => raw27617 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27617step0 raw27617; decide +kernel
      have hl : raw27617step0Labels = raw27617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27617 raw27617Labels permutation434 hz
    mixedMoment B raw27617step0 raw27617step0Labels = mixedMoment B raw27617step1 raw27617step1Labels := by
      have hz : ∀ j, raw27617step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27617step1 = (fun i j => raw27617step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27617step1 raw27617step0; decide +kernel
      have hl : raw27617step1Labels = raw27617step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27617step0 raw27617step0Labels permutation80 hz
    mixedMoment B raw27617step1 raw27617step1Labels = mixedMoment B raw27617step2 raw27617step2Labels := by
      have ha : raw27617step2 = (fun i j => raw27617step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27617step2 raw27617step1; decide +kernel
      have hl : raw27617step2Labels = raw27617step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27617step1 raw27617step1Labels permutation31 permutation3
    mixedMoment B raw27617step2 raw27617step2Labels = mixedMoment B raw27617step3 raw27617step3Labels := by
      have ha : raw27617step3 = -raw27617step2 := by apply Matrix.ext; change ∀ i j, raw27617step3 i j = -(raw27617step2 i j); unfold raw27617step3 raw27617step2; decide +kernel
      have hl : raw27617step3Labels = raw27617step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27617step3 raw27617step3Labels = mixedMoment B raw27617step4 raw27617step4Labels := by
      have ha : raw27617step4 = raw27617step3 := by apply Matrix.ext; unfold raw27617step4 raw27617step3; decide +kernel
      have hl : raw27617step3Labels = labelEmbedding6 ∘ raw27617step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27617step3 raw27617step3Labels raw27617step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4953 node4953Labels := by rfl

def raw27618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27618Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27618step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27618step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27618step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27618step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27618step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27618step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27618step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27618 raw27618Labels = mixedMoment B node4948 node4948Labels := by
  calc
    mixedMoment B raw27618 raw27618Labels = mixedMoment B raw27618step0 raw27618step0Labels := by
      have hz : ∀ j, raw27618 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27618step0 = (fun i j => raw27618 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27618step0 raw27618; decide +kernel
      have hl : raw27618step0Labels = raw27618Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27618 raw27618Labels permutation434 hz
    mixedMoment B raw27618step0 raw27618step0Labels = mixedMoment B raw27618step1 raw27618step1Labels := by
      have ha : raw27618step1 = (fun i j => raw27618step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27618step1 raw27618step0; decide +kernel
      have hl : raw27618step1Labels = raw27618step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27618step0 raw27618step0Labels permutation149 permutation3
    mixedMoment B raw27618step1 raw27618step1Labels = mixedMoment B raw27618step2 raw27618step2Labels := by
      have ha : raw27618step2 = -raw27618step1 := by apply Matrix.ext; change ∀ i j, raw27618step2 i j = -(raw27618step1 i j); unfold raw27618step2 raw27618step1; decide +kernel
      have hl : raw27618step2Labels = raw27618step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27618step2 raw27618step2Labels = mixedMoment B raw27618step3 raw27618step3Labels := by
      have ha : raw27618step3 = raw27618step2 := by apply Matrix.ext; unfold raw27618step3 raw27618step2; decide +kernel
      have hl : raw27618step2Labels = labelEmbedding6 ∘ raw27618step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27618step2 raw27618step2Labels raw27618step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4948 node4948Labels := by rfl

def raw27619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27619step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27619step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27619step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27619step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27619step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27619step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27619 raw27619Labels = mixedMoment B node4948 node4948Labels := by
  calc
    mixedMoment B raw27619 raw27619Labels = mixedMoment B raw27619step0 raw27619step0Labels := by
      have hz : ∀ j, raw27619 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27619step0 = (fun i j => raw27619 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27619step0 raw27619; decide +kernel
      have hl : raw27619step0Labels = raw27619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27619 raw27619Labels permutation346 hz
    mixedMoment B raw27619step0 raw27619step0Labels = mixedMoment B raw27619step1 raw27619step1Labels := by
      have ha : raw27619step1 = (fun i j => raw27619step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27619step1 raw27619step0; decide +kernel
      have hl : raw27619step1Labels = raw27619step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27619step0 raw27619step0Labels permutation149 permutation3
    mixedMoment B raw27619step1 raw27619step1Labels = mixedMoment B raw27619step2 raw27619step2Labels := by
      have ha : raw27619step2 = -raw27619step1 := by apply Matrix.ext; change ∀ i j, raw27619step2 i j = -(raw27619step1 i j); unfold raw27619step2 raw27619step1; decide +kernel
      have hl : raw27619step2Labels = raw27619step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27619step2 raw27619step2Labels = mixedMoment B raw27619step3 raw27619step3Labels := by
      have ha : raw27619step3 = raw27619step2 := by apply Matrix.ext; unfold raw27619step3 raw27619step2; decide +kernel
      have hl : raw27619step2Labels = labelEmbedding6 ∘ raw27619step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27619step2 raw27619step2Labels raw27619step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4948 node4948Labels := by rfl

def raw27620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27620Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27620step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27620step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27620step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27620step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw27620step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27620step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw27620step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27620step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw27620step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27620 raw27620Labels = mixedMoment B node4361 node4361Labels := by
  calc
    mixedMoment B raw27620 raw27620Labels = mixedMoment B raw27620step0 raw27620step0Labels := by
      have hz : ∀ j, raw27620 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27620step0 = (fun i j => raw27620 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27620step0 raw27620; decide +kernel
      have hl : raw27620step0Labels = raw27620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27620 raw27620Labels permutation434 hz
    mixedMoment B raw27620step0 raw27620step0Labels = mixedMoment B raw27620step1 raw27620step1Labels := by
      have hz : ∀ j, raw27620step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27620step1 = (fun i j => raw27620step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27620step1 raw27620step0; decide +kernel
      have hl : raw27620step1Labels = raw27620step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27620step0 raw27620step0Labels permutation80 hz
    mixedMoment B raw27620step1 raw27620step1Labels = mixedMoment B raw27620step2 raw27620step2Labels := by
      have ha : raw27620step2 = (fun i j => raw27620step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27620step2 raw27620step1; decide +kernel
      have hl : raw27620step2Labels = raw27620step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27620step1 raw27620step1Labels permutation31 permutation3
    mixedMoment B raw27620step2 raw27620step2Labels = mixedMoment B raw27620step3 raw27620step3Labels := by
      have ha : raw27620step3 = -raw27620step2 := by apply Matrix.ext; change ∀ i j, raw27620step3 i j = -(raw27620step2 i j); unfold raw27620step3 raw27620step2; decide +kernel
      have hl : raw27620step3Labels = raw27620step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27620step3 raw27620step3Labels = mixedMoment B raw27620step4 raw27620step4Labels := by
      have ha : raw27620step4 = raw27620step3 := by apply Matrix.ext; unfold raw27620step4 raw27620step3; decide +kernel
      have hl : raw27620step3Labels = labelEmbedding6 ∘ raw27620step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27620step3 raw27620step3Labels raw27620step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4361 node4361Labels := by rfl

def raw27621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27621Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27621step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27621step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27621step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27621step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27621step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27621 raw27621Labels = mixedMoment B node4352 node4352Labels := by
  calc
    mixedMoment B raw27621 raw27621Labels = mixedMoment B raw27621step0 raw27621step0Labels := by
      have hz : ∀ j, raw27621 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27621step0 = (fun i j => raw27621 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27621step0 raw27621; decide +kernel
      have hl : raw27621step0Labels = raw27621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27621 raw27621Labels permutation434 hz
    mixedMoment B raw27621step0 raw27621step0Labels = mixedMoment B raw27621step1 raw27621step1Labels := by
      have ha : raw27621step1 = (fun i j => raw27621step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27621step1 raw27621step0; decide +kernel
      have hl : raw27621step1Labels = raw27621step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27621step0 raw27621step0Labels permutation149 permutation3
    mixedMoment B raw27621step1 raw27621step1Labels = mixedMoment B raw27621step2 raw27621step2Labels := by
      have ha : raw27621step2 = -raw27621step1 := by apply Matrix.ext; change ∀ i j, raw27621step2 i j = -(raw27621step1 i j); unfold raw27621step2 raw27621step1; decide +kernel
      have hl : raw27621step2Labels = raw27621step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27621step2 raw27621step2Labels = mixedMoment B raw27621step3 raw27621step3Labels := by
      have ha : raw27621step3 = raw27621step2 := by apply Matrix.ext; unfold raw27621step3 raw27621step2; decide +kernel
      have hl : raw27621step2Labels = labelEmbedding6 ∘ raw27621step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27621step2 raw27621step2Labels raw27621step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4352 node4352Labels := by rfl

def raw27622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27622Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27622step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27622step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27622step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27622step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27622step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27622step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27622 raw27622Labels = mixedMoment B node4352 node4352Labels := by
  calc
    mixedMoment B raw27622 raw27622Labels = mixedMoment B raw27622step0 raw27622step0Labels := by
      have hz : ∀ j, raw27622 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27622step0 = (fun i j => raw27622 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27622step0 raw27622; decide +kernel
      have hl : raw27622step0Labels = raw27622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27622 raw27622Labels permutation346 hz
    mixedMoment B raw27622step0 raw27622step0Labels = mixedMoment B raw27622step1 raw27622step1Labels := by
      have ha : raw27622step1 = (fun i j => raw27622step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27622step1 raw27622step0; decide +kernel
      have hl : raw27622step1Labels = raw27622step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27622step0 raw27622step0Labels permutation149 permutation3
    mixedMoment B raw27622step1 raw27622step1Labels = mixedMoment B raw27622step2 raw27622step2Labels := by
      have ha : raw27622step2 = -raw27622step1 := by apply Matrix.ext; change ∀ i j, raw27622step2 i j = -(raw27622step1 i j); unfold raw27622step2 raw27622step1; decide +kernel
      have hl : raw27622step2Labels = raw27622step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27622step2 raw27622step2Labels = mixedMoment B raw27622step3 raw27622step3Labels := by
      have ha : raw27622step3 = raw27622step2 := by apply Matrix.ext; unfold raw27622step3 raw27622step2; decide +kernel
      have hl : raw27622step2Labels = labelEmbedding6 ∘ raw27622step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27622step2 raw27622step2Labels raw27622step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4352 node4352Labels := by rfl

def raw27623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27623Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27623step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27623step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27623step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27623step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw27623step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27623step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw27623step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27623 raw27623Labels = mixedMoment B node2604 node2604Labels := by
  calc
    mixedMoment B raw27623 raw27623Labels = mixedMoment B raw27623step0 raw27623step0Labels := by
      have hz : ∀ j, raw27623 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27623step0 = (fun i j => raw27623 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27623step0 raw27623; decide +kernel
      have hl : raw27623step0Labels = raw27623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27623 raw27623Labels permutation434 hz
    mixedMoment B raw27623step0 raw27623step0Labels = mixedMoment B raw27623step1 raw27623step1Labels := by
      have hz : ∀ j, raw27623step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27623step1 = (fun i j => raw27623step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27623step1 raw27623step0; decide +kernel
      have hl : raw27623step1Labels = raw27623step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27623step0 raw27623step0Labels permutation80 hz
    mixedMoment B raw27623step1 raw27623step1Labels = mixedMoment B raw27623step2 raw27623step2Labels := by
      have ha : raw27623step2 = (fun i j => raw27623step1 (permutation30 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27623step2 raw27623step1; decide +kernel
      have hl : raw27623step2Labels = raw27623step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27623step1 raw27623step1Labels permutation30 permutation3
    mixedMoment B raw27623step2 raw27623step2Labels = mixedMoment B raw27623step3 raw27623step3Labels := by
      have ha : raw27623step3 = -raw27623step2 := by apply Matrix.ext; change ∀ i j, raw27623step3 i j = -(raw27623step2 i j); unfold raw27623step3 raw27623step2; decide +kernel
      have hl : raw27623step3Labels = raw27623step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2604 node2604Labels := by rfl

def raw27624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27624Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27624step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw27624step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27624step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27624step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27624 raw27624Labels = mixedMoment B node2599 node2599Labels := by
  calc
    mixedMoment B raw27624 raw27624Labels = mixedMoment B raw27624step0 raw27624step0Labels := by
      have hz : ∀ j, raw27624 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27624step0 = (fun i j => raw27624 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27624step0 raw27624; decide +kernel
      have hl : raw27624step0Labels = raw27624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27624 raw27624Labels permutation434 hz
    mixedMoment B raw27624step0 raw27624step0Labels = mixedMoment B raw27624step1 raw27624step1Labels := by
      have ha : raw27624step1 = (fun i j => raw27624step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27624step1 raw27624step0; decide +kernel
      have hl : raw27624step1Labels = raw27624step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27624step0 raw27624step0Labels permutation149 permutation3
    mixedMoment B raw27624step1 raw27624step1Labels = mixedMoment B raw27624step2 raw27624step2Labels := by
      have ha : raw27624step2 = -raw27624step1 := by apply Matrix.ext; change ∀ i j, raw27624step2 i j = -(raw27624step1 i j); unfold raw27624step2 raw27624step1; decide +kernel
      have hl : raw27624step2Labels = raw27624step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2599 node2599Labels := by rfl

def raw27625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27625Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27625step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw27625step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27625step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27625 raw27625Labels = mixedMoment B node2599 node2599Labels := by
  calc
    mixedMoment B raw27625 raw27625Labels = mixedMoment B raw27625step0 raw27625step0Labels := by
      have hz : ∀ j, raw27625 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27625step0 = (fun i j => raw27625 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27625step0 raw27625; decide +kernel
      have hl : raw27625step0Labels = raw27625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27625 raw27625Labels permutation346 hz
    mixedMoment B raw27625step0 raw27625step0Labels = mixedMoment B raw27625step1 raw27625step1Labels := by
      have ha : raw27625step1 = (fun i j => raw27625step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27625step1 raw27625step0; decide +kernel
      have hl : raw27625step1Labels = raw27625step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27625step0 raw27625step0Labels permutation149 permutation3
    mixedMoment B raw27625step1 raw27625step1Labels = mixedMoment B raw27625step2 raw27625step2Labels := by
      have ha : raw27625step2 = -raw27625step1 := by apply Matrix.ext; change ∀ i j, raw27625step2 i j = -(raw27625step1 i j); unfold raw27625step2 raw27625step1; decide +kernel
      have hl : raw27625step2Labels = raw27625step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2599 node2599Labels := by rfl

def raw27626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27626Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27626step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27626step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27626step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27626step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw27626step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27626step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw27626step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27626 raw27626Labels = mixedMoment B node4001 node4001Labels := by
  calc
    mixedMoment B raw27626 raw27626Labels = mixedMoment B raw27626step0 raw27626step0Labels := by
      have hz : ∀ j, raw27626 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27626step0 = (fun i j => raw27626 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27626step0 raw27626; decide +kernel
      have hl : raw27626step0Labels = raw27626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27626 raw27626Labels permutation434 hz
    mixedMoment B raw27626step0 raw27626step0Labels = mixedMoment B raw27626step1 raw27626step1Labels := by
      have hz : ∀ j, raw27626step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27626step1 = (fun i j => raw27626step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27626step1 raw27626step0; decide +kernel
      have hl : raw27626step1Labels = raw27626step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27626step0 raw27626step0Labels permutation80 hz
    mixedMoment B raw27626step1 raw27626step1Labels = mixedMoment B raw27626step2 raw27626step2Labels := by
      have ha : raw27626step2 = (fun i j => raw27626step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27626step2 raw27626step1; decide +kernel
      have hl : raw27626step2Labels = raw27626step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27626step1 raw27626step1Labels permutation31 permutation3
    mixedMoment B raw27626step2 raw27626step2Labels = mixedMoment B raw27626step3 raw27626step3Labels := by
      have ha : raw27626step3 = -raw27626step2 := by apply Matrix.ext; change ∀ i j, raw27626step3 i j = -(raw27626step2 i j); unfold raw27626step3 raw27626step2; decide +kernel
      have hl : raw27626step3Labels = raw27626step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4001 node4001Labels := by rfl

def raw27627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27627Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27627step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27627step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw27627step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27627step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw27627step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27627 raw27627Labels = mixedMoment B node2434 node2434Labels := by
  calc
    mixedMoment B raw27627 raw27627Labels = mixedMoment B raw27627step0 raw27627step0Labels := by
      have hz : ∀ j, raw27627 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27627step0 = (fun i j => raw27627 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27627step0 raw27627; decide +kernel
      have hl : raw27627step0Labels = raw27627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27627 raw27627Labels permutation434 hz
    mixedMoment B raw27627step0 raw27627step0Labels = mixedMoment B raw27627step1 raw27627step1Labels := by
      have ha : raw27627step1 = (fun i j => raw27627step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27627step1 raw27627step0; decide +kernel
      have hl : raw27627step1Labels = raw27627step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27627step0 raw27627step0Labels permutation145 permutation3
    mixedMoment B raw27627step1 raw27627step1Labels = mixedMoment B raw27627step2 raw27627step2Labels := by
      have ha : raw27627step2 = -raw27627step1 := by apply Matrix.ext; change ∀ i j, raw27627step2 i j = -(raw27627step1 i j); unfold raw27627step2 raw27627step1; decide +kernel
      have hl : raw27627step2Labels = raw27627step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2434 node2434Labels := by rfl

def raw27628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27628Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27628step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27628step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27628step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27628 raw27628Labels = mixedMoment B node2429 node2429Labels := by
  calc
    mixedMoment B raw27628 raw27628Labels = mixedMoment B raw27628step0 raw27628step0Labels := by
      have ha : raw27628step0 = (fun i j => raw27628 (permutation644 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27628step0 raw27628; decide +kernel
      have hl : raw27628step0Labels = raw27628Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27628 raw27628Labels permutation644 permutation3
    mixedMoment B raw27628step0 raw27628step0Labels = mixedMoment B raw27628step1 raw27628step1Labels := by
      have ha : raw27628step1 = -raw27628step0 := by apply Matrix.ext; change ∀ i j, raw27628step1 i j = -(raw27628step0 i j); unfold raw27628step1 raw27628step0; decide +kernel
      have hl : raw27628step1Labels = raw27628step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2429 node2429Labels := by rfl

def raw27629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27629Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27629step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27629step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27629step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27629 raw27629Labels = mixedMoment B node2960 node2960Labels := by
  calc
    mixedMoment B raw27629 raw27629Labels = mixedMoment B raw27629step0 raw27629step0Labels := by
      have hz : ∀ j, raw27629 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27629step0 = (fun i j => raw27629 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27629step0 raw27629; decide +kernel
      have hl : raw27629step0Labels = raw27629Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27629 raw27629Labels permutation434 hz
    mixedMoment B raw27629step0 raw27629step0Labels = mixedMoment B raw27629step1 raw27629step1Labels := by
      have ha : raw27629step1 = (fun i j => raw27629step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27629step1 raw27629step0; decide +kernel
      have hl : raw27629step1Labels = raw27629step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27629step0 raw27629step0Labels permutation34 permutation3
    _ = mixedMoment B node2960 node2960Labels := by rfl

def raw27630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27630Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27630step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw27630step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27630step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw27630step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27630 raw27630Labels = mixedMoment B node2434 node2434Labels := by
  calc
    mixedMoment B raw27630 raw27630Labels = mixedMoment B raw27630step0 raw27630step0Labels := by
      have hz : ∀ j, raw27630 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27630step0 = (fun i j => raw27630 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27630step0 raw27630; decide +kernel
      have hl : raw27630step0Labels = raw27630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27630 raw27630Labels permutation346 hz
    mixedMoment B raw27630step0 raw27630step0Labels = mixedMoment B raw27630step1 raw27630step1Labels := by
      have ha : raw27630step1 = (fun i j => raw27630step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27630step1 raw27630step0; decide +kernel
      have hl : raw27630step1Labels = raw27630step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27630step0 raw27630step0Labels permutation145 permutation3
    mixedMoment B raw27630step1 raw27630step1Labels = mixedMoment B raw27630step2 raw27630step2Labels := by
      have ha : raw27630step2 = -raw27630step1 := by apply Matrix.ext; change ∀ i j, raw27630step2 i j = -(raw27630step1 i j); unfold raw27630step2 raw27630step1; decide +kernel
      have hl : raw27630step2Labels = raw27630step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2434 node2434Labels := by rfl

def raw27631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27631Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27631step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27631step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27631step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27631 raw27631Labels = mixedMoment B node2429 node2429Labels := by
  calc
    mixedMoment B raw27631 raw27631Labels = mixedMoment B raw27631step0 raw27631step0Labels := by
      have ha : raw27631step0 = (fun i j => raw27631 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27631step0 raw27631; decide +kernel
      have hl : raw27631step0Labels = raw27631Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27631 raw27631Labels permutation662 permutation3
    mixedMoment B raw27631step0 raw27631step0Labels = mixedMoment B raw27631step1 raw27631step1Labels := by
      have ha : raw27631step1 = -raw27631step0 := by apply Matrix.ext; change ∀ i j, raw27631step1 i j = -(raw27631step0 i j); unfold raw27631step1 raw27631step0; decide +kernel
      have hl : raw27631step1Labels = raw27631step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2429 node2429Labels := by rfl

def raw27632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27632Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27632step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27632step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27632step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27632step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw27632step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27632step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27632step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27632 raw27632Labels = mixedMoment B node2345 node2345Labels := by
  calc
    mixedMoment B raw27632 raw27632Labels = mixedMoment B raw27632step0 raw27632step0Labels := by
      have hz : ∀ j, raw27632 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27632step0 = (fun i j => raw27632 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27632step0 raw27632; decide +kernel
      have hl : raw27632step0Labels = raw27632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27632 raw27632Labels permutation434 hz
    mixedMoment B raw27632step0 raw27632step0Labels = mixedMoment B raw27632step1 raw27632step1Labels := by
      have hz : ∀ j, raw27632step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27632step1 = (fun i j => raw27632step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27632step1 raw27632step0; decide +kernel
      have hl : raw27632step1Labels = raw27632step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27632step0 raw27632step0Labels permutation80 hz
    mixedMoment B raw27632step1 raw27632step1Labels = mixedMoment B raw27632step2 raw27632step2Labels := by
      have ha : raw27632step2 = (fun i j => raw27632step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27632step2 raw27632step1; decide +kernel
      have hl : raw27632step2Labels = raw27632step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27632step1 raw27632step1Labels permutation31 permutation3
    mixedMoment B raw27632step2 raw27632step2Labels = mixedMoment B raw27632step3 raw27632step3Labels := by
      have ha : raw27632step3 = -raw27632step2 := by apply Matrix.ext; change ∀ i j, raw27632step3 i j = -(raw27632step2 i j); unfold raw27632step3 raw27632step2; decide +kernel
      have hl : raw27632step3Labels = raw27632step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2345 node2345Labels := by rfl

def raw27633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27633Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27633step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27633step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27633step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27633step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27633 raw27633Labels = mixedMoment B node2339 node2339Labels := by
  calc
    mixedMoment B raw27633 raw27633Labels = mixedMoment B raw27633step0 raw27633step0Labels := by
      have hz : ∀ j, raw27633 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27633step0 = (fun i j => raw27633 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27633step0 raw27633; decide +kernel
      have hl : raw27633step0Labels = raw27633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27633 raw27633Labels permutation434 hz
    mixedMoment B raw27633step0 raw27633step0Labels = mixedMoment B raw27633step1 raw27633step1Labels := by
      have ha : raw27633step1 = (fun i j => raw27633step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27633step1 raw27633step0; decide +kernel
      have hl : raw27633step1Labels = raw27633step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27633step0 raw27633step0Labels permutation149 permutation3
    mixedMoment B raw27633step1 raw27633step1Labels = mixedMoment B raw27633step2 raw27633step2Labels := by
      have ha : raw27633step2 = -raw27633step1 := by apply Matrix.ext; change ∀ i j, raw27633step2 i j = -(raw27633step1 i j); unfold raw27633step2 raw27633step1; decide +kernel
      have hl : raw27633step2Labels = raw27633step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2339 node2339Labels := by rfl

def raw27634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27634Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw27634step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27634step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27634step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27634 raw27634Labels = mixedMoment B node2339 node2339Labels := by
  calc
    mixedMoment B raw27634 raw27634Labels = mixedMoment B raw27634step0 raw27634step0Labels := by
      have hz : ∀ j, raw27634 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27634step0 = (fun i j => raw27634 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27634step0 raw27634; decide +kernel
      have hl : raw27634step0Labels = raw27634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27634 raw27634Labels permutation346 hz
    mixedMoment B raw27634step0 raw27634step0Labels = mixedMoment B raw27634step1 raw27634step1Labels := by
      have ha : raw27634step1 = (fun i j => raw27634step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27634step1 raw27634step0; decide +kernel
      have hl : raw27634step1Labels = raw27634step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27634step0 raw27634step0Labels permutation149 permutation3
    mixedMoment B raw27634step1 raw27634step1Labels = mixedMoment B raw27634step2 raw27634step2Labels := by
      have ha : raw27634step2 = -raw27634step1 := by apply Matrix.ext; change ∀ i j, raw27634step2 i j = -(raw27634step1 i j); unfold raw27634step2 raw27634step1; decide +kernel
      have hl : raw27634step2Labels = raw27634step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2339 node2339Labels := by rfl

def raw27635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27635Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27635step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27635step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27635step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27635step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw27635step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27635step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw27635step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27635 raw27635Labels = mixedMoment B node939 node939Labels := by
  calc
    mixedMoment B raw27635 raw27635Labels = mixedMoment B raw27635step0 raw27635step0Labels := by
      have hz : ∀ j, raw27635 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27635step0 = (fun i j => raw27635 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27635step0 raw27635; decide +kernel
      have hl : raw27635step0Labels = raw27635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27635 raw27635Labels permutation434 hz
    mixedMoment B raw27635step0 raw27635step0Labels = mixedMoment B raw27635step1 raw27635step1Labels := by
      have hz : ∀ j, raw27635step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27635step1 = (fun i j => raw27635step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27635step1 raw27635step0; decide +kernel
      have hl : raw27635step1Labels = raw27635step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27635step0 raw27635step0Labels permutation80 hz
    mixedMoment B raw27635step1 raw27635step1Labels = mixedMoment B raw27635step2 raw27635step2Labels := by
      have ha : raw27635step2 = (fun i j => raw27635step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27635step2 raw27635step1; decide +kernel
      have hl : raw27635step2Labels = raw27635step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27635step1 raw27635step1Labels permutation31 permutation3
    mixedMoment B raw27635step2 raw27635step2Labels = mixedMoment B raw27635step3 raw27635step3Labels := by
      have ha : raw27635step3 = -raw27635step2 := by apply Matrix.ext; change ∀ i j, raw27635step3 i j = -(raw27635step2 i j); unfold raw27635step3 raw27635step2; decide +kernel
      have hl : raw27635step3Labels = raw27635step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node939 node939Labels := by rfl

def raw27636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27636Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27636step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27636step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27636step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27636step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27636step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27636 raw27636Labels = mixedMoment B node930 node930Labels := by
  calc
    mixedMoment B raw27636 raw27636Labels = mixedMoment B raw27636step0 raw27636step0Labels := by
      have hz : ∀ j, raw27636 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27636step0 = (fun i j => raw27636 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27636step0 raw27636; decide +kernel
      have hl : raw27636step0Labels = raw27636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27636 raw27636Labels permutation434 hz
    mixedMoment B raw27636step0 raw27636step0Labels = mixedMoment B raw27636step1 raw27636step1Labels := by
      have ha : raw27636step1 = (fun i j => raw27636step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27636step1 raw27636step0; decide +kernel
      have hl : raw27636step1Labels = raw27636step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27636step0 raw27636step0Labels permutation149 permutation3
    mixedMoment B raw27636step1 raw27636step1Labels = mixedMoment B raw27636step2 raw27636step2Labels := by
      have ha : raw27636step2 = -raw27636step1 := by apply Matrix.ext; change ∀ i j, raw27636step2 i j = -(raw27636step1 i j); unfold raw27636step2 raw27636step1; decide +kernel
      have hl : raw27636step2Labels = raw27636step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node930 node930Labels := by rfl

def raw27637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27637Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw27637step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27637step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27637step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27637step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27637 raw27637Labels = mixedMoment B node930 node930Labels := by
  calc
    mixedMoment B raw27637 raw27637Labels = mixedMoment B raw27637step0 raw27637step0Labels := by
      have hz : ∀ j, raw27637 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27637step0 = (fun i j => raw27637 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27637step0 raw27637; decide +kernel
      have hl : raw27637step0Labels = raw27637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27637 raw27637Labels permutation346 hz
    mixedMoment B raw27637step0 raw27637step0Labels = mixedMoment B raw27637step1 raw27637step1Labels := by
      have ha : raw27637step1 = (fun i j => raw27637step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27637step1 raw27637step0; decide +kernel
      have hl : raw27637step1Labels = raw27637step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27637step0 raw27637step0Labels permutation149 permutation3
    mixedMoment B raw27637step1 raw27637step1Labels = mixedMoment B raw27637step2 raw27637step2Labels := by
      have ha : raw27637step2 = -raw27637step1 := by apply Matrix.ext; change ∀ i j, raw27637step2 i j = -(raw27637step1 i j); unfold raw27637step2 raw27637step1; decide +kernel
      have hl : raw27637step2Labels = raw27637step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node930 node930Labels := by rfl

def raw27638 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27638Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27638step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27638step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![-2, -1, 3]]
def raw27638step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27638step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27638step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27638step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw27638step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27638 raw27638Labels = mixedMoment B node5171 node5171Labels := by
  calc
    mixedMoment B raw27638 raw27638Labels = mixedMoment B raw27638step0 raw27638step0Labels := by
      have hz : ∀ j, raw27638 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27638step0 = (fun i j => raw27638 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27638step0 raw27638; decide +kernel
      have hl : raw27638step0Labels = raw27638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27638 raw27638Labels permutation434 hz
    mixedMoment B raw27638step0 raw27638step0Labels = mixedMoment B raw27638step1 raw27638step1Labels := by
      have hz : ∀ j, raw27638step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27638step1 = (fun i j => raw27638step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27638step1 raw27638step0; decide +kernel
      have hl : raw27638step1Labels = raw27638step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27638step0 raw27638step0Labels permutation80 hz
    mixedMoment B raw27638step1 raw27638step1Labels = mixedMoment B raw27638step2 raw27638step2Labels := by
      have ha : raw27638step2 = (fun i j => raw27638step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27638step2 raw27638step1; decide +kernel
      have hl : raw27638step2Labels = raw27638step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27638step1 raw27638step1Labels permutation8 permutation7
    mixedMoment B raw27638step2 raw27638step2Labels = mixedMoment B raw27638step3 raw27638step3Labels := by
      have ha : raw27638step3 = raw27638step2 := by apply Matrix.ext; unfold raw27638step3 raw27638step2; decide +kernel
      have hl : raw27638step2Labels = labelEmbedding10 ∘ raw27638step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27638step2 raw27638step2Labels raw27638step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5171 node5171Labels := by rfl

def raw27639 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27639Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27639step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27639step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27639step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27639step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27639 raw27639Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw27639 raw27639Labels = mixedMoment B raw27639step0 raw27639step0Labels := by
      have hz : ∀ j, raw27639 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27639step0 = (fun i j => raw27639 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27639step0 raw27639; decide +kernel
      have hl : raw27639step0Labels = raw27639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27639 raw27639Labels permutation434 hz
    mixedMoment B raw27639step0 raw27639step0Labels = mixedMoment B raw27639step1 raw27639step1Labels := by
      have ha : raw27639step1 = (fun i j => raw27639step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27639step1 raw27639step0; decide +kernel
      have hl : raw27639step1Labels = raw27639step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27639step0 raw27639step0Labels permutation32 permutation7
    mixedMoment B raw27639step1 raw27639step1Labels = mixedMoment B raw27639step2 raw27639step2Labels := by
      have ha : raw27639step2 = raw27639step1 := by apply Matrix.ext; unfold raw27639step2 raw27639step1; decide +kernel
      have hl : raw27639step1Labels = labelEmbedding10 ∘ raw27639step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27639step1 raw27639step1Labels raw27639step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5075 node5075Labels := by rfl

def raw27640 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27640Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27640step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27640step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27640step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27640step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27640 raw27640Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw27640 raw27640Labels = mixedMoment B raw27640step0 raw27640step0Labels := by
      have hz : ∀ j, raw27640 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27640step0 = (fun i j => raw27640 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27640step0 raw27640; decide +kernel
      have hl : raw27640step0Labels = raw27640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27640 raw27640Labels permutation346 hz
    mixedMoment B raw27640step0 raw27640step0Labels = mixedMoment B raw27640step1 raw27640step1Labels := by
      have ha : raw27640step1 = (fun i j => raw27640step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27640step1 raw27640step0; decide +kernel
      have hl : raw27640step1Labels = raw27640step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27640step0 raw27640step0Labels permutation32 permutation7
    mixedMoment B raw27640step1 raw27640step1Labels = mixedMoment B raw27640step2 raw27640step2Labels := by
      have ha : raw27640step2 = raw27640step1 := by apply Matrix.ext; unfold raw27640step2 raw27640step1; decide +kernel
      have hl : raw27640step1Labels = labelEmbedding10 ∘ raw27640step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27640step1 raw27640step1Labels raw27640step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5075 node5075Labels := by rfl

def raw27641 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27641Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27641step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw27641step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27641step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27641step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27641step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27641step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27641 raw27641Labels = mixedMoment B node5107 node5107Labels := by
  calc
    mixedMoment B raw27641 raw27641Labels = mixedMoment B raw27641step0 raw27641step0Labels := by
      have hz : ∀ j, raw27641 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27641step0 = (fun i j => raw27641 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27641step0 raw27641; decide +kernel
      have hl : raw27641step0Labels = raw27641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27641 raw27641Labels permutation434 hz
    mixedMoment B raw27641step0 raw27641step0Labels = mixedMoment B raw27641step1 raw27641step1Labels := by
      have hz : ∀ j, raw27641step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27641step1 = (fun i j => raw27641step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27641step1 raw27641step0; decide +kernel
      have hl : raw27641step1Labels = raw27641step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27641step0 raw27641step0Labels permutation80 hz
    mixedMoment B raw27641step1 raw27641step1Labels = mixedMoment B raw27641step2 raw27641step2Labels := by
      have ha : raw27641step2 = (fun i j => raw27641step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27641step2 raw27641step1; decide +kernel
      have hl : raw27641step2Labels = raw27641step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27641step1 raw27641step1Labels permutation8 permutation7
    mixedMoment B raw27641step2 raw27641step2Labels = mixedMoment B raw27641step3 raw27641step3Labels := by
      have ha : raw27641step3 = raw27641step2 := by apply Matrix.ext; unfold raw27641step3 raw27641step2; decide +kernel
      have hl : raw27641step2Labels = labelEmbedding10 ∘ raw27641step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27641step2 raw27641step2Labels raw27641step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5107 node5107Labels := by rfl

def raw27642 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27642Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27642step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27642step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-3, 0, 3]]
def raw27642step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27642step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw27642step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27642step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27642step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27642step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27642step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27642 raw27642Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw27642 raw27642Labels = mixedMoment B raw27642step0 raw27642step0Labels := by
      have hz : ∀ j, raw27642 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27642step0 = (fun i j => raw27642 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27642step0 raw27642; decide +kernel
      have hl : raw27642step0Labels = raw27642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27642 raw27642Labels permutation434 hz
    mixedMoment B raw27642step0 raw27642step0Labels = mixedMoment B raw27642step1 raw27642step1Labels := by
      have hz : ∀ j, raw27642step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27642step1 = (fun i j => raw27642step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27642step1 raw27642step0; decide +kernel
      have hl : raw27642step1Labels = raw27642step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27642step0 raw27642step0Labels permutation80 hz
    mixedMoment B raw27642step1 raw27642step1Labels = mixedMoment B raw27642step2 raw27642step2Labels := by
      have ha : raw27642step2 = (fun i j => raw27642step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27642step2 raw27642step1; decide +kernel
      have hl : raw27642step2Labels = raw27642step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27642step1 raw27642step1Labels permutation31 permutation7
    mixedMoment B raw27642step2 raw27642step2Labels = mixedMoment B raw27642step3 raw27642step3Labels := by
      have ha : raw27642step3 = -raw27642step2 := by apply Matrix.ext; change ∀ i j, raw27642step3 i j = -(raw27642step2 i j); unfold raw27642step3 raw27642step2; decide +kernel
      have hl : raw27642step3Labels = raw27642step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27642step3 raw27642step3Labels = mixedMoment B raw27642step4 raw27642step4Labels := by
      have ha : raw27642step4 = raw27642step3 := by apply Matrix.ext; unfold raw27642step4 raw27642step3; decide +kernel
      have hl : raw27642step3Labels = labelEmbedding10 ∘ raw27642step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27642step3 raw27642step3Labels raw27642step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4841 node4841Labels := by rfl

def raw27643 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27643Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27643step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27643step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -1, 1], ![-2, -1, 3]]
def raw27643step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27643step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27643step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27643step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27643step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27643 raw27643Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw27643 raw27643Labels = mixedMoment B raw27643step0 raw27643step0Labels := by
      have hz : ∀ j, raw27643 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27643step0 = (fun i j => raw27643 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27643step0 raw27643; decide +kernel
      have hl : raw27643step0Labels = raw27643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27643 raw27643Labels permutation434 hz
    mixedMoment B raw27643step0 raw27643step0Labels = mixedMoment B raw27643step1 raw27643step1Labels := by
      have hz : ∀ j, raw27643step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27643step1 = (fun i j => raw27643step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27643step1 raw27643step0; decide +kernel
      have hl : raw27643step1Labels = raw27643step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27643step0 raw27643step0Labels permutation80 hz
    mixedMoment B raw27643step1 raw27643step1Labels = mixedMoment B raw27643step2 raw27643step2Labels := by
      have ha : raw27643step2 = (fun i j => raw27643step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27643step2 raw27643step1; decide +kernel
      have hl : raw27643step2Labels = raw27643step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27643step1 raw27643step1Labels permutation8 permutation6
    mixedMoment B raw27643step2 raw27643step2Labels = mixedMoment B raw27643step3 raw27643step3Labels := by
      have ha : raw27643step3 = raw27643step2 := by apply Matrix.ext; unfold raw27643step3 raw27643step2; decide +kernel
      have hl : raw27643step2Labels = labelEmbedding9 ∘ raw27643step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27643step2 raw27643step2Labels raw27643step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4871 node4871Labels := by rfl

def raw27644 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27644Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27644step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27644step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw27644step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27644step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27644step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27644step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27644step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27644 raw27644Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw27644 raw27644Labels = mixedMoment B raw27644step0 raw27644step0Labels := by
      have hz : ∀ j, raw27644 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27644step0 = (fun i j => raw27644 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27644step0 raw27644; decide +kernel
      have hl : raw27644step0Labels = raw27644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27644 raw27644Labels permutation434 hz
    mixedMoment B raw27644step0 raw27644step0Labels = mixedMoment B raw27644step1 raw27644step1Labels := by
      have ha : raw27644step1 = (fun i j => raw27644step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27644step1 raw27644step0; decide +kernel
      have hl : raw27644step1Labels = raw27644step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27644step0 raw27644step0Labels permutation151 permutation7
    mixedMoment B raw27644step1 raw27644step1Labels = mixedMoment B raw27644step2 raw27644step2Labels := by
      have ha : raw27644step2 = -raw27644step1 := by apply Matrix.ext; change ∀ i j, raw27644step2 i j = -(raw27644step1 i j); unfold raw27644step2 raw27644step1; decide +kernel
      have hl : raw27644step2Labels = raw27644step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27644step2 raw27644step2Labels = mixedMoment B raw27644step3 raw27644step3Labels := by
      have ha : raw27644step3 = raw27644step2 := by apply Matrix.ext; unfold raw27644step3 raw27644step2; decide +kernel
      have hl : raw27644step2Labels = labelEmbedding10 ∘ raw27644step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27644step2 raw27644step2Labels raw27644step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5139 node5139Labels := by rfl

def raw27645 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27645Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27645step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw27645step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27645step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27645step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27645step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27645step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27645 raw27645Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw27645 raw27645Labels = mixedMoment B raw27645step0 raw27645step0Labels := by
      have hz : ∀ j, raw27645 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27645step0 = (fun i j => raw27645 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27645step0 raw27645; decide +kernel
      have hl : raw27645step0Labels = raw27645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27645 raw27645Labels permutation346 hz
    mixedMoment B raw27645step0 raw27645step0Labels = mixedMoment B raw27645step1 raw27645step1Labels := by
      have ha : raw27645step1 = (fun i j => raw27645step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27645step1 raw27645step0; decide +kernel
      have hl : raw27645step1Labels = raw27645step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27645step0 raw27645step0Labels permutation151 permutation7
    mixedMoment B raw27645step1 raw27645step1Labels = mixedMoment B raw27645step2 raw27645step2Labels := by
      have ha : raw27645step2 = -raw27645step1 := by apply Matrix.ext; change ∀ i j, raw27645step2 i j = -(raw27645step1 i j); unfold raw27645step2 raw27645step1; decide +kernel
      have hl : raw27645step2Labels = raw27645step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27645step2 raw27645step2Labels = mixedMoment B raw27645step3 raw27645step3Labels := by
      have ha : raw27645step3 = raw27645step2 := by apply Matrix.ext; unfold raw27645step3 raw27645step2; decide +kernel
      have hl : raw27645step2Labels = labelEmbedding10 ∘ raw27645step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27645step2 raw27645step2Labels raw27645step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5139 node5139Labels := by rfl

def raw27646 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27646Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27646step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw27646step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27646step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw27646step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27646step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27646step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27646step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27646step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27646 raw27646Labels = mixedMoment B node5109 node5109Labels := by
  calc
    mixedMoment B raw27646 raw27646Labels = mixedMoment B raw27646step0 raw27646step0Labels := by
      have hz : ∀ j, raw27646 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27646step0 = (fun i j => raw27646 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27646step0 raw27646; decide +kernel
      have hl : raw27646step0Labels = raw27646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27646 raw27646Labels permutation434 hz
    mixedMoment B raw27646step0 raw27646step0Labels = mixedMoment B raw27646step1 raw27646step1Labels := by
      have hz : ∀ j, raw27646step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27646step1 = (fun i j => raw27646step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27646step1 raw27646step0; decide +kernel
      have hl : raw27646step1Labels = raw27646step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27646step0 raw27646step0Labels permutation80 hz
    mixedMoment B raw27646step1 raw27646step1Labels = mixedMoment B raw27646step2 raw27646step2Labels := by
      have ha : raw27646step2 = (fun i j => raw27646step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27646step2 raw27646step1; decide +kernel
      have hl : raw27646step2Labels = raw27646step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27646step1 raw27646step1Labels permutation31 permutation7
    mixedMoment B raw27646step2 raw27646step2Labels = mixedMoment B raw27646step3 raw27646step3Labels := by
      have ha : raw27646step3 = -raw27646step2 := by apply Matrix.ext; change ∀ i j, raw27646step3 i j = -(raw27646step2 i j); unfold raw27646step3 raw27646step2; decide +kernel
      have hl : raw27646step3Labels = raw27646step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27646step3 raw27646step3Labels = mixedMoment B raw27646step4 raw27646step4Labels := by
      have ha : raw27646step4 = raw27646step3 := by apply Matrix.ext; unfold raw27646step4 raw27646step3; decide +kernel
      have hl : raw27646step3Labels = labelEmbedding10 ∘ raw27646step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27646step3 raw27646step3Labels raw27646step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5109 node5109Labels := by rfl

def raw27647 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27647Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27647step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27647step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, -1, 1], ![-3, 0, 3]]
def raw27647step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27647step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw27647step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27647step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27647step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27647step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27647step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27647 raw27647Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw27647 raw27647Labels = mixedMoment B raw27647step0 raw27647step0Labels := by
      have hz : ∀ j, raw27647 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27647step0 = (fun i j => raw27647 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27647step0 raw27647; decide +kernel
      have hl : raw27647step0Labels = raw27647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27647 raw27647Labels permutation434 hz
    mixedMoment B raw27647step0 raw27647step0Labels = mixedMoment B raw27647step1 raw27647step1Labels := by
      have hz : ∀ j, raw27647step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27647step1 = (fun i j => raw27647step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27647step1 raw27647step0; decide +kernel
      have hl : raw27647step1Labels = raw27647step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27647step0 raw27647step0Labels permutation80 hz
    mixedMoment B raw27647step1 raw27647step1Labels = mixedMoment B raw27647step2 raw27647step2Labels := by
      have ha : raw27647step2 = (fun i j => raw27647step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27647step2 raw27647step1; decide +kernel
      have hl : raw27647step2Labels = raw27647step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27647step1 raw27647step1Labels permutation31 permutation7
    mixedMoment B raw27647step2 raw27647step2Labels = mixedMoment B raw27647step3 raw27647step3Labels := by
      have ha : raw27647step3 = -raw27647step2 := by apply Matrix.ext; change ∀ i j, raw27647step3 i j = -(raw27647step2 i j); unfold raw27647step3 raw27647step2; decide +kernel
      have hl : raw27647step3Labels = raw27647step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27647step3 raw27647step3Labels = mixedMoment B raw27647step4 raw27647step4Labels := by
      have ha : raw27647step4 = raw27647step3 := by apply Matrix.ext; unfold raw27647step4 raw27647step3; decide +kernel
      have hl : raw27647step3Labels = labelEmbedding10 ∘ raw27647step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27647step3 raw27647step3Labels raw27647step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4843 node4843Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
