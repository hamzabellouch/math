import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw40704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw40704Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw40704step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40704step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40704 raw40704Labels = mixedMoment B node2952 node2952Labels := by
  calc
    mixedMoment B raw40704 raw40704Labels = mixedMoment B raw40704step0 raw40704step0Labels := by
      have hz : ∀ j, raw40704 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40704step0 = (fun i j => raw40704 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40704step0 raw40704; decide +kernel
      have hl : raw40704step0Labels = raw40704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40704 raw40704Labels permutation434 hz
    mixedMoment B raw40704step0 raw40704step0Labels = mixedMoment B raw40704step1 raw40704step1Labels := by
      have ha : raw40704step1 = (fun i j => raw40704step0 (permutation140 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40704step1 raw40704step0; decide +kernel
      have hl : raw40704step1Labels = raw40704step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40704step0 raw40704step0Labels permutation140 permutation6
    _ = mixedMoment B node2952 node2952Labels := by rfl

def raw40705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw40705Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40705step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40705step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40705 raw40705Labels = mixedMoment B node2951 node2951Labels := by
  calc
    mixedMoment B raw40705 raw40705Labels = mixedMoment B raw40705step0 raw40705step0Labels := by
      have ha : raw40705step0 = (fun i j => raw40705 (permutation623 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40705step0 raw40705; decide +kernel
      have hl : raw40705step0Labels = raw40705Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40705 raw40705Labels permutation623 permutation6
    _ = mixedMoment B node2951 node2951Labels := by rfl

def raw40706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40706Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40706step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40706step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40706step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40706step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40706 raw40706Labels = mixedMoment B node3827 node3827Labels := by
  calc
    mixedMoment B raw40706 raw40706Labels = mixedMoment B raw40706step0 raw40706step0Labels := by
      have ha : raw40706step0 = (fun i j => raw40706 (permutation455 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40706step0 raw40706; decide +kernel
      have hl : raw40706step0Labels = raw40706Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40706 raw40706Labels permutation455 permutation6
    mixedMoment B raw40706step0 raw40706step0Labels = mixedMoment B raw40706step1 raw40706step1Labels := by
      have ha : raw40706step1 = -raw40706step0 := by apply Matrix.ext; change ∀ i j, raw40706step1 i j = -(raw40706step0 i j); unfold raw40706step1 raw40706step0; decide +kernel
      have hl : raw40706step1Labels = raw40706step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3827 node3827Labels := by rfl

def raw40707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40707Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40707step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40707step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40707 raw40707Labels = mixedMoment B node2933 node2933Labels := by
  calc
    mixedMoment B raw40707 raw40707Labels = mixedMoment B raw40707step0 raw40707step0Labels := by
      have ha : raw40707step0 = (fun i j => raw40707 (permutation641 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40707step0 raw40707; decide +kernel
      have hl : raw40707step0Labels = raw40707Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40707 raw40707Labels permutation641 permutation6
    _ = mixedMoment B node2933 node2933Labels := by rfl

def raw40708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw40708Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw40708step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40708step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2], ![2, 2, -4]]
def raw40708step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40708step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40708step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40708 raw40708Labels = mixedMoment B node1292 node1292Labels := by
  calc
    mixedMoment B raw40708 raw40708Labels = mixedMoment B raw40708step0 raw40708step0Labels := by
      have hz : ∀ j, raw40708 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40708step0 = (fun i j => raw40708 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40708step0 raw40708; decide +kernel
      have hl : raw40708step0Labels = raw40708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40708 raw40708Labels permutation434 hz
    mixedMoment B raw40708step0 raw40708step0Labels = mixedMoment B raw40708step1 raw40708step1Labels := by
      have hz : ∀ j, raw40708step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40708step1 = (fun i j => raw40708step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40708step1 raw40708step0; decide +kernel
      have hl : raw40708step1Labels = raw40708step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40708step0 raw40708step0Labels permutation80 hz
    mixedMoment B raw40708step1 raw40708step1Labels = mixedMoment B raw40708step2 raw40708step2Labels := by
      have ha : raw40708step2 = (fun i j => raw40708step1 (permutation26 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40708step2 raw40708step1; decide +kernel
      have hl : raw40708step2Labels = raw40708step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40708step1 raw40708step1Labels permutation26 permutation6
    _ = mixedMoment B node1292 node1292Labels := by rfl

def raw40709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw40709Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw40709step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw40709step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40709 raw40709Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw40709 raw40709Labels = mixedMoment B raw40709step0 raw40709step0Labels := by
      have hz : ∀ j, raw40709 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40709step0 = (fun i j => raw40709 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40709step0 raw40709; decide +kernel
      have hl : raw40709step0Labels = raw40709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40709 raw40709Labels permutation346 hz
    mixedMoment B raw40709step0 raw40709step0Labels = mixedMoment B raw40709step1 raw40709step1Labels := by
      have ha : raw40709step1 = (fun i j => raw40709step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40709step1 raw40709step0; decide +kernel
      have hl : raw40709step1Labels = raw40709step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40709step0 raw40709step0Labels permutation122 permutation6
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw40710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw40710Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw40710step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40710step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40710 raw40710Labels = mixedMoment B node1291 node1291Labels := by
  calc
    mixedMoment B raw40710 raw40710Labels = mixedMoment B raw40710step0 raw40710step0Labels := by
      have hz : ∀ j, raw40710 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40710step0 = (fun i j => raw40710 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40710step0 raw40710; decide +kernel
      have hl : raw40710step0Labels = raw40710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40710 raw40710Labels permutation346 hz
    mixedMoment B raw40710step0 raw40710step0Labels = mixedMoment B raw40710step1 raw40710step1Labels := by
      have ha : raw40710step1 = (fun i j => raw40710step0 (permutation128 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40710step1 raw40710step0; decide +kernel
      have hl : raw40710step1Labels = raw40710step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40710step0 raw40710step0Labels permutation128 permutation6
    _ = mixedMoment B node1291 node1291Labels := by rfl

def raw40711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw40711Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw40711step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40711step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40711step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40711 raw40711Labels = mixedMoment B node2632 node2632Labels := by
  calc
    mixedMoment B raw40711 raw40711Labels = mixedMoment B raw40711step0 raw40711step0Labels := by
      have hz : ∀ j, raw40711 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40711step0 = (fun i j => raw40711 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40711step0 raw40711; decide +kernel
      have hl : raw40711step0Labels = raw40711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40711 raw40711Labels permutation346 hz
    mixedMoment B raw40711step0 raw40711step0Labels = mixedMoment B raw40711step1 raw40711step1Labels := by
      have ha : raw40711step1 = (fun i j => raw40711step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40711step1 raw40711step0; decide +kernel
      have hl : raw40711step1Labels = raw40711step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40711step0 raw40711step0Labels permutation122 permutation6
    _ = mixedMoment B node2632 node2632Labels := by rfl

def raw40712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw40712Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw40712step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40712step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40712 raw40712Labels = mixedMoment B node1261 node1261Labels := by
  calc
    mixedMoment B raw40712 raw40712Labels = mixedMoment B raw40712step0 raw40712step0Labels := by
      have hz : ∀ j, raw40712 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40712step0 = (fun i j => raw40712 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40712step0 raw40712; decide +kernel
      have hl : raw40712step0Labels = raw40712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40712 raw40712Labels permutation346 hz
    mixedMoment B raw40712step0 raw40712step0Labels = mixedMoment B raw40712step1 raw40712step1Labels := by
      have ha : raw40712step1 = (fun i j => raw40712step0 (permutation146 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40712step1 raw40712step0; decide +kernel
      have hl : raw40712step1Labels = raw40712step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40712step0 raw40712step0Labels permutation146 permutation6
    _ = mixedMoment B node1261 node1261Labels := by rfl

def raw40713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw40713Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40713step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40713 raw40713Labels = mixedMoment B node2631 node2631Labels := by
  calc
    mixedMoment B raw40713 raw40713Labels = mixedMoment B raw40713step0 raw40713step0Labels := by
      have ha : raw40713step0 = (fun i j => raw40713 (permutation569 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40713step0 raw40713; decide +kernel
      have hl : raw40713step0Labels = raw40713Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40713 raw40713Labels permutation569 permutation6
    _ = mixedMoment B node2631 node2631Labels := by rfl

def raw40714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw40714Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40714step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40714step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40714 raw40714Labels = mixedMoment B node1260 node1260Labels := by
  calc
    mixedMoment B raw40714 raw40714Labels = mixedMoment B raw40714step0 raw40714step0Labels := by
      have ha : raw40714step0 = (fun i j => raw40714 (permutation665 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40714step0 raw40714; decide +kernel
      have hl : raw40714step0Labels = raw40714Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40714 raw40714Labels permutation665 permutation6
    _ = mixedMoment B node1260 node1260Labels := by rfl

def raw40715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw40715Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40715step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40715step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40715 raw40715Labels = mixedMoment B node2587 node2587Labels := by
  calc
    mixedMoment B raw40715 raw40715Labels = mixedMoment B raw40715step0 raw40715step0Labels := by
      have ha : raw40715step0 = (fun i j => raw40715 (permutation484 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40715step0 raw40715; decide +kernel
      have hl : raw40715step0Labels = raw40715Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40715 raw40715Labels permutation484 permutation6
    _ = mixedMoment B node2587 node2587Labels := by rfl

def raw40716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw40716Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw40716step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40716 raw40716Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw40716 raw40716Labels = mixedMoment B raw40716step0 raw40716step0Labels := by
      have ha : raw40716step0 = (fun i j => raw40716 (permutation499 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40716step0 raw40716; decide +kernel
      have hl : raw40716step0Labels = raw40716Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40716 raw40716Labels permutation499 permutation6
    _ = mixedMoment B node2750 node2750Labels := by rfl

def raw40717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw40717Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40717step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40717 raw40717Labels = mixedMoment B node2566 node2566Labels := by
  calc
    mixedMoment B raw40717 raw40717Labels = mixedMoment B raw40717step0 raw40717step0Labels := by
      have ha : raw40717step0 = (fun i j => raw40717 (permutation499 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40717step0 raw40717; decide +kernel
      have hl : raw40717step0Labels = raw40717Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40717 raw40717Labels permutation499 permutation6
    _ = mixedMoment B node2566 node2566Labels := by rfl

def raw40718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw40718Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![3, -2, -1]]
def raw40718step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40718step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![3, -2, -1]]
def raw40718step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40718step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw40718step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40718step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw40718step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40718 raw40718Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw40718 raw40718Labels = mixedMoment B raw40718step0 raw40718step0Labels := by
      have hz : ∀ j, raw40718 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40718step0 = (fun i j => raw40718 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40718step0 raw40718; decide +kernel
      have hl : raw40718step0Labels = raw40718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40718 raw40718Labels permutation520 hz
    mixedMoment B raw40718step0 raw40718step0Labels = mixedMoment B raw40718step1 raw40718step1Labels := by
      have hz : ∀ j, raw40718step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40718step1 = (fun i j => raw40718step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40718step1 raw40718step0; decide +kernel
      have hl : raw40718step1Labels = raw40718step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40718step0 raw40718step0Labels permutation104 hz
    mixedMoment B raw40718step1 raw40718step1Labels = mixedMoment B raw40718step2 raw40718step2Labels := by
      have ha : raw40718step2 = (fun i j => raw40718step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40718step2 raw40718step1; decide +kernel
      have hl : raw40718step2Labels = raw40718step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40718step1 raw40718step1Labels permutation31 permutation3
    mixedMoment B raw40718step2 raw40718step2Labels = mixedMoment B raw40718step3 raw40718step3Labels := by
      have ha : raw40718step3 = -raw40718step2 := by apply Matrix.ext; change ∀ i j, raw40718step3 i j = -(raw40718step2 i j); unfold raw40718step3 raw40718step2; decide +kernel
      have hl : raw40718step3Labels = raw40718step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2774 node2774Labels := by rfl

def raw40719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw40719Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![3, -1, -2]]
def raw40719step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw40719step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40719step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw40719step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40719 raw40719Labels = mixedMoment B node3092 node3092Labels := by
  calc
    mixedMoment B raw40719 raw40719Labels = mixedMoment B raw40719step0 raw40719step0Labels := by
      have hz : ∀ j, raw40719 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40719step0 = (fun i j => raw40719 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40719step0 raw40719; decide +kernel
      have hl : raw40719step0Labels = raw40719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40719 raw40719Labels permutation434 hz
    mixedMoment B raw40719step0 raw40719step0Labels = mixedMoment B raw40719step1 raw40719step1Labels := by
      have ha : raw40719step1 = (fun i j => raw40719step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40719step1 raw40719step0; decide +kernel
      have hl : raw40719step1Labels = raw40719step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40719step0 raw40719step0Labels permutation151 permutation3
    mixedMoment B raw40719step1 raw40719step1Labels = mixedMoment B raw40719step2 raw40719step2Labels := by
      have ha : raw40719step2 = -raw40719step1 := by apply Matrix.ext; change ∀ i j, raw40719step2 i j = -(raw40719step1 i j); unfold raw40719step2 raw40719step1; decide +kernel
      have hl : raw40719step2Labels = raw40719step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3092 node3092Labels := by rfl

def raw40720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw40720Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40720step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw40720step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40720step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw40720step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40720 raw40720Labels = mixedMoment B node3854 node3854Labels := by
  calc
    mixedMoment B raw40720 raw40720Labels = mixedMoment B raw40720step0 raw40720step0Labels := by
      have hz : ∀ j, raw40720 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40720step0 = (fun i j => raw40720 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40720step0 raw40720; decide +kernel
      have hl : raw40720step0Labels = raw40720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40720 raw40720Labels permutation434 hz
    mixedMoment B raw40720step0 raw40720step0Labels = mixedMoment B raw40720step1 raw40720step1Labels := by
      have ha : raw40720step1 = (fun i j => raw40720step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40720step1 raw40720step0; decide +kernel
      have hl : raw40720step1Labels = raw40720step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40720step0 raw40720step0Labels permutation151 permutation3
    mixedMoment B raw40720step1 raw40720step1Labels = mixedMoment B raw40720step2 raw40720step2Labels := by
      have ha : raw40720step2 = -raw40720step1 := by apply Matrix.ext; change ∀ i j, raw40720step2 i j = -(raw40720step1 i j); unfold raw40720step2 raw40720step1; decide +kernel
      have hl : raw40720step2Labels = raw40720step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3854 node3854Labels := by rfl

def raw40721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw40721Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw40721step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw40721step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40721 raw40721Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw40721 raw40721Labels = mixedMoment B raw40721step0 raw40721step0Labels := by
      have hz : ∀ j, raw40721 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40721step0 = (fun i j => raw40721 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40721step0 raw40721; decide +kernel
      have hl : raw40721step0Labels = raw40721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40721 raw40721Labels permutation434 hz
    mixedMoment B raw40721step0 raw40721step0Labels = mixedMoment B raw40721step1 raw40721step1Labels := by
      have ha : raw40721step1 = (fun i j => raw40721step0 (permutation102 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40721step1 raw40721step0; decide +kernel
      have hl : raw40721step1Labels = raw40721step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40721step0 raw40721step0Labels permutation102 permutation6
    _ = mixedMoment B node3881 node3881Labels := by rfl

def raw40722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw40722Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw40722step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40722step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40722 raw40722Labels = mixedMoment B node3733 node3733Labels := by
  calc
    mixedMoment B raw40722 raw40722Labels = mixedMoment B raw40722step0 raw40722step0Labels := by
      have hz : ∀ j, raw40722 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40722step0 = (fun i j => raw40722 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40722step0 raw40722; decide +kernel
      have hl : raw40722step0Labels = raw40722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40722 raw40722Labels permutation434 hz
    mixedMoment B raw40722step0 raw40722step0Labels = mixedMoment B raw40722step1 raw40722step1Labels := by
      have ha : raw40722step1 = (fun i j => raw40722step0 (permutation99 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40722step1 raw40722step0; decide +kernel
      have hl : raw40722step1Labels = raw40722step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40722step0 raw40722step0Labels permutation99 permutation6
    _ = mixedMoment B node3733 node3733Labels := by rfl

def raw40723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40723Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40723step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40723step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40723 raw40723Labels = mixedMoment B node3827 node3827Labels := by
  calc
    mixedMoment B raw40723 raw40723Labels = mixedMoment B raw40723step0 raw40723step0Labels := by
      have ha : raw40723step0 = (fun i j => raw40723 (permutation410 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40723step0 raw40723; decide +kernel
      have hl : raw40723step0Labels = raw40723Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40723 raw40723Labels permutation410 permutation6
    _ = mixedMoment B node3827 node3827Labels := by rfl

def raw40724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40724Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40724step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40724step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40724 raw40724Labels = mixedMoment B node3724 node3724Labels := by
  calc
    mixedMoment B raw40724 raw40724Labels = mixedMoment B raw40724step0 raw40724step0Labels := by
      have ha : raw40724step0 = (fun i j => raw40724 (permutation429 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40724step0 raw40724; decide +kernel
      have hl : raw40724step0Labels = raw40724Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40724 raw40724Labels permutation429 permutation6
    _ = mixedMoment B node3724 node3724Labels := by rfl

def raw40725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw40725Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40725step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40725step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40725 raw40725Labels = mixedMoment B node3819 node3819Labels := by
  calc
    mixedMoment B raw40725 raw40725Labels = mixedMoment B raw40725step0 raw40725step0Labels := by
      have ha : raw40725step0 = (fun i j => raw40725 (permutation390 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40725step0 raw40725; decide +kernel
      have hl : raw40725step0Labels = raw40725Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40725 raw40725Labels permutation390 permutation6
    _ = mixedMoment B node3819 node3819Labels := by rfl

def raw40726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw40726Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40726step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw40726step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40726 raw40726Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw40726 raw40726Labels = mixedMoment B raw40726step0 raw40726step0Labels := by
      have ha : raw40726step0 = (fun i j => raw40726 (permutation393 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40726step0 raw40726; decide +kernel
      have hl : raw40726step0Labels = raw40726Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40726 raw40726Labels permutation393 permutation6
    _ = mixedMoment B node3846 node3846Labels := by rfl

def raw40727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw40727Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40727step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40727step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40727step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40727step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40727 raw40727Labels = mixedMoment B node3949 node3949Labels := by
  calc
    mixedMoment B raw40727 raw40727Labels = mixedMoment B raw40727step0 raw40727step0Labels := by
      have ha : raw40727step0 = (fun i j => raw40727 (permutation322 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40727step0 raw40727; decide +kernel
      have hl : raw40727step0Labels = raw40727Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40727 raw40727Labels permutation322 permutation6
    mixedMoment B raw40727step0 raw40727step0Labels = mixedMoment B raw40727step1 raw40727step1Labels := by
      have ha : raw40727step1 = -raw40727step0 := by apply Matrix.ext; change ∀ i j, raw40727step1 i j = -(raw40727step0 i j); unfold raw40727step1 raw40727step0; decide +kernel
      have hl : raw40727step1Labels = raw40727step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3949 node3949Labels := by rfl

def raw40728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw40728Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw40728step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40728step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40728 raw40728Labels = mixedMoment B node2955 node2955Labels := by
  calc
    mixedMoment B raw40728 raw40728Labels = mixedMoment B raw40728step0 raw40728step0Labels := by
      have hz : ∀ j, raw40728 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40728step0 = (fun i j => raw40728 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40728step0 raw40728; decide +kernel
      have hl : raw40728step0Labels = raw40728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40728 raw40728Labels permutation434 hz
    mixedMoment B raw40728step0 raw40728step0Labels = mixedMoment B raw40728step1 raw40728step1Labels := by
      have ha : raw40728step1 = (fun i j => raw40728step0 (permutation141 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40728step1 raw40728step0; decide +kernel
      have hl : raw40728step1Labels = raw40728step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40728step0 raw40728step0Labels permutation141 permutation6
    _ = mixedMoment B node2955 node2955Labels := by rfl

def raw40729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw40729Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw40729step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40729step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 2, -3], ![2, -2, 0]]
def raw40729step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40729step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw40729step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40729 raw40729Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw40729 raw40729Labels = mixedMoment B raw40729step0 raw40729step0Labels := by
      have hz : ∀ j, raw40729 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40729step0 = (fun i j => raw40729 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40729step0 raw40729; decide +kernel
      have hl : raw40729step0Labels = raw40729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40729 raw40729Labels permutation434 hz
    mixedMoment B raw40729step0 raw40729step0Labels = mixedMoment B raw40729step1 raw40729step1Labels := by
      have hz : ∀ j, raw40729step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40729step1 = (fun i j => raw40729step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40729step1 raw40729step0; decide +kernel
      have hl : raw40729step1Labels = raw40729step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40729step0 raw40729step0Labels permutation80 hz
    mixedMoment B raw40729step1 raw40729step1Labels = mixedMoment B raw40729step2 raw40729step2Labels := by
      have ha : raw40729step2 = (fun i j => raw40729step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40729step2 raw40729step1; decide +kernel
      have hl : raw40729step2Labels = raw40729step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40729step1 raw40729step1Labels permutation24 permutation6
    _ = mixedMoment B node2774 node2774Labels := by rfl

def raw40730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw40730Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw40730step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40730step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 2, -4]]
def raw40730step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40730step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40730step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40730 raw40730Labels = mixedMoment B node1295 node1295Labels := by
  calc
    mixedMoment B raw40730 raw40730Labels = mixedMoment B raw40730step0 raw40730step0Labels := by
      have hz : ∀ j, raw40730 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40730step0 = (fun i j => raw40730 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40730step0 raw40730; decide +kernel
      have hl : raw40730step0Labels = raw40730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40730 raw40730Labels permutation434 hz
    mixedMoment B raw40730step0 raw40730step0Labels = mixedMoment B raw40730step1 raw40730step1Labels := by
      have hz : ∀ j, raw40730step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40730step1 = (fun i j => raw40730step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40730step1 raw40730step0; decide +kernel
      have hl : raw40730step1Labels = raw40730step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40730step0 raw40730step0Labels permutation80 hz
    mixedMoment B raw40730step1 raw40730step1Labels = mixedMoment B raw40730step2 raw40730step2Labels := by
      have ha : raw40730step2 = (fun i j => raw40730step1 (permutation27 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40730step2 raw40730step1; decide +kernel
      have hl : raw40730step2Labels = raw40730step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40730step1 raw40730step1Labels permutation27 permutation6
    _ = mixedMoment B node1295 node1295Labels := by rfl

def raw40731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw40731Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw40731step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40731step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40731 raw40731Labels = mixedMoment B node2633 node2633Labels := by
  calc
    mixedMoment B raw40731 raw40731Labels = mixedMoment B raw40731step0 raw40731step0Labels := by
      have hz : ∀ j, raw40731 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40731step0 = (fun i j => raw40731 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40731step0 raw40731; decide +kernel
      have hl : raw40731step0Labels = raw40731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40731 raw40731Labels permutation346 hz
    mixedMoment B raw40731step0 raw40731step0Labels = mixedMoment B raw40731step1 raw40731step1Labels := by
      have ha : raw40731step1 = (fun i j => raw40731step0 (permutation123 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40731step1 raw40731step0; decide +kernel
      have hl : raw40731step1Labels = raw40731step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40731step0 raw40731step0Labels permutation123 permutation6
    _ = mixedMoment B node2633 node2633Labels := by rfl

def raw40732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw40732Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw40732step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40732step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40732 raw40732Labels = mixedMoment B node1262 node1262Labels := by
  calc
    mixedMoment B raw40732 raw40732Labels = mixedMoment B raw40732step0 raw40732step0Labels := by
      have hz : ∀ j, raw40732 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40732step0 = (fun i j => raw40732 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40732step0 raw40732; decide +kernel
      have hl : raw40732step0Labels = raw40732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40732 raw40732Labels permutation346 hz
    mixedMoment B raw40732step0 raw40732step0Labels = mixedMoment B raw40732step1 raw40732step1Labels := by
      have ha : raw40732step1 = (fun i j => raw40732step0 (permutation147 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40732step1 raw40732step0; decide +kernel
      have hl : raw40732step1Labels = raw40732step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40732step0 raw40732step0Labels permutation147 permutation6
    _ = mixedMoment B node1262 node1262Labels := by rfl

def raw40733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw40733Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw40733step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40733step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40733 raw40733Labels = mixedMoment B node2591 node2591Labels := by
  calc
    mixedMoment B raw40733 raw40733Labels = mixedMoment B raw40733step0 raw40733step0Labels := by
      have hz : ∀ j, raw40733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40733step0 = (fun i j => raw40733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40733step0 raw40733; decide +kernel
      have hl : raw40733step0Labels = raw40733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40733 raw40733Labels permutation346 hz
    mixedMoment B raw40733step0 raw40733step0Labels = mixedMoment B raw40733step1 raw40733step1Labels := by
      have ha : raw40733step1 = (fun i j => raw40733step0 (permutation93 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40733step1 raw40733step0; decide +kernel
      have hl : raw40733step1Labels = raw40733step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40733step0 raw40733step0Labels permutation93 permutation6
    _ = mixedMoment B node2591 node2591Labels := by rfl

def raw40734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw40734Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw40734step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw40734step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40734 raw40734Labels = mixedMoment B node2751 node2751Labels := by
  calc
    mixedMoment B raw40734 raw40734Labels = mixedMoment B raw40734step0 raw40734step0Labels := by
      have hz : ∀ j, raw40734 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40734step0 = (fun i j => raw40734 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40734step0 raw40734; decide +kernel
      have hl : raw40734step0Labels = raw40734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40734 raw40734Labels permutation346 hz
    mixedMoment B raw40734step0 raw40734step0Labels = mixedMoment B raw40734step1 raw40734step1Labels := by
      have ha : raw40734step1 = (fun i j => raw40734step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40734step1 raw40734step0; decide +kernel
      have hl : raw40734step1Labels = raw40734step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40734step0 raw40734step0Labels permutation96 permutation6
    _ = mixedMoment B node2751 node2751Labels := by rfl

def raw40735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw40735Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![3, -1, -2]]
def raw40735step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40735step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 2, -2], ![3, -1, -2]]
def raw40735step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40735step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw40735step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40735step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw40735step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40735 raw40735Labels = mixedMoment B node2643 node2643Labels := by
  calc
    mixedMoment B raw40735 raw40735Labels = mixedMoment B raw40735step0 raw40735step0Labels := by
      have hz : ∀ j, raw40735 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40735step0 = (fun i j => raw40735 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40735step0 raw40735; decide +kernel
      have hl : raw40735step0Labels = raw40735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40735 raw40735Labels permutation520 hz
    mixedMoment B raw40735step0 raw40735step0Labels = mixedMoment B raw40735step1 raw40735step1Labels := by
      have hz : ∀ j, raw40735step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40735step1 = (fun i j => raw40735step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40735step1 raw40735step0; decide +kernel
      have hl : raw40735step1Labels = raw40735step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40735step0 raw40735step0Labels permutation104 hz
    mixedMoment B raw40735step1 raw40735step1Labels = mixedMoment B raw40735step2 raw40735step2Labels := by
      have ha : raw40735step2 = (fun i j => raw40735step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40735step2 raw40735step1; decide +kernel
      have hl : raw40735step2Labels = raw40735step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40735step1 raw40735step1Labels permutation15 permutation6
    mixedMoment B raw40735step2 raw40735step2Labels = mixedMoment B raw40735step3 raw40735step3Labels := by
      have ha : raw40735step3 = -raw40735step2 := by apply Matrix.ext; change ∀ i j, raw40735step3 i j = -(raw40735step2 i j); unfold raw40735step3 raw40735step2; decide +kernel
      have hl : raw40735step3Labels = raw40735step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2643 node2643Labels := by rfl

def raw40736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40736Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw40736step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40736step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw40736step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40736step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40736step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40736 raw40736Labels = mixedMoment B node2632 node2632Labels := by
  calc
    mixedMoment B raw40736 raw40736Labels = mixedMoment B raw40736step0 raw40736step0Labels := by
      have hz : ∀ j, raw40736 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40736step0 = (fun i j => raw40736 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40736step0 raw40736; decide +kernel
      have hl : raw40736step0Labels = raw40736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40736 raw40736Labels permutation434 hz
    mixedMoment B raw40736step0 raw40736step0Labels = mixedMoment B raw40736step1 raw40736step1Labels := by
      have ha : raw40736step1 = (fun i j => raw40736step0 (permutation61 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40736step1 raw40736step0; decide +kernel
      have hl : raw40736step1Labels = raw40736step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40736step0 raw40736step0Labels permutation61 permutation6
    mixedMoment B raw40736step1 raw40736step1Labels = mixedMoment B raw40736step2 raw40736step2Labels := by
      have ha : raw40736step2 = -raw40736step1 := by apply Matrix.ext; change ∀ i j, raw40736step2 i j = -(raw40736step1 i j); unfold raw40736step2 raw40736step1; decide +kernel
      have hl : raw40736step2Labels = raw40736step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2632 node2632Labels := by rfl

def raw40737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40737Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw40737step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40737step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40737step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw40737step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40737 raw40737Labels = mixedMoment B node2620 node2620Labels := by
  calc
    mixedMoment B raw40737 raw40737Labels = mixedMoment B raw40737step0 raw40737step0Labels := by
      have hz : ∀ j, raw40737 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40737step0 = (fun i j => raw40737 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40737step0 raw40737; decide +kernel
      have hl : raw40737step0Labels = raw40737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40737 raw40737Labels permutation434 hz
    mixedMoment B raw40737step0 raw40737step0Labels = mixedMoment B raw40737step1 raw40737step1Labels := by
      have ha : raw40737step1 = (fun i j => raw40737step0 (permutation59 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40737step1 raw40737step0; decide +kernel
      have hl : raw40737step1Labels = raw40737step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40737step0 raw40737step0Labels permutation59 permutation6
    mixedMoment B raw40737step1 raw40737step1Labels = mixedMoment B raw40737step2 raw40737step2Labels := by
      have ha : raw40737step2 = -raw40737step1 := by apply Matrix.ext; change ∀ i j, raw40737step2 i j = -(raw40737step1 i j); unfold raw40737step2 raw40737step1; decide +kernel
      have hl : raw40737step2Labels = raw40737step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2620 node2620Labels := by rfl

def raw40738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw40738Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40738step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw40738step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40738step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40738step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40738 raw40738Labels = mixedMoment B node2614 node2614Labels := by
  calc
    mixedMoment B raw40738 raw40738Labels = mixedMoment B raw40738step0 raw40738step0Labels := by
      have ha : raw40738step0 = (fun i j => raw40738 (permutation286 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40738step0 raw40738; decide +kernel
      have hl : raw40738step0Labels = raw40738Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40738 raw40738Labels permutation286 permutation6
    mixedMoment B raw40738step0 raw40738step0Labels = mixedMoment B raw40738step1 raw40738step1Labels := by
      have ha : raw40738step1 = -raw40738step0 := by apply Matrix.ext; change ∀ i j, raw40738step1 i j = -(raw40738step0 i j); unfold raw40738step1 raw40738step0; decide +kernel
      have hl : raw40738step1Labels = raw40738step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2614 node2614Labels := by rfl

def raw40739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw40739Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw40739step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw40739step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw40739step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40739 raw40739Labels = mixedMoment B node2641 node2641Labels := by
  calc
    mixedMoment B raw40739 raw40739Labels = mixedMoment B raw40739step0 raw40739step0Labels := by
      have hz : ∀ j, raw40739 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40739step0 = (fun i j => raw40739 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40739step0 raw40739; decide +kernel
      have hl : raw40739step0Labels = raw40739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40739 raw40739Labels permutation520 hz
    mixedMoment B raw40739step0 raw40739step0Labels = mixedMoment B raw40739step1 raw40739step1Labels := by
      have ha : raw40739step1 = (fun i j => raw40739step0 (permutation56 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40739step1 raw40739step0; decide +kernel
      have hl : raw40739step1Labels = raw40739step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40739step0 raw40739step0Labels permutation56 permutation6
    mixedMoment B raw40739step1 raw40739step1Labels = mixedMoment B raw40739step2 raw40739step2Labels := by
      have ha : raw40739step2 = -raw40739step1 := by apply Matrix.ext; change ∀ i j, raw40739step2 i j = -(raw40739step1 i j); unfold raw40739step2 raw40739step1; decide +kernel
      have hl : raw40739step2Labels = raw40739step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2641 node2641Labels := by rfl

def raw40740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40740Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw40740step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40740step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40740step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40740 raw40740Labels = mixedMoment B node2631 node2631Labels := by
  calc
    mixedMoment B raw40740 raw40740Labels = mixedMoment B raw40740step0 raw40740step0Labels := by
      have ha : raw40740step0 = (fun i j => raw40740 (permutation287 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40740step0 raw40740; decide +kernel
      have hl : raw40740step0Labels = raw40740Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40740 raw40740Labels permutation287 permutation6
    mixedMoment B raw40740step0 raw40740step0Labels = mixedMoment B raw40740step1 raw40740step1Labels := by
      have ha : raw40740step1 = -raw40740step0 := by apply Matrix.ext; change ∀ i j, raw40740step1 i j = -(raw40740step0 i j); unfold raw40740step1 raw40740step0; decide +kernel
      have hl : raw40740step1Labels = raw40740step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2631 node2631Labels := by rfl

def raw40741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40741Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40741step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40741step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40741step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40741 raw40741Labels = mixedMoment B node2617 node2617Labels := by
  calc
    mixedMoment B raw40741 raw40741Labels = mixedMoment B raw40741step0 raw40741step0Labels := by
      have ha : raw40741step0 = (fun i j => raw40741 (permutation277 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40741step0 raw40741; decide +kernel
      have hl : raw40741step0Labels = raw40741Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40741 raw40741Labels permutation277 permutation6
    mixedMoment B raw40741step0 raw40741step0Labels = mixedMoment B raw40741step1 raw40741step1Labels := by
      have ha : raw40741step1 = -raw40741step0 := by apply Matrix.ext; change ∀ i j, raw40741step1 i j = -(raw40741step0 i j); unfold raw40741step1 raw40741step0; decide +kernel
      have hl : raw40741step1Labels = raw40741step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2617 node2617Labels := by rfl

def raw40742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw40742Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw40742step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40742step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40742step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40742step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40742 raw40742Labels = mixedMoment B node2633 node2633Labels := by
  calc
    mixedMoment B raw40742 raw40742Labels = mixedMoment B raw40742step0 raw40742step0Labels := by
      have hz : ∀ j, raw40742 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40742step0 = (fun i j => raw40742 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40742step0 raw40742; decide +kernel
      have hl : raw40742step0Labels = raw40742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40742 raw40742Labels permutation434 hz
    mixedMoment B raw40742step0 raw40742step0Labels = mixedMoment B raw40742step1 raw40742step1Labels := by
      have ha : raw40742step1 = (fun i j => raw40742step0 (permutation60 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40742step1 raw40742step0; decide +kernel
      have hl : raw40742step1Labels = raw40742step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40742step0 raw40742step0Labels permutation60 permutation6
    mixedMoment B raw40742step1 raw40742step1Labels = mixedMoment B raw40742step2 raw40742step2Labels := by
      have ha : raw40742step2 = -raw40742step1 := by apply Matrix.ext; change ∀ i j, raw40742step2 i j = -(raw40742step1 i j); unfold raw40742step2 raw40742step1; decide +kernel
      have hl : raw40742step2Labels = raw40742step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2633 node2633Labels := by rfl

def raw40743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw40743Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw40743step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw40743step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40743step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw40743step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40743 raw40743Labels = mixedMoment B node2618 node2618Labels := by
  calc
    mixedMoment B raw40743 raw40743Labels = mixedMoment B raw40743step0 raw40743step0Labels := by
      have hz : ∀ j, raw40743 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40743step0 = (fun i j => raw40743 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40743step0 raw40743; decide +kernel
      have hl : raw40743step0Labels = raw40743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40743 raw40743Labels permutation434 hz
    mixedMoment B raw40743step0 raw40743step0Labels = mixedMoment B raw40743step1 raw40743step1Labels := by
      have ha : raw40743step1 = (fun i j => raw40743step0 (permutation58 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40743step1 raw40743step0; decide +kernel
      have hl : raw40743step1Labels = raw40743step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40743step0 raw40743step0Labels permutation58 permutation6
    mixedMoment B raw40743step1 raw40743step1Labels = mixedMoment B raw40743step2 raw40743step2Labels := by
      have ha : raw40743step2 = -raw40743step1 := by apply Matrix.ext; change ∀ i j, raw40743step2 i j = -(raw40743step1 i j); unfold raw40743step2 raw40743step1; decide +kernel
      have hl : raw40743step2Labels = raw40743step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2618 node2618Labels := by rfl

def raw40744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -1, -1]]
def raw40744Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 0, 0], ![1, 2, -3], ![2, -1, -1]]
def raw40744step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40744step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![1, 2, -3], ![2, -1, -1]]
def raw40744step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40744step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw40744step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40744 raw40744Labels = mixedMoment B node2635 node2635Labels := by
  calc
    mixedMoment B raw40744 raw40744Labels = mixedMoment B raw40744step0 raw40744step0Labels := by
      have hz : ∀ j, raw40744 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40744step0 = (fun i j => raw40744 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40744step0 raw40744; decide +kernel
      have hl : raw40744step0Labels = raw40744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40744 raw40744Labels permutation434 hz
    mixedMoment B raw40744step0 raw40744step0Labels = mixedMoment B raw40744step1 raw40744step1Labels := by
      have hz : ∀ j, raw40744step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40744step1 = (fun i j => raw40744step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40744step1 raw40744step0; decide +kernel
      have hl : raw40744step1Labels = raw40744step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40744step0 raw40744step0Labels permutation80 hz
    mixedMoment B raw40744step1 raw40744step1Labels = mixedMoment B raw40744step2 raw40744step2Labels := by
      have ha : raw40744step2 = (fun i j => raw40744step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40744step2 raw40744step1; decide +kernel
      have hl : raw40744step2Labels = raw40744step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40744step1 raw40744step1Labels permutation24 permutation6
    _ = mixedMoment B node2635 node2635Labels := by rfl

def raw40745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw40745Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw40745step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40745step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 2, -4]]
def raw40745step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40745step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw40745step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40745 raw40745Labels = mixedMoment B node1264 node1264Labels := by
  calc
    mixedMoment B raw40745 raw40745Labels = mixedMoment B raw40745step0 raw40745step0Labels := by
      have hz : ∀ j, raw40745 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40745step0 = (fun i j => raw40745 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40745step0 raw40745; decide +kernel
      have hl : raw40745step0Labels = raw40745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40745 raw40745Labels permutation434 hz
    mixedMoment B raw40745step0 raw40745step0Labels = mixedMoment B raw40745step1 raw40745step1Labels := by
      have hz : ∀ j, raw40745step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40745step1 = (fun i j => raw40745step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40745step1 raw40745step0; decide +kernel
      have hl : raw40745step1Labels = raw40745step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40745step0 raw40745step0Labels permutation80 hz
    mixedMoment B raw40745step1 raw40745step1Labels = mixedMoment B raw40745step2 raw40745step2Labels := by
      have ha : raw40745step2 = (fun i j => raw40745step1 (permutation30 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40745step2 raw40745step1; decide +kernel
      have hl : raw40745step2Labels = raw40745step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40745step1 raw40745step1Labels permutation30 permutation6
    _ = mixedMoment B node1264 node1264Labels := by rfl

def raw40746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw40746Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw40746step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw40746step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40746 raw40746Labels = mixedMoment B node2569 node2569Labels := by
  calc
    mixedMoment B raw40746 raw40746Labels = mixedMoment B raw40746step0 raw40746step0Labels := by
      have hz : ∀ j, raw40746 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40746step0 = (fun i j => raw40746 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40746step0 raw40746; decide +kernel
      have hl : raw40746step0Labels = raw40746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40746 raw40746Labels permutation346 hz
    mixedMoment B raw40746step0 raw40746step0Labels = mixedMoment B raw40746step1 raw40746step1Labels := by
      have ha : raw40746step1 = (fun i j => raw40746step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40746step1 raw40746step0; decide +kernel
      have hl : raw40746step1Labels = raw40746step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40746step0 raw40746step0Labels permutation96 permutation6
    _ = mixedMoment B node2569 node2569Labels := by rfl

def raw40747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw40747Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw40747step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40747step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![2, -3, 1]]
def raw40747step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40747step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![2, -3, 1]]
def raw40747step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40747step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-2, 1, 1]]
def raw40747step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40747step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]
def raw40747step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40747 raw40747Labels = mixedMoment B node3633 node3633Labels := by
  calc
    mixedMoment B raw40747 raw40747Labels = mixedMoment B raw40747step0 raw40747step0Labels := by
      have hz : ∀ j, raw40747 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40747step0 = (fun i j => raw40747 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40747step0 raw40747; decide +kernel
      have hl : raw40747step0Labels = raw40747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40747 raw40747Labels permutation520 hz
    mixedMoment B raw40747step0 raw40747step0Labels = mixedMoment B raw40747step1 raw40747step1Labels := by
      have hz : ∀ j, raw40747step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40747step1 = (fun i j => raw40747step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40747step1 raw40747step0; decide +kernel
      have hl : raw40747step1Labels = raw40747step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40747step0 raw40747step0Labels permutation104 hz
    mixedMoment B raw40747step1 raw40747step1Labels = mixedMoment B raw40747step2 raw40747step2Labels := by
      have hz : ∀ j, raw40747step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40747step2 = (fun i j => raw40747step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40747step2 raw40747step1; decide +kernel
      have hl : raw40747step2Labels = raw40747step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40747step1 raw40747step1Labels permutation20 hz
    mixedMoment B raw40747step2 raw40747step2Labels = mixedMoment B raw40747step3 raw40747step3Labels := by
      have ha : raw40747step3 = (fun i j => raw40747step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40747step3 raw40747step2; decide +kernel
      have hl : raw40747step3Labels = raw40747step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40747step2 raw40747step2Labels permutation7 permutation3
    mixedMoment B raw40747step3 raw40747step3Labels = mixedMoment B raw40747step4 raw40747step4Labels := by
      have ha : raw40747step4 = -raw40747step3 := by apply Matrix.ext; change ∀ i j, raw40747step4 i j = -(raw40747step3 i j); unfold raw40747step4 raw40747step3; decide +kernel
      have hl : raw40747step4Labels = raw40747step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3633 node3633Labels := by rfl

def raw40748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw40748Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw40748step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40748step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -1, 1], ![2, -2, 0]]
def raw40748step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40748step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1]]
def raw40748step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40748step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw40748step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40748 raw40748Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw40748 raw40748Labels = mixedMoment B raw40748step0 raw40748step0Labels := by
      have hz : ∀ j, raw40748 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40748step0 = (fun i j => raw40748 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40748step0 raw40748; decide +kernel
      have hl : raw40748step0Labels = raw40748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40748 raw40748Labels permutation434 hz
    mixedMoment B raw40748step0 raw40748step0Labels = mixedMoment B raw40748step1 raw40748step1Labels := by
      have hz : ∀ j, raw40748step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40748step1 = (fun i j => raw40748step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40748step1 raw40748step0; decide +kernel
      have hl : raw40748step1Labels = raw40748step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40748step0 raw40748step0Labels permutation80 hz
    mixedMoment B raw40748step1 raw40748step1Labels = mixedMoment B raw40748step2 raw40748step2Labels := by
      have ha : raw40748step2 = (fun i j => raw40748step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40748step2 raw40748step1; decide +kernel
      have hl : raw40748step2Labels = raw40748step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40748step1 raw40748step1Labels permutation31 permutation3
    mixedMoment B raw40748step2 raw40748step2Labels = mixedMoment B raw40748step3 raw40748step3Labels := by
      have ha : raw40748step3 = -raw40748step2 := by apply Matrix.ext; change ∀ i j, raw40748step3 i j = -(raw40748step2 i j); unfold raw40748step3 raw40748step2; decide +kernel
      have hl : raw40748step3Labels = raw40748step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3907 node3907Labels := by rfl

def raw40749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw40749Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw40749step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40749step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -2, 2], ![2, -1, -1]]
def raw40749step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40749step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw40749step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40749 raw40749Labels = mixedMoment B node3886 node3886Labels := by
  calc
    mixedMoment B raw40749 raw40749Labels = mixedMoment B raw40749step0 raw40749step0Labels := by
      have hz : ∀ j, raw40749 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40749step0 = (fun i j => raw40749 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40749step0 raw40749; decide +kernel
      have hl : raw40749step0Labels = raw40749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40749 raw40749Labels permutation434 hz
    mixedMoment B raw40749step0 raw40749step0Labels = mixedMoment B raw40749step1 raw40749step1Labels := by
      have hz : ∀ j, raw40749step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40749step1 = (fun i j => raw40749step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40749step1 raw40749step0; decide +kernel
      have hl : raw40749step1Labels = raw40749step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40749step0 raw40749step0Labels permutation80 hz
    mixedMoment B raw40749step1 raw40749step1Labels = mixedMoment B raw40749step2 raw40749step2Labels := by
      have ha : raw40749step2 = (fun i j => raw40749step1 (permutation18 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40749step2 raw40749step1; decide +kernel
      have hl : raw40749step2Labels = raw40749step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40749step1 raw40749step1Labels permutation18 permutation6
    _ = mixedMoment B node3886 node3886Labels := by rfl

def raw40750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw40750Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw40750step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40750step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -3, 3], ![2, 0, -2]]
def raw40750step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40750step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40750step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40750step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40750step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40750 raw40750Labels = mixedMoment B node2115 node2115Labels := by
  calc
    mixedMoment B raw40750 raw40750Labels = mixedMoment B raw40750step0 raw40750step0Labels := by
      have hz : ∀ j, raw40750 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40750step0 = (fun i j => raw40750 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40750step0 raw40750; decide +kernel
      have hl : raw40750step0Labels = raw40750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40750 raw40750Labels permutation434 hz
    mixedMoment B raw40750step0 raw40750step0Labels = mixedMoment B raw40750step1 raw40750step1Labels := by
      have hz : ∀ j, raw40750step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40750step1 = (fun i j => raw40750step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40750step1 raw40750step0; decide +kernel
      have hl : raw40750step1Labels = raw40750step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40750step0 raw40750step0Labels permutation80 hz
    mixedMoment B raw40750step1 raw40750step1Labels = mixedMoment B raw40750step2 raw40750step2Labels := by
      have ha : raw40750step2 = (fun i j => raw40750step1 (permutation21 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40750step2 raw40750step1; decide +kernel
      have hl : raw40750step2Labels = raw40750step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40750step1 raw40750step1Labels permutation21 permutation6
    mixedMoment B raw40750step2 raw40750step2Labels = mixedMoment B raw40750step3 raw40750step3Labels := by
      have ha : raw40750step3 = -raw40750step2 := by apply Matrix.ext; change ∀ i j, raw40750step3 i j = -(raw40750step2 i j); unfold raw40750step3 raw40750step2; decide +kernel
      have hl : raw40750step3Labels = raw40750step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2115 node2115Labels := by rfl

def raw40751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2]]
def raw40751Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -3, 2]]
def raw40751step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40751step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -3, 2]]
def raw40751step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40751step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw40751step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40751step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40751step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40751 raw40751Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw40751 raw40751Labels = mixedMoment B raw40751step0 raw40751step0Labels := by
      have hz : ∀ j, raw40751 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40751step0 = (fun i j => raw40751 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40751step0 raw40751; decide +kernel
      have hl : raw40751step0Labels = raw40751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40751 raw40751Labels permutation434 hz
    mixedMoment B raw40751step0 raw40751step0Labels = mixedMoment B raw40751step1 raw40751step1Labels := by
      have hz : ∀ j, raw40751step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40751step1 = (fun i j => raw40751step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40751step1 raw40751step0; decide +kernel
      have hl : raw40751step1Labels = raw40751step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40751step0 raw40751step0Labels permutation80 hz
    mixedMoment B raw40751step1 raw40751step1Labels = mixedMoment B raw40751step2 raw40751step2Labels := by
      have ha : raw40751step2 = (fun i j => raw40751step1 (permutation27 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40751step2 raw40751step1; decide +kernel
      have hl : raw40751step2Labels = raw40751step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40751step1 raw40751step1Labels permutation27 permutation6
    mixedMoment B raw40751step2 raw40751step2Labels = mixedMoment B raw40751step3 raw40751step3Labels := by
      have ha : raw40751step3 = -raw40751step2 := by apply Matrix.ext; change ∀ i j, raw40751step3 i j = -(raw40751step2 i j); unfold raw40751step3 raw40751step2; decide +kernel
      have hl : raw40751step3Labels = raw40751step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3582 node3582Labels := by rfl

def raw40752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40752Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40752step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40752step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -2, 1]]
def raw40752step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40752step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw40752step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40752 raw40752Labels = mixedMoment B node3913 node3913Labels := by
  calc
    mixedMoment B raw40752 raw40752Labels = mixedMoment B raw40752step0 raw40752step0Labels := by
      have hz : ∀ j, raw40752 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40752step0 = (fun i j => raw40752 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40752step0 raw40752; decide +kernel
      have hl : raw40752step0Labels = raw40752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40752 raw40752Labels permutation434 hz
    mixedMoment B raw40752step0 raw40752step0Labels = mixedMoment B raw40752step1 raw40752step1Labels := by
      have hz : ∀ j, raw40752step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40752step1 = (fun i j => raw40752step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40752step1 raw40752step0; decide +kernel
      have hl : raw40752step1Labels = raw40752step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40752step0 raw40752step0Labels permutation80 hz
    mixedMoment B raw40752step1 raw40752step1Labels = mixedMoment B raw40752step2 raw40752step2Labels := by
      have ha : raw40752step2 = (fun i j => raw40752step1 (permutation16 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40752step2 raw40752step1; decide +kernel
      have hl : raw40752step2Labels = raw40752step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40752step1 raw40752step1Labels permutation16 permutation6
    _ = mixedMoment B node3913 node3913Labels := by rfl

def raw40753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw40753Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw40753step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40753step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40753step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40753 raw40753Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw40753 raw40753Labels = mixedMoment B raw40753step0 raw40753step0Labels := by
      have hz : ∀ j, raw40753 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40753step0 = (fun i j => raw40753 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40753step0 raw40753; decide +kernel
      have hl : raw40753step0Labels = raw40753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40753 raw40753Labels permutation346 hz
    mixedMoment B raw40753step0 raw40753step0Labels = mixedMoment B raw40753step1 raw40753step1Labels := by
      have ha : raw40753step1 = (fun i j => raw40753step0 (permutation74 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40753step1 raw40753step0; decide +kernel
      have hl : raw40753step1Labels = raw40753step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40753step0 raw40753step0Labels permutation74 permutation6
    _ = mixedMoment B node3885 node3885Labels := by rfl

def raw40754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw40754Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw40754step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw40754step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40754 raw40754Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw40754 raw40754Labels = mixedMoment B raw40754step0 raw40754step0Labels := by
      have hz : ∀ j, raw40754 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40754step0 = (fun i j => raw40754 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40754step0 raw40754; decide +kernel
      have hl : raw40754step0Labels = raw40754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40754 raw40754Labels permutation346 hz
    mixedMoment B raw40754step0 raw40754step0Labels = mixedMoment B raw40754step1 raw40754step1Labels := by
      have ha : raw40754step1 = (fun i j => raw40754step0 (permutation74 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40754step1 raw40754step0; decide +kernel
      have hl : raw40754step1Labels = raw40754step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40754step0 raw40754step0Labels permutation74 permutation6
    _ = mixedMoment B node3732 node3732Labels := by rfl

def raw40755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw40755Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw40755step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw40755step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40755 raw40755Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw40755 raw40755Labels = mixedMoment B raw40755step0 raw40755step0Labels := by
      have hz : ∀ j, raw40755 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40755step0 = (fun i j => raw40755 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40755step0 raw40755; decide +kernel
      have hl : raw40755step0Labels = raw40755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40755 raw40755Labels permutation346 hz
    mixedMoment B raw40755step0 raw40755step0Labels = mixedMoment B raw40755step1 raw40755step1Labels := by
      have ha : raw40755step1 = (fun i j => raw40755step0 (permutation68 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40755step1 raw40755step0; decide +kernel
      have hl : raw40755step1Labels = raw40755step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40755step0 raw40755step0Labels permutation68 permutation6
    _ = mixedMoment B node3857 node3857Labels := by rfl

def raw40756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw40756Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw40756step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw40756step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40756 raw40756Labels = mixedMoment B node3910 node3910Labels := by
  calc
    mixedMoment B raw40756 raw40756Labels = mixedMoment B raw40756step0 raw40756step0Labels := by
      have hz : ∀ j, raw40756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40756step0 = (fun i j => raw40756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40756step0 raw40756; decide +kernel
      have hl : raw40756step0Labels = raw40756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40756 raw40756Labels permutation346 hz
    mixedMoment B raw40756step0 raw40756step0Labels = mixedMoment B raw40756step1 raw40756step1Labels := by
      have ha : raw40756step1 = (fun i j => raw40756step0 (permutation72 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40756step1 raw40756step0; decide +kernel
      have hl : raw40756step1Labels = raw40756step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40756step0 raw40756step0Labels permutation72 permutation6
    _ = mixedMoment B node3910 node3910Labels := by rfl

def raw40757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40757Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40757step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw40757step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40757 raw40757Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw40757 raw40757Labels = mixedMoment B raw40757step0 raw40757step0Labels := by
      have hz : ∀ j, raw40757 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40757step0 = (fun i j => raw40757 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40757step0 raw40757; decide +kernel
      have hl : raw40757step0Labels = raw40757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40757 raw40757Labels permutation346 hz
    mixedMoment B raw40757step0 raw40757step0Labels = mixedMoment B raw40757step1 raw40757step1Labels := by
      have ha : raw40757step1 = (fun i j => raw40757step0 (permutation72 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40757step1 raw40757step0; decide +kernel
      have hl : raw40757step1Labels = raw40757step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40757step0 raw40757step0Labels permutation72 permutation6
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw40758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, 0, 0], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]
def raw40758Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]
def raw40758step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw40758step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40758step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40758step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40758 raw40758Labels = mixedMoment B node2106 node2106Labels := by
  calc
    mixedMoment B raw40758 raw40758Labels = mixedMoment B raw40758step0 raw40758step0Labels := by
      have hz : ∀ j, raw40758 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40758step0 = (fun i j => raw40758 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40758step0 raw40758; decide +kernel
      have hl : raw40758step0Labels = raw40758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40758 raw40758Labels permutation346 hz
    mixedMoment B raw40758step0 raw40758step0Labels = mixedMoment B raw40758step1 raw40758step1Labels := by
      have ha : raw40758step1 = (fun i j => raw40758step0 (permutation83 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40758step1 raw40758step0; decide +kernel
      have hl : raw40758step1Labels = raw40758step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40758step0 raw40758step0Labels permutation83 permutation6
    mixedMoment B raw40758step1 raw40758step1Labels = mixedMoment B raw40758step2 raw40758step2Labels := by
      have ha : raw40758step2 = -raw40758step1 := by apply Matrix.ext; change ∀ i j, raw40758step2 i j = -(raw40758step1 i j); unfold raw40758step2 raw40758step1; decide +kernel
      have hl : raw40758step2Labels = raw40758step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2106 node2106Labels := by rfl

def raw40759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw40759Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40759step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40759step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40759 raw40759Labels = mixedMoment B node3731 node3731Labels := by
  calc
    mixedMoment B raw40759 raw40759Labels = mixedMoment B raw40759step0 raw40759step0Labels := by
      have ha : raw40759step0 = (fun i j => raw40759 (permutation333 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40759step0 raw40759; decide +kernel
      have hl : raw40759step0Labels = raw40759Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40759 raw40759Labels permutation333 permutation6
    _ = mixedMoment B node3731 node3731Labels := by rfl

def raw40760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw40760Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40760step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40760step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40760 raw40760Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw40760 raw40760Labels = mixedMoment B raw40760step0 raw40760step0Labels := by
      have ha : raw40760step0 = (fun i j => raw40760 (permutation329 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40760step0 raw40760; decide +kernel
      have hl : raw40760step0Labels = raw40760Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40760 raw40760Labels permutation329 permutation6
    _ = mixedMoment B node3849 node3849Labels := by rfl

def raw40761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw40761Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40761step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw40761step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40761step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40761step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40761 raw40761Labels = mixedMoment B node3786 node3786Labels := by
  calc
    mixedMoment B raw40761 raw40761Labels = mixedMoment B raw40761step0 raw40761step0Labels := by
      have ha : raw40761step0 = (fun i j => raw40761 (permutation468 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40761step0 raw40761; decide +kernel
      have hl : raw40761step0Labels = raw40761Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40761 raw40761Labels permutation468 permutation6
    mixedMoment B raw40761step0 raw40761step0Labels = mixedMoment B raw40761step1 raw40761step1Labels := by
      have ha : raw40761step1 = -raw40761step0 := by apply Matrix.ext; change ∀ i j, raw40761step1 i j = -(raw40761step0 i j); unfold raw40761step1 raw40761step0; decide +kernel
      have hl : raw40761step1Labels = raw40761step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3786 node3786Labels := by rfl

def raw40762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw40762Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1]]
def raw40762step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40762step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw40762step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40762step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw40762step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40762step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw40762step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40762 raw40762Labels = mixedMoment B node3623 node3623Labels := by
  calc
    mixedMoment B raw40762 raw40762Labels = mixedMoment B raw40762step0 raw40762step0Labels := by
      have hz : ∀ j, raw40762 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40762step0 = (fun i j => raw40762 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40762step0 raw40762; decide +kernel
      have hl : raw40762step0Labels = raw40762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40762 raw40762Labels permutation520 hz
    mixedMoment B raw40762step0 raw40762step0Labels = mixedMoment B raw40762step1 raw40762step1Labels := by
      have hz : ∀ j, raw40762step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40762step1 = (fun i j => raw40762step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40762step1 raw40762step0; decide +kernel
      have hl : raw40762step1Labels = raw40762step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40762step0 raw40762step0Labels permutation104 hz
    mixedMoment B raw40762step1 raw40762step1Labels = mixedMoment B raw40762step2 raw40762step2Labels := by
      have ha : raw40762step2 = (fun i j => raw40762step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40762step2 raw40762step1; decide +kernel
      have hl : raw40762step2Labels = raw40762step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40762step1 raw40762step1Labels permutation29 permutation3
    mixedMoment B raw40762step2 raw40762step2Labels = mixedMoment B raw40762step3 raw40762step3Labels := by
      have ha : raw40762step3 = -raw40762step2 := by apply Matrix.ext; change ∀ i j, raw40762step3 i j = -(raw40762step2 i j); unfold raw40762step3 raw40762step2; decide +kernel
      have hl : raw40762step3Labels = raw40762step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3623 node3623Labels := by rfl

def raw40763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw40763Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1]]
def raw40763step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw40763step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40763step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40763step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40763 raw40763Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw40763 raw40763Labels = mixedMoment B raw40763step0 raw40763step0Labels := by
      have hz : ∀ j, raw40763 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40763step0 = (fun i j => raw40763 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40763step0 raw40763; decide +kernel
      have hl : raw40763step0Labels = raw40763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40763 raw40763Labels permutation434 hz
    mixedMoment B raw40763step0 raw40763step0Labels = mixedMoment B raw40763step1 raw40763step1Labels := by
      have ha : raw40763step1 = (fun i j => raw40763step0 (permutation108 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40763step1 raw40763step0; decide +kernel
      have hl : raw40763step1Labels = raw40763step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40763step0 raw40763step0Labels permutation108 permutation6
    mixedMoment B raw40763step1 raw40763step1Labels = mixedMoment B raw40763step2 raw40763step2Labels := by
      have ha : raw40763step2 = -raw40763step1 := by apply Matrix.ext; change ∀ i j, raw40763step2 i j = -(raw40763step1 i j); unfold raw40763step2 raw40763step1; decide +kernel
      have hl : raw40763step2Labels = raw40763step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3885 node3885Labels := by rfl

def raw40764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw40764Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, -3, 3], ![2, 0, -2]]
def raw40764step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40764step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40764step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40764step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40764 raw40764Labels = mixedMoment B node2110 node2110Labels := by
  calc
    mixedMoment B raw40764 raw40764Labels = mixedMoment B raw40764step0 raw40764step0Labels := by
      have hz : ∀ j, raw40764 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40764step0 = (fun i j => raw40764 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40764step0 raw40764; decide +kernel
      have hl : raw40764step0Labels = raw40764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40764 raw40764Labels permutation434 hz
    mixedMoment B raw40764step0 raw40764step0Labels = mixedMoment B raw40764step1 raw40764step1Labels := by
      have ha : raw40764step1 = (fun i j => raw40764step0 (permutation104 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40764step1 raw40764step0; decide +kernel
      have hl : raw40764step1Labels = raw40764step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40764step0 raw40764step0Labels permutation104 permutation6
    mixedMoment B raw40764step1 raw40764step1Labels = mixedMoment B raw40764step2 raw40764step2Labels := by
      have ha : raw40764step2 = -raw40764step1 := by apply Matrix.ext; change ∀ i j, raw40764step2 i j = -(raw40764step1 i j); unfold raw40764step2 raw40764step1; decide +kernel
      have hl : raw40764step2Labels = raw40764step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2110 node2110Labels := by rfl

def raw40765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40765Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40765step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw40765step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40765 raw40765Labels = mixedMoment B node4010 node4010Labels := by
  calc
    mixedMoment B raw40765 raw40765Labels = mixedMoment B raw40765step0 raw40765step0Labels := by
      have hz : ∀ j, raw40765 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40765step0 = (fun i j => raw40765 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40765step0 raw40765; decide +kernel
      have hl : raw40765step0Labels = raw40765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40765 raw40765Labels permutation434 hz
    mixedMoment B raw40765step0 raw40765step0Labels = mixedMoment B raw40765step1 raw40765step1Labels := by
      have ha : raw40765step1 = (fun i j => raw40765step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40765step1 raw40765step0; decide +kernel
      have hl : raw40765step1Labels = raw40765step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40765step0 raw40765step0Labels permutation32 permutation3
    _ = mixedMoment B node4010 node4010Labels := by rfl

def raw40766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw40766Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40766step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40766step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40766step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40766step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40766 raw40766Labels = mixedMoment B node3789 node3789Labels := by
  calc
    mixedMoment B raw40766 raw40766Labels = mixedMoment B raw40766step0 raw40766step0Labels := by
      have ha : raw40766step0 = (fun i j => raw40766 (permutation553 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40766step0 raw40766; decide +kernel
      have hl : raw40766step0Labels = raw40766Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40766 raw40766Labels permutation553 permutation6
    mixedMoment B raw40766step0 raw40766step0Labels = mixedMoment B raw40766step1 raw40766step1Labels := by
      have ha : raw40766step1 = -raw40766step0 := by apply Matrix.ext; change ∀ i j, raw40766step1 i j = -(raw40766step0 i j); unfold raw40766step1 raw40766step0; decide +kernel
      have hl : raw40766step1Labels = raw40766step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3789 node3789Labels := by rfl

def raw40767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40767Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40767step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw40767step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40767step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40767step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40767 raw40767Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw40767 raw40767Labels = mixedMoment B raw40767step0 raw40767step0Labels := by
      have ha : raw40767step0 = (fun i j => raw40767 (permutation449 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40767step0 raw40767; decide +kernel
      have hl : raw40767step0Labels = raw40767Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40767 raw40767Labels permutation449 permutation6
    mixedMoment B raw40767step0 raw40767step0Labels = mixedMoment B raw40767step1 raw40767step1Labels := by
      have ha : raw40767step1 = -raw40767step0 := by apply Matrix.ext; change ∀ i j, raw40767step1 i j = -(raw40767step0 i j); unfold raw40767step1 raw40767step0; decide +kernel
      have hl : raw40767step1Labels = raw40767step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3875 node3875Labels := by rfl

def raw40768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]
def raw40768Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw40768step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40768step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw40768step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40768 raw40768Labels = mixedMoment B node2105 node2105Labels := by
  calc
    mixedMoment B raw40768 raw40768Labels = mixedMoment B raw40768step0 raw40768step0Labels := by
      have ha : raw40768step0 = (fun i j => raw40768 (permutation446 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40768step0 raw40768; decide +kernel
      have hl : raw40768step0Labels = raw40768Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40768 raw40768Labels permutation446 permutation6
    mixedMoment B raw40768step0 raw40768step0Labels = mixedMoment B raw40768step1 raw40768step1Labels := by
      have ha : raw40768step1 = -raw40768step0 := by apply Matrix.ext; change ∀ i j, raw40768step1 i j = -(raw40768step0 i j); unfold raw40768step1 raw40768step0; decide +kernel
      have hl : raw40768step1Labels = raw40768step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2105 node2105Labels := by rfl

def raw40769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw40769Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw40769step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40769step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -3, 3], ![2, 1, -3]]
def raw40769step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40769step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw40769step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40769step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw40769step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40769 raw40769Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw40769 raw40769Labels = mixedMoment B raw40769step0 raw40769step0Labels := by
      have hz : ∀ j, raw40769 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40769step0 = (fun i j => raw40769 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40769step0 raw40769; decide +kernel
      have hl : raw40769step0Labels = raw40769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40769 raw40769Labels permutation434 hz
    mixedMoment B raw40769step0 raw40769step0Labels = mixedMoment B raw40769step1 raw40769step1Labels := by
      have hz : ∀ j, raw40769step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40769step1 = (fun i j => raw40769step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40769step1 raw40769step0; decide +kernel
      have hl : raw40769step1Labels = raw40769step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40769step0 raw40769step0Labels permutation80 hz
    mixedMoment B raw40769step1 raw40769step1Labels = mixedMoment B raw40769step2 raw40769step2Labels := by
      have ha : raw40769step2 = (fun i j => raw40769step1 (permutation20 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40769step2 raw40769step1; decide +kernel
      have hl : raw40769step2Labels = raw40769step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40769step1 raw40769step1Labels permutation20 permutation6
    mixedMoment B raw40769step2 raw40769step2Labels = mixedMoment B raw40769step3 raw40769step3Labels := by
      have ha : raw40769step3 = -raw40769step2 := by apply Matrix.ext; change ∀ i j, raw40769step3 i j = -(raw40769step2 i j); unfold raw40769step3 raw40769step2; decide +kernel
      have hl : raw40769step3Labels = raw40769step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2112 node2112Labels := by rfl

def raw40770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw40770Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 1, -3]]
def raw40770step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw40770step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40770 raw40770Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw40770 raw40770Labels = mixedMoment B raw40770step0 raw40770step0Labels := by
      have hz : ∀ j, raw40770 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40770step0 = (fun i j => raw40770 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40770step0 raw40770; decide +kernel
      have hl : raw40770step0Labels = raw40770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40770 raw40770Labels permutation346 hz
    mixedMoment B raw40770step0 raw40770step0Labels = mixedMoment B raw40770step1 raw40770step1Labels := by
      have ha : raw40770step1 = (fun i j => raw40770step0 (permutation134 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40770step1 raw40770step0; decide +kernel
      have hl : raw40770step1Labels = raw40770step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40770step0 raw40770step0Labels permutation134 permutation6
    _ = mixedMoment B node2954 node2954Labels := by rfl

def raw40771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw40771Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw40771step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40771step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw40771step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40771step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40771step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40771 raw40771Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw40771 raw40771Labels = mixedMoment B raw40771step0 raw40771step0Labels := by
      have hz : ∀ j, raw40771 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40771step0 = (fun i j => raw40771 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40771step0 raw40771; decide +kernel
      have hl : raw40771step0Labels = raw40771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40771 raw40771Labels permutation346 hz
    mixedMoment B raw40771step0 raw40771step0Labels = mixedMoment B raw40771step1 raw40771step1Labels := by
      have ha : raw40771step1 = (fun i j => raw40771step0 (permutation84 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40771step1 raw40771step0; decide +kernel
      have hl : raw40771step1Labels = raw40771step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40771step0 raw40771step0Labels permutation84 permutation6
    mixedMoment B raw40771step1 raw40771step1Labels = mixedMoment B raw40771step2 raw40771step2Labels := by
      have ha : raw40771step2 = -raw40771step1 := by apply Matrix.ext; change ∀ i j, raw40771step2 i j = -(raw40771step1 i j); unfold raw40771step2 raw40771step1; decide +kernel
      have hl : raw40771step2Labels = raw40771step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw40772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw40772Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40772step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw40772step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40772step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40772step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40772 raw40772Labels = mixedMoment B node3787 node3787Labels := by
  calc
    mixedMoment B raw40772 raw40772Labels = mixedMoment B raw40772step0 raw40772step0Labels := by
      have ha : raw40772step0 = (fun i j => raw40772 (permutation469 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40772step0 raw40772; decide +kernel
      have hl : raw40772step0Labels = raw40772Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40772 raw40772Labels permutation469 permutation6
    mixedMoment B raw40772step0 raw40772step0Labels = mixedMoment B raw40772step1 raw40772step1Labels := by
      have ha : raw40772step1 = -raw40772step0 := by apply Matrix.ext; change ∀ i j, raw40772step1 i j = -(raw40772step0 i j); unfold raw40772step1 raw40772step0; decide +kernel
      have hl : raw40772step1Labels = raw40772step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3787 node3787Labels := by rfl

def raw40773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 2, -4]]
def raw40773Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 2, -4]]
def raw40773step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40773step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -3, 3], ![2, 2, -4]]
def raw40773step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40773step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![2, 2, -4]]
def raw40773step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40773step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw40773step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40773 raw40773Labels = mixedMoment B node1297 node1297Labels := by
  calc
    mixedMoment B raw40773 raw40773Labels = mixedMoment B raw40773step0 raw40773step0Labels := by
      have hz : ∀ j, raw40773 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40773step0 = (fun i j => raw40773 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40773step0 raw40773; decide +kernel
      have hl : raw40773step0Labels = raw40773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40773 raw40773Labels permutation434 hz
    mixedMoment B raw40773step0 raw40773step0Labels = mixedMoment B raw40773step1 raw40773step1Labels := by
      have hz : ∀ j, raw40773step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40773step1 = (fun i j => raw40773step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40773step1 raw40773step0; decide +kernel
      have hl : raw40773step1Labels = raw40773step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40773step0 raw40773step0Labels permutation80 hz
    mixedMoment B raw40773step1 raw40773step1Labels = mixedMoment B raw40773step2 raw40773step2Labels := by
      have hz : ∀ j, raw40773step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40773step2 = (fun i j => raw40773step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40773step2 raw40773step1; decide +kernel
      have hl : raw40773step2Labels = raw40773step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40773step1 raw40773step1Labels permutation14 hz
    mixedMoment B raw40773step2 raw40773step2Labels = mixedMoment B raw40773step3 raw40773step3Labels := by
      have ha : raw40773step3 = (fun i j => raw40773step2 (permutation6 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40773step3 raw40773step2; decide +kernel
      have hl : raw40773step3Labels = raw40773step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40773step2 raw40773step2Labels permutation6 permutation6
    _ = mixedMoment B node1297 node1297Labels := by rfl

def raw40774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -3, 2]]
def raw40774Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -3, 2]]
def raw40774step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40774step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, 2, -3], ![1, -3, 2]]
def raw40774step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40774step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, 2, -3], ![1, -3, 2]]
def raw40774step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40774step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw40774step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40774 raw40774Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw40774 raw40774Labels = mixedMoment B raw40774step0 raw40774step0Labels := by
      have hz : ∀ j, raw40774 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40774step0 = (fun i j => raw40774 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40774step0 raw40774; decide +kernel
      have hl : raw40774step0Labels = raw40774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40774 raw40774Labels permutation434 hz
    mixedMoment B raw40774step0 raw40774step0Labels = mixedMoment B raw40774step1 raw40774step1Labels := by
      have hz : ∀ j, raw40774step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40774step1 = (fun i j => raw40774step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40774step1 raw40774step0; decide +kernel
      have hl : raw40774step1Labels = raw40774step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40774step0 raw40774step0Labels permutation80 hz
    mixedMoment B raw40774step1 raw40774step1Labels = mixedMoment B raw40774step2 raw40774step2Labels := by
      have hz : ∀ j, raw40774step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40774step2 = (fun i j => raw40774step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40774step2 raw40774step1; decide +kernel
      have hl : raw40774step2Labels = raw40774step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40774step1 raw40774step1Labels permutation14 hz
    mixedMoment B raw40774step2 raw40774step2Labels = mixedMoment B raw40774step3 raw40774step3Labels := by
      have ha : raw40774step3 = (fun i j => raw40774step2 (permutation4 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40774step3 raw40774step2; decide +kernel
      have hl : raw40774step3Labels = raw40774step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40774step2 raw40774step2Labels permutation4 permutation6
    _ = mixedMoment B node2783 node2783Labels := by rfl

def raw40775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 2, -4]]
def raw40775Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 2, -4]]
def raw40775step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40775step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -2, 2], ![2, 2, -4]]
def raw40775step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40775step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw40775step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40775 raw40775Labels = mixedMoment B node1294 node1294Labels := by
  calc
    mixedMoment B raw40775 raw40775Labels = mixedMoment B raw40775step0 raw40775step0Labels := by
      have hz : ∀ j, raw40775 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40775step0 = (fun i j => raw40775 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40775step0 raw40775; decide +kernel
      have hl : raw40775step0Labels = raw40775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40775 raw40775Labels permutation346 hz
    mixedMoment B raw40775step0 raw40775step0Labels = mixedMoment B raw40775step1 raw40775step1Labels := by
      have hz : ∀ j, raw40775step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40775step1 = (fun i j => raw40775step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40775step1 raw40775step0; decide +kernel
      have hl : raw40775step1Labels = raw40775step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40775step0 raw40775step0Labels permutation56 hz
    mixedMoment B raw40775step1 raw40775step1Labels = mixedMoment B raw40775step2 raw40775step2Labels := by
      have ha : raw40775step2 = (fun i j => raw40775step1 (permutation26 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40775step2 raw40775step1; decide +kernel
      have hl : raw40775step2Labels = raw40775step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40775step1 raw40775step1Labels permutation26 permutation6
    _ = mixedMoment B node1294 node1294Labels := by rfl

def raw40776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw40776Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw40776step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40776step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 2, -3], ![1, -2, 1]]
def raw40776step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40776step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw40776step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40776 raw40776Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw40776 raw40776Labels = mixedMoment B raw40776step0 raw40776step0Labels := by
      have hz : ∀ j, raw40776 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40776step0 = (fun i j => raw40776 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40776step0 raw40776; decide +kernel
      have hl : raw40776step0Labels = raw40776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40776 raw40776Labels permutation346 hz
    mixedMoment B raw40776step0 raw40776step0Labels = mixedMoment B raw40776step1 raw40776step1Labels := by
      have hz : ∀ j, raw40776step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40776step1 = (fun i j => raw40776step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40776step1 raw40776step0; decide +kernel
      have hl : raw40776step1Labels = raw40776step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40776step0 raw40776step0Labels permutation56 hz
    mixedMoment B raw40776step1 raw40776step1Labels = mixedMoment B raw40776step2 raw40776step2Labels := by
      have ha : raw40776step2 = (fun i j => raw40776step1 (permutation20 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40776step2 raw40776step1; decide +kernel
      have hl : raw40776step2Labels = raw40776step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40776step1 raw40776step1Labels permutation20 permutation6
    _ = mixedMoment B node2782 node2782Labels := by rfl

def raw40777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw40777Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw40777step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40777step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 2, -3], ![1, -1, 0]]
def raw40777step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40777step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw40777step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40777 raw40777Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw40777 raw40777Labels = mixedMoment B raw40777step0 raw40777step0Labels := by
      have hz : ∀ j, raw40777 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40777step0 = (fun i j => raw40777 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40777step0 raw40777; decide +kernel
      have hl : raw40777step0Labels = raw40777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40777 raw40777Labels permutation346 hz
    mixedMoment B raw40777step0 raw40777step0Labels = mixedMoment B raw40777step1 raw40777step1Labels := by
      have hz : ∀ j, raw40777step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40777step1 = (fun i j => raw40777step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40777step1 raw40777step0; decide +kernel
      have hl : raw40777step1Labels = raw40777step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40777step0 raw40777step0Labels permutation56 hz
    mixedMoment B raw40777step1 raw40777step1Labels = mixedMoment B raw40777step2 raw40777step2Labels := by
      have ha : raw40777step2 = (fun i j => raw40777step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40777step2 raw40777step1; decide +kernel
      have hl : raw40777step2Labels = raw40777step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40777step1 raw40777step1Labels permutation24 permutation6
    _ = mixedMoment B node2765 node2765Labels := by rfl

def raw40778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![1, 2, -3], ![1, 0, -1]]
def raw40778Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -3, 3], ![1, 2, -3], ![1, 0, -1]]
def raw40778step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40778step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 2, -3], ![1, 0, -1]]
def raw40778step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40778step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw40778step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40778step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw40778step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40778 raw40778Labels = mixedMoment B node2109 node2109Labels := by
  calc
    mixedMoment B raw40778 raw40778Labels = mixedMoment B raw40778step0 raw40778step0Labels := by
      have hz : ∀ j, raw40778 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40778step0 = (fun i j => raw40778 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40778step0 raw40778; decide +kernel
      have hl : raw40778step0Labels = raw40778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40778 raw40778Labels permutation346 hz
    mixedMoment B raw40778step0 raw40778step0Labels = mixedMoment B raw40778step1 raw40778step1Labels := by
      have hz : ∀ j, raw40778step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40778step1 = (fun i j => raw40778step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40778step1 raw40778step0; decide +kernel
      have hl : raw40778step1Labels = raw40778step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40778step0 raw40778step0Labels permutation56 hz
    mixedMoment B raw40778step1 raw40778step1Labels = mixedMoment B raw40778step2 raw40778step2Labels := by
      have ha : raw40778step2 = (fun i j => raw40778step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40778step2 raw40778step1; decide +kernel
      have hl : raw40778step2Labels = raw40778step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40778step1 raw40778step1Labels permutation15 permutation6
    mixedMoment B raw40778step2 raw40778step2Labels = mixedMoment B raw40778step3 raw40778step3Labels := by
      have ha : raw40778step3 = -raw40778step2 := by apply Matrix.ext; change ∀ i j, raw40778step3 i j = -(raw40778step2 i j); unfold raw40778step3 raw40778step2; decide +kernel
      have hl : raw40778step3Labels = raw40778step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2109 node2109Labels := by rfl

def raw40779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]
def raw40779Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]
def raw40779step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40779step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -3, 3], ![1, 1, -2], ![1, 1, -2]]
def raw40779step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40779step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw40779step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40779step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw40779step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40779 raw40779Labels = mixedMoment B node2116 node2116Labels := by
  calc
    mixedMoment B raw40779 raw40779Labels = mixedMoment B raw40779step0 raw40779step0Labels := by
      have hz : ∀ j, raw40779 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40779step0 = (fun i j => raw40779 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40779step0 raw40779; decide +kernel
      have hl : raw40779step0Labels = raw40779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40779 raw40779Labels permutation346 hz
    mixedMoment B raw40779step0 raw40779step0Labels = mixedMoment B raw40779step1 raw40779step1Labels := by
      have hz : ∀ j, raw40779step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40779step1 = (fun i j => raw40779step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40779step1 raw40779step0; decide +kernel
      have hl : raw40779step1Labels = raw40779step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40779step0 raw40779step0Labels permutation56 hz
    mixedMoment B raw40779step1 raw40779step1Labels = mixedMoment B raw40779step2 raw40779step2Labels := by
      have ha : raw40779step2 = (fun i j => raw40779step1 (permutation14 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40779step2 raw40779step1; decide +kernel
      have hl : raw40779step2Labels = raw40779step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40779step1 raw40779step1Labels permutation14 permutation6
    mixedMoment B raw40779step2 raw40779step2Labels = mixedMoment B raw40779step3 raw40779step3Labels := by
      have ha : raw40779step3 = -raw40779step2 := by apply Matrix.ext; change ∀ i j, raw40779step3 i j = -(raw40779step2 i j); unfold raw40779step3 raw40779step2; decide +kernel
      have hl : raw40779step3Labels = raw40779step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2116 node2116Labels := by rfl

def raw40780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0]]
def raw40780Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0]]
def raw40780step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw40780step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40780 raw40780Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw40780 raw40780Labels = mixedMoment B raw40780step0 raw40780step0Labels := by
      have hz : ∀ j, raw40780 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40780step0 = (fun i j => raw40780 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40780step0 raw40780; decide +kernel
      have hl : raw40780step0Labels = raw40780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40780 raw40780Labels permutation265 hz
    mixedMoment B raw40780step0 raw40780step0Labels = mixedMoment B raw40780step1 raw40780step1Labels := by
      have ha : raw40780step1 = (fun i j => raw40780step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40780step1 raw40780step0; decide +kernel
      have hl : raw40780step1Labels = raw40780step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40780step0 raw40780step0Labels permutation122 permutation6
    _ = mixedMoment B node2764 node2764Labels := by rfl

def raw40781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw40781Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw40781step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40781step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw40781step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40781 raw40781Labels = mixedMoment B node2590 node2590Labels := by
  calc
    mixedMoment B raw40781 raw40781Labels = mixedMoment B raw40781step0 raw40781step0Labels := by
      have hz : ∀ j, raw40781 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40781step0 = (fun i j => raw40781 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40781step0 raw40781; decide +kernel
      have hl : raw40781step0Labels = raw40781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40781 raw40781Labels permutation265 hz
    mixedMoment B raw40781step0 raw40781step0Labels = mixedMoment B raw40781step1 raw40781step1Labels := by
      have ha : raw40781step1 = (fun i j => raw40781step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40781step1 raw40781step0; decide +kernel
      have hl : raw40781step1Labels = raw40781step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40781step0 raw40781step0Labels permutation122 permutation6
    _ = mixedMoment B node2590 node2590Labels := by rfl

def raw40782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw40782Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40782step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw40782step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40782 raw40782Labels = mixedMoment B node2589 node2589Labels := by
  calc
    mixedMoment B raw40782 raw40782Labels = mixedMoment B raw40782step0 raw40782step0Labels := by
      have ha : raw40782step0 = (fun i j => raw40782 (permutation569 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40782step0 raw40782; decide +kernel
      have hl : raw40782step0Labels = raw40782Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40782 raw40782Labels permutation569 permutation6
    _ = mixedMoment B node2589 node2589Labels := by rfl

def raw40783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40783Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40783step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40783step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![3, -3, 0]]
def raw40783step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40783step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![3, -3, 0]]
def raw40783step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40783step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -2, 3], ![-2, 2, 0]]
def raw40783step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40783step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw40783step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40783 raw40783Labels = mixedMoment B node2294 node2294Labels := by
  calc
    mixedMoment B raw40783 raw40783Labels = mixedMoment B raw40783step0 raw40783step0Labels := by
      have hz : ∀ j, raw40783 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40783step0 = (fun i j => raw40783 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40783step0 raw40783; decide +kernel
      have hl : raw40783step0Labels = raw40783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40783 raw40783Labels permutation520 hz
    mixedMoment B raw40783step0 raw40783step0Labels = mixedMoment B raw40783step1 raw40783step1Labels := by
      have hz : ∀ j, raw40783step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40783step1 = (fun i j => raw40783step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40783step1 raw40783step0; decide +kernel
      have hl : raw40783step1Labels = raw40783step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40783step0 raw40783step0Labels permutation104 hz
    mixedMoment B raw40783step1 raw40783step1Labels = mixedMoment B raw40783step2 raw40783step2Labels := by
      have hz : ∀ j, raw40783step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40783step2 = (fun i j => raw40783step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40783step2 raw40783step1; decide +kernel
      have hl : raw40783step2Labels = raw40783step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40783step1 raw40783step1Labels permutation20 hz
    mixedMoment B raw40783step2 raw40783step2Labels = mixedMoment B raw40783step3 raw40783step3Labels := by
      have ha : raw40783step3 = (fun i j => raw40783step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40783step3 raw40783step2; decide +kernel
      have hl : raw40783step3Labels = raw40783step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40783step2 raw40783step2Labels permutation7 permutation3
    mixedMoment B raw40783step3 raw40783step3Labels = mixedMoment B raw40783step4 raw40783step4Labels := by
      have ha : raw40783step4 = -raw40783step3 := by apply Matrix.ext; change ∀ i j, raw40783step4 i j = -(raw40783step3 i j); unfold raw40783step4 raw40783step3; decide +kernel
      have hl : raw40783step4Labels = raw40783step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2294 node2294Labels := by rfl

def raw40784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40784Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40784step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40784step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![3, -2, -1]]
def raw40784step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40784step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -2, 3], ![-2, 2, 0]]
def raw40784step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40784step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw40784step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40784 raw40784Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw40784 raw40784Labels = mixedMoment B raw40784step0 raw40784step0Labels := by
      have hz : ∀ j, raw40784 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40784step0 = (fun i j => raw40784 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40784step0 raw40784; decide +kernel
      have hl : raw40784step0Labels = raw40784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40784 raw40784Labels permutation434 hz
    mixedMoment B raw40784step0 raw40784step0Labels = mixedMoment B raw40784step1 raw40784step1Labels := by
      have hz : ∀ j, raw40784step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40784step1 = (fun i j => raw40784step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40784step1 raw40784step0; decide +kernel
      have hl : raw40784step1Labels = raw40784step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40784step0 raw40784step0Labels permutation80 hz
    mixedMoment B raw40784step1 raw40784step1Labels = mixedMoment B raw40784step2 raw40784step2Labels := by
      have ha : raw40784step2 = (fun i j => raw40784step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40784step2 raw40784step1; decide +kernel
      have hl : raw40784step2Labels = raw40784step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40784step1 raw40784step1Labels permutation31 permutation3
    mixedMoment B raw40784step2 raw40784step2Labels = mixedMoment B raw40784step3 raw40784step3Labels := by
      have ha : raw40784step3 = -raw40784step2 := by apply Matrix.ext; change ∀ i j, raw40784step3 i j = -(raw40784step2 i j); unfold raw40784step3 raw40784step2; decide +kernel
      have hl : raw40784step3Labels = raw40784step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2744 node2744Labels := by rfl

def raw40785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40785Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40785step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40785step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -2, 2], ![3, -1, -2]]
def raw40785step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40785step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, -2, 3], ![-2, 2, 0]]
def raw40785step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40785step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 2, -3], ![2, -2, 0]]
def raw40785step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40785 raw40785Labels = mixedMoment B node3056 node3056Labels := by
  calc
    mixedMoment B raw40785 raw40785Labels = mixedMoment B raw40785step0 raw40785step0Labels := by
      have hz : ∀ j, raw40785 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40785step0 = (fun i j => raw40785 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40785step0 raw40785; decide +kernel
      have hl : raw40785step0Labels = raw40785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40785 raw40785Labels permutation434 hz
    mixedMoment B raw40785step0 raw40785step0Labels = mixedMoment B raw40785step1 raw40785step1Labels := by
      have hz : ∀ j, raw40785step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40785step1 = (fun i j => raw40785step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40785step1 raw40785step0; decide +kernel
      have hl : raw40785step1Labels = raw40785step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40785step0 raw40785step0Labels permutation80 hz
    mixedMoment B raw40785step1 raw40785step1Labels = mixedMoment B raw40785step2 raw40785step2Labels := by
      have ha : raw40785step2 = (fun i j => raw40785step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40785step2 raw40785step1; decide +kernel
      have hl : raw40785step2Labels = raw40785step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40785step1 raw40785step1Labels permutation31 permutation3
    mixedMoment B raw40785step2 raw40785step2Labels = mixedMoment B raw40785step3 raw40785step3Labels := by
      have ha : raw40785step3 = -raw40785step2 := by apply Matrix.ext; change ∀ i j, raw40785step3 i j = -(raw40785step2 i j); unfold raw40785step3 raw40785step2; decide +kernel
      have hl : raw40785step3Labels = raw40785step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3056 node3056Labels := by rfl

def raw40786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40786Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40786step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40786step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw40786step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40786step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw40786step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40786 raw40786Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw40786 raw40786Labels = mixedMoment B raw40786step0 raw40786step0Labels := by
      have hz : ∀ j, raw40786 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40786step0 = (fun i j => raw40786 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40786step0 raw40786; decide +kernel
      have hl : raw40786step0Labels = raw40786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40786 raw40786Labels permutation434 hz
    mixedMoment B raw40786step0 raw40786step0Labels = mixedMoment B raw40786step1 raw40786step1Labels := by
      have hz : ∀ j, raw40786step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40786step1 = (fun i j => raw40786step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40786step1 raw40786step0; decide +kernel
      have hl : raw40786step1Labels = raw40786step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40786step0 raw40786step0Labels permutation80 hz
    mixedMoment B raw40786step1 raw40786step1Labels = mixedMoment B raw40786step2 raw40786step2Labels := by
      have ha : raw40786step2 = (fun i j => raw40786step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40786step2 raw40786step1; decide +kernel
      have hl : raw40786step2Labels = raw40786step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40786step1 raw40786step1Labels permutation17 permutation6
    _ = mixedMoment B node3626 node3626Labels := by rfl

def raw40787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40787Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40787step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40787step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw40787step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40787step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40787step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40787 raw40787Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw40787 raw40787Labels = mixedMoment B raw40787step0 raw40787step0Labels := by
      have hz : ∀ j, raw40787 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40787step0 = (fun i j => raw40787 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40787step0 raw40787; decide +kernel
      have hl : raw40787step0Labels = raw40787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40787 raw40787Labels permutation434 hz
    mixedMoment B raw40787step0 raw40787step0Labels = mixedMoment B raw40787step1 raw40787step1Labels := by
      have hz : ∀ j, raw40787step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40787step1 = (fun i j => raw40787step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40787step1 raw40787step0; decide +kernel
      have hl : raw40787step1Labels = raw40787step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40787step0 raw40787step0Labels permutation80 hz
    mixedMoment B raw40787step1 raw40787step1Labels = mixedMoment B raw40787step2 raw40787step2Labels := by
      have ha : raw40787step2 = (fun i j => raw40787step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40787step2 raw40787step1; decide +kernel
      have hl : raw40787step2Labels = raw40787step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40787step1 raw40787step1Labels permutation19 permutation6
    _ = mixedMoment B node3584 node3584Labels := by rfl

def raw40788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40788Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40788step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40788step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -3, 2], ![2, 0, -2]]
def raw40788step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40788step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -2, 0], ![2, 1, -3]]
def raw40788step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40788 raw40788Labels = mixedMoment B node3396 node3396Labels := by
  calc
    mixedMoment B raw40788 raw40788Labels = mixedMoment B raw40788step0 raw40788step0Labels := by
      have hz : ∀ j, raw40788 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40788step0 = (fun i j => raw40788 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40788step0 raw40788; decide +kernel
      have hl : raw40788step0Labels = raw40788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40788 raw40788Labels permutation434 hz
    mixedMoment B raw40788step0 raw40788step0Labels = mixedMoment B raw40788step1 raw40788step1Labels := by
      have hz : ∀ j, raw40788step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40788step1 = (fun i j => raw40788step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40788step1 raw40788step0; decide +kernel
      have hl : raw40788step1Labels = raw40788step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40788step0 raw40788step0Labels permutation80 hz
    mixedMoment B raw40788step1 raw40788step1Labels = mixedMoment B raw40788step2 raw40788step2Labels := by
      have ha : raw40788step2 = (fun i j => raw40788step1 (permutation18 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40788step2 raw40788step1; decide +kernel
      have hl : raw40788step2Labels = raw40788step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40788step1 raw40788step1Labels permutation18 permutation6
    _ = mixedMoment B node3396 node3396Labels := by rfl

def raw40789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40789Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40789step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, -2, 3], ![-2, 2, 0]]
def raw40789step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40789step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw40789step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40789 raw40789Labels = mixedMoment B node3079 node3079Labels := by
  calc
    mixedMoment B raw40789 raw40789Labels = mixedMoment B raw40789step0 raw40789step0Labels := by
      have hz : ∀ j, raw40789 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40789step0 = (fun i j => raw40789 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40789step0 raw40789; decide +kernel
      have hl : raw40789step0Labels = raw40789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40789 raw40789Labels permutation346 hz
    mixedMoment B raw40789step0 raw40789step0Labels = mixedMoment B raw40789step1 raw40789step1Labels := by
      have ha : raw40789step1 = (fun i j => raw40789step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40789step1 raw40789step0; decide +kernel
      have hl : raw40789step1Labels = raw40789step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40789step0 raw40789step0Labels permutation145 permutation3
    mixedMoment B raw40789step1 raw40789step1Labels = mixedMoment B raw40789step2 raw40789step2Labels := by
      have ha : raw40789step2 = -raw40789step1 := by apply Matrix.ext; change ∀ i j, raw40789step2 i j = -(raw40789step1 i j); unfold raw40789step2 raw40789step1; decide +kernel
      have hl : raw40789step2Labels = raw40789step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3079 node3079Labels := by rfl

def raw40790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40790Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40790step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40790step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40790step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40790 raw40790Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw40790 raw40790Labels = mixedMoment B raw40790step0 raw40790step0Labels := by
      have hz : ∀ j, raw40790 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40790step0 = (fun i j => raw40790 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40790step0 raw40790; decide +kernel
      have hl : raw40790step0Labels = raw40790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40790 raw40790Labels permutation346 hz
    mixedMoment B raw40790step0 raw40790step0Labels = mixedMoment B raw40790step1 raw40790step1Labels := by
      have ha : raw40790step1 = (fun i j => raw40790step0 (permutation73 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40790step1 raw40790step0; decide +kernel
      have hl : raw40790step1Labels = raw40790step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40790step0 raw40790step0Labels permutation73 permutation6
    _ = mixedMoment B node3541 node3541Labels := by rfl

def raw40791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40791Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40791step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40791step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40791 raw40791Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw40791 raw40791Labels = mixedMoment B raw40791step0 raw40791step0Labels := by
      have hz : ∀ j, raw40791 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40791step0 = (fun i j => raw40791 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40791step0 raw40791; decide +kernel
      have hl : raw40791step0Labels = raw40791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40791 raw40791Labels permutation346 hz
    mixedMoment B raw40791step0 raw40791step0Labels = mixedMoment B raw40791step1 raw40791step1Labels := by
      have ha : raw40791step1 = (fun i j => raw40791step0 (permutation79 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40791step1 raw40791step0; decide +kernel
      have hl : raw40791step1Labels = raw40791step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40791step0 raw40791step0Labels permutation79 permutation6
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw40792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40792Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40792step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40792step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40792 raw40792Labels = mixedMoment B node3395 node3395Labels := by
  calc
    mixedMoment B raw40792 raw40792Labels = mixedMoment B raw40792step0 raw40792step0Labels := by
      have hz : ∀ j, raw40792 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40792step0 = (fun i j => raw40792 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40792step0 raw40792; decide +kernel
      have hl : raw40792step0Labels = raw40792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40792 raw40792Labels permutation346 hz
    mixedMoment B raw40792step0 raw40792step0Labels = mixedMoment B raw40792step1 raw40792step1Labels := by
      have ha : raw40792step1 = (fun i j => raw40792step0 (permutation77 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40792step1 raw40792step0; decide +kernel
      have hl : raw40792step1Labels = raw40792step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40792step0 raw40792step0Labels permutation77 permutation6
    _ = mixedMoment B node3395 node3395Labels := by rfl

def raw40793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40793Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40793step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40793step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40793 raw40793Labels = mixedMoment B node3506 node3506Labels := by
  calc
    mixedMoment B raw40793 raw40793Labels = mixedMoment B raw40793step0 raw40793step0Labels := by
      have hz : ∀ j, raw40793 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40793step0 = (fun i j => raw40793 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40793step0 raw40793; decide +kernel
      have hl : raw40793step0Labels = raw40793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40793 raw40793Labels permutation346 hz
    mixedMoment B raw40793step0 raw40793step0Labels = mixedMoment B raw40793step1 raw40793step1Labels := by
      have ha : raw40793step1 = (fun i j => raw40793step0 (permutation72 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40793step1 raw40793step0; decide +kernel
      have hl : raw40793step1Labels = raw40793step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40793step0 raw40793step0Labels permutation72 permutation6
    _ = mixedMoment B node3506 node3506Labels := by rfl

def raw40794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40794Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40794step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40794step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40794 raw40794Labels = mixedMoment B node3379 node3379Labels := by
  calc
    mixedMoment B raw40794 raw40794Labels = mixedMoment B raw40794step0 raw40794step0Labels := by
      have hz : ∀ j, raw40794 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40794step0 = (fun i j => raw40794 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40794step0 raw40794; decide +kernel
      have hl : raw40794step0Labels = raw40794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40794 raw40794Labels permutation346 hz
    mixedMoment B raw40794step0 raw40794step0Labels = mixedMoment B raw40794step1 raw40794step1Labels := by
      have ha : raw40794step1 = (fun i j => raw40794step0 (permutation78 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40794step1 raw40794step0; decide +kernel
      have hl : raw40794step1Labels = raw40794step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40794step0 raw40794step0Labels permutation78 permutation6
    _ = mixedMoment B node3379 node3379Labels := by rfl

def raw40795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40795Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40795step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40795step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40795 raw40795Labels = mixedMoment B node3505 node3505Labels := by
  calc
    mixedMoment B raw40795 raw40795Labels = mixedMoment B raw40795step0 raw40795step0Labels := by
      have ha : raw40795step0 = (fun i j => raw40795 (permutation332 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40795step0 raw40795; decide +kernel
      have hl : raw40795step0Labels = raw40795Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40795 raw40795Labels permutation332 permutation6
    _ = mixedMoment B node3505 node3505Labels := by rfl

def raw40796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40796Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40796step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40796 raw40796Labels = mixedMoment B node3378 node3378Labels := by
  calc
    mixedMoment B raw40796 raw40796Labels = mixedMoment B raw40796step0 raw40796step0Labels := by
      have ha : raw40796step0 = (fun i j => raw40796 (permutation345 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40796step0 raw40796; decide +kernel
      have hl : raw40796step0Labels = raw40796Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40796 raw40796Labels permutation345 permutation6
    _ = mixedMoment B node3378 node3378Labels := by rfl

def raw40797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40797Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw40797step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40797step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw40797step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40797step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40797step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40797step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40797step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40797 raw40797Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw40797 raw40797Labels = mixedMoment B raw40797step0 raw40797step0Labels := by
      have hz : ∀ j, raw40797 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40797step0 = (fun i j => raw40797 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40797step0 raw40797; decide +kernel
      have hl : raw40797step0Labels = raw40797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40797 raw40797Labels permutation520 hz
    mixedMoment B raw40797step0 raw40797step0Labels = mixedMoment B raw40797step1 raw40797step1Labels := by
      have hz : ∀ j, raw40797step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40797step1 = (fun i j => raw40797step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40797step1 raw40797step0; decide +kernel
      have hl : raw40797step1Labels = raw40797step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40797step0 raw40797step0Labels permutation104 hz
    mixedMoment B raw40797step1 raw40797step1Labels = mixedMoment B raw40797step2 raw40797step2Labels := by
      have ha : raw40797step2 = (fun i j => raw40797step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40797step2 raw40797step1; decide +kernel
      have hl : raw40797step2Labels = raw40797step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40797step1 raw40797step1Labels permutation31 permutation3
    mixedMoment B raw40797step2 raw40797step2Labels = mixedMoment B raw40797step3 raw40797step3Labels := by
      have ha : raw40797step3 = -raw40797step2 := by apply Matrix.ext; change ∀ i j, raw40797step3 i j = -(raw40797step2 i j); unfold raw40797step3 raw40797step2; decide +kernel
      have hl : raw40797step3Labels = raw40797step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2266 node2266Labels := by rfl

def raw40798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40798Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw40798step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40798step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40798step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40798step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40798 raw40798Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw40798 raw40798Labels = mixedMoment B raw40798step0 raw40798step0Labels := by
      have hz : ∀ j, raw40798 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40798step0 = (fun i j => raw40798 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40798step0 raw40798; decide +kernel
      have hl : raw40798step0Labels = raw40798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40798 raw40798Labels permutation434 hz
    mixedMoment B raw40798step0 raw40798step0Labels = mixedMoment B raw40798step1 raw40798step1Labels := by
      have ha : raw40798step1 = (fun i j => raw40798step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40798step1 raw40798step0; decide +kernel
      have hl : raw40798step1Labels = raw40798step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40798step0 raw40798step0Labels permutation151 permutation3
    mixedMoment B raw40798step1 raw40798step1Labels = mixedMoment B raw40798step2 raw40798step2Labels := by
      have ha : raw40798step2 = -raw40798step1 := by apply Matrix.ext; change ∀ i j, raw40798step2 i j = -(raw40798step1 i j); unfold raw40798step2 raw40798step1; decide +kernel
      have hl : raw40798step2Labels = raw40798step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2724 node2724Labels := by rfl

def raw40799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40799Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -2, 2], ![3, -1, -2]]
def raw40799step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40799step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40799step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40799 raw40799Labels = mixedMoment B node3040 node3040Labels := by
  calc
    mixedMoment B raw40799 raw40799Labels = mixedMoment B raw40799step0 raw40799step0Labels := by
      have hz : ∀ j, raw40799 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40799step0 = (fun i j => raw40799 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40799step0 raw40799; decide +kernel
      have hl : raw40799step0Labels = raw40799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40799 raw40799Labels permutation434 hz
    mixedMoment B raw40799step0 raw40799step0Labels = mixedMoment B raw40799step1 raw40799step1Labels := by
      have ha : raw40799step1 = (fun i j => raw40799step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40799step1 raw40799step0; decide +kernel
      have hl : raw40799step1Labels = raw40799step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40799step0 raw40799step0Labels permutation151 permutation3
    mixedMoment B raw40799step1 raw40799step1Labels = mixedMoment B raw40799step2 raw40799step2Labels := by
      have ha : raw40799step2 = -raw40799step1 := by apply Matrix.ext; change ∀ i j, raw40799step2 i j = -(raw40799step1 i j); unfold raw40799step2 raw40799step1; decide +kernel
      have hl : raw40799step2Labels = raw40799step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3040 node3040Labels := by rfl

def raw40800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw40800Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw40800step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40800step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40800step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40800step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40800 raw40800Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw40800 raw40800Labels = mixedMoment B raw40800step0 raw40800step0Labels := by
      have hz : ∀ j, raw40800 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40800step0 = (fun i j => raw40800 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40800step0 raw40800; decide +kernel
      have hl : raw40800step0Labels = raw40800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40800 raw40800Labels permutation434 hz
    mixedMoment B raw40800step0 raw40800step0Labels = mixedMoment B raw40800step1 raw40800step1Labels := by
      have ha : raw40800step1 = (fun i j => raw40800step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40800step1 raw40800step0; decide +kernel
      have hl : raw40800step1Labels = raw40800step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40800step0 raw40800step0Labels permutation151 permutation3
    mixedMoment B raw40800step1 raw40800step1Labels = mixedMoment B raw40800step2 raw40800step2Labels := by
      have ha : raw40800step2 = -raw40800step1 := by apply Matrix.ext; change ∀ i j, raw40800step2 i j = -(raw40800step1 i j); unfold raw40800step2 raw40800step1; decide +kernel
      have hl : raw40800step2Labels = raw40800step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw40801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40801Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw40801step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40801step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40801step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40801step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40801step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40801 raw40801Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw40801 raw40801Labels = mixedMoment B raw40801step0 raw40801step0Labels := by
      have hz : ∀ j, raw40801 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40801step0 = (fun i j => raw40801 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40801step0 raw40801; decide +kernel
      have hl : raw40801step0Labels = raw40801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40801 raw40801Labels permutation434 hz
    mixedMoment B raw40801step0 raw40801step0Labels = mixedMoment B raw40801step1 raw40801step1Labels := by
      have ha : raw40801step1 = (fun i j => raw40801step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40801step1 raw40801step0; decide +kernel
      have hl : raw40801step1Labels = raw40801step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40801step0 raw40801step0Labels permutation151 permutation3
    mixedMoment B raw40801step1 raw40801step1Labels = mixedMoment B raw40801step2 raw40801step2Labels := by
      have ha : raw40801step2 = -raw40801step1 := by apply Matrix.ext; change ∀ i j, raw40801step2 i j = -(raw40801step1 i j); unfold raw40801step2 raw40801step1; decide +kernel
      have hl : raw40801step2Labels = raw40801step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3959 node3959Labels := by rfl

def raw40802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40802Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw40802step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40802step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40802step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40802step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40802step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40802 raw40802Labels = mixedMoment B node3395 node3395Labels := by
  calc
    mixedMoment B raw40802 raw40802Labels = mixedMoment B raw40802step0 raw40802step0Labels := by
      have hz : ∀ j, raw40802 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40802step0 = (fun i j => raw40802 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40802step0 raw40802; decide +kernel
      have hl : raw40802step0Labels = raw40802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40802 raw40802Labels permutation434 hz
    mixedMoment B raw40802step0 raw40802step0Labels = mixedMoment B raw40802step1 raw40802step1Labels := by
      have ha : raw40802step1 = (fun i j => raw40802step0 (permutation106 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40802step1 raw40802step0; decide +kernel
      have hl : raw40802step1Labels = raw40802step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40802step0 raw40802step0Labels permutation106 permutation6
    mixedMoment B raw40802step1 raw40802step1Labels = mixedMoment B raw40802step2 raw40802step2Labels := by
      have ha : raw40802step2 = -raw40802step1 := by apply Matrix.ext; change ∀ i j, raw40802step2 i j = -(raw40802step1 i j); unfold raw40802step2 raw40802step1; decide +kernel
      have hl : raw40802step2Labels = raw40802step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3395 node3395Labels := by rfl

def raw40803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40803Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40803step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40803step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40803step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40803 raw40803Labels = mixedMoment B node3066 node3066Labels := by
  calc
    mixedMoment B raw40803 raw40803Labels = mixedMoment B raw40803step0 raw40803step0Labels := by
      have ha : raw40803step0 = (fun i j => raw40803 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40803step0 raw40803; decide +kernel
      have hl : raw40803step0Labels = raw40803Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40803 raw40803Labels permutation664 permutation3
    mixedMoment B raw40803step0 raw40803step0Labels = mixedMoment B raw40803step1 raw40803step1Labels := by
      have ha : raw40803step1 = -raw40803step0 := by apply Matrix.ext; change ∀ i j, raw40803step1 i j = -(raw40803step0 i j); unfold raw40803step1 raw40803step0; decide +kernel
      have hl : raw40803step1Labels = raw40803step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3066 node3066Labels := by rfl

def raw40804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40804Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40804step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40804step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40804step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40804step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40804 raw40804Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw40804 raw40804Labels = mixedMoment B raw40804step0 raw40804step0Labels := by
      have ha : raw40804step0 = (fun i j => raw40804 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40804step0 raw40804; decide +kernel
      have hl : raw40804step0Labels = raw40804Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40804 raw40804Labels permutation688 permutation3
    mixedMoment B raw40804step0 raw40804step0Labels = mixedMoment B raw40804step1 raw40804step1Labels := by
      have ha : raw40804step1 = -raw40804step0 := by apply Matrix.ext; change ∀ i j, raw40804step1 i j = -(raw40804step0 i j); unfold raw40804step1 raw40804step0; decide +kernel
      have hl : raw40804step1Labels = raw40804step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3839 node3839Labels := by rfl

def raw40805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40805Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40805step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40805step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40805step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40805step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40805 raw40805Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw40805 raw40805Labels = mixedMoment B raw40805step0 raw40805step0Labels := by
      have ha : raw40805step0 = (fun i j => raw40805 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40805step0 raw40805; decide +kernel
      have hl : raw40805step0Labels = raw40805Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40805 raw40805Labels permutation688 permutation3
    mixedMoment B raw40805step0 raw40805step0Labels = mixedMoment B raw40805step1 raw40805step1Labels := by
      have ha : raw40805step1 = -raw40805step0 := by apply Matrix.ext; change ∀ i j, raw40805step1 i j = -(raw40805step0 i j); unfold raw40805step1 raw40805step0; decide +kernel
      have hl : raw40805step1Labels = raw40805step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3972 node3972Labels := by rfl

def raw40806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40806Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40806step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40806step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40806 raw40806Labels = mixedMoment B node4022 node4022Labels := by
  calc
    mixedMoment B raw40806 raw40806Labels = mixedMoment B raw40806step0 raw40806step0Labels := by
      have ha : raw40806step0 = (fun i j => raw40806 (permutation609 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40806step0 raw40806; decide +kernel
      have hl : raw40806step0Labels = raw40806Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40806 raw40806Labels permutation609 permutation6
    _ = mixedMoment B node4022 node4022Labels := by rfl

def raw40807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40807Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40807step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw40807step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40807step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40807step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40807 raw40807Labels = mixedMoment B node3730 node3730Labels := by
  calc
    mixedMoment B raw40807 raw40807Labels = mixedMoment B raw40807step0 raw40807step0Labels := by
      have ha : raw40807step0 = (fun i j => raw40807 (permutation450 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40807step0 raw40807; decide +kernel
      have hl : raw40807step0Labels = raw40807Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40807 raw40807Labels permutation450 permutation6
    mixedMoment B raw40807step0 raw40807step0Labels = mixedMoment B raw40807step1 raw40807step1Labels := by
      have ha : raw40807step1 = -raw40807step0 := by apply Matrix.ext; change ∀ i j, raw40807step1 i j = -(raw40807step0 i j); unfold raw40807step1 raw40807step0; decide +kernel
      have hl : raw40807step1Labels = raw40807step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3730 node3730Labels := by rfl

def raw40808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40808Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40808step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40808step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40808step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40808 raw40808Labels = mixedMoment B node3722 node3722Labels := by
  calc
    mixedMoment B raw40808 raw40808Labels = mixedMoment B raw40808step0 raw40808step0Labels := by
      have ha : raw40808step0 = (fun i j => raw40808 (permutation445 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40808step0 raw40808; decide +kernel
      have hl : raw40808step0Labels = raw40808Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40808 raw40808Labels permutation445 permutation6
    mixedMoment B raw40808step0 raw40808step0Labels = mixedMoment B raw40808step1 raw40808step1Labels := by
      have ha : raw40808step1 = -raw40808step0 := by apply Matrix.ext; change ∀ i j, raw40808step1 i j = -(raw40808step0 i j); unfold raw40808step1 raw40808step0; decide +kernel
      have hl : raw40808step1Labels = raw40808step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3722 node3722Labels := by rfl

def raw40809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40809Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40809step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw40809step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40809 raw40809Labels = mixedMoment B node4024 node4024Labels := by
  calc
    mixedMoment B raw40809 raw40809Labels = mixedMoment B raw40809step0 raw40809step0Labels := by
      have ha : raw40809step0 = (fun i j => raw40809 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40809step0 raw40809; decide +kernel
      have hl : raw40809step0Labels = raw40809Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40809 raw40809Labels permutation152 permutation3
    _ = mixedMoment B node4024 node4024Labels := by rfl

def raw40810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw40810Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw40810step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40810step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw40810step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40810step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40810step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40810step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40810step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40810 raw40810Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw40810 raw40810Labels = mixedMoment B raw40810step0 raw40810step0Labels := by
      have hz : ∀ j, raw40810 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40810step0 = (fun i j => raw40810 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40810step0 raw40810; decide +kernel
      have hl : raw40810step0Labels = raw40810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40810 raw40810Labels permutation434 hz
    mixedMoment B raw40810step0 raw40810step0Labels = mixedMoment B raw40810step1 raw40810step1Labels := by
      have hz : ∀ j, raw40810step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40810step1 = (fun i j => raw40810step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40810step1 raw40810step0; decide +kernel
      have hl : raw40810step1Labels = raw40810step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40810step0 raw40810step0Labels permutation80 hz
    mixedMoment B raw40810step1 raw40810step1Labels = mixedMoment B raw40810step2 raw40810step2Labels := by
      have ha : raw40810step2 = (fun i j => raw40810step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40810step2 raw40810step1; decide +kernel
      have hl : raw40810step2Labels = raw40810step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40810step1 raw40810step1Labels permutation31 permutation3
    mixedMoment B raw40810step2 raw40810step2Labels = mixedMoment B raw40810step3 raw40810step3Labels := by
      have ha : raw40810step3 = -raw40810step2 := by apply Matrix.ext; change ∀ i j, raw40810step3 i j = -(raw40810step2 i j); unfold raw40810step3 raw40810step2; decide +kernel
      have hl : raw40810step3Labels = raw40810step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3584 node3584Labels := by rfl

def raw40811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw40811Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw40811step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40811step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -3, 2], ![2, 1, -3]]
def raw40811step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40811step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def raw40811step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40811 raw40811Labels = mixedMoment B node2888 node2888Labels := by
  calc
    mixedMoment B raw40811 raw40811Labels = mixedMoment B raw40811step0 raw40811step0Labels := by
      have hz : ∀ j, raw40811 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40811step0 = (fun i j => raw40811 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40811step0 raw40811; decide +kernel
      have hl : raw40811step0Labels = raw40811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40811 raw40811Labels permutation434 hz
    mixedMoment B raw40811step0 raw40811step0Labels = mixedMoment B raw40811step1 raw40811step1Labels := by
      have hz : ∀ j, raw40811step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40811step1 = (fun i j => raw40811step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40811step1 raw40811step0; decide +kernel
      have hl : raw40811step1Labels = raw40811step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40811step0 raw40811step0Labels permutation80 hz
    mixedMoment B raw40811step1 raw40811step1Labels = mixedMoment B raw40811step2 raw40811step2Labels := by
      have ha : raw40811step2 = (fun i j => raw40811step1 (permutation28 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40811step2 raw40811step1; decide +kernel
      have hl : raw40811step2Labels = raw40811step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40811step1 raw40811step1Labels permutation28 permutation6
    _ = mixedMoment B node2888 node2888Labels := by rfl

def raw40812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw40812Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw40812step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw40812step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40812step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw40812step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40812 raw40812Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw40812 raw40812Labels = mixedMoment B raw40812step0 raw40812step0Labels := by
      have hz : ∀ j, raw40812 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40812step0 = (fun i j => raw40812 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40812step0 raw40812; decide +kernel
      have hl : raw40812step0Labels = raw40812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40812 raw40812Labels permutation346 hz
    mixedMoment B raw40812step0 raw40812step0Labels = mixedMoment B raw40812step1 raw40812step1Labels := by
      have ha : raw40812step1 = (fun i j => raw40812step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40812step1 raw40812step0; decide +kernel
      have hl : raw40812step1Labels = raw40812step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40812step0 raw40812step0Labels permutation151 permutation3
    mixedMoment B raw40812step1 raw40812step1Labels = mixedMoment B raw40812step2 raw40812step2Labels := by
      have ha : raw40812step2 = -raw40812step1 := by apply Matrix.ext; change ∀ i j, raw40812step2 i j = -(raw40812step1 i j); unfold raw40812step2 raw40812step1; decide +kernel
      have hl : raw40812step2Labels = raw40812step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3877 node3877Labels := by rfl

def raw40813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw40813Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw40813step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40813step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40813step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40813 raw40813Labels = mixedMoment B node2885 node2885Labels := by
  calc
    mixedMoment B raw40813 raw40813Labels = mixedMoment B raw40813step0 raw40813step0Labels := by
      have hz : ∀ j, raw40813 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40813step0 = (fun i j => raw40813 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40813step0 raw40813; decide +kernel
      have hl : raw40813step0Labels = raw40813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40813 raw40813Labels permutation346 hz
    mixedMoment B raw40813step0 raw40813step0Labels = mixedMoment B raw40813step1 raw40813step1Labels := by
      have ha : raw40813step1 = (fun i j => raw40813step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40813step1 raw40813step0; decide +kernel
      have hl : raw40813step1Labels = raw40813step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40813step0 raw40813step0Labels permutation137 permutation6
    _ = mixedMoment B node2885 node2885Labels := by rfl

def raw40814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40814Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40814step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40814step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw40814step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40814step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40814step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40814 raw40814Labels = mixedMoment B node3733 node3733Labels := by
  calc
    mixedMoment B raw40814 raw40814Labels = mixedMoment B raw40814step0 raw40814step0Labels := by
      have hz : ∀ j, raw40814 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40814step0 = (fun i j => raw40814 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40814step0 raw40814; decide +kernel
      have hl : raw40814step0Labels = raw40814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40814 raw40814Labels permutation346 hz
    mixedMoment B raw40814step0 raw40814step0Labels = mixedMoment B raw40814step1 raw40814step1Labels := by
      have ha : raw40814step1 = (fun i j => raw40814step0 (permutation84 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40814step1 raw40814step0; decide +kernel
      have hl : raw40814step1Labels = raw40814step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40814step0 raw40814step0Labels permutation84 permutation6
    mixedMoment B raw40814step1 raw40814step1Labels = mixedMoment B raw40814step2 raw40814step2Labels := by
      have ha : raw40814step2 = -raw40814step1 := by apply Matrix.ext; change ∀ i j, raw40814step2 i j = -(raw40814step1 i j); unfold raw40814step2 raw40814step1; decide +kernel
      have hl : raw40814step2Labels = raw40814step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3733 node3733Labels := by rfl

def raw40815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40815Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40815step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40815step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40815 raw40815Labels = mixedMoment B node2867 node2867Labels := by
  calc
    mixedMoment B raw40815 raw40815Labels = mixedMoment B raw40815step0 raw40815step0Labels := by
      have hz : ∀ j, raw40815 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40815step0 = (fun i j => raw40815 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40815step0 raw40815; decide +kernel
      have hl : raw40815step0Labels = raw40815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40815 raw40815Labels permutation346 hz
    mixedMoment B raw40815step0 raw40815step0Labels = mixedMoment B raw40815step1 raw40815step1Labels := by
      have ha : raw40815step1 = (fun i j => raw40815step0 (permutation138 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40815step1 raw40815step0; decide +kernel
      have hl : raw40815step1Labels = raw40815step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40815step0 raw40815step0Labels permutation138 permutation6
    _ = mixedMoment B node2867 node2867Labels := by rfl

def raw40816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40816Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40816step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40816step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40816 raw40816Labels = mixedMoment B node3949 node3949Labels := by
  calc
    mixedMoment B raw40816 raw40816Labels = mixedMoment B raw40816step0 raw40816step0Labels := by
      have ha : raw40816step0 = (fun i j => raw40816 (permutation540 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40816step0 raw40816; decide +kernel
      have hl : raw40816step0Labels = raw40816Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40816 raw40816Labels permutation540 permutation6
    _ = mixedMoment B node3949 node3949Labels := by rfl

def raw40817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40817Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40817step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40817step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40817 raw40817Labels = mixedMoment B node2864 node2864Labels := by
  calc
    mixedMoment B raw40817 raw40817Labels = mixedMoment B raw40817step0 raw40817step0Labels := by
      have ha : raw40817step0 = (fun i j => raw40817 (permutation620 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40817step0 raw40817; decide +kernel
      have hl : raw40817step0Labels = raw40817Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40817 raw40817Labels permutation620 permutation6
    _ = mixedMoment B node2864 node2864Labels := by rfl

def raw40818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw40818Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40818step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40818step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40818 raw40818Labels = mixedMoment B node3946 node3946Labels := by
  calc
    mixedMoment B raw40818 raw40818Labels = mixedMoment B raw40818step0 raw40818step0Labels := by
      have ha : raw40818step0 = (fun i j => raw40818 (permutation462 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40818step0 raw40818; decide +kernel
      have hl : raw40818step0Labels = raw40818Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40818 raw40818Labels permutation462 permutation6
    _ = mixedMoment B node3946 node3946Labels := by rfl

def raw40819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw40819Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40819step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40819step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40819 raw40819Labels = mixedMoment B node3954 node3954Labels := by
  calc
    mixedMoment B raw40819 raw40819Labels = mixedMoment B raw40819step0 raw40819step0Labels := by
      have ha : raw40819step0 = (fun i j => raw40819 (permutation463 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40819step0 raw40819; decide +kernel
      have hl : raw40819step0Labels = raw40819Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40819 raw40819Labels permutation463 permutation6
    _ = mixedMoment B node3954 node3954Labels := by rfl

def raw40820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw40820Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40820step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw40820step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40820step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw40820step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40820 raw40820Labels = mixedMoment B node3720 node3720Labels := by
  calc
    mixedMoment B raw40820 raw40820Labels = mixedMoment B raw40820step0 raw40820step0Labels := by
      have ha : raw40820step0 = (fun i j => raw40820 (permutation365 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40820step0 raw40820; decide +kernel
      have hl : raw40820step0Labels = raw40820Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40820 raw40820Labels permutation365 permutation6
    mixedMoment B raw40820step0 raw40820step0Labels = mixedMoment B raw40820step1 raw40820step1Labels := by
      have ha : raw40820step1 = -raw40820step0 := by apply Matrix.ext; change ∀ i j, raw40820step1 i j = -(raw40820step0 i j); unfold raw40820step1 raw40820step0; decide +kernel
      have hl : raw40820step1Labels = raw40820step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3720 node3720Labels := by rfl

def raw40821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40821Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw40821step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40821step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw40821step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40821step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw40821step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40821step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40821step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40821 raw40821Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw40821 raw40821Labels = mixedMoment B raw40821step0 raw40821step0Labels := by
      have hz : ∀ j, raw40821 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40821step0 = (fun i j => raw40821 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40821step0 raw40821; decide +kernel
      have hl : raw40821step0Labels = raw40821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40821 raw40821Labels permutation520 hz
    mixedMoment B raw40821step0 raw40821step0Labels = mixedMoment B raw40821step1 raw40821step1Labels := by
      have hz : ∀ j, raw40821step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40821step1 = (fun i j => raw40821step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40821step1 raw40821step0; decide +kernel
      have hl : raw40821step1Labels = raw40821step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40821step0 raw40821step0Labels permutation104 hz
    mixedMoment B raw40821step1 raw40821step1Labels = mixedMoment B raw40821step2 raw40821step2Labels := by
      have ha : raw40821step2 = (fun i j => raw40821step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40821step2 raw40821step1; decide +kernel
      have hl : raw40821step2Labels = raw40821step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40821step1 raw40821step1Labels permutation31 permutation3
    mixedMoment B raw40821step2 raw40821step2Labels = mixedMoment B raw40821step3 raw40821step3Labels := by
      have ha : raw40821step3 = -raw40821step2 := by apply Matrix.ext; change ∀ i j, raw40821step3 i j = -(raw40821step2 i j); unfold raw40821step3 raw40821step2; decide +kernel
      have hl : raw40821step3Labels = raw40821step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2279 node2279Labels := by rfl

def raw40822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40822Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![3, -2, -1]]
def raw40822step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40822step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw40822step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40822step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40822step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40822 raw40822Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw40822 raw40822Labels = mixedMoment B raw40822step0 raw40822step0Labels := by
      have hz : ∀ j, raw40822 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40822step0 = (fun i j => raw40822 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40822step0 raw40822; decide +kernel
      have hl : raw40822step0Labels = raw40822Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40822 raw40822Labels permutation434 hz
    mixedMoment B raw40822step0 raw40822step0Labels = mixedMoment B raw40822step1 raw40822step1Labels := by
      have ha : raw40822step1 = (fun i j => raw40822step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40822step1 raw40822step0; decide +kernel
      have hl : raw40822step1Labels = raw40822step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40822step0 raw40822step0Labels permutation151 permutation3
    mixedMoment B raw40822step1 raw40822step1Labels = mixedMoment B raw40822step2 raw40822step2Labels := by
      have ha : raw40822step2 = -raw40822step1 := by apply Matrix.ext; change ∀ i j, raw40822step2 i j = -(raw40822step1 i j); unfold raw40822step2 raw40822step1; decide +kernel
      have hl : raw40822step2Labels = raw40822step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2732 node2732Labels := by rfl

def raw40823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40823Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -2, 2], ![3, -1, -2]]
def raw40823step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40823step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw40823step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40823step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40823step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40823 raw40823Labels = mixedMoment B node3045 node3045Labels := by
  calc
    mixedMoment B raw40823 raw40823Labels = mixedMoment B raw40823step0 raw40823step0Labels := by
      have hz : ∀ j, raw40823 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40823step0 = (fun i j => raw40823 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40823step0 raw40823; decide +kernel
      have hl : raw40823step0Labels = raw40823Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40823 raw40823Labels permutation434 hz
    mixedMoment B raw40823step0 raw40823step0Labels = mixedMoment B raw40823step1 raw40823step1Labels := by
      have ha : raw40823step1 = (fun i j => raw40823step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40823step1 raw40823step0; decide +kernel
      have hl : raw40823step1Labels = raw40823step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40823step0 raw40823step0Labels permutation151 permutation3
    mixedMoment B raw40823step1 raw40823step1Labels = mixedMoment B raw40823step2 raw40823step2Labels := by
      have ha : raw40823step2 = -raw40823step1 := by apply Matrix.ext; change ∀ i j, raw40823step2 i j = -(raw40823step1 i j); unfold raw40823step2 raw40823step1; decide +kernel
      have hl : raw40823step2Labels = raw40823step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3045 node3045Labels := by rfl

def raw40824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw40824Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw40824step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw40824step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40824step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40824step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40824 raw40824Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw40824 raw40824Labels = mixedMoment B raw40824step0 raw40824step0Labels := by
      have hz : ∀ j, raw40824 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40824step0 = (fun i j => raw40824 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40824step0 raw40824; decide +kernel
      have hl : raw40824step0Labels = raw40824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40824 raw40824Labels permutation434 hz
    mixedMoment B raw40824step0 raw40824step0Labels = mixedMoment B raw40824step1 raw40824step1Labels := by
      have ha : raw40824step1 = (fun i j => raw40824step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40824step1 raw40824step0; decide +kernel
      have hl : raw40824step1Labels = raw40824step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40824step0 raw40824step0Labels permutation151 permutation3
    mixedMoment B raw40824step1 raw40824step1Labels = mixedMoment B raw40824step2 raw40824step2Labels := by
      have ha : raw40824step2 = -raw40824step1 := by apply Matrix.ext; change ∀ i j, raw40824step2 i j = -(raw40824step1 i j); unfold raw40824step2 raw40824step1; decide +kernel
      have hl : raw40824step2Labels = raw40824step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3541 node3541Labels := by rfl

def raw40825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40825Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw40825step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw40825step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40825step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40825step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40825 raw40825Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw40825 raw40825Labels = mixedMoment B raw40825step0 raw40825step0Labels := by
      have hz : ∀ j, raw40825 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40825step0 = (fun i j => raw40825 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40825step0 raw40825; decide +kernel
      have hl : raw40825step0Labels = raw40825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40825 raw40825Labels permutation434 hz
    mixedMoment B raw40825step0 raw40825step0Labels = mixedMoment B raw40825step1 raw40825step1Labels := by
      have ha : raw40825step1 = (fun i j => raw40825step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40825step1 raw40825step0; decide +kernel
      have hl : raw40825step1Labels = raw40825step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40825step0 raw40825step0Labels permutation151 permutation3
    mixedMoment B raw40825step1 raw40825step1Labels = mixedMoment B raw40825step2 raw40825step2Labels := by
      have ha : raw40825step2 = -raw40825step1 := by apply Matrix.ext; change ∀ i j, raw40825step2 i j = -(raw40825step1 i j); unfold raw40825step2 raw40825step1; decide +kernel
      have hl : raw40825step2Labels = raw40825step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3814 node3814Labels := by rfl

def raw40826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40826Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw40826step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40826step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw40826step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40826 raw40826Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw40826 raw40826Labels = mixedMoment B raw40826step0 raw40826step0Labels := by
      have hz : ∀ j, raw40826 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40826step0 = (fun i j => raw40826 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40826step0 raw40826; decide +kernel
      have hl : raw40826step0Labels = raw40826Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40826 raw40826Labels permutation434 hz
    mixedMoment B raw40826step0 raw40826step0Labels = mixedMoment B raw40826step1 raw40826step1Labels := by
      have ha : raw40826step1 = (fun i j => raw40826step0 (permutation101 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40826step1 raw40826step0; decide +kernel
      have hl : raw40826step1Labels = raw40826step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40826step0 raw40826step0Labels permutation101 permutation6
    _ = mixedMoment B node3877 node3877Labels := by rfl

def raw40827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40827Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw40827step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40827step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40827step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40827step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40827step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40827 raw40827Labels = mixedMoment B node3379 node3379Labels := by
  calc
    mixedMoment B raw40827 raw40827Labels = mixedMoment B raw40827step0 raw40827step0Labels := by
      have hz : ∀ j, raw40827 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40827step0 = (fun i j => raw40827 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40827step0 raw40827; decide +kernel
      have hl : raw40827step0Labels = raw40827Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40827 raw40827Labels permutation434 hz
    mixedMoment B raw40827step0 raw40827step0Labels = mixedMoment B raw40827step1 raw40827step1Labels := by
      have ha : raw40827step1 = (fun i j => raw40827step0 (permutation105 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40827step1 raw40827step0; decide +kernel
      have hl : raw40827step1Labels = raw40827step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40827step0 raw40827step0Labels permutation105 permutation6
    mixedMoment B raw40827step1 raw40827step1Labels = mixedMoment B raw40827step2 raw40827step2Labels := by
      have ha : raw40827step2 = -raw40827step1 := by apply Matrix.ext; change ∀ i j, raw40827step2 i j = -(raw40827step1 i j); unfold raw40827step2 raw40827step1; decide +kernel
      have hl : raw40827step2Labels = raw40827step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3379 node3379Labels := by rfl

def raw40828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40828Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40828step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw40828step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40828step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40828step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40828 raw40828Labels = mixedMoment B node3069 node3069Labels := by
  calc
    mixedMoment B raw40828 raw40828Labels = mixedMoment B raw40828step0 raw40828step0Labels := by
      have ha : raw40828step0 = (fun i j => raw40828 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40828step0 raw40828; decide +kernel
      have hl : raw40828step0Labels = raw40828Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40828 raw40828Labels permutation664 permutation3
    mixedMoment B raw40828step0 raw40828step0Labels = mixedMoment B raw40828step1 raw40828step1Labels := by
      have ha : raw40828step1 = -raw40828step0 := by apply Matrix.ext; change ∀ i j, raw40828step1 i j = -(raw40828step0 i j); unfold raw40828step1 raw40828step0; decide +kernel
      have hl : raw40828step1Labels = raw40828step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3069 node3069Labels := by rfl

def raw40829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw40829Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw40829step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40829step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40829step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40829 raw40829Labels = mixedMoment B node3841 node3841Labels := by
  calc
    mixedMoment B raw40829 raw40829Labels = mixedMoment B raw40829step0 raw40829step0Labels := by
      have ha : raw40829step0 = (fun i j => raw40829 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40829step0 raw40829; decide +kernel
      have hl : raw40829step0Labels = raw40829Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40829 raw40829Labels permutation688 permutation3
    mixedMoment B raw40829step0 raw40829step0Labels = mixedMoment B raw40829step1 raw40829step1Labels := by
      have ha : raw40829step1 = -raw40829step0 := by apply Matrix.ext; change ∀ i j, raw40829step1 i j = -(raw40829step0 i j); unfold raw40829step1 raw40829step0; decide +kernel
      have hl : raw40829step1Labels = raw40829step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3841 node3841Labels := by rfl

def raw40830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40830Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40830step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40830step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40830 raw40830Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw40830 raw40830Labels = mixedMoment B raw40830step0 raw40830step0Labels := by
      have ha : raw40830step0 = (fun i j => raw40830 (permutation423 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40830step0 raw40830; decide +kernel
      have hl : raw40830step0Labels = raw40830Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40830 raw40830Labels permutation423 permutation6
    _ = mixedMoment B node3872 node3872Labels := by rfl

def raw40831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40831Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40831step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40831step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40831 raw40831Labels = mixedMoment B node3722 node3722Labels := by
  calc
    mixedMoment B raw40831 raw40831Labels = mixedMoment B raw40831step0 raw40831step0Labels := by
      have ha : raw40831step0 = (fun i j => raw40831 (permutation421 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40831step0 raw40831; decide +kernel
      have hl : raw40831step0Labels = raw40831Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40831 raw40831Labels permutation421 permutation6
    _ = mixedMoment B node3722 node3722Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
