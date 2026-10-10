import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw11648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw11648Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11648step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11648step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11648 raw11648Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw11648 raw11648Labels = mixedMoment B raw11648step0 raw11648step0Labels := by
      have hz : ∀ j, raw11648 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11648step0 = (fun i j => raw11648 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11648step0 raw11648; decide +kernel
      have hl : raw11648step0Labels = raw11648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11648 raw11648Labels permutation520 hz
    mixedMoment B raw11648step0 raw11648step0Labels = mixedMoment B raw11648step1 raw11648step1Labels := by
      have ha : raw11648step1 = (fun i j => raw11648step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11648step1 raw11648step0; decide +kernel
      have hl : raw11648step1Labels = raw11648step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11648step0 raw11648step0Labels permutation38 permutation2
    _ = mixedMoment B node2763 node2763Labels := by rfl

def raw11649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw11649Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw11649step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11649 raw11649Labels = mixedMoment B node2757 node2757Labels := by
  calc
    mixedMoment B raw11649 raw11649Labels = mixedMoment B raw11649step0 raw11649step0Labels := by
      have ha : raw11649step0 = (fun i j => raw11649 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11649step0 raw11649; decide +kernel
      have hl : raw11649step0Labels = raw11649Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11649 raw11649Labels permutation194 permutation2
    _ = mixedMoment B node2757 node2757Labels := by rfl

def raw11650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11650Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11650step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11650 raw11650Labels = mixedMoment B node2508 node2508Labels := by
  calc
    mixedMoment B raw11650 raw11650Labels = mixedMoment B raw11650step0 raw11650step0Labels := by
      have ha : raw11650step0 = (fun i j => raw11650 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11650step0 raw11650; decide +kernel
      have hl : raw11650step0Labels = raw11650Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11650 raw11650Labels permutation160 permutation2
    _ = mixedMoment B node2508 node2508Labels := by rfl

def raw11651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11651Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11651step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11651 raw11651Labels = mixedMoment B node2481 node2481Labels := by
  calc
    mixedMoment B raw11651 raw11651Labels = mixedMoment B raw11651step0 raw11651step0Labels := by
      have ha : raw11651step0 = (fun i j => raw11651 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11651step0 raw11651; decide +kernel
      have hl : raw11651step0Labels = raw11651Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11651 raw11651Labels permutation155 permutation2
    _ = mixedMoment B node2481 node2481Labels := by rfl

def raw11652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11652Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11652step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11652step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11652 raw11652Labels = mixedMoment B node2481 node2481Labels := by
  calc
    mixedMoment B raw11652 raw11652Labels = mixedMoment B raw11652step0 raw11652step0Labels := by
      have ha : raw11652step0 = (fun i j => raw11652 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11652step0 raw11652; decide +kernel
      have hl : raw11652step0Labels = raw11652Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11652 raw11652Labels permutation153 permutation2
    _ = mixedMoment B node2481 node2481Labels := by rfl

def raw11653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11653Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11653 raw11653Labels = mixedMoment B node2479 node2479Labels := by
  calc
    _ = mixedMoment B node2479 node2479Labels := by rfl

def raw11654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11654Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11654step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11654step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11654 raw11654Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw11654 raw11654Labels = mixedMoment B raw11654step0 raw11654step0Labels := by
      have hz : ∀ j, raw11654 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11654step0 = (fun i j => raw11654 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11654step0 raw11654; decide +kernel
      have hl : raw11654step0Labels = raw11654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11654 raw11654Labels permutation434 hz
    mixedMoment B raw11654step0 raw11654step0Labels = mixedMoment B raw11654step1 raw11654step1Labels := by
      have ha : raw11654step1 = (fun i j => raw11654step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11654step1 raw11654step0; decide +kernel
      have hl : raw11654step1Labels = raw11654step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11654step0 raw11654step0Labels permutation34 permutation2
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw11655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw11655Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw11655step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11655step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11655step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11655 raw11655Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw11655 raw11655Labels = mixedMoment B raw11655step0 raw11655step0Labels := by
      have hz : ∀ j, raw11655 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11655step0 = (fun i j => raw11655 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11655step0 raw11655; decide +kernel
      have hl : raw11655step0Labels = raw11655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11655 raw11655Labels permutation520 hz
    mixedMoment B raw11655step0 raw11655step0Labels = mixedMoment B raw11655step1 raw11655step1Labels := by
      have ha : raw11655step1 = (fun i j => raw11655step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11655step1 raw11655step0; decide +kernel
      have hl : raw11655step1Labels = raw11655step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11655step0 raw11655step0Labels permutation34 permutation2
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw11656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw11656Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11656step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11656 raw11656Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw11656 raw11656Labels = mixedMoment B raw11656step0 raw11656step0Labels := by
      have ha : raw11656step0 = (fun i j => raw11656 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11656step0 raw11656; decide +kernel
      have hl : raw11656step0Labels = raw11656Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11656 raw11656Labels permutation173 permutation2
    _ = mixedMoment B node2730 node2730Labels := by rfl

def raw11657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11657Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11657step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11657 raw11657Labels = mixedMoment B node2616 node2616Labels := by
  calc
    mixedMoment B raw11657 raw11657Labels = mixedMoment B raw11657step0 raw11657step0Labels := by
      have ha : raw11657step0 = (fun i j => raw11657 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11657step0 raw11657; decide +kernel
      have hl : raw11657step0Labels = raw11657Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11657 raw11657Labels permutation179 permutation2
    _ = mixedMoment B node2616 node2616Labels := by rfl

def raw11658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw11658Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11658step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw11658step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11658 raw11658Labels = mixedMoment B node2616 node2616Labels := by
  calc
    mixedMoment B raw11658 raw11658Labels = mixedMoment B raw11658step0 raw11658step0Labels := by
      have ha : raw11658step0 = (fun i j => raw11658 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11658step0 raw11658; decide +kernel
      have hl : raw11658step0Labels = raw11658Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11658 raw11658Labels permutation177 permutation2
    _ = mixedMoment B node2616 node2616Labels := by rfl

def raw11659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11659Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11659step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11659step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11659 raw11659Labels = mixedMoment B node2614 node2614Labels := by
  calc
    mixedMoment B raw11659 raw11659Labels = mixedMoment B raw11659step0 raw11659step0Labels := by
      have ha : raw11659step0 = (fun i j => raw11659 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11659step0 raw11659; decide +kernel
      have hl : raw11659step0Labels = raw11659Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11659 raw11659Labels permutation176 permutation2
    _ = mixedMoment B node2614 node2614Labels := by rfl

def raw11660 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11660step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11660step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11660step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11660step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11660 raw11660Labels = mixedMoment B node5263 node5263Labels := by
  calc
    mixedMoment B raw11660 raw11660Labels = mixedMoment B raw11660step0 raw11660step0Labels := by
      have ha : raw11660step0 = (fun i j => raw11660 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11660step0 raw11660; decide +kernel
      have hl : raw11660step0Labels = raw11660Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11660 raw11660Labels permutation180 permutation7
    mixedMoment B raw11660step0 raw11660step0Labels = mixedMoment B raw11660step1 raw11660step1Labels := by
      have ha : raw11660step1 = raw11660step0 := by apply Matrix.ext; unfold raw11660step1 raw11660step0; decide +kernel
      have hl : raw11660step0Labels = labelEmbedding10 ∘ raw11660step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11660step0 raw11660step0Labels raw11660step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5263 node5263Labels := by rfl

def raw11661 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11661Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11661step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11661step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11661step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11661step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11661 raw11661Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw11661 raw11661Labels = mixedMoment B raw11661step0 raw11661step0Labels := by
      have hz : ∀ j, raw11661 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11661step0 = (fun i j => raw11661 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11661step0 raw11661; decide +kernel
      have hl : raw11661step0Labels = raw11661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11661 raw11661Labels permutation346 hz
    mixedMoment B raw11661step0 raw11661step0Labels = mixedMoment B raw11661step1 raw11661step1Labels := by
      have ha : raw11661step1 = (fun i j => raw11661step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11661step1 raw11661step0; decide +kernel
      have hl : raw11661step1Labels = raw11661step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11661step0 raw11661step0Labels permutation36 permutation7
    mixedMoment B raw11661step1 raw11661step1Labels = mixedMoment B raw11661step2 raw11661step2Labels := by
      have ha : raw11661step2 = raw11661step1 := by apply Matrix.ext; unfold raw11661step2 raw11661step1; decide +kernel
      have hl : raw11661step1Labels = labelEmbedding10 ∘ raw11661step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11661step1 raw11661step1Labels raw11661step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw11662 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11662step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11662step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11662step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11662step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11662 raw11662Labels = mixedMoment B node5255 node5255Labels := by
  calc
    mixedMoment B raw11662 raw11662Labels = mixedMoment B raw11662step0 raw11662step0Labels := by
      have ha : raw11662step0 = (fun i j => raw11662 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11662step0 raw11662; decide +kernel
      have hl : raw11662step0Labels = raw11662Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11662 raw11662Labels permutation181 permutation7
    mixedMoment B raw11662step0 raw11662step0Labels = mixedMoment B raw11662step1 raw11662step1Labels := by
      have ha : raw11662step1 = raw11662step0 := by apply Matrix.ext; unfold raw11662step1 raw11662step0; decide +kernel
      have hl : raw11662step0Labels = labelEmbedding10 ∘ raw11662step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11662step0 raw11662step0Labels raw11662step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5255 node5255Labels := by rfl

def raw11663 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11663step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11663step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11663step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11663step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11663 raw11663Labels = mixedMoment B node5255 node5255Labels := by
  calc
    mixedMoment B raw11663 raw11663Labels = mixedMoment B raw11663step0 raw11663step0Labels := by
      have ha : raw11663step0 = (fun i j => raw11663 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11663step0 raw11663; decide +kernel
      have hl : raw11663step0Labels = raw11663Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11663 raw11663Labels permutation180 permutation7
    mixedMoment B raw11663step0 raw11663step0Labels = mixedMoment B raw11663step1 raw11663step1Labels := by
      have ha : raw11663step1 = raw11663step0 := by apply Matrix.ext; unfold raw11663step1 raw11663step0; decide +kernel
      have hl : raw11663step0Labels = labelEmbedding10 ∘ raw11663step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11663step0 raw11663step0Labels raw11663step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5255 node5255Labels := by rfl

def raw11664 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11664step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11664step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11664step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11664step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11664 raw11664Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw11664 raw11664Labels = mixedMoment B raw11664step0 raw11664step0Labels := by
      have ha : raw11664step0 = (fun i j => raw11664 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11664step0 raw11664; decide +kernel
      have hl : raw11664step0Labels = raw11664Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11664 raw11664Labels permutation180 permutation7
    mixedMoment B raw11664step0 raw11664step0Labels = mixedMoment B raw11664step1 raw11664step1Labels := by
      have ha : raw11664step1 = raw11664step0 := by apply Matrix.ext; unfold raw11664step1 raw11664step0; decide +kernel
      have hl : raw11664step0Labels = labelEmbedding10 ∘ raw11664step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11664step0 raw11664step0Labels raw11664step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw11665 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw11665step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11665step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11665step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11665step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11665 raw11665Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw11665 raw11665Labels = mixedMoment B raw11665step0 raw11665step0Labels := by
      have hz : ∀ j, raw11665 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11665step0 = (fun i j => raw11665 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11665step0 raw11665; decide +kernel
      have hl : raw11665step0Labels = raw11665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11665 raw11665Labels permutation265 hz
    mixedMoment B raw11665step0 raw11665step0Labels = mixedMoment B raw11665step1 raw11665step1Labels := by
      have ha : raw11665step1 = (fun i j => raw11665step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11665step1 raw11665step0; decide +kernel
      have hl : raw11665step1Labels = raw11665step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11665step0 raw11665step0Labels permutation40 permutation4
    mixedMoment B raw11665step1 raw11665step1Labels = mixedMoment B raw11665step2 raw11665step2Labels := by
      have ha : raw11665step2 = -raw11665step1 := by apply Matrix.ext; change ∀ i j, raw11665step2 i j = -(raw11665step1 i j); unfold raw11665step2 raw11665step1; decide +kernel
      have hl : raw11665step2Labels = raw11665step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11665step2 raw11665step2Labels = mixedMoment B raw11665step3 raw11665step3Labels := by
      have ha : raw11665step3 = raw11665step2 := by apply Matrix.ext; unfold raw11665step3 raw11665step2; decide +kernel
      have hl : raw11665step2Labels = labelEmbedding7 ∘ raw11665step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11665step2 raw11665step2Labels raw11665step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw11666 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11666step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11666step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11666step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11666step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11666step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11666step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11666step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11666 raw11666Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw11666 raw11666Labels = mixedMoment B raw11666step0 raw11666step0Labels := by
      have hz : ∀ j, raw11666 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11666step0 = (fun i j => raw11666 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11666step0 raw11666; decide +kernel
      have hl : raw11666step0Labels = raw11666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11666 raw11666Labels permutation346 hz
    mixedMoment B raw11666step0 raw11666step0Labels = mixedMoment B raw11666step1 raw11666step1Labels := by
      have hz : ∀ j, raw11666step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11666step1 = (fun i j => raw11666step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11666step1 raw11666step0; decide +kernel
      have hl : raw11666step1Labels = raw11666step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11666step0 raw11666step0Labels permutation56 hz
    mixedMoment B raw11666step1 raw11666step1Labels = mixedMoment B raw11666step2 raw11666step2Labels := by
      have ha : raw11666step2 = (fun i j => raw11666step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11666step2 raw11666step1; decide +kernel
      have hl : raw11666step2Labels = raw11666step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11666step1 raw11666step1Labels permutation8 permutation6
    mixedMoment B raw11666step2 raw11666step2Labels = mixedMoment B raw11666step3 raw11666step3Labels := by
      have ha : raw11666step3 = raw11666step2 := by apply Matrix.ext; unfold raw11666step3 raw11666step2; decide +kernel
      have hl : raw11666step2Labels = labelEmbedding9 ∘ raw11666step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11666step2 raw11666step2Labels raw11666step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw11667 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11667step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11667step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11667step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11667 raw11667Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw11667 raw11667Labels = mixedMoment B raw11667step0 raw11667step0Labels := by
      have hz : ∀ j, raw11667 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11667step0 = (fun i j => raw11667 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11667step0 raw11667; decide +kernel
      have hl : raw11667step0Labels = raw11667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11667 raw11667Labels permutation265 hz
    mixedMoment B raw11667step0 raw11667step0Labels = mixedMoment B raw11667step1 raw11667step1Labels := by
      have ha : raw11667step1 = (fun i j => raw11667step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11667step1 raw11667step0; decide +kernel
      have hl : raw11667step1Labels = raw11667step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11667step0 raw11667step0Labels permutation32 permutation6
    mixedMoment B raw11667step1 raw11667step1Labels = mixedMoment B raw11667step2 raw11667step2Labels := by
      have ha : raw11667step2 = raw11667step1 := by apply Matrix.ext; unfold raw11667step2 raw11667step1; decide +kernel
      have hl : raw11667step1Labels = labelEmbedding9 ∘ raw11667step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11667step1 raw11667step1Labels raw11667step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw11668 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11668step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11668step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11668step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11668 raw11668Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw11668 raw11668Labels = mixedMoment B raw11668step0 raw11668step0Labels := by
      have hz : ∀ j, raw11668 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11668step0 = (fun i j => raw11668 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11668step0 raw11668; decide +kernel
      have hl : raw11668step0Labels = raw11668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11668 raw11668Labels permutation265 hz
    mixedMoment B raw11668step0 raw11668step0Labels = mixedMoment B raw11668step1 raw11668step1Labels := by
      have ha : raw11668step1 = (fun i j => raw11668step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11668step1 raw11668step0; decide +kernel
      have hl : raw11668step1Labels = raw11668step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11668step0 raw11668step0Labels permutation34 permutation6
    mixedMoment B raw11668step1 raw11668step1Labels = mixedMoment B raw11668step2 raw11668step2Labels := by
      have ha : raw11668step2 = raw11668step1 := by apply Matrix.ext; unfold raw11668step2 raw11668step1; decide +kernel
      have hl : raw11668step1Labels = labelEmbedding9 ∘ raw11668step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11668step1 raw11668step1Labels raw11668step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw11669 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11669step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11669step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11669 raw11669Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw11669 raw11669Labels = mixedMoment B raw11669step0 raw11669step0Labels := by
      have hz : ∀ j, raw11669 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11669step0 = (fun i j => raw11669 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11669step0 raw11669; decide +kernel
      have hl : raw11669step0Labels = raw11669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11669 raw11669Labels permutation265 hz
    mixedMoment B raw11669step0 raw11669step0Labels = mixedMoment B raw11669step1 raw11669step1Labels := by
      have ha : raw11669step1 = (fun i j => raw11669step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11669step1 raw11669step0; decide +kernel
      have hl : raw11669step1Labels = raw11669step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11669step0 raw11669step0Labels permutation32 permutation6
    mixedMoment B raw11669step1 raw11669step1Labels = mixedMoment B raw11669step2 raw11669step2Labels := by
      have ha : raw11669step2 = raw11669step1 := by apply Matrix.ext; unfold raw11669step2 raw11669step1; decide +kernel
      have hl : raw11669step1Labels = labelEmbedding9 ∘ raw11669step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11669step1 raw11669step1Labels raw11669step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw11670 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11670step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw11670step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11670step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11670step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11670step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11670step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11670 raw11670Labels = mixedMoment B node4795 node4795Labels := by
  calc
    mixedMoment B raw11670 raw11670Labels = mixedMoment B raw11670step0 raw11670step0Labels := by
      have ha : raw11670step0 = (fun i j => raw11670 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11670step0 raw11670; decide +kernel
      have hl : raw11670step0Labels = raw11670Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11670 raw11670Labels permutation160 permutation4
    mixedMoment B raw11670step0 raw11670step0Labels = mixedMoment B raw11670step1 raw11670step1Labels := by
      have ha : raw11670step1 = -raw11670step0 := by apply Matrix.ext; change ∀ i j, raw11670step1 i j = -(raw11670step0 i j); unfold raw11670step1 raw11670step0; decide +kernel
      have hl : raw11670step1Labels = raw11670step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11670step1 raw11670step1Labels = mixedMoment B raw11670step2 raw11670step2Labels := by
      have ha : raw11670step2 = raw11670step1 := by apply Matrix.ext; unfold raw11670step2 raw11670step1; decide +kernel
      have hl : raw11670step1Labels = labelEmbedding7 ∘ raw11670step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11670step1 raw11670step1Labels raw11670step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4795 node4795Labels := by rfl

def raw11671 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11671step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11671step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11671step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11671step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11671 raw11671Labels = mixedMoment B node5230 node5230Labels := by
  calc
    mixedMoment B raw11671 raw11671Labels = mixedMoment B raw11671step0 raw11671step0Labels := by
      have ha : raw11671step0 = (fun i j => raw11671 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11671step0 raw11671; decide +kernel
      have hl : raw11671step0Labels = raw11671Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11671 raw11671Labels permutation152 permutation6
    mixedMoment B raw11671step0 raw11671step0Labels = mixedMoment B raw11671step1 raw11671step1Labels := by
      have ha : raw11671step1 = raw11671step0 := by apply Matrix.ext; unfold raw11671step1 raw11671step0; decide +kernel
      have hl : raw11671step0Labels = labelEmbedding9 ∘ raw11671step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11671step0 raw11671step0Labels raw11671step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5230 node5230Labels := by rfl

def raw11672 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11672step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11672step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11672step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11672step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11672 raw11672Labels = mixedMoment B node5262 node5262Labels := by
  calc
    mixedMoment B raw11672 raw11672Labels = mixedMoment B raw11672step0 raw11672step0Labels := by
      have ha : raw11672step0 = (fun i j => raw11672 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11672step0 raw11672; decide +kernel
      have hl : raw11672step0Labels = raw11672Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11672 raw11672Labels permutation152 permutation6
    mixedMoment B raw11672step0 raw11672step0Labels = mixedMoment B raw11672step1 raw11672step1Labels := by
      have ha : raw11672step1 = raw11672step0 := by apply Matrix.ext; unfold raw11672step1 raw11672step0; decide +kernel
      have hl : raw11672step0Labels = labelEmbedding9 ∘ raw11672step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11672step0 raw11672step0Labels raw11672step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5262 node5262Labels := by rfl

def raw11673 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11673step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11673step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11673step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11673step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11673 raw11673Labels = mixedMoment B node5262 node5262Labels := by
  calc
    mixedMoment B raw11673 raw11673Labels = mixedMoment B raw11673step0 raw11673step0Labels := by
      have ha : raw11673step0 = (fun i j => raw11673 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11673step0 raw11673; decide +kernel
      have hl : raw11673step0Labels = raw11673Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11673 raw11673Labels permutation154 permutation6
    mixedMoment B raw11673step0 raw11673step0Labels = mixedMoment B raw11673step1 raw11673step1Labels := by
      have ha : raw11673step1 = raw11673step0 := by apply Matrix.ext; unfold raw11673step1 raw11673step0; decide +kernel
      have hl : raw11673step0Labels = labelEmbedding9 ∘ raw11673step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11673step0 raw11673step0Labels raw11673step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5262 node5262Labels := by rfl

def raw11674 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11674step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11674step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11674step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11674step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11674 raw11674Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw11674 raw11674Labels = mixedMoment B raw11674step0 raw11674step0Labels := by
      have ha : raw11674step0 = (fun i j => raw11674 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11674step0 raw11674; decide +kernel
      have hl : raw11674step0Labels = raw11674Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11674 raw11674Labels permutation152 permutation6
    mixedMoment B raw11674step0 raw11674step0Labels = mixedMoment B raw11674step1 raw11674step1Labels := by
      have ha : raw11674step1 = raw11674step0 := by apply Matrix.ext; unfold raw11674step1 raw11674step0; decide +kernel
      have hl : raw11674step0Labels = labelEmbedding9 ∘ raw11674step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11674step0 raw11674step0Labels raw11674step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw11675 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11675step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw11675step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11675step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11675step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11675step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11675step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11675 raw11675Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw11675 raw11675Labels = mixedMoment B raw11675step0 raw11675step0Labels := by
      have ha : raw11675step0 = (fun i j => raw11675 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11675step0 raw11675; decide +kernel
      have hl : raw11675step0Labels = raw11675Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11675 raw11675Labels permutation164 permutation4
    mixedMoment B raw11675step0 raw11675step0Labels = mixedMoment B raw11675step1 raw11675step1Labels := by
      have ha : raw11675step1 = -raw11675step0 := by apply Matrix.ext; change ∀ i j, raw11675step1 i j = -(raw11675step0 i j); unfold raw11675step1 raw11675step0; decide +kernel
      have hl : raw11675step1Labels = raw11675step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11675step1 raw11675step1Labels = mixedMoment B raw11675step2 raw11675step2Labels := by
      have ha : raw11675step2 = raw11675step1 := by apply Matrix.ext; unfold raw11675step2 raw11675step1; decide +kernel
      have hl : raw11675step1Labels = labelEmbedding7 ∘ raw11675step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11675step1 raw11675step1Labels raw11675step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw11676 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11676step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11676step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11676step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11676step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11676 raw11676Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw11676 raw11676Labels = mixedMoment B raw11676step0 raw11676step0Labels := by
      have ha : raw11676step0 = (fun i j => raw11676 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11676step0 raw11676; decide +kernel
      have hl : raw11676step0Labels = raw11676Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11676 raw11676Labels permutation154 permutation6
    mixedMoment B raw11676step0 raw11676step0Labels = mixedMoment B raw11676step1 raw11676step1Labels := by
      have ha : raw11676step1 = raw11676step0 := by apply Matrix.ext; unfold raw11676step1 raw11676step0; decide +kernel
      have hl : raw11676step0Labels = labelEmbedding9 ∘ raw11676step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11676step0 raw11676step0Labels raw11676step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

def raw11677 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11677step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11677step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11677step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11677 raw11677Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw11677 raw11677Labels = mixedMoment B raw11677step0 raw11677step0Labels := by
      have hz : ∀ j, raw11677 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11677step0 = (fun i j => raw11677 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11677step0 raw11677; decide +kernel
      have hl : raw11677step0Labels = raw11677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11677 raw11677Labels permutation346 hz
    mixedMoment B raw11677step0 raw11677step0Labels = mixedMoment B raw11677step1 raw11677step1Labels := by
      have ha : raw11677step1 = (fun i j => raw11677step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11677step1 raw11677step0; decide +kernel
      have hl : raw11677step1Labels = raw11677step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11677step0 raw11677step0Labels permutation34 permutation6
    mixedMoment B raw11677step1 raw11677step1Labels = mixedMoment B raw11677step2 raw11677step2Labels := by
      have ha : raw11677step2 = raw11677step1 := by apply Matrix.ext; unfold raw11677step2 raw11677step1; decide +kernel
      have hl : raw11677step1Labels = labelEmbedding9 ∘ raw11677step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11677step1 raw11677step1Labels raw11677step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw11678 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11678step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11678step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11678step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11678step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11678 raw11678Labels = mixedMoment B node5255 node5255Labels := by
  calc
    mixedMoment B raw11678 raw11678Labels = mixedMoment B raw11678step0 raw11678step0Labels := by
      have ha : raw11678step0 = (fun i j => raw11678 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11678step0 raw11678; decide +kernel
      have hl : raw11678step0Labels = raw11678Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11678 raw11678Labels permutation154 permutation6
    mixedMoment B raw11678step0 raw11678step0Labels = mixedMoment B raw11678step1 raw11678step1Labels := by
      have ha : raw11678step1 = raw11678step0 := by apply Matrix.ext; unfold raw11678step1 raw11678step0; decide +kernel
      have hl : raw11678step0Labels = labelEmbedding9 ∘ raw11678step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11678step0 raw11678step0Labels raw11678step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5255 node5255Labels := by rfl

def raw11679 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11679step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11679step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11679step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11679step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11679 raw11679Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw11679 raw11679Labels = mixedMoment B raw11679step0 raw11679step0Labels := by
      have ha : raw11679step0 = (fun i j => raw11679 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11679step0 raw11679; decide +kernel
      have hl : raw11679step0Labels = raw11679Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11679 raw11679Labels permutation154 permutation6
    mixedMoment B raw11679step0 raw11679step0Labels = mixedMoment B raw11679step1 raw11679step1Labels := by
      have ha : raw11679step1 = raw11679step0 := by apply Matrix.ext; unfold raw11679step1 raw11679step0; decide +kernel
      have hl : raw11679step0Labels = labelEmbedding9 ∘ raw11679step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11679step0 raw11679step0Labels raw11679step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw11680 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11680step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw11680step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11680step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11680step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11680step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11680step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11680 raw11680Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw11680 raw11680Labels = mixedMoment B raw11680step0 raw11680step0Labels := by
      have ha : raw11680step0 = (fun i j => raw11680 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11680step0 raw11680; decide +kernel
      have hl : raw11680step0Labels = raw11680Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11680 raw11680Labels permutation158 permutation4
    mixedMoment B raw11680step0 raw11680step0Labels = mixedMoment B raw11680step1 raw11680step1Labels := by
      have ha : raw11680step1 = -raw11680step0 := by apply Matrix.ext; change ∀ i j, raw11680step1 i j = -(raw11680step0 i j); unfold raw11680step1 raw11680step0; decide +kernel
      have hl : raw11680step1Labels = raw11680step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11680step1 raw11680step1Labels = mixedMoment B raw11680step2 raw11680step2Labels := by
      have ha : raw11680step2 = raw11680step1 := by apply Matrix.ext; unfold raw11680step2 raw11680step1; decide +kernel
      have hl : raw11680step1Labels = labelEmbedding7 ∘ raw11680step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11680step1 raw11680step1Labels raw11680step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw11681 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11681step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11681step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11681step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11681step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11681 raw11681Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw11681 raw11681Labels = mixedMoment B raw11681step0 raw11681step0Labels := by
      have ha : raw11681step0 = (fun i j => raw11681 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11681step0 raw11681; decide +kernel
      have hl : raw11681step0Labels = raw11681Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11681 raw11681Labels permutation152 permutation6
    mixedMoment B raw11681step0 raw11681step0Labels = mixedMoment B raw11681step1 raw11681step1Labels := by
      have ha : raw11681step1 = raw11681step0 := by apply Matrix.ext; unfold raw11681step1 raw11681step0; decide +kernel
      have hl : raw11681step0Labels = labelEmbedding9 ∘ raw11681step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11681step0 raw11681step0Labels raw11681step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

def raw11682 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11682step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11682step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11682step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11682step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11682 raw11682Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw11682 raw11682Labels = mixedMoment B raw11682step0 raw11682step0Labels := by
      have hz : ∀ j, raw11682 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11682step0 = (fun i j => raw11682 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11682step0 raw11682; decide +kernel
      have hl : raw11682step0Labels = raw11682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11682 raw11682Labels permutation346 hz
    mixedMoment B raw11682step0 raw11682step0Labels = mixedMoment B raw11682step1 raw11682step1Labels := by
      have ha : raw11682step1 = (fun i j => raw11682step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11682step1 raw11682step0; decide +kernel
      have hl : raw11682step1Labels = raw11682step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11682step0 raw11682step0Labels permutation32 permutation6
    mixedMoment B raw11682step1 raw11682step1Labels = mixedMoment B raw11682step2 raw11682step2Labels := by
      have ha : raw11682step2 = raw11682step1 := by apply Matrix.ext; unfold raw11682step2 raw11682step1; decide +kernel
      have hl : raw11682step1Labels = labelEmbedding9 ∘ raw11682step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11682step1 raw11682step1Labels raw11682step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw11683 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11683step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11683step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11683step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11683step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11683 raw11683Labels = mixedMoment B node5255 node5255Labels := by
  calc
    mixedMoment B raw11683 raw11683Labels = mixedMoment B raw11683step0 raw11683step0Labels := by
      have ha : raw11683step0 = (fun i j => raw11683 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11683step0 raw11683; decide +kernel
      have hl : raw11683step0Labels = raw11683Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11683 raw11683Labels permutation152 permutation6
    mixedMoment B raw11683step0 raw11683step0Labels = mixedMoment B raw11683step1 raw11683step1Labels := by
      have ha : raw11683step1 = raw11683step0 := by apply Matrix.ext; unfold raw11683step1 raw11683step0; decide +kernel
      have hl : raw11683step0Labels = labelEmbedding9 ∘ raw11683step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11683step0 raw11683step0Labels raw11683step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5255 node5255Labels := by rfl

def raw11684 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw11684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11684step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11684step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11684step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11684step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11684 raw11684Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw11684 raw11684Labels = mixedMoment B raw11684step0 raw11684step0Labels := by
      have ha : raw11684step0 = (fun i j => raw11684 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11684step0 raw11684; decide +kernel
      have hl : raw11684step0Labels = raw11684Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11684 raw11684Labels permutation152 permutation6
    mixedMoment B raw11684step0 raw11684step0Labels = mixedMoment B raw11684step1 raw11684step1Labels := by
      have ha : raw11684step1 = raw11684step0 := by apply Matrix.ext; unfold raw11684step1 raw11684step0; decide +kernel
      have hl : raw11684step0Labels = labelEmbedding9 ∘ raw11684step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11684step0 raw11684step0Labels raw11684step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw11685 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11685step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw11685step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11685step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw11685step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11685step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw11685step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11685 raw11685Labels = mixedMoment B node4792 node4792Labels := by
  calc
    mixedMoment B raw11685 raw11685Labels = mixedMoment B raw11685step0 raw11685step0Labels := by
      have ha : raw11685step0 = (fun i j => raw11685 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11685step0 raw11685; decide +kernel
      have hl : raw11685step0Labels = raw11685Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11685 raw11685Labels permutation160 permutation4
    mixedMoment B raw11685step0 raw11685step0Labels = mixedMoment B raw11685step1 raw11685step1Labels := by
      have ha : raw11685step1 = -raw11685step0 := by apply Matrix.ext; change ∀ i j, raw11685step1 i j = -(raw11685step0 i j); unfold raw11685step1 raw11685step0; decide +kernel
      have hl : raw11685step1Labels = raw11685step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11685step1 raw11685step1Labels = mixedMoment B raw11685step2 raw11685step2Labels := by
      have ha : raw11685step2 = raw11685step1 := by apply Matrix.ext; unfold raw11685step2 raw11685step1; decide +kernel
      have hl : raw11685step1Labels = labelEmbedding7 ∘ raw11685step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11685step1 raw11685step1Labels raw11685step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4792 node4792Labels := by rfl

def raw11686 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11686step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw11686step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11686step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw11686step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11686 raw11686Labels = mixedMoment B node5066 node5066Labels := by
  calc
    mixedMoment B raw11686 raw11686Labels = mixedMoment B raw11686step0 raw11686step0Labels := by
      have ha : raw11686step0 = (fun i j => raw11686 (permutation639 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11686step0 raw11686; decide +kernel
      have hl : raw11686step0Labels = raw11686Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11686 raw11686Labels permutation639 permutation5
    mixedMoment B raw11686step0 raw11686step0Labels = mixedMoment B raw11686step1 raw11686step1Labels := by
      have ha : raw11686step1 = raw11686step0 := by apply Matrix.ext; unfold raw11686step1 raw11686step0; decide +kernel
      have hl : raw11686step0Labels = labelEmbedding8 ∘ raw11686step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11686step0 raw11686step0Labels raw11686step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5066 node5066Labels := by rfl

def raw11687 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11687step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw11687step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11687step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw11687step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11687 raw11687Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw11687 raw11687Labels = mixedMoment B raw11687step0 raw11687step0Labels := by
      have hz : ∀ j, raw11687 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11687step0 = (fun i j => raw11687 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11687step0 raw11687; decide +kernel
      have hl : raw11687step0Labels = raw11687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11687 raw11687Labels permutation346 hz
    mixedMoment B raw11687step0 raw11687step0Labels = mixedMoment B raw11687step1 raw11687step1Labels := by
      have ha : raw11687step1 = (fun i j => raw11687step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11687step1 raw11687step0; decide +kernel
      have hl : raw11687step1Labels = raw11687step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11687step0 raw11687step0Labels permutation32 permutation6
    mixedMoment B raw11687step1 raw11687step1Labels = mixedMoment B raw11687step2 raw11687step2Labels := by
      have ha : raw11687step2 = raw11687step1 := by apply Matrix.ext; unfold raw11687step2 raw11687step1; decide +kernel
      have hl : raw11687step1Labels = labelEmbedding9 ∘ raw11687step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11687step1 raw11687step1Labels raw11687step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw11688 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11688step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw11688step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11688step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw11688step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11688 raw11688Labels = mixedMoment B node5077 node5077Labels := by
  calc
    mixedMoment B raw11688 raw11688Labels = mixedMoment B raw11688step0 raw11688step0Labels := by
      have ha : raw11688step0 = (fun i j => raw11688 (permutation644 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11688step0 raw11688; decide +kernel
      have hl : raw11688step0Labels = raw11688Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11688 raw11688Labels permutation644 permutation5
    mixedMoment B raw11688step0 raw11688step0Labels = mixedMoment B raw11688step1 raw11688step1Labels := by
      have ha : raw11688step1 = raw11688step0 := by apply Matrix.ext; unfold raw11688step1 raw11688step0; decide +kernel
      have hl : raw11688step0Labels = labelEmbedding8 ∘ raw11688step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11688step0 raw11688step0Labels raw11688step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5077 node5077Labels := by rfl

def raw11689 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw11689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11689step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw11689step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw11689step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw11689step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11689 raw11689Labels = mixedMoment B node5077 node5077Labels := by
  calc
    mixedMoment B raw11689 raw11689Labels = mixedMoment B raw11689step0 raw11689step0Labels := by
      have ha : raw11689step0 = (fun i j => raw11689 (permutation638 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11689step0 raw11689; decide +kernel
      have hl : raw11689step0Labels = raw11689Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11689 raw11689Labels permutation638 permutation5
    mixedMoment B raw11689step0 raw11689step0Labels = mixedMoment B raw11689step1 raw11689step1Labels := by
      have ha : raw11689step1 = raw11689step0 := by apply Matrix.ext; unfold raw11689step1 raw11689step0; decide +kernel
      have hl : raw11689step0Labels = labelEmbedding8 ∘ raw11689step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11689step0 raw11689step0Labels raw11689step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5077 node5077Labels := by rfl

def raw11690 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11690Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11690step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11690step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11690 raw11690Labels = mixedMoment B node3036 node3036Labels := by
  calc
    mixedMoment B raw11690 raw11690Labels = mixedMoment B raw11690step0 raw11690step0Labels := by
      have ha : raw11690step0 = (fun i j => raw11690 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11690step0 raw11690; decide +kernel
      have hl : raw11690step0Labels = raw11690Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11690 raw11690Labels permutation152 permutation6
    _ = mixedMoment B node3036 node3036Labels := by rfl

def raw11691 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11691Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11691step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11691step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11691 raw11691Labels = mixedMoment B node3099 node3099Labels := by
  calc
    mixedMoment B raw11691 raw11691Labels = mixedMoment B raw11691step0 raw11691step0Labels := by
      have hz : ∀ j, raw11691 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11691step0 = (fun i j => raw11691 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11691step0 raw11691; decide +kernel
      have hl : raw11691step0Labels = raw11691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11691 raw11691Labels permutation346 hz
    mixedMoment B raw11691step0 raw11691step0Labels = mixedMoment B raw11691step1 raw11691step1Labels := by
      have ha : raw11691step1 = (fun i j => raw11691step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11691step1 raw11691step0; decide +kernel
      have hl : raw11691step1Labels = raw11691step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11691step0 raw11691step0Labels permutation32 permutation6
    _ = mixedMoment B node3099 node3099Labels := by rfl

def raw11692 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11692Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11692step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11692step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11692 raw11692Labels = mixedMoment B node3084 node3084Labels := by
  calc
    mixedMoment B raw11692 raw11692Labels = mixedMoment B raw11692step0 raw11692step0Labels := by
      have ha : raw11692step0 = (fun i j => raw11692 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11692step0 raw11692; decide +kernel
      have hl : raw11692step0Labels = raw11692Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11692 raw11692Labels permutation152 permutation6
    _ = mixedMoment B node3084 node3084Labels := by rfl

def raw11693 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11693Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11693step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11693step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11693 raw11693Labels = mixedMoment B node3084 node3084Labels := by
  calc
    mixedMoment B raw11693 raw11693Labels = mixedMoment B raw11693step0 raw11693step0Labels := by
      have ha : raw11693step0 = (fun i j => raw11693 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11693step0 raw11693; decide +kernel
      have hl : raw11693step0Labels = raw11693Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11693 raw11693Labels permutation154 permutation6
    _ = mixedMoment B node3084 node3084Labels := by rfl

def raw11694 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11694Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11694step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11694step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11694 raw11694Labels = mixedMoment B node3087 node3087Labels := by
  calc
    mixedMoment B raw11694 raw11694Labels = mixedMoment B raw11694step0 raw11694step0Labels := by
      have ha : raw11694step0 = (fun i j => raw11694 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11694step0 raw11694; decide +kernel
      have hl : raw11694step0Labels = raw11694Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11694 raw11694Labels permutation152 permutation6
    _ = mixedMoment B node3087 node3087Labels := by rfl

def raw11695 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11695Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11695step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11695step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11695 raw11695Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw11695 raw11695Labels = mixedMoment B raw11695step0 raw11695step0Labels := by
      have hz : ∀ j, raw11695 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11695step0 = (fun i j => raw11695 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11695step0 raw11695; decide +kernel
      have hl : raw11695step0Labels = raw11695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11695 raw11695Labels permutation265 hz
    mixedMoment B raw11695step0 raw11695step0Labels = mixedMoment B raw11695step1 raw11695step1Labels := by
      have ha : raw11695step1 = (fun i j => raw11695step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11695step1 raw11695step0; decide +kernel
      have hl : raw11695step1Labels = raw11695step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11695step0 raw11695step0Labels permutation32 permutation6
    _ = mixedMoment B node2262 node2262Labels := by rfl

def raw11696 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11696Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11696step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11696step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11696step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11696step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11696step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11696 raw11696Labels = mixedMoment B node2784 node2784Labels := by
  calc
    mixedMoment B raw11696 raw11696Labels = mixedMoment B raw11696step0 raw11696step0Labels := by
      have hz : ∀ j, raw11696 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11696step0 = (fun i j => raw11696 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11696step0 raw11696; decide +kernel
      have hl : raw11696step0Labels = raw11696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11696 raw11696Labels permutation346 hz
    mixedMoment B raw11696step0 raw11696step0Labels = mixedMoment B raw11696step1 raw11696step1Labels := by
      have hz : ∀ j, raw11696step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11696step1 = (fun i j => raw11696step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11696step1 raw11696step0; decide +kernel
      have hl : raw11696step1Labels = raw11696step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11696step0 raw11696step0Labels permutation56 hz
    mixedMoment B raw11696step1 raw11696step1Labels = mixedMoment B raw11696step2 raw11696step2Labels := by
      have ha : raw11696step2 = (fun i j => raw11696step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11696step2 raw11696step1; decide +kernel
      have hl : raw11696step2Labels = raw11696step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11696step1 raw11696step1Labels permutation8 permutation6
    _ = mixedMoment B node2784 node2784Labels := by rfl

def raw11697 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11697Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11697step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11697step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11697 raw11697Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw11697 raw11697Labels = mixedMoment B raw11697step0 raw11697step0Labels := by
      have hz : ∀ j, raw11697 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11697step0 = (fun i j => raw11697 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11697step0 raw11697; decide +kernel
      have hl : raw11697step0Labels = raw11697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11697 raw11697Labels permutation265 hz
    mixedMoment B raw11697step0 raw11697step0Labels = mixedMoment B raw11697step1 raw11697step1Labels := by
      have ha : raw11697step1 = (fun i j => raw11697step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11697step1 raw11697step0; decide +kernel
      have hl : raw11697step1Labels = raw11697step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11697step0 raw11697step0Labels permutation32 permutation6
    _ = mixedMoment B node2763 node2763Labels := by rfl

def raw11698 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11698Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11698step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11698step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11698 raw11698Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw11698 raw11698Labels = mixedMoment B raw11698step0 raw11698step0Labels := by
      have hz : ∀ j, raw11698 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11698step0 = (fun i j => raw11698 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11698step0 raw11698; decide +kernel
      have hl : raw11698step0Labels = raw11698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11698 raw11698Labels permutation265 hz
    mixedMoment B raw11698step0 raw11698step0Labels = mixedMoment B raw11698step1 raw11698step1Labels := by
      have ha : raw11698step1 = (fun i j => raw11698step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11698step1 raw11698step0; decide +kernel
      have hl : raw11698step1Labels = raw11698step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11698step0 raw11698step0Labels permutation34 permutation6
    _ = mixedMoment B node2763 node2763Labels := by rfl

def raw11699 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11699Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11699step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11699 raw11699Labels = mixedMoment B node2766 node2766Labels := by
  calc
    mixedMoment B raw11699 raw11699Labels = mixedMoment B raw11699step0 raw11699step0Labels := by
      have hz : ∀ j, raw11699 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11699step0 = (fun i j => raw11699 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11699step0 raw11699; decide +kernel
      have hl : raw11699step0Labels = raw11699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11699 raw11699Labels permutation265 hz
    mixedMoment B raw11699step0 raw11699step0Labels = mixedMoment B raw11699step1 raw11699step1Labels := by
      have ha : raw11699step1 = (fun i j => raw11699step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11699step1 raw11699step0; decide +kernel
      have hl : raw11699step1Labels = raw11699step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11699step0 raw11699step0Labels permutation32 permutation6
    _ = mixedMoment B node2766 node2766Labels := by rfl

def raw11700 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11700Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11700step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11700step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11700 raw11700Labels = mixedMoment B node2213 node2213Labels := by
  calc
    mixedMoment B raw11700 raw11700Labels = mixedMoment B raw11700step0 raw11700step0Labels := by
      have ha : raw11700step0 = (fun i j => raw11700 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11700step0 raw11700; decide +kernel
      have hl : raw11700step0Labels = raw11700Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11700 raw11700Labels permutation152 permutation6
    _ = mixedMoment B node2213 node2213Labels := by rfl

def raw11701 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11701Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11701step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11701step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11701 raw11701Labels = mixedMoment B node2675 node2675Labels := by
  calc
    mixedMoment B raw11701 raw11701Labels = mixedMoment B raw11701step0 raw11701step0Labels := by
      have ha : raw11701step0 = (fun i j => raw11701 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11701step0 raw11701; decide +kernel
      have hl : raw11701step0Labels = raw11701Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11701 raw11701Labels permutation152 permutation6
    _ = mixedMoment B node2675 node2675Labels := by rfl

def raw11702 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11702Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11702step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11702step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11702 raw11702Labels = mixedMoment B node2727 node2727Labels := by
  calc
    mixedMoment B raw11702 raw11702Labels = mixedMoment B raw11702step0 raw11702step0Labels := by
      have ha : raw11702step0 = (fun i j => raw11702 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11702step0 raw11702; decide +kernel
      have hl : raw11702step0Labels = raw11702Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11702 raw11702Labels permutation152 permutation6
    _ = mixedMoment B node2727 node2727Labels := by rfl

def raw11703 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11703Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11703step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11703step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11703 raw11703Labels = mixedMoment B node2727 node2727Labels := by
  calc
    mixedMoment B raw11703 raw11703Labels = mixedMoment B raw11703step0 raw11703step0Labels := by
      have ha : raw11703step0 = (fun i j => raw11703 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11703step0 raw11703; decide +kernel
      have hl : raw11703step0Labels = raw11703Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11703 raw11703Labels permutation154 permutation6
    _ = mixedMoment B node2727 node2727Labels := by rfl

def raw11704 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11704Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11704step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11704step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11704 raw11704Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw11704 raw11704Labels = mixedMoment B raw11704step0 raw11704step0Labels := by
      have ha : raw11704step0 = (fun i j => raw11704 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11704step0 raw11704; decide +kernel
      have hl : raw11704step0Labels = raw11704Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11704 raw11704Labels permutation152 permutation6
    _ = mixedMoment B node2730 node2730Labels := by rfl

def raw11705 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11705Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11705step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11705step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11705 raw11705Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw11705 raw11705Labels = mixedMoment B raw11705step0 raw11705step0Labels := by
      have ha : raw11705step0 = (fun i j => raw11705 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11705step0 raw11705; decide +kernel
      have hl : raw11705step0Labels = raw11705Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11705 raw11705Labels permutation154 permutation6
    _ = mixedMoment B node2202 node2202Labels := by rfl

def raw11706 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11706Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11706step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11706step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11706 raw11706Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw11706 raw11706Labels = mixedMoment B raw11706step0 raw11706step0Labels := by
      have ha : raw11706step0 = (fun i j => raw11706 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11706step0 raw11706; decide +kernel
      have hl : raw11706step0Labels = raw11706Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11706 raw11706Labels permutation154 permutation6
    _ = mixedMoment B node2669 node2669Labels := by rfl

def raw11707 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11707Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11707step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11707step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11707 raw11707Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw11707 raw11707Labels = mixedMoment B raw11707step0 raw11707step0Labels := by
      have hz : ∀ j, raw11707 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11707step0 = (fun i j => raw11707 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11707step0 raw11707; decide +kernel
      have hl : raw11707step0Labels = raw11707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11707 raw11707Labels permutation346 hz
    mixedMoment B raw11707step0 raw11707step0Labels = mixedMoment B raw11707step1 raw11707step1Labels := by
      have ha : raw11707step1 = (fun i j => raw11707step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11707step1 raw11707step0; decide +kernel
      have hl : raw11707step1Labels = raw11707step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11707step0 raw11707step0Labels permutation34 permutation6
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw11708 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11708Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11708step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11708step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11708 raw11708Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw11708 raw11708Labels = mixedMoment B raw11708step0 raw11708step0Labels := by
      have ha : raw11708step0 = (fun i j => raw11708 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11708step0 raw11708; decide +kernel
      have hl : raw11708step0Labels = raw11708Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11708 raw11708Labels permutation154 permutation6
    _ = mixedMoment B node2718 node2718Labels := by rfl

def raw11709 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11709Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11709step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11709step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11709 raw11709Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw11709 raw11709Labels = mixedMoment B raw11709step0 raw11709step0Labels := by
      have ha : raw11709step0 = (fun i j => raw11709 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11709step0 raw11709; decide +kernel
      have hl : raw11709step0Labels = raw11709Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11709 raw11709Labels permutation154 permutation6
    _ = mixedMoment B node2721 node2721Labels := by rfl

def raw11710 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11710Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11710step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11710step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11710 raw11710Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw11710 raw11710Labels = mixedMoment B raw11710step0 raw11710step0Labels := by
      have ha : raw11710step0 = (fun i j => raw11710 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11710step0 raw11710; decide +kernel
      have hl : raw11710step0Labels = raw11710Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11710 raw11710Labels permutation152 permutation6
    _ = mixedMoment B node2202 node2202Labels := by rfl

def raw11711 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11711Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11711step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11711step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11711 raw11711Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw11711 raw11711Labels = mixedMoment B raw11711step0 raw11711step0Labels := by
      have ha : raw11711step0 = (fun i j => raw11711 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11711step0 raw11711; decide +kernel
      have hl : raw11711step0Labels = raw11711Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11711 raw11711Labels permutation152 permutation6
    _ = mixedMoment B node2669 node2669Labels := by rfl

def raw11712 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11712Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11712step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11712step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11712 raw11712Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw11712 raw11712Labels = mixedMoment B raw11712step0 raw11712step0Labels := by
      have hz : ∀ j, raw11712 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11712step0 = (fun i j => raw11712 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11712step0 raw11712; decide +kernel
      have hl : raw11712step0Labels = raw11712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11712 raw11712Labels permutation346 hz
    mixedMoment B raw11712step0 raw11712step0Labels = mixedMoment B raw11712step1 raw11712step1Labels := by
      have ha : raw11712step1 = (fun i j => raw11712step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11712step1 raw11712step0; decide +kernel
      have hl : raw11712step1Labels = raw11712step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11712step0 raw11712step0Labels permutation32 permutation6
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw11713 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11713Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11713step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11713 raw11713Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw11713 raw11713Labels = mixedMoment B raw11713step0 raw11713step0Labels := by
      have ha : raw11713step0 = (fun i j => raw11713 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11713step0 raw11713; decide +kernel
      have hl : raw11713step0Labels = raw11713Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11713 raw11713Labels permutation152 permutation6
    _ = mixedMoment B node2718 node2718Labels := by rfl

def raw11714 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw11714Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11714step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11714step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11714 raw11714Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw11714 raw11714Labels = mixedMoment B raw11714step0 raw11714step0Labels := by
      have ha : raw11714step0 = (fun i j => raw11714 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11714step0 raw11714; decide +kernel
      have hl : raw11714step0Labels = raw11714Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11714 raw11714Labels permutation152 permutation6
    _ = mixedMoment B node2721 node2721Labels := by rfl

def raw11715 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11715Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11715step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw11715step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11715 raw11715Labels = mixedMoment B node2201 node2201Labels := by
  calc
    mixedMoment B raw11715 raw11715Labels = mixedMoment B raw11715step0 raw11715step0Labels := by
      have ha : raw11715step0 = (fun i j => raw11715 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11715step0 raw11715; decide +kernel
      have hl : raw11715step0Labels = raw11715Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11715 raw11715Labels permutation152 permutation6
    _ = mixedMoment B node2201 node2201Labels := by rfl

def raw11716 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11716Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw11716step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11716 raw11716Labels = mixedMoment B node2668 node2668Labels := by
  calc
    mixedMoment B raw11716 raw11716Labels = mixedMoment B raw11716step0 raw11716step0Labels := by
      have ha : raw11716step0 = (fun i j => raw11716 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11716step0 raw11716; decide +kernel
      have hl : raw11716step0Labels = raw11716Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11716 raw11716Labels permutation152 permutation6
    _ = mixedMoment B node2668 node2668Labels := by rfl

def raw11717 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11717Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11717step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw11717step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11717 raw11717Labels = mixedMoment B node2738 node2738Labels := by
  calc
    mixedMoment B raw11717 raw11717Labels = mixedMoment B raw11717step0 raw11717step0Labels := by
      have hz : ∀ j, raw11717 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11717step0 = (fun i j => raw11717 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11717step0 raw11717; decide +kernel
      have hl : raw11717step0Labels = raw11717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11717 raw11717Labels permutation346 hz
    mixedMoment B raw11717step0 raw11717step0Labels = mixedMoment B raw11717step1 raw11717step1Labels := by
      have ha : raw11717step1 = (fun i j => raw11717step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11717step1 raw11717step0; decide +kernel
      have hl : raw11717step1Labels = raw11717step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11717step0 raw11717step0Labels permutation32 permutation6
    _ = mixedMoment B node2738 node2738Labels := by rfl

def raw11718 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11718Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11718step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw11718step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11718 raw11718Labels = mixedMoment B node2717 node2717Labels := by
  calc
    mixedMoment B raw11718 raw11718Labels = mixedMoment B raw11718step0 raw11718step0Labels := by
      have ha : raw11718step0 = (fun i j => raw11718 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11718step0 raw11718; decide +kernel
      have hl : raw11718step0Labels = raw11718Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11718 raw11718Labels permutation152 permutation6
    _ = mixedMoment B node2717 node2717Labels := by rfl

def raw11719 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw11719Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw11719step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11719 raw11719Labels = mixedMoment B node2717 node2717Labels := by
  calc
    mixedMoment B raw11719 raw11719Labels = mixedMoment B raw11719step0 raw11719step0Labels := by
      have ha : raw11719step0 = (fun i j => raw11719 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11719step0 raw11719; decide +kernel
      have hl : raw11719step0Labels = raw11719Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11719 raw11719Labels permutation154 permutation6
    _ = mixedMoment B node2717 node2717Labels := by rfl

def raw11720 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11720step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11720step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11720step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11720step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11720 raw11720Labels = mixedMoment B node2728 node2728Labels := by
  calc
    mixedMoment B raw11720 raw11720Labels = mixedMoment B raw11720step0 raw11720step0Labels := by
      have ha : raw11720step0 = (fun i j => raw11720 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11720step0 raw11720; decide +kernel
      have hl : raw11720step0Labels = raw11720Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11720 raw11720Labels permutation180 permutation7
    mixedMoment B raw11720step0 raw11720step0Labels = mixedMoment B raw11720step1 raw11720step1Labels := by
      have ha : raw11720step1 = raw11720step0 := by apply Matrix.ext; unfold raw11720step1 raw11720step0; decide +kernel
      have hl : raw11720step0Labels = labelEmbedding1 ∘ raw11720step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11720step0 raw11720step0Labels raw11720step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2728 node2728Labels := by rfl

def raw11721 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11721Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11721step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11721step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11721step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11721step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11721 raw11721Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw11721 raw11721Labels = mixedMoment B raw11721step0 raw11721step0Labels := by
      have hz : ∀ j, raw11721 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11721step0 = (fun i j => raw11721 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11721step0 raw11721; decide +kernel
      have hl : raw11721step0Labels = raw11721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11721 raw11721Labels permutation346 hz
    mixedMoment B raw11721step0 raw11721step0Labels = mixedMoment B raw11721step1 raw11721step1Labels := by
      have ha : raw11721step1 = (fun i j => raw11721step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11721step1 raw11721step0; decide +kernel
      have hl : raw11721step1Labels = raw11721step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11721step0 raw11721step0Labels permutation36 permutation7
    mixedMoment B raw11721step1 raw11721step1Labels = mixedMoment B raw11721step2 raw11721step2Labels := by
      have ha : raw11721step2 = raw11721step1 := by apply Matrix.ext; unfold raw11721step2 raw11721step1; decide +kernel
      have hl : raw11721step1Labels = labelEmbedding1 ∘ raw11721step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11721step1 raw11721step1Labels raw11721step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2764 node2764Labels := by rfl

def raw11722 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11722Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11722step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11722step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11722step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11722step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11722 raw11722Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw11722 raw11722Labels = mixedMoment B raw11722step0 raw11722step0Labels := by
      have ha : raw11722step0 = (fun i j => raw11722 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11722step0 raw11722; decide +kernel
      have hl : raw11722step0Labels = raw11722Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11722 raw11722Labels permutation181 permutation7
    mixedMoment B raw11722step0 raw11722step0Labels = mixedMoment B raw11722step1 raw11722step1Labels := by
      have ha : raw11722step1 = raw11722step0 := by apply Matrix.ext; unfold raw11722step1 raw11722step0; decide +kernel
      have hl : raw11722step0Labels = labelEmbedding1 ∘ raw11722step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11722step0 raw11722step0Labels raw11722step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2718 node2718Labels := by rfl

def raw11723 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11723Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11723step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11723step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11723step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11723step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11723 raw11723Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw11723 raw11723Labels = mixedMoment B raw11723step0 raw11723step0Labels := by
      have ha : raw11723step0 = (fun i j => raw11723 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11723step0 raw11723; decide +kernel
      have hl : raw11723step0Labels = raw11723Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11723 raw11723Labels permutation180 permutation7
    mixedMoment B raw11723step0 raw11723step0Labels = mixedMoment B raw11723step1 raw11723step1Labels := by
      have ha : raw11723step1 = raw11723step0 := by apply Matrix.ext; unfold raw11723step1 raw11723step0; decide +kernel
      have hl : raw11723step0Labels = labelEmbedding1 ∘ raw11723step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11723step0 raw11723step0Labels raw11723step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2718 node2718Labels := by rfl

def raw11724 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11724Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11724step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11724step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11724step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11724step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11724 raw11724Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw11724 raw11724Labels = mixedMoment B raw11724step0 raw11724step0Labels := by
      have ha : raw11724step0 = (fun i j => raw11724 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11724step0 raw11724; decide +kernel
      have hl : raw11724step0Labels = raw11724Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11724 raw11724Labels permutation180 permutation7
    mixedMoment B raw11724step0 raw11724step0Labels = mixedMoment B raw11724step1 raw11724step1Labels := by
      have ha : raw11724step1 = raw11724step0 := by apply Matrix.ext; unfold raw11724step1 raw11724step0; decide +kernel
      have hl : raw11724step0Labels = labelEmbedding1 ∘ raw11724step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11724step0 raw11724step0Labels raw11724step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2721 node2721Labels := by rfl

def raw11725 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11725Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11725step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11725step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11725step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw11725step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11725step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw11725step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11725 raw11725Labels = mixedMoment B node3227 node3227Labels := by
  calc
    mixedMoment B raw11725 raw11725Labels = mixedMoment B raw11725step0 raw11725step0Labels := by
      have hz : ∀ j, raw11725 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11725step0 = (fun i j => raw11725 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11725step0 raw11725; decide +kernel
      have hl : raw11725step0Labels = raw11725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11725 raw11725Labels permutation265 hz
    mixedMoment B raw11725step0 raw11725step0Labels = mixedMoment B raw11725step1 raw11725step1Labels := by
      have ha : raw11725step1 = (fun i j => raw11725step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11725step1 raw11725step0; decide +kernel
      have hl : raw11725step1Labels = raw11725step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11725step0 raw11725step0Labels permutation40 permutation5
    mixedMoment B raw11725step1 raw11725step1Labels = mixedMoment B raw11725step2 raw11725step2Labels := by
      have ha : raw11725step2 = -raw11725step1 := by apply Matrix.ext; change ∀ i j, raw11725step2 i j = -(raw11725step1 i j); unfold raw11725step2 raw11725step1; decide +kernel
      have hl : raw11725step2Labels = raw11725step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11725step2 raw11725step2Labels = mixedMoment B raw11725step3 raw11725step3Labels := by
      have ha : raw11725step3 = raw11725step2 := by apply Matrix.ext; unfold raw11725step3 raw11725step2; decide +kernel
      have hl : raw11725step2Labels = labelEmbedding1 ∘ raw11725step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11725step2 raw11725step2Labels raw11725step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3227 node3227Labels := by rfl

def raw11726 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11726Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11726step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11726step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11726step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11726step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11726step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11726step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11726step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11726 raw11726Labels = mixedMoment B node3120 node3120Labels := by
  calc
    mixedMoment B raw11726 raw11726Labels = mixedMoment B raw11726step0 raw11726step0Labels := by
      have hz : ∀ j, raw11726 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11726step0 = (fun i j => raw11726 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11726step0 raw11726; decide +kernel
      have hl : raw11726step0Labels = raw11726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11726 raw11726Labels permutation346 hz
    mixedMoment B raw11726step0 raw11726step0Labels = mixedMoment B raw11726step1 raw11726step1Labels := by
      have hz : ∀ j, raw11726step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11726step1 = (fun i j => raw11726step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11726step1 raw11726step0; decide +kernel
      have hl : raw11726step1Labels = raw11726step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11726step0 raw11726step0Labels permutation56 hz
    mixedMoment B raw11726step1 raw11726step1Labels = mixedMoment B raw11726step2 raw11726step2Labels := by
      have ha : raw11726step2 = (fun i j => raw11726step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11726step2 raw11726step1; decide +kernel
      have hl : raw11726step2Labels = raw11726step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11726step1 raw11726step1Labels permutation12 permutation7
    mixedMoment B raw11726step2 raw11726step2Labels = mixedMoment B raw11726step3 raw11726step3Labels := by
      have ha : raw11726step3 = raw11726step2 := by apply Matrix.ext; unfold raw11726step3 raw11726step2; decide +kernel
      have hl : raw11726step2Labels = labelEmbedding1 ∘ raw11726step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11726step2 raw11726step2Labels raw11726step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3120 node3120Labels := by rfl

def raw11727 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11727Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11727step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11727step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11727step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11727step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11727step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11727 raw11727Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw11727 raw11727Labels = mixedMoment B raw11727step0 raw11727step0Labels := by
      have hz : ∀ j, raw11727 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11727step0 = (fun i j => raw11727 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11727step0 raw11727; decide +kernel
      have hl : raw11727step0Labels = raw11727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11727 raw11727Labels permutation265 hz
    mixedMoment B raw11727step0 raw11727step0Labels = mixedMoment B raw11727step1 raw11727step1Labels := by
      have ha : raw11727step1 = (fun i j => raw11727step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11727step1 raw11727step0; decide +kernel
      have hl : raw11727step1Labels = raw11727step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11727step0 raw11727step0Labels permutation37 permutation7
    mixedMoment B raw11727step1 raw11727step1Labels = mixedMoment B raw11727step2 raw11727step2Labels := by
      have ha : raw11727step2 = raw11727step1 := by apply Matrix.ext; unfold raw11727step2 raw11727step1; decide +kernel
      have hl : raw11727step1Labels = labelEmbedding1 ∘ raw11727step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11727step1 raw11727step1Labels raw11727step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3097 node3097Labels := by rfl

def raw11728 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11728Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11728step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11728step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11728step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11728step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11728 raw11728Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw11728 raw11728Labels = mixedMoment B raw11728step0 raw11728step0Labels := by
      have hz : ∀ j, raw11728 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11728step0 = (fun i j => raw11728 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11728step0 raw11728; decide +kernel
      have hl : raw11728step0Labels = raw11728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11728 raw11728Labels permutation265 hz
    mixedMoment B raw11728step0 raw11728step0Labels = mixedMoment B raw11728step1 raw11728step1Labels := by
      have ha : raw11728step1 = (fun i j => raw11728step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11728step1 raw11728step0; decide +kernel
      have hl : raw11728step1Labels = raw11728step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11728step0 raw11728step0Labels permutation36 permutation7
    mixedMoment B raw11728step1 raw11728step1Labels = mixedMoment B raw11728step2 raw11728step2Labels := by
      have ha : raw11728step2 = raw11728step1 := by apply Matrix.ext; unfold raw11728step2 raw11728step1; decide +kernel
      have hl : raw11728step1Labels = labelEmbedding1 ∘ raw11728step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11728step1 raw11728step1Labels raw11728step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3097 node3097Labels := by rfl

def raw11729 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11729Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11729step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11729step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11729step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11729 raw11729Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw11729 raw11729Labels = mixedMoment B raw11729step0 raw11729step0Labels := by
      have hz : ∀ j, raw11729 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11729step0 = (fun i j => raw11729 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11729step0 raw11729; decide +kernel
      have hl : raw11729step0Labels = raw11729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11729 raw11729Labels permutation265 hz
    mixedMoment B raw11729step0 raw11729step0Labels = mixedMoment B raw11729step1 raw11729step1Labels := by
      have ha : raw11729step1 = (fun i j => raw11729step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11729step1 raw11729step0; decide +kernel
      have hl : raw11729step1Labels = raw11729step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11729step0 raw11729step0Labels permutation36 permutation7
    mixedMoment B raw11729step1 raw11729step1Labels = mixedMoment B raw11729step2 raw11729step2Labels := by
      have ha : raw11729step2 = raw11729step1 := by apply Matrix.ext; unfold raw11729step2 raw11729step1; decide +kernel
      have hl : raw11729step1Labels = labelEmbedding1 ∘ raw11729step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11729step1 raw11729step1Labels raw11729step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3100 node3100Labels := by rfl

def raw11730 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11730Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11730step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw11730step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11730step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw11730step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11730step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw11730step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11730 raw11730Labels = mixedMoment B node3199 node3199Labels := by
  calc
    mixedMoment B raw11730 raw11730Labels = mixedMoment B raw11730step0 raw11730step0Labels := by
      have ha : raw11730step0 = (fun i j => raw11730 (permutation161 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11730step0 raw11730; decide +kernel
      have hl : raw11730step0Labels = raw11730Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11730 raw11730Labels permutation161 permutation5
    mixedMoment B raw11730step0 raw11730step0Labels = mixedMoment B raw11730step1 raw11730step1Labels := by
      have ha : raw11730step1 = -raw11730step0 := by apply Matrix.ext; change ∀ i j, raw11730step1 i j = -(raw11730step0 i j); unfold raw11730step1 raw11730step0; decide +kernel
      have hl : raw11730step1Labels = raw11730step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11730step1 raw11730step1Labels = mixedMoment B raw11730step2 raw11730step2Labels := by
      have ha : raw11730step2 = raw11730step1 := by apply Matrix.ext; unfold raw11730step2 raw11730step1; decide +kernel
      have hl : raw11730step1Labels = labelEmbedding1 ∘ raw11730step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11730step1 raw11730step1Labels raw11730step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3199 node3199Labels := by rfl

def raw11731 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11731Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11731step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11731step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11731step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11731 raw11731Labels = mixedMoment B node3041 node3041Labels := by
  calc
    mixedMoment B raw11731 raw11731Labels = mixedMoment B raw11731step0 raw11731step0Labels := by
      have ha : raw11731step0 = (fun i j => raw11731 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11731step0 raw11731; decide +kernel
      have hl : raw11731step0Labels = raw11731Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11731 raw11731Labels permutation180 permutation7
    mixedMoment B raw11731step0 raw11731step0Labels = mixedMoment B raw11731step1 raw11731step1Labels := by
      have ha : raw11731step1 = raw11731step0 := by apply Matrix.ext; unfold raw11731step1 raw11731step0; decide +kernel
      have hl : raw11731step0Labels = labelEmbedding1 ∘ raw11731step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11731step0 raw11731step0Labels raw11731step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3041 node3041Labels := by rfl

def raw11732 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11732Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11732step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11732step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11732step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11732step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11732 raw11732Labels = mixedMoment B node3034 node3034Labels := by
  calc
    mixedMoment B raw11732 raw11732Labels = mixedMoment B raw11732step0 raw11732step0Labels := by
      have ha : raw11732step0 = (fun i j => raw11732 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11732step0 raw11732; decide +kernel
      have hl : raw11732step0Labels = raw11732Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11732 raw11732Labels permutation181 permutation7
    mixedMoment B raw11732step0 raw11732step0Labels = mixedMoment B raw11732step1 raw11732step1Labels := by
      have ha : raw11732step1 = raw11732step0 := by apply Matrix.ext; unfold raw11732step1 raw11732step0; decide +kernel
      have hl : raw11732step0Labels = labelEmbedding1 ∘ raw11732step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11732step0 raw11732step0Labels raw11732step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3034 node3034Labels := by rfl

def raw11733 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11733step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11733step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11733step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11733step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11733 raw11733Labels = mixedMoment B node3034 node3034Labels := by
  calc
    mixedMoment B raw11733 raw11733Labels = mixedMoment B raw11733step0 raw11733step0Labels := by
      have ha : raw11733step0 = (fun i j => raw11733 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11733step0 raw11733; decide +kernel
      have hl : raw11733step0Labels = raw11733Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11733 raw11733Labels permutation180 permutation7
    mixedMoment B raw11733step0 raw11733step0Labels = mixedMoment B raw11733step1 raw11733step1Labels := by
      have ha : raw11733step1 = raw11733step0 := by apply Matrix.ext; unfold raw11733step1 raw11733step0; decide +kernel
      have hl : raw11733step0Labels = labelEmbedding1 ∘ raw11733step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11733step0 raw11733step0Labels raw11733step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3034 node3034Labels := by rfl

def raw11734 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11734step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11734step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11734step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11734step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11734 raw11734Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw11734 raw11734Labels = mixedMoment B raw11734step0 raw11734step0Labels := by
      have ha : raw11734step0 = (fun i j => raw11734 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11734step0 raw11734; decide +kernel
      have hl : raw11734step0Labels = raw11734Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11734 raw11734Labels permutation180 permutation7
    mixedMoment B raw11734step0 raw11734step0Labels = mixedMoment B raw11734step1 raw11734step1Labels := by
      have ha : raw11734step1 = raw11734step0 := by apply Matrix.ext; unfold raw11734step1 raw11734step0; decide +kernel
      have hl : raw11734step0Labels = labelEmbedding1 ∘ raw11734step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11734step0 raw11734step0Labels raw11734step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3037 node3037Labels := by rfl

def raw11735 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11735step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw11735step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11735step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11735step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11735step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11735step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11735 raw11735Labels = mixedMoment B node3204 node3204Labels := by
  calc
    mixedMoment B raw11735 raw11735Labels = mixedMoment B raw11735step0 raw11735step0Labels := by
      have ha : raw11735step0 = (fun i j => raw11735 (permutation166 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11735step0 raw11735; decide +kernel
      have hl : raw11735step0Labels = raw11735Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11735 raw11735Labels permutation166 permutation5
    mixedMoment B raw11735step0 raw11735step0Labels = mixedMoment B raw11735step1 raw11735step1Labels := by
      have ha : raw11735step1 = -raw11735step0 := by apply Matrix.ext; change ∀ i j, raw11735step1 i j = -(raw11735step0 i j); unfold raw11735step1 raw11735step0; decide +kernel
      have hl : raw11735step1Labels = raw11735step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11735step1 raw11735step1Labels = mixedMoment B raw11735step2 raw11735step2Labels := by
      have ha : raw11735step2 = raw11735step1 := by apply Matrix.ext; unfold raw11735step2 raw11735step1; decide +kernel
      have hl : raw11735step1Labels = labelEmbedding1 ∘ raw11735step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11735step1 raw11735step1Labels raw11735step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3204 node3204Labels := by rfl

def raw11736 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11736step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11736step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11736step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11736 raw11736Labels = mixedMoment B node3091 node3091Labels := by
  calc
    mixedMoment B raw11736 raw11736Labels = mixedMoment B raw11736step0 raw11736step0Labels := by
      have ha : raw11736step0 = (fun i j => raw11736 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11736step0 raw11736; decide +kernel
      have hl : raw11736step0Labels = raw11736Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11736 raw11736Labels permutation180 permutation7
    mixedMoment B raw11736step0 raw11736step0Labels = mixedMoment B raw11736step1 raw11736step1Labels := by
      have ha : raw11736step1 = raw11736step0 := by apply Matrix.ext; unfold raw11736step1 raw11736step0; decide +kernel
      have hl : raw11736step0Labels = labelEmbedding1 ∘ raw11736step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11736step0 raw11736step0Labels raw11736step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3091 node3091Labels := by rfl

def raw11737 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11737Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11737step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11737step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11737step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11737step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11737 raw11737Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw11737 raw11737Labels = mixedMoment B raw11737step0 raw11737step0Labels := by
      have hz : ∀ j, raw11737 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11737step0 = (fun i j => raw11737 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11737step0 raw11737; decide +kernel
      have hl : raw11737step0Labels = raw11737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11737 raw11737Labels permutation346 hz
    mixedMoment B raw11737step0 raw11737step0Labels = mixedMoment B raw11737step1 raw11737step1Labels := by
      have ha : raw11737step1 = (fun i j => raw11737step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11737step1 raw11737step0; decide +kernel
      have hl : raw11737step1Labels = raw11737step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11737step0 raw11737step0Labels permutation36 permutation7
    mixedMoment B raw11737step1 raw11737step1Labels = mixedMoment B raw11737step2 raw11737step2Labels := by
      have ha : raw11737step2 = raw11737step1 := by apply Matrix.ext; unfold raw11737step2 raw11737step1; decide +kernel
      have hl : raw11737step1Labels = labelEmbedding1 ∘ raw11737step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11737step1 raw11737step1Labels raw11737step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw11738 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11738Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11738step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11738step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11738step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11738step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11738 raw11738Labels = mixedMoment B node3084 node3084Labels := by
  calc
    mixedMoment B raw11738 raw11738Labels = mixedMoment B raw11738step0 raw11738step0Labels := by
      have ha : raw11738step0 = (fun i j => raw11738 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11738step0 raw11738; decide +kernel
      have hl : raw11738step0Labels = raw11738Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11738 raw11738Labels permutation180 permutation7
    mixedMoment B raw11738step0 raw11738step0Labels = mixedMoment B raw11738step1 raw11738step1Labels := by
      have ha : raw11738step1 = raw11738step0 := by apply Matrix.ext; unfold raw11738step1 raw11738step0; decide +kernel
      have hl : raw11738step0Labels = labelEmbedding1 ∘ raw11738step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11738step0 raw11738step0Labels raw11738step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3084 node3084Labels := by rfl

def raw11739 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11739Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11739step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11739step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11739step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11739step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11739 raw11739Labels = mixedMoment B node3087 node3087Labels := by
  calc
    mixedMoment B raw11739 raw11739Labels = mixedMoment B raw11739step0 raw11739step0Labels := by
      have ha : raw11739step0 = (fun i j => raw11739 (permutation177 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11739step0 raw11739; decide +kernel
      have hl : raw11739step0Labels = raw11739Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11739 raw11739Labels permutation177 permutation7
    mixedMoment B raw11739step0 raw11739step0Labels = mixedMoment B raw11739step1 raw11739step1Labels := by
      have ha : raw11739step1 = raw11739step0 := by apply Matrix.ext; unfold raw11739step1 raw11739step0; decide +kernel
      have hl : raw11739step0Labels = labelEmbedding1 ∘ raw11739step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11739step0 raw11739step0Labels raw11739step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3087 node3087Labels := by rfl

def raw11740 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11740Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw11740step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11740step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11740step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11740step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11740step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11740 raw11740Labels = mixedMoment B node3204 node3204Labels := by
  calc
    mixedMoment B raw11740 raw11740Labels = mixedMoment B raw11740step0 raw11740step0Labels := by
      have ha : raw11740step0 = (fun i j => raw11740 (permutation160 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11740step0 raw11740; decide +kernel
      have hl : raw11740step0Labels = raw11740Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11740 raw11740Labels permutation160 permutation5
    mixedMoment B raw11740step0 raw11740step0Labels = mixedMoment B raw11740step1 raw11740step1Labels := by
      have ha : raw11740step1 = -raw11740step0 := by apply Matrix.ext; change ∀ i j, raw11740step1 i j = -(raw11740step0 i j); unfold raw11740step1 raw11740step0; decide +kernel
      have hl : raw11740step1Labels = raw11740step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11740step1 raw11740step1Labels = mixedMoment B raw11740step2 raw11740step2Labels := by
      have ha : raw11740step2 = raw11740step1 := by apply Matrix.ext; unfold raw11740step2 raw11740step1; decide +kernel
      have hl : raw11740step1Labels = labelEmbedding1 ∘ raw11740step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11740step1 raw11740step1Labels raw11740step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3204 node3204Labels := by rfl

def raw11741 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11741Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11741step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11741step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11741step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11741 raw11741Labels = mixedMoment B node3091 node3091Labels := by
  calc
    mixedMoment B raw11741 raw11741Labels = mixedMoment B raw11741step0 raw11741step0Labels := by
      have ha : raw11741step0 = (fun i j => raw11741 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11741step0 raw11741; decide +kernel
      have hl : raw11741step0Labels = raw11741Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11741 raw11741Labels permutation181 permutation7
    mixedMoment B raw11741step0 raw11741step0Labels = mixedMoment B raw11741step1 raw11741step1Labels := by
      have ha : raw11741step1 = raw11741step0 := by apply Matrix.ext; unfold raw11741step1 raw11741step0; decide +kernel
      have hl : raw11741step0Labels = labelEmbedding1 ∘ raw11741step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11741step0 raw11741step0Labels raw11741step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3091 node3091Labels := by rfl

def raw11742 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11742Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11742step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11742step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11742step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw11742step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11742 raw11742Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw11742 raw11742Labels = mixedMoment B raw11742step0 raw11742step0Labels := by
      have hz : ∀ j, raw11742 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11742step0 = (fun i j => raw11742 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11742step0 raw11742; decide +kernel
      have hl : raw11742step0Labels = raw11742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11742 raw11742Labels permutation346 hz
    mixedMoment B raw11742step0 raw11742step0Labels = mixedMoment B raw11742step1 raw11742step1Labels := by
      have ha : raw11742step1 = (fun i j => raw11742step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11742step1 raw11742step0; decide +kernel
      have hl : raw11742step1Labels = raw11742step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11742step0 raw11742step0Labels permutation37 permutation7
    mixedMoment B raw11742step1 raw11742step1Labels = mixedMoment B raw11742step2 raw11742step2Labels := by
      have ha : raw11742step2 = raw11742step1 := by apply Matrix.ext; unfold raw11742step2 raw11742step1; decide +kernel
      have hl : raw11742step1Labels = labelEmbedding1 ∘ raw11742step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11742step1 raw11742step1Labels raw11742step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw11743 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11743Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11743step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11743step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw11743step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11743 raw11743Labels = mixedMoment B node3084 node3084Labels := by
  calc
    mixedMoment B raw11743 raw11743Labels = mixedMoment B raw11743step0 raw11743step0Labels := by
      have ha : raw11743step0 = (fun i j => raw11743 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11743step0 raw11743; decide +kernel
      have hl : raw11743step0Labels = raw11743Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11743 raw11743Labels permutation181 permutation7
    mixedMoment B raw11743step0 raw11743step0Labels = mixedMoment B raw11743step1 raw11743step1Labels := by
      have ha : raw11743step1 = raw11743step0 := by apply Matrix.ext; unfold raw11743step1 raw11743step0; decide +kernel
      have hl : raw11743step0Labels = labelEmbedding1 ∘ raw11743step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11743step0 raw11743step0Labels raw11743step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3084 node3084Labels := by rfl

def raw11744 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw11744Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11744step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11744step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11744step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11744step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11744 raw11744Labels = mixedMoment B node3087 node3087Labels := by
  calc
    mixedMoment B raw11744 raw11744Labels = mixedMoment B raw11744step0 raw11744step0Labels := by
      have ha : raw11744step0 = (fun i j => raw11744 (permutation179 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11744step0 raw11744; decide +kernel
      have hl : raw11744step0Labels = raw11744Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11744 raw11744Labels permutation179 permutation7
    mixedMoment B raw11744step0 raw11744step0Labels = mixedMoment B raw11744step1 raw11744step1Labels := by
      have ha : raw11744step1 = raw11744step0 := by apply Matrix.ext; unfold raw11744step1 raw11744step0; decide +kernel
      have hl : raw11744step0Labels = labelEmbedding1 ∘ raw11744step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11744step0 raw11744step0Labels raw11744step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3087 node3087Labels := by rfl

def raw11745 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11745Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11745step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw11745step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11745step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw11745step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11745 raw11745Labels = mixedMoment B node2471 node2471Labels := by
  calc
    mixedMoment B raw11745 raw11745Labels = mixedMoment B raw11745step0 raw11745step0Labels := by
      have ha : raw11745step0 = (fun i j => raw11745 (permutation640 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11745step0 raw11745; decide +kernel
      have hl : raw11745step0Labels = raw11745Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11745 raw11745Labels permutation640 permutation5
    mixedMoment B raw11745step0 raw11745step0Labels = mixedMoment B raw11745step1 raw11745step1Labels := by
      have ha : raw11745step1 = raw11745step0 := by apply Matrix.ext; unfold raw11745step1 raw11745step0; decide +kernel
      have hl : raw11745step0Labels = labelEmbedding1 ∘ raw11745step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11745step0 raw11745step0Labels raw11745step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2471 node2471Labels := by rfl

def raw11746 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11746Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw11746step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11746step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw11746step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11746 raw11746Labels = mixedMoment B node2472 node2472Labels := by
  calc
    mixedMoment B raw11746 raw11746Labels = mixedMoment B raw11746step0 raw11746step0Labels := by
      have ha : raw11746step0 = (fun i j => raw11746 (permutation639 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11746step0 raw11746; decide +kernel
      have hl : raw11746step0Labels = raw11746Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11746 raw11746Labels permutation639 permutation5
    mixedMoment B raw11746step0 raw11746step0Labels = mixedMoment B raw11746step1 raw11746step1Labels := by
      have ha : raw11746step1 = raw11746step0 := by apply Matrix.ext; unfold raw11746step1 raw11746step0; decide +kernel
      have hl : raw11746step0Labels = labelEmbedding1 ∘ raw11746step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11746step0 raw11746step0Labels raw11746step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2472 node2472Labels := by rfl

def raw11747 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11747Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11747step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw11747step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11747step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw11747step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11747 raw11747Labels = mixedMoment B node2754 node2754Labels := by
  calc
    mixedMoment B raw11747 raw11747Labels = mixedMoment B raw11747step0 raw11747step0Labels := by
      have hz : ∀ j, raw11747 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11747step0 = (fun i j => raw11747 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11747step0 raw11747; decide +kernel
      have hl : raw11747step0Labels = raw11747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11747 raw11747Labels permutation346 hz
    mixedMoment B raw11747step0 raw11747step0Labels = mixedMoment B raw11747step1 raw11747step1Labels := by
      have ha : raw11747step1 = (fun i j => raw11747step0 (permutation145 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11747step1 raw11747step0; decide +kernel
      have hl : raw11747step1Labels = raw11747step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11747step0 raw11747step0Labels permutation145 permutation5
    mixedMoment B raw11747step1 raw11747step1Labels = mixedMoment B raw11747step2 raw11747step2Labels := by
      have ha : raw11747step2 = raw11747step1 := by apply Matrix.ext; unfold raw11747step2 raw11747step1; decide +kernel
      have hl : raw11747step1Labels = labelEmbedding1 ∘ raw11747step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11747step1 raw11747step1Labels raw11747step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2754 node2754Labels := by rfl

def raw11748 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11748Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11748step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw11748step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11748step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw11748step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11748 raw11748Labels = mixedMoment B node2484 node2484Labels := by
  calc
    mixedMoment B raw11748 raw11748Labels = mixedMoment B raw11748step0 raw11748step0Labels := by
      have ha : raw11748step0 = (fun i j => raw11748 (permutation644 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11748step0 raw11748; decide +kernel
      have hl : raw11748step0Labels = raw11748Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11748 raw11748Labels permutation644 permutation5
    mixedMoment B raw11748step0 raw11748step0Labels = mixedMoment B raw11748step1 raw11748step1Labels := by
      have ha : raw11748step1 = raw11748step0 := by apply Matrix.ext; unfold raw11748step1 raw11748step0; decide +kernel
      have hl : raw11748step0Labels = labelEmbedding1 ∘ raw11748step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11748step0 raw11748step0Labels raw11748step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2484 node2484Labels := by rfl

def raw11749 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![2, -3, 1]]
def raw11749Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11749step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw11749step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11749step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw11749step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11749 raw11749Labels = mixedMoment B node2484 node2484Labels := by
  calc
    mixedMoment B raw11749 raw11749Labels = mixedMoment B raw11749step0 raw11749step0Labels := by
      have ha : raw11749step0 = (fun i j => raw11749 (permutation638 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11749step0 raw11749; decide +kernel
      have hl : raw11749step0Labels = raw11749Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11749 raw11749Labels permutation638 permutation5
    mixedMoment B raw11749step0 raw11749step0Labels = mixedMoment B raw11749step1 raw11749step1Labels := by
      have ha : raw11749step1 = raw11749step0 := by apply Matrix.ext; unfold raw11749step1 raw11749step0; decide +kernel
      have hl : raw11749step0Labels = labelEmbedding1 ∘ raw11749step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11749step0 raw11749step0Labels raw11749step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2484 node2484Labels := by rfl

def raw11750 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11750Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw11750step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11750step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11750step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11750 raw11750Labels = mixedMoment B node3525 node3525Labels := by
  calc
    mixedMoment B raw11750 raw11750Labels = mixedMoment B raw11750step0 raw11750step0Labels := by
      have ha : raw11750step0 = (fun i j => raw11750 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11750step0 raw11750; decide +kernel
      have hl : raw11750step0Labels = raw11750Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11750 raw11750Labels permutation160 permutation4
    mixedMoment B raw11750step0 raw11750step0Labels = mixedMoment B raw11750step1 raw11750step1Labels := by
      have ha : raw11750step1 = -raw11750step0 := by apply Matrix.ext; change ∀ i j, raw11750step1 i j = -(raw11750step0 i j); unfold raw11750step1 raw11750step0; decide +kernel
      have hl : raw11750step1Labels = raw11750step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3525 node3525Labels := by rfl

def raw11751 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11751Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11751step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw11751step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11751step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11751step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11751 raw11751Labels = mixedMoment B node3505 node3505Labels := by
  calc
    mixedMoment B raw11751 raw11751Labels = mixedMoment B raw11751step0 raw11751step0Labels := by
      have ha : raw11751step0 = (fun i j => raw11751 (permutation197 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11751step0 raw11751; decide +kernel
      have hl : raw11751step0Labels = raw11751Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11751 raw11751Labels permutation197 permutation2
    mixedMoment B raw11751step0 raw11751step0Labels = mixedMoment B raw11751step1 raw11751step1Labels := by
      have ha : raw11751step1 = -raw11751step0 := by apply Matrix.ext; change ∀ i j, raw11751step1 i j = -(raw11751step0 i j); unfold raw11751step1 raw11751step0; decide +kernel
      have hl : raw11751step1Labels = raw11751step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3505 node3505Labels := by rfl

def raw11752 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11752Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11752step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11752step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11752step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11752step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11752 raw11752Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw11752 raw11752Labels = mixedMoment B raw11752step0 raw11752step0Labels := by
      have hz : ∀ j, raw11752 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11752step0 = (fun i j => raw11752 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11752step0 raw11752; decide +kernel
      have hl : raw11752step0Labels = raw11752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11752 raw11752Labels permutation346 hz
    mixedMoment B raw11752step0 raw11752step0Labels = mixedMoment B raw11752step1 raw11752step1Labels := by
      have ha : raw11752step1 = (fun i j => raw11752step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11752step1 raw11752step0; decide +kernel
      have hl : raw11752step1Labels = raw11752step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11752step0 raw11752step0Labels permutation50 permutation2
    mixedMoment B raw11752step1 raw11752step1Labels = mixedMoment B raw11752step2 raw11752step2Labels := by
      have ha : raw11752step2 = -raw11752step1 := by apply Matrix.ext; change ∀ i j, raw11752step2 i j = -(raw11752step1 i j); unfold raw11752step2 raw11752step1; decide +kernel
      have hl : raw11752step2Labels = raw11752step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3581 node3581Labels := by rfl

def raw11753 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11753Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw11753step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11753step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11753step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11753 raw11753Labels = mixedMoment B node3503 node3503Labels := by
  calc
    mixedMoment B raw11753 raw11753Labels = mixedMoment B raw11753step0 raw11753step0Labels := by
      have ha : raw11753step0 = (fun i j => raw11753 (permutation195 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11753step0 raw11753; decide +kernel
      have hl : raw11753step0Labels = raw11753Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11753 raw11753Labels permutation195 permutation2
    mixedMoment B raw11753step0 raw11753step0Labels = mixedMoment B raw11753step1 raw11753step1Labels := by
      have ha : raw11753step1 = -raw11753step0 := by apply Matrix.ext; change ∀ i j, raw11753step1 i j = -(raw11753step0 i j); unfold raw11753step1 raw11753step0; decide +kernel
      have hl : raw11753step1Labels = raw11753step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3503 node3503Labels := by rfl

def raw11754 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11754Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11754step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw11754step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11754step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11754step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11754 raw11754Labels = mixedMoment B node3503 node3503Labels := by
  calc
    mixedMoment B raw11754 raw11754Labels = mixedMoment B raw11754step0 raw11754step0Labels := by
      have ha : raw11754step0 = (fun i j => raw11754 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11754step0 raw11754; decide +kernel
      have hl : raw11754step0Labels = raw11754Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11754 raw11754Labels permutation194 permutation2
    mixedMoment B raw11754step0 raw11754step0Labels = mixedMoment B raw11754step1 raw11754step1Labels := by
      have ha : raw11754step1 = -raw11754step0 := by apply Matrix.ext; change ∀ i j, raw11754step1 i j = -(raw11754step0 i j); unfold raw11754step1 raw11754step0; decide +kernel
      have hl : raw11754step1Labels = raw11754step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3503 node3503Labels := by rfl

def raw11755 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11755Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11755step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11755step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11755step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11755 raw11755Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw11755 raw11755Labels = mixedMoment B raw11755step0 raw11755step0Labels := by
      have ha : raw11755step0 = (fun i j => raw11755 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11755step0 raw11755; decide +kernel
      have hl : raw11755step0Labels = raw11755Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11755 raw11755Labels permutation194 permutation2
    mixedMoment B raw11755step0 raw11755step0Labels = mixedMoment B raw11755step1 raw11755step1Labels := by
      have ha : raw11755step1 = -raw11755step0 := by apply Matrix.ext; change ∀ i j, raw11755step1 i j = -(raw11755step0 i j); unfold raw11755step1 raw11755step0; decide +kernel
      have hl : raw11755step1Labels = raw11755step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3532 node3532Labels := by rfl

def raw11756 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![0, 0], ![0, 0], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw11756Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11756step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![0, 0], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw11756step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11756step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw11756step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11756step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw11756step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical11756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11756 raw11756Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw11756 raw11756Labels = mixedMoment B raw11756step0 raw11756step0Labels := by
      have hz : ∀ j, raw11756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11756step0 = (fun i j => raw11756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11756step0 raw11756; decide +kernel
      have hl : raw11756step0Labels = raw11756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11756 raw11756Labels permutation346 hz
    mixedMoment B raw11756step0 raw11756step0Labels = mixedMoment B raw11756step1 raw11756step1Labels := by
      have hz : ∀ j, raw11756step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw11756step1 = (fun i j => raw11756step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw11756step1 raw11756step0; decide +kernel
      have hl : raw11756step1Labels = raw11756step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11756step0 raw11756step0Labels permutation56 hz
    mixedMoment B raw11756step1 raw11756step1Labels = mixedMoment B raw11756step2 raw11756step2Labels := by
      have ha : raw11756step2 = -raw11756step1 := by apply Matrix.ext; change ∀ i j, raw11756step2 i j = -(raw11756step1 i j); unfold raw11756step2 raw11756step1; decide +kernel
      have hl : raw11756step2Labels = raw11756step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw11757 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11757Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11757step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw11757step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11757step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11757step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11757 raw11757Labels = mixedMoment B node3373 node3373Labels := by
  calc
    mixedMoment B raw11757 raw11757Labels = mixedMoment B raw11757step0 raw11757step0Labels := by
      have ha : raw11757step0 = (fun i j => raw11757 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11757step0 raw11757; decide +kernel
      have hl : raw11757step0Labels = raw11757Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11757 raw11757Labels permutation160 permutation4
    mixedMoment B raw11757step0 raw11757step0Labels = mixedMoment B raw11757step1 raw11757step1Labels := by
      have ha : raw11757step1 = -raw11757step0 := by apply Matrix.ext; change ∀ i j, raw11757step1 i j = -(raw11757step0 i j); unfold raw11757step1 raw11757step0; decide +kernel
      have hl : raw11757step1Labels = raw11757step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3373 node3373Labels := by rfl

def raw11758 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11758Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw11758step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11758step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11758step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11758 raw11758Labels = mixedMoment B node3376 node3376Labels := by
  calc
    mixedMoment B raw11758 raw11758Labels = mixedMoment B raw11758step0 raw11758step0Labels := by
      have ha : raw11758step0 = (fun i j => raw11758 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11758step0 raw11758; decide +kernel
      have hl : raw11758step0Labels = raw11758Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11758 raw11758Labels permutation164 permutation4
    mixedMoment B raw11758step0 raw11758step0Labels = mixedMoment B raw11758step1 raw11758step1Labels := by
      have ha : raw11758step1 = -raw11758step0 := by apply Matrix.ext; change ∀ i j, raw11758step1 i j = -(raw11758step0 i j); unfold raw11758step1 raw11758step0; decide +kernel
      have hl : raw11758step1Labels = raw11758step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3376 node3376Labels := by rfl

def raw11759 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11759Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11759step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw11759step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11759step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11759step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11759 raw11759Labels = mixedMoment B node3376 node3376Labels := by
  calc
    mixedMoment B raw11759 raw11759Labels = mixedMoment B raw11759step0 raw11759step0Labels := by
      have ha : raw11759step0 = (fun i j => raw11759 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11759step0 raw11759; decide +kernel
      have hl : raw11759step0Labels = raw11759Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11759 raw11759Labels permutation158 permutation4
    mixedMoment B raw11759step0 raw11759step0Labels = mixedMoment B raw11759step1 raw11759step1Labels := by
      have ha : raw11759step1 = -raw11759step0 := by apply Matrix.ext; change ∀ i j, raw11759step1 i j = -(raw11759step0 i j); unfold raw11759step1 raw11759step0; decide +kernel
      have hl : raw11759step1Labels = raw11759step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3376 node3376Labels := by rfl

def raw11760 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11760Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11760step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw11760step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11760 raw11760Labels = mixedMoment B node2980 node2980Labels := by
  calc
    mixedMoment B raw11760 raw11760Labels = mixedMoment B raw11760step0 raw11760step0Labels := by
      have ha : raw11760step0 = (fun i j => raw11760 (permutation640 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11760step0 raw11760; decide +kernel
      have hl : raw11760step0Labels = raw11760Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11760 raw11760Labels permutation640 permutation4
    _ = mixedMoment B node2980 node2980Labels := by rfl

def raw11761 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11761Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11761step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw11761step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11761step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11761step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11761 raw11761Labels = mixedMoment B node2012 node2012Labels := by
  calc
    mixedMoment B raw11761 raw11761Labels = mixedMoment B raw11761step0 raw11761step0Labels := by
      have ha : raw11761step0 = (fun i j => raw11761 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11761step0 raw11761; decide +kernel
      have hl : raw11761step0Labels = raw11761Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11761 raw11761Labels permutation160 permutation4
    mixedMoment B raw11761step0 raw11761step0Labels = mixedMoment B raw11761step1 raw11761step1Labels := by
      have ha : raw11761step1 = -raw11761step0 := by apply Matrix.ext; change ∀ i j, raw11761step1 i j = -(raw11761step0 i j); unfold raw11761step1 raw11761step0; decide +kernel
      have hl : raw11761step1Labels = raw11761step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2012 node2012Labels := by rfl

def raw11762 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11762Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11762step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw11762step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11762step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11762step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11762 raw11762Labels = mixedMoment B node3500 node3500Labels := by
  calc
    mixedMoment B raw11762 raw11762Labels = mixedMoment B raw11762step0 raw11762step0Labels := by
      have ha : raw11762step0 = (fun i j => raw11762 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11762step0 raw11762; decide +kernel
      have hl : raw11762step0Labels = raw11762Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11762 raw11762Labels permutation160 permutation4
    mixedMoment B raw11762step0 raw11762step0Labels = mixedMoment B raw11762step1 raw11762step1Labels := by
      have ha : raw11762step1 = -raw11762step0 := by apply Matrix.ext; change ∀ i j, raw11762step1 i j = -(raw11762step0 i j); unfold raw11762step1 raw11762step0; decide +kernel
      have hl : raw11762step1Labels = raw11762step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3500 node3500Labels := by rfl

def raw11763 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11763Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw11763step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11763step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw11763step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11763 raw11763Labels = mixedMoment B node3500 node3500Labels := by
  calc
    mixedMoment B raw11763 raw11763Labels = mixedMoment B raw11763step0 raw11763step0Labels := by
      have ha : raw11763step0 = (fun i j => raw11763 (permutation166 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11763step0 raw11763; decide +kernel
      have hl : raw11763step0Labels = raw11763Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11763 raw11763Labels permutation166 permutation4
    mixedMoment B raw11763step0 raw11763step0Labels = mixedMoment B raw11763step1 raw11763step1Labels := by
      have ha : raw11763step1 = -raw11763step0 := by apply Matrix.ext; change ∀ i j, raw11763step1 i j = -(raw11763step0 i j); unfold raw11763step1 raw11763step0; decide +kernel
      have hl : raw11763step1Labels = raw11763step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3500 node3500Labels := by rfl

def raw11764 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11764Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11764step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw11764step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11764step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11764step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11764 raw11764Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw11764 raw11764Labels = mixedMoment B raw11764step0 raw11764step0Labels := by
      have ha : raw11764step0 = (fun i j => raw11764 (permutation161 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11764step0 raw11764; decide +kernel
      have hl : raw11764step0Labels = raw11764Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11764 raw11764Labels permutation161 permutation4
    mixedMoment B raw11764step0 raw11764step0Labels = mixedMoment B raw11764step1 raw11764step1Labels := by
      have ha : raw11764step1 = -raw11764step0 := by apply Matrix.ext; change ∀ i j, raw11764step1 i j = -(raw11764step0 i j); unfold raw11764step1 raw11764step0; decide +kernel
      have hl : raw11764step1Labels = raw11764step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3526 node3526Labels := by rfl

def raw11765 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11765Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11765step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw11765step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11765step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11765step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11765 raw11765Labels = mixedMoment B node2020 node2020Labels := by
  calc
    mixedMoment B raw11765 raw11765Labels = mixedMoment B raw11765step0 raw11765step0Labels := by
      have ha : raw11765step0 = (fun i j => raw11765 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11765step0 raw11765; decide +kernel
      have hl : raw11765step0Labels = raw11765Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11765 raw11765Labels permutation164 permutation4
    mixedMoment B raw11765step0 raw11765step0Labels = mixedMoment B raw11765step1 raw11765step1Labels := by
      have ha : raw11765step1 = -raw11765step0 := by apply Matrix.ext; change ∀ i j, raw11765step1 i j = -(raw11765step0 i j); unfold raw11765step1 raw11765step0; decide +kernel
      have hl : raw11765step1Labels = raw11765step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2020 node2020Labels := by rfl

def raw11766 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11766Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11766step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw11766step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11766step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw11766step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11766 raw11766Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw11766 raw11766Labels = mixedMoment B raw11766step0 raw11766step0Labels := by
      have hz : ∀ j, raw11766 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw11766step0 = (fun i j => raw11766 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw11766step0 raw11766; decide +kernel
      have hl : raw11766step0Labels = raw11766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11766 raw11766Labels permutation346 hz
    mixedMoment B raw11766step0 raw11766step0Labels = mixedMoment B raw11766step1 raw11766step1Labels := by
      have ha : raw11766step1 = (fun i j => raw11766step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11766step1 raw11766step0; decide +kernel
      have hl : raw11766step1Labels = raw11766step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11766step0 raw11766step0Labels permutation34 permutation4
    mixedMoment B raw11766step1 raw11766step1Labels = mixedMoment B raw11766step2 raw11766step2Labels := by
      have ha : raw11766step2 = -raw11766step1 := by apply Matrix.ext; change ∀ i j, raw11766step2 i j = -(raw11766step1 i j); unfold raw11766step2 raw11766step1; decide +kernel
      have hl : raw11766step2Labels = raw11766step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3534 node3534Labels := by rfl

def raw11767 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw11767Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11767step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw11767step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11767step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11767step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11767 raw11767Labels = mixedMoment B node3503 node3503Labels := by
  calc
    mixedMoment B raw11767 raw11767Labels = mixedMoment B raw11767step0 raw11767step0Labels := by
      have ha : raw11767step0 = (fun i j => raw11767 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11767step0 raw11767; decide +kernel
      have hl : raw11767step0Labels = raw11767Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11767 raw11767Labels permutation164 permutation4
    mixedMoment B raw11767step0 raw11767step0Labels = mixedMoment B raw11767step1 raw11767step1Labels := by
      have ha : raw11767step1 = -raw11767step0 := by apply Matrix.ext; change ∀ i j, raw11767step1 i j = -(raw11767step0 i j); unfold raw11767step1 raw11767step0; decide +kernel
      have hl : raw11767step1Labels = raw11767step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3503 node3503Labels := by rfl

def raw11768 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11768Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11768step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11768step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11768step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11768 raw11768Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw11768 raw11768Labels = mixedMoment B raw11768step0 raw11768step0Labels := by
      have ha : raw11768step0 = (fun i j => raw11768 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11768step0 raw11768; decide +kernel
      have hl : raw11768step0Labels = raw11768Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11768 raw11768Labels permutation164 permutation4
    mixedMoment B raw11768step0 raw11768step0Labels = mixedMoment B raw11768step1 raw11768step1Labels := by
      have ha : raw11768step1 = -raw11768step0 := by apply Matrix.ext; change ∀ i j, raw11768step1 i j = -(raw11768step0 i j); unfold raw11768step1 raw11768step0; decide +kernel
      have hl : raw11768step1Labels = raw11768step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3532 node3532Labels := by rfl

def raw11769 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11769Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw11769step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw11769step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11769step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11769step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11769 raw11769Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw11769 raw11769Labels = mixedMoment B raw11769step0 raw11769step0Labels := by
      have hz : ∀ j, raw11769 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw11769step0 = (fun i j => raw11769 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw11769step0 raw11769; decide +kernel
      have hl : raw11769step0Labels = raw11769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11769 raw11769Labels permutation265 hz
    mixedMoment B raw11769step0 raw11769step0Labels = mixedMoment B raw11769step1 raw11769step1Labels := by
      have ha : raw11769step1 = (fun i j => raw11769step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11769step1 raw11769step0; decide +kernel
      have hl : raw11769step1Labels = raw11769step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11769step0 raw11769step0Labels permutation40 permutation4
    mixedMoment B raw11769step1 raw11769step1Labels = mixedMoment B raw11769step2 raw11769step2Labels := by
      have ha : raw11769step2 = -raw11769step1 := by apply Matrix.ext; change ∀ i j, raw11769step2 i j = -(raw11769step1 i j); unfold raw11769step2 raw11769step1; decide +kernel
      have hl : raw11769step2Labels = raw11769step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw11770 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1]]
def raw11770Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw11770step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11770step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11770step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11770 raw11770Labels = mixedMoment B node3503 node3503Labels := by
  calc
    mixedMoment B raw11770 raw11770Labels = mixedMoment B raw11770step0 raw11770step0Labels := by
      have ha : raw11770step0 = (fun i j => raw11770 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11770step0 raw11770; decide +kernel
      have hl : raw11770step0Labels = raw11770Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11770 raw11770Labels permutation158 permutation4
    mixedMoment B raw11770step0 raw11770step0Labels = mixedMoment B raw11770step1 raw11770step1Labels := by
      have ha : raw11770step1 = -raw11770step0 := by apply Matrix.ext; change ∀ i j, raw11770step1 i j = -(raw11770step0 i j); unfold raw11770step1 raw11770step0; decide +kernel
      have hl : raw11770step1Labels = raw11770step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3503 node3503Labels := by rfl

def raw11771 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw11771Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw11771step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11771 raw11771Labels = mixedMoment B node2983 node2983Labels := by
  calc
    mixedMoment B raw11771 raw11771Labels = mixedMoment B raw11771step0 raw11771step0Labels := by
      have ha : raw11771step0 = (fun i j => raw11771 (permutation646 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11771step0 raw11771; decide +kernel
      have hl : raw11771step0Labels = raw11771Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11771 raw11771Labels permutation646 permutation4
    _ = mixedMoment B node2983 node2983Labels := by rfl

def raw11772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11772step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw11772step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11772step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11772step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11772step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11772step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11772 raw11772Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw11772 raw11772Labels = mixedMoment B raw11772step0 raw11772step0Labels := by
      have ha : raw11772step0 = (fun i j => raw11772 (permutation161 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11772step0 raw11772; decide +kernel
      have hl : raw11772step0Labels = raw11772Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11772 raw11772Labels permutation161 permutation7
    mixedMoment B raw11772step0 raw11772step0Labels = mixedMoment B raw11772step1 raw11772step1Labels := by
      have ha : raw11772step1 = -raw11772step0 := by apply Matrix.ext; change ∀ i j, raw11772step1 i j = -(raw11772step0 i j); unfold raw11772step1 raw11772step0; decide +kernel
      have hl : raw11772step1Labels = raw11772step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11772step1 raw11772step1Labels = mixedMoment B raw11772step2 raw11772step2Labels := by
      have ha : raw11772step2 = raw11772step1 := by apply Matrix.ext; unfold raw11772step2 raw11772step1; decide +kernel
      have hl : raw11772step1Labels = labelEmbedding10 ∘ raw11772step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11772step1 raw11772step1Labels raw11772step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw11773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11773step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11773step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11773step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw11773step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11773step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11773 raw11773Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw11773 raw11773Labels = mixedMoment B raw11773step0 raw11773step0Labels := by
      have ha : raw11773step0 = (fun i j => raw11773 (permutation416 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11773step0 raw11773; decide +kernel
      have hl : raw11773step0Labels = raw11773Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11773 raw11773Labels permutation416 permutation4
    mixedMoment B raw11773step0 raw11773step0Labels = mixedMoment B raw11773step1 raw11773step1Labels := by
      have ha : raw11773step1 = -raw11773step0 := by apply Matrix.ext; change ∀ i j, raw11773step1 i j = -(raw11773step0 i j); unfold raw11773step1 raw11773step0; decide +kernel
      have hl : raw11773step1Labels = raw11773step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11773step1 raw11773step1Labels = mixedMoment B raw11773step2 raw11773step2Labels := by
      have ha : raw11773step2 = raw11773step1 := by apply Matrix.ext; unfold raw11773step2 raw11773step1; decide +kernel
      have hl : raw11773step1Labels = labelEmbedding7 ∘ raw11773step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11773step1 raw11773step1Labels raw11773step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw11774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11774step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11774step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11774step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11774step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11774 raw11774Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw11774 raw11774Labels = mixedMoment B raw11774step0 raw11774step0Labels := by
      have hz : ∀ j, raw11774 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11774step0 = (fun i j => raw11774 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11774step0 raw11774; decide +kernel
      have hl : raw11774step0Labels = raw11774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11774 raw11774Labels permutation434 hz
    mixedMoment B raw11774step0 raw11774step0Labels = mixedMoment B raw11774step1 raw11774step1Labels := by
      have ha : raw11774step1 = (fun i j => raw11774step0 (permutation103 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11774step1 raw11774step0; decide +kernel
      have hl : raw11774step1Labels = raw11774step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11774step0 raw11774step0Labels permutation103 permutation6
    mixedMoment B raw11774step1 raw11774step1Labels = mixedMoment B raw11774step2 raw11774step2Labels := by
      have ha : raw11774step2 = raw11774step1 := by apply Matrix.ext; unfold raw11774step2 raw11774step1; decide +kernel
      have hl : raw11774step1Labels = labelEmbedding9 ∘ raw11774step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11774step1 raw11774step1Labels raw11774step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw11775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw11775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw11775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11775step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw11775step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11775step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11775 raw11775Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw11775 raw11775Labels = mixedMoment B raw11775step0 raw11775step0Labels := by
      have hz : ∀ j, raw11775 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11775step0 = (fun i j => raw11775 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11775step0 raw11775; decide +kernel
      have hl : raw11775step0Labels = raw11775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11775 raw11775Labels permutation520 hz
    mixedMoment B raw11775step0 raw11775step0Labels = mixedMoment B raw11775step1 raw11775step1Labels := by
      have ha : raw11775step1 = (fun i j => raw11775step0 (permutation103 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11775step1 raw11775step0; decide +kernel
      have hl : raw11775step1Labels = raw11775step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11775step0 raw11775step0Labels permutation103 permutation6
    mixedMoment B raw11775step1 raw11775step1Labels = mixedMoment B raw11775step2 raw11775step2Labels := by
      have ha : raw11775step2 = raw11775step1 := by apply Matrix.ext; unfold raw11775step2 raw11775step1; decide +kernel
      have hl : raw11775step1Labels = labelEmbedding9 ∘ raw11775step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11775step1 raw11775step1Labels raw11775step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5435 node5435Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
