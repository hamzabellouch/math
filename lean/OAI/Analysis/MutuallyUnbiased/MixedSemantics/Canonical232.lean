import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw29696 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29696Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29696step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29696step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw29696step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29696step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw29696step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29696 raw29696Labels = mixedMoment B node3616 node3616Labels := by
  calc
    mixedMoment B raw29696 raw29696Labels = mixedMoment B raw29696step0 raw29696step0Labels := by
      have hz : ∀ j, raw29696 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29696step0 = (fun i j => raw29696 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29696step0 raw29696; decide +kernel
      have hl : raw29696step0Labels = raw29696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29696 raw29696Labels permutation434 hz
    mixedMoment B raw29696step0 raw29696step0Labels = mixedMoment B raw29696step1 raw29696step1Labels := by
      have hz : ∀ j, raw29696step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29696step1 = (fun i j => raw29696step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29696step1 raw29696step0; decide +kernel
      have hl : raw29696step1Labels = raw29696step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29696step0 raw29696step0Labels permutation80 hz
    mixedMoment B raw29696step1 raw29696step1Labels = mixedMoment B raw29696step2 raw29696step2Labels := by
      have ha : raw29696step2 = -raw29696step1 := by apply Matrix.ext; change ∀ i j, raw29696step2 i j = -(raw29696step1 i j); unfold raw29696step2 raw29696step1; decide +kernel
      have hl : raw29696step2Labels = raw29696step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3616 node3616Labels := by rfl

def raw29697 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29697Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29697step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw29697step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29697 raw29697Labels = mixedMoment B node3482 node3482Labels := by
  calc
    mixedMoment B raw29697 raw29697Labels = mixedMoment B raw29697step0 raw29697step0Labels := by
      have hz : ∀ j, raw29697 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29697step0 = (fun i j => raw29697 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29697step0 raw29697; decide +kernel
      have hl : raw29697step0Labels = raw29697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29697 raw29697Labels permutation346 hz
    mixedMoment B raw29697step0 raw29697step0Labels = mixedMoment B raw29697step1 raw29697step1Labels := by
      have ha : raw29697step1 = -raw29697step0 := by apply Matrix.ext; change ∀ i j, raw29697step1 i j = -(raw29697step0 i j); unfold raw29697step1 raw29697step0; decide +kernel
      have hl : raw29697step1Labels = raw29697step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3482 node3482Labels := by rfl

def raw29698 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29698Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29698step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29698step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-2, 0, 2], ![-1, -1, 2]]
def raw29698step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29698step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29698step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29698step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29698step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29698 raw29698Labels = mixedMoment B node3485 node3485Labels := by
  calc
    mixedMoment B raw29698 raw29698Labels = mixedMoment B raw29698step0 raw29698step0Labels := by
      have hz : ∀ j, raw29698 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29698step0 = (fun i j => raw29698 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29698step0 raw29698; decide +kernel
      have hl : raw29698step0Labels = raw29698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29698 raw29698Labels permutation434 hz
    mixedMoment B raw29698step0 raw29698step0Labels = mixedMoment B raw29698step1 raw29698step1Labels := by
      have hz : ∀ j, raw29698step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29698step1 = (fun i j => raw29698step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29698step1 raw29698step0; decide +kernel
      have hl : raw29698step1Labels = raw29698step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29698step0 raw29698step0Labels permutation80 hz
    mixedMoment B raw29698step1 raw29698step1Labels = mixedMoment B raw29698step2 raw29698step2Labels := by
      have ha : raw29698step2 = (fun i j => raw29698step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29698step2 raw29698step1; decide +kernel
      have hl : raw29698step2Labels = raw29698step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29698step1 raw29698step1Labels permutation9 permutation2
    mixedMoment B raw29698step2 raw29698step2Labels = mixedMoment B raw29698step3 raw29698step3Labels := by
      have ha : raw29698step3 = -raw29698step2 := by apply Matrix.ext; change ∀ i j, raw29698step3 i j = -(raw29698step2 i j); unfold raw29698step3 raw29698step2; decide +kernel
      have hl : raw29698step3Labels = raw29698step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3485 node3485Labels := by rfl

def raw29699 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29699Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29699step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29699step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29699step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29699 raw29699Labels = mixedMoment B node3485 node3485Labels := by
  calc
    mixedMoment B raw29699 raw29699Labels = mixedMoment B raw29699step0 raw29699step0Labels := by
      have hz : ∀ j, raw29699 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29699step0 = (fun i j => raw29699 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29699step0 raw29699; decide +kernel
      have hl : raw29699step0Labels = raw29699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29699 raw29699Labels permutation434 hz
    mixedMoment B raw29699step0 raw29699step0Labels = mixedMoment B raw29699step1 raw29699step1Labels := by
      have hz : ∀ j, raw29699step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29699step1 = (fun i j => raw29699step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29699step1 raw29699step0; decide +kernel
      have hl : raw29699step1Labels = raw29699step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29699step0 raw29699step0Labels permutation80 hz
    mixedMoment B raw29699step1 raw29699step1Labels = mixedMoment B raw29699step2 raw29699step2Labels := by
      have ha : raw29699step2 = -raw29699step1 := by apply Matrix.ext; change ∀ i j, raw29699step2 i j = -(raw29699step1 i j); unfold raw29699step2 raw29699step1; decide +kernel
      have hl : raw29699step2Labels = raw29699step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3485 node3485Labels := by rfl

def raw29700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29700Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29700step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29700 raw29700Labels = mixedMoment B node1171 node1171Labels := by
  calc
    mixedMoment B raw29700 raw29700Labels = mixedMoment B raw29700step0 raw29700step0Labels := by
      have hz : ∀ j, raw29700 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29700step0 = (fun i j => raw29700 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29700step0 raw29700; decide +kernel
      have hl : raw29700step0Labels = raw29700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29700 raw29700Labels permutation346 hz
    _ = mixedMoment B node1171 node1171Labels := by rfl

def raw29701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29701Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29701step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29701 raw29701Labels = mixedMoment B node2362 node2362Labels := by
  calc
    mixedMoment B raw29701 raw29701Labels = mixedMoment B raw29701step0 raw29701step0Labels := by
      have hz : ∀ j, raw29701 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29701step0 = (fun i j => raw29701 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29701step0 raw29701; decide +kernel
      have hl : raw29701step0Labels = raw29701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29701 raw29701Labels permutation346 hz
    _ = mixedMoment B node2362 node2362Labels := by rfl

def raw29702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29702Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29702 raw29702Labels = mixedMoment B node2529 node2529Labels := by
  calc
    _ = mixedMoment B node2529 node2529Labels := by rfl

def raw29703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29703Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29703step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29703 raw29703Labels = mixedMoment B node2575 node2575Labels := by
  calc
    mixedMoment B raw29703 raw29703Labels = mixedMoment B raw29703step0 raw29703step0Labels := by
      have hz : ∀ j, raw29703 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29703step0 = (fun i j => raw29703 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29703step0 raw29703; decide +kernel
      have hl : raw29703step0Labels = raw29703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29703 raw29703Labels permutation346 hz
    _ = mixedMoment B node2575 node2575Labels := by rfl

def raw29704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw29704Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw29704step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw29704step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29704 raw29704Labels = mixedMoment B node2600 node2600Labels := by
  calc
    mixedMoment B raw29704 raw29704Labels = mixedMoment B raw29704step0 raw29704step0Labels := by
      have hz : ∀ j, raw29704 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29704step0 = (fun i j => raw29704 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29704step0 raw29704; decide +kernel
      have hl : raw29704step0Labels = raw29704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29704 raw29704Labels permutation346 hz
    mixedMoment B raw29704step0 raw29704step0Labels = mixedMoment B raw29704step1 raw29704step1Labels := by
      have ha : raw29704step1 = (fun i j => raw29704step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29704step1 raw29704step0; decide +kernel
      have hl : raw29704step1Labels = raw29704step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29704step0 raw29704step0Labels permutation33 permutation2
    _ = mixedMoment B node2600 node2600Labels := by rfl

def raw29705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 1, -3], ![2, -2, 0]]
def raw29705Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 1, -3], ![2, -2, 0]]
def raw29705step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29705step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw29705step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29705step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw29705step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29705 raw29705Labels = mixedMoment B node3394 node3394Labels := by
  calc
    mixedMoment B raw29705 raw29705Labels = mixedMoment B raw29705step0 raw29705step0Labels := by
      have hz : ∀ j, raw29705 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29705step0 = (fun i j => raw29705 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29705step0 raw29705; decide +kernel
      have hl : raw29705step0Labels = raw29705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29705 raw29705Labels permutation346 hz
    mixedMoment B raw29705step0 raw29705step0Labels = mixedMoment B raw29705step1 raw29705step1Labels := by
      have ha : raw29705step1 = (fun i j => raw29705step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29705step1 raw29705step0; decide +kernel
      have hl : raw29705step1Labels = raw29705step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29705step0 raw29705step0Labels permutation125 permutation2
    mixedMoment B raw29705step1 raw29705step1Labels = mixedMoment B raw29705step2 raw29705step2Labels := by
      have ha : raw29705step2 = -raw29705step1 := by apply Matrix.ext; change ∀ i j, raw29705step2 i j = -(raw29705step1 i j); unfold raw29705step2 raw29705step1; decide +kernel
      have hl : raw29705step2Labels = raw29705step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3394 node3394Labels := by rfl

def raw29706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 1, -3], ![2, -2, 0]]
def raw29706Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 1, -3], ![2, -2, 0]]
def raw29706step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29706step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29706 raw29706Labels = mixedMoment B node2930 node2930Labels := by
  calc
    mixedMoment B raw29706 raw29706Labels = mixedMoment B raw29706step0 raw29706step0Labels := by
      have hz : ∀ j, raw29706 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29706step0 = (fun i j => raw29706 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29706step0 raw29706; decide +kernel
      have hl : raw29706step0Labels = raw29706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29706 raw29706Labels permutation346 hz
    mixedMoment B raw29706step0 raw29706step0Labels = mixedMoment B raw29706step1 raw29706step1Labels := by
      have ha : raw29706step1 = (fun i j => raw29706step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29706step1 raw29706step0; decide +kernel
      have hl : raw29706step1Labels = raw29706step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29706step0 raw29706step0Labels permutation39 permutation2
    _ = mixedMoment B node2930 node2930Labels := by rfl

def raw29707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 1, -3], ![2, -2, 0]]
def raw29707Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29707step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29707step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29707 raw29707Labels = mixedMoment B node2892 node2892Labels := by
  calc
    mixedMoment B raw29707 raw29707Labels = mixedMoment B raw29707step0 raw29707step0Labels := by
      have ha : raw29707step0 = (fun i j => raw29707 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29707step0 raw29707; decide +kernel
      have hl : raw29707step0Labels = raw29707Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29707 raw29707Labels permutation159 permutation2
    _ = mixedMoment B node2892 node2892Labels := by rfl

def raw29708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw29708Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw29708step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29708step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29708 raw29708Labels = mixedMoment B node2930 node2930Labels := by
  calc
    mixedMoment B raw29708 raw29708Labels = mixedMoment B raw29708step0 raw29708step0Labels := by
      have hz : ∀ j, raw29708 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29708step0 = (fun i j => raw29708 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29708step0 raw29708; decide +kernel
      have hl : raw29708step0Labels = raw29708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29708 raw29708Labels permutation346 hz
    mixedMoment B raw29708step0 raw29708step0Labels = mixedMoment B raw29708step1 raw29708step1Labels := by
      have ha : raw29708step1 = (fun i j => raw29708step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29708step1 raw29708step0; decide +kernel
      have hl : raw29708step1Labels = raw29708step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29708step0 raw29708step0Labels permutation33 permutation2
    _ = mixedMoment B node2930 node2930Labels := by rfl

def raw29709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3], ![2, -2, 0]]
def raw29709Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![3, 0, -3], ![2, -2, 0]]
def raw29709step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29709step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29709step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29709step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29709 raw29709Labels = mixedMoment B node1812 node1812Labels := by
  calc
    mixedMoment B raw29709 raw29709Labels = mixedMoment B raw29709step0 raw29709step0Labels := by
      have hz : ∀ j, raw29709 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29709step0 = (fun i j => raw29709 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29709step0 raw29709; decide +kernel
      have hl : raw29709step0Labels = raw29709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29709 raw29709Labels permutation346 hz
    mixedMoment B raw29709step0 raw29709step0Labels = mixedMoment B raw29709step1 raw29709step1Labels := by
      have ha : raw29709step1 = (fun i j => raw29709step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29709step1 raw29709step0; decide +kernel
      have hl : raw29709step1Labels = raw29709step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29709step0 raw29709step0Labels permutation125 permutation2
    mixedMoment B raw29709step1 raw29709step1Labels = mixedMoment B raw29709step2 raw29709step2Labels := by
      have ha : raw29709step2 = -raw29709step1 := by apply Matrix.ext; change ∀ i j, raw29709step2 i j = -(raw29709step1 i j); unfold raw29709step2 raw29709step1; decide +kernel
      have hl : raw29709step2Labels = raw29709step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1812 node1812Labels := by rfl

def raw29710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw29710Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw29710step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29710 raw29710Labels = mixedMoment B node2899 node2899Labels := by
  calc
    mixedMoment B raw29710 raw29710Labels = mixedMoment B raw29710step0 raw29710step0Labels := by
      have hz : ∀ j, raw29710 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29710step0 = (fun i j => raw29710 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29710step0 raw29710; decide +kernel
      have hl : raw29710step0Labels = raw29710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29710 raw29710Labels permutation346 hz
    _ = mixedMoment B node2899 node2899Labels := by rfl

def raw29711 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![-1, 1], ![3, -3], ![0, 0]]
def raw29711Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29711step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![-1, 1], ![3, -3]]
def raw29711step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29711step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw29711step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29711step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw29711step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29711step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw29711step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29711 raw29711Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw29711 raw29711Labels = mixedMoment B raw29711step0 raw29711step0Labels := by
      have hz : ∀ j, raw29711 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw29711step0 = (fun i j => raw29711 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw29711step0 raw29711; decide +kernel
      have hl : raw29711step0Labels = raw29711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29711 raw29711Labels permutation590 hz
    mixedMoment B raw29711step0 raw29711step0Labels = mixedMoment B raw29711step1 raw29711step1Labels := by
      have hz : ∀ j, raw29711step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29711step1 = (fun i j => raw29711step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29711step1 raw29711step0; decide +kernel
      have hl : raw29711step1Labels = raw29711step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29711step0 raw29711step0Labels permutation80 hz
    mixedMoment B raw29711step1 raw29711step1Labels = mixedMoment B raw29711step2 raw29711step2Labels := by
      have ha : raw29711step2 = (fun i j => raw29711step1 (permutation26 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29711step2 raw29711step1; decide +kernel
      have hl : raw29711step2Labels = raw29711step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29711step1 raw29711step1Labels permutation26 permutation0
    mixedMoment B raw29711step2 raw29711step2Labels = mixedMoment B raw29711step3 raw29711step3Labels := by
      have ha : raw29711step3 = -raw29711step2 := by apply Matrix.ext; change ∀ i j, raw29711step3 i j = -(raw29711step2 i j); unfold raw29711step3 raw29711step2; decide +kernel
      have hl : raw29711step3Labels = raw29711step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw29712 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29712Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29712step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw29712step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29712 raw29712Labels = mixedMoment B node2399 node2399Labels := by
  calc
    mixedMoment B raw29712 raw29712Labels = mixedMoment B raw29712step0 raw29712step0Labels := by
      have hz : ∀ j, raw29712 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29712step0 = (fun i j => raw29712 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29712step0 raw29712; decide +kernel
      have hl : raw29712step0Labels = raw29712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29712 raw29712Labels permutation346 hz
    mixedMoment B raw29712step0 raw29712step0Labels = mixedMoment B raw29712step1 raw29712step1Labels := by
      have ha : raw29712step1 = (fun i j => raw29712step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29712step1 raw29712step0; decide +kernel
      have hl : raw29712step1Labels = raw29712step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29712step0 raw29712step0Labels permutation127 permutation2
    _ = mixedMoment B node2399 node2399Labels := by rfl

def raw29713 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29713Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![2, -2, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29713step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29713step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw29713step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29713 raw29713Labels = mixedMoment B node2405 node2405Labels := by
  calc
    mixedMoment B raw29713 raw29713Labels = mixedMoment B raw29713step0 raw29713step0Labels := by
      have hz : ∀ j, raw29713 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29713step0 = (fun i j => raw29713 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29713step0 raw29713; decide +kernel
      have hl : raw29713step0Labels = raw29713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29713 raw29713Labels permutation346 hz
    mixedMoment B raw29713step0 raw29713step0Labels = mixedMoment B raw29713step1 raw29713step1Labels := by
      have ha : raw29713step1 = (fun i j => raw29713step0 (permutation124 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29713step1 raw29713step0; decide +kernel
      have hl : raw29713step1Labels = raw29713step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29713step0 raw29713step0Labels permutation124 permutation2
    _ = mixedMoment B node2405 node2405Labels := by rfl

def raw29714 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29714Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29714step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw29714step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29714 raw29714Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw29714 raw29714Labels = mixedMoment B raw29714step0 raw29714step0Labels := by
      have hz : ∀ j, raw29714 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29714step0 = (fun i j => raw29714 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29714step0 raw29714; decide +kernel
      have hl : raw29714step0Labels = raw29714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29714 raw29714Labels permutation346 hz
    mixedMoment B raw29714step0 raw29714step0Labels = mixedMoment B raw29714step1 raw29714step1Labels := by
      have ha : raw29714step1 = (fun i j => raw29714step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29714step1 raw29714step0; decide +kernel
      have hl : raw29714step1Labels = raw29714step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29714step0 raw29714step0Labels permutation127 permutation2
    _ = mixedMoment B node2681 node2681Labels := by rfl

def raw29715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29715Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29715step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29715step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29715 raw29715Labels = mixedMoment B node4961 node4961Labels := by
  calc
    mixedMoment B raw29715 raw29715Labels = mixedMoment B raw29715step0 raw29715step0Labels := by
      have ha : raw29715step0 = (fun i j => raw29715 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29715step0 raw29715; decide +kernel
      have hl : raw29715step0Labels = raw29715Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29715 raw29715Labels permutation158 permutation2
    _ = mixedMoment B node4961 node4961Labels := by rfl

def raw29716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29716Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw29716step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29716 raw29716Labels = mixedMoment B node5119 node5119Labels := by
  calc
    mixedMoment B raw29716 raw29716Labels = mixedMoment B raw29716step0 raw29716step0Labels := by
      have ha : raw29716step0 = (fun i j => raw29716 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29716step0 raw29716; decide +kernel
      have hl : raw29716step0Labels = raw29716Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29716 raw29716Labels permutation158 permutation2
    _ = mixedMoment B node5119 node5119Labels := by rfl

def raw29717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw29717Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw29717step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29717 raw29717Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw29717 raw29717Labels = mixedMoment B raw29717step0 raw29717step0Labels := by
      have ha : raw29717step0 = (fun i j => raw29717 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29717step0 raw29717; decide +kernel
      have hl : raw29717step0Labels = raw29717Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29717 raw29717Labels permutation159 permutation2
    _ = mixedMoment B node5149 node5149Labels := by rfl

def raw29718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29718Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29718step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29718 raw29718Labels = mixedMoment B node4977 node4977Labels := by
  calc
    mixedMoment B raw29718 raw29718Labels = mixedMoment B raw29718step0 raw29718step0Labels := by
      have hz : ∀ j, raw29718 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29718step0 = (fun i j => raw29718 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29718step0 raw29718; decide +kernel
      have hl : raw29718step0Labels = raw29718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29718 raw29718Labels permutation346 hz
    _ = mixedMoment B node4977 node4977Labels := by rfl

def raw29719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29719Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29719 raw29719Labels = mixedMoment B node5117 node5117Labels := by
  calc
    _ = mixedMoment B node5117 node5117Labels := by rfl

def raw29720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw29720Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw29720step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29720step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29720 raw29720Labels = mixedMoment B node5172 node5172Labels := by
  calc
    mixedMoment B raw29720 raw29720Labels = mixedMoment B raw29720step0 raw29720step0Labels := by
      have hz : ∀ j, raw29720 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29720step0 = (fun i j => raw29720 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29720step0 raw29720; decide +kernel
      have hl : raw29720step0Labels = raw29720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29720 raw29720Labels permutation346 hz
    mixedMoment B raw29720step0 raw29720step0Labels = mixedMoment B raw29720step1 raw29720step1Labels := by
      have ha : raw29720step1 = (fun i j => raw29720step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29720step1 raw29720step0; decide +kernel
      have hl : raw29720step1Labels = raw29720step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29720step0 raw29720step0Labels permutation33 permutation2
    _ = mixedMoment B node5172 node5172Labels := by rfl

def raw29721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw29721Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw29721step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw29721step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29721step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw29721step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29721step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw29721step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29721 raw29721Labels = mixedMoment B node4638 node4638Labels := by
  calc
    mixedMoment B raw29721 raw29721Labels = mixedMoment B raw29721step0 raw29721step0Labels := by
      have hz : ∀ j, raw29721 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29721step0 = (fun i j => raw29721 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29721step0 raw29721; decide +kernel
      have hl : raw29721step0Labels = raw29721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29721 raw29721Labels permutation346 hz
    mixedMoment B raw29721step0 raw29721step0Labels = mixedMoment B raw29721step1 raw29721step1Labels := by
      have ha : raw29721step1 = (fun i j => raw29721step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29721step1 raw29721step0; decide +kernel
      have hl : raw29721step1Labels = raw29721step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29721step0 raw29721step0Labels permutation127 permutation3
    mixedMoment B raw29721step1 raw29721step1Labels = mixedMoment B raw29721step2 raw29721step2Labels := by
      have ha : raw29721step2 = -raw29721step1 := by apply Matrix.ext; change ∀ i j, raw29721step2 i j = -(raw29721step1 i j); unfold raw29721step2 raw29721step1; decide +kernel
      have hl : raw29721step2Labels = raw29721step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29721step2 raw29721step2Labels = mixedMoment B raw29721step3 raw29721step3Labels := by
      have ha : raw29721step3 = raw29721step2 := by apply Matrix.ext; unfold raw29721step3 raw29721step2; decide +kernel
      have hl : raw29721step2Labels = labelEmbedding6 ∘ raw29721step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29721step2 raw29721step2Labels raw29721step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4638 node4638Labels := by rfl

def raw29722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw29722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29722step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29722step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29722step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29722step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29722step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29722step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29722 raw29722Labels = mixedMoment B node4633 node4633Labels := by
  calc
    mixedMoment B raw29722 raw29722Labels = mixedMoment B raw29722step0 raw29722step0Labels := by
      have ha : raw29722step0 = (fun i j => raw29722 (permutation587 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29722step0 raw29722; decide +kernel
      have hl : raw29722step0Labels = raw29722Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29722 raw29722Labels permutation587 permutation3
    mixedMoment B raw29722step0 raw29722step0Labels = mixedMoment B raw29722step1 raw29722step1Labels := by
      have ha : raw29722step1 = -raw29722step0 := by apply Matrix.ext; change ∀ i j, raw29722step1 i j = -(raw29722step0 i j); unfold raw29722step1 raw29722step0; decide +kernel
      have hl : raw29722step1Labels = raw29722step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29722step1 raw29722step1Labels = mixedMoment B raw29722step2 raw29722step2Labels := by
      have ha : raw29722step2 = raw29722step1 := by apply Matrix.ext; unfold raw29722step2 raw29722step1; decide +kernel
      have hl : raw29722step1Labels = labelEmbedding6 ∘ raw29722step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29722step1 raw29722step1Labels raw29722step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4633 node4633Labels := by rfl

def raw29723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw29723Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw29723step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw29723step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29723step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw29723step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29723step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw29723step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29723 raw29723Labels = mixedMoment B node4650 node4650Labels := by
  calc
    mixedMoment B raw29723 raw29723Labels = mixedMoment B raw29723step0 raw29723step0Labels := by
      have hz : ∀ j, raw29723 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29723step0 = (fun i j => raw29723 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29723step0 raw29723; decide +kernel
      have hl : raw29723step0Labels = raw29723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29723 raw29723Labels permutation346 hz
    mixedMoment B raw29723step0 raw29723step0Labels = mixedMoment B raw29723step1 raw29723step1Labels := by
      have ha : raw29723step1 = (fun i j => raw29723step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29723step1 raw29723step0; decide +kernel
      have hl : raw29723step1Labels = raw29723step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29723step0 raw29723step0Labels permutation125 permutation3
    mixedMoment B raw29723step1 raw29723step1Labels = mixedMoment B raw29723step2 raw29723step2Labels := by
      have ha : raw29723step2 = -raw29723step1 := by apply Matrix.ext; change ∀ i j, raw29723step2 i j = -(raw29723step1 i j); unfold raw29723step2 raw29723step1; decide +kernel
      have hl : raw29723step2Labels = raw29723step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29723step2 raw29723step2Labels = mixedMoment B raw29723step3 raw29723step3Labels := by
      have ha : raw29723step3 = raw29723step2 := by apply Matrix.ext; unfold raw29723step3 raw29723step2; decide +kernel
      have hl : raw29723step2Labels = labelEmbedding6 ∘ raw29723step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29723step2 raw29723step2Labels raw29723step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4650 node4650Labels := by rfl

def raw29724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw29724Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw29724step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29724step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29724step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29724step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29724step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29724 raw29724Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw29724 raw29724Labels = mixedMoment B raw29724step0 raw29724step0Labels := by
      have hz : ∀ j, raw29724 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29724step0 = (fun i j => raw29724 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29724step0 raw29724; decide +kernel
      have hl : raw29724step0Labels = raw29724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29724 raw29724Labels permutation346 hz
    mixedMoment B raw29724step0 raw29724step0Labels = mixedMoment B raw29724step1 raw29724step1Labels := by
      have ha : raw29724step1 = (fun i j => raw29724step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29724step1 raw29724step0; decide +kernel
      have hl : raw29724step1Labels = raw29724step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29724step0 raw29724step0Labels permutation127 permutation3
    mixedMoment B raw29724step1 raw29724step1Labels = mixedMoment B raw29724step2 raw29724step2Labels := by
      have ha : raw29724step2 = -raw29724step1 := by apply Matrix.ext; change ∀ i j, raw29724step2 i j = -(raw29724step1 i j); unfold raw29724step2 raw29724step1; decide +kernel
      have hl : raw29724step2Labels = raw29724step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29724step2 raw29724step2Labels = mixedMoment B raw29724step3 raw29724step3Labels := by
      have ha : raw29724step3 = raw29724step2 := by apply Matrix.ext; unfold raw29724step3 raw29724step2; decide +kernel
      have hl : raw29724step2Labels = labelEmbedding6 ∘ raw29724step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29724step2 raw29724step2Labels raw29724step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw29725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29725Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29725step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw29725step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29725 raw29725Labels = mixedMoment B node2796 node2796Labels := by
  calc
    mixedMoment B raw29725 raw29725Labels = mixedMoment B raw29725step0 raw29725step0Labels := by
      have ha : raw29725step0 = (fun i j => raw29725 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29725step0 raw29725; decide +kernel
      have hl : raw29725step0Labels = raw29725Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29725 raw29725Labels permutation159 permutation3
    _ = mixedMoment B node2796 node2796Labels := by rfl

def raw29726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29726Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29726step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw29726step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29726 raw29726Labels = mixedMoment B node2845 node2845Labels := by
  calc
    mixedMoment B raw29726 raw29726Labels = mixedMoment B raw29726step0 raw29726step0Labels := by
      have ha : raw29726step0 = (fun i j => raw29726 (permutation201 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29726step0 raw29726; decide +kernel
      have hl : raw29726step0Labels = raw29726Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29726 raw29726Labels permutation201 permutation3
    _ = mixedMoment B node2845 node2845Labels := by rfl

def raw29727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw29727Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29727step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29727step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29727 raw29727Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw29727 raw29727Labels = mixedMoment B raw29727step0 raw29727step0Labels := by
      have ha : raw29727step0 = (fun i j => raw29727 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29727step0 raw29727; decide +kernel
      have hl : raw29727step0Labels = raw29727Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29727 raw29727Labels permutation162 permutation3
    _ = mixedMoment B node2924 node2924Labels := by rfl

def raw29728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29728Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29728step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29728step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29728 raw29728Labels = mixedMoment B node2813 node2813Labels := by
  calc
    mixedMoment B raw29728 raw29728Labels = mixedMoment B raw29728step0 raw29728step0Labels := by
      have hz : ∀ j, raw29728 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29728step0 = (fun i j => raw29728 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29728step0 raw29728; decide +kernel
      have hl : raw29728step0Labels = raw29728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29728 raw29728Labels permutation346 hz
    mixedMoment B raw29728step0 raw29728step0Labels = mixedMoment B raw29728step1 raw29728step1Labels := by
      have ha : raw29728step1 = (fun i j => raw29728step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29728step1 raw29728step0; decide +kernel
      have hl : raw29728step1Labels = raw29728step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29728step0 raw29728step0Labels permutation33 permutation3
    _ = mixedMoment B node2813 node2813Labels := by rfl

def raw29729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29729Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29729step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29729step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29729 raw29729Labels = mixedMoment B node2893 node2893Labels := by
  calc
    mixedMoment B raw29729 raw29729Labels = mixedMoment B raw29729step0 raw29729step0Labels := by
      have ha : raw29729step0 = (fun i j => raw29729 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29729step0 raw29729; decide +kernel
      have hl : raw29729step0Labels = raw29729Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29729 raw29729Labels permutation153 permutation3
    _ = mixedMoment B node2893 node2893Labels := by rfl

def raw29730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw29730Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw29730step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw29730step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29730 raw29730Labels = mixedMoment B node2959 node2959Labels := by
  calc
    mixedMoment B raw29730 raw29730Labels = mixedMoment B raw29730step0 raw29730step0Labels := by
      have hz : ∀ j, raw29730 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29730step0 = (fun i j => raw29730 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29730step0 raw29730; decide +kernel
      have hl : raw29730step0Labels = raw29730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29730 raw29730Labels permutation346 hz
    mixedMoment B raw29730step0 raw29730step0Labels = mixedMoment B raw29730step1 raw29730step1Labels := by
      have ha : raw29730step1 = (fun i j => raw29730step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29730step1 raw29730step0; decide +kernel
      have hl : raw29730step1Labels = raw29730step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29730step0 raw29730step0Labels permutation33 permutation3
    _ = mixedMoment B node2959 node2959Labels := by rfl

def raw29731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw29731Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw29731step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw29731step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29731step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw29731step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29731 raw29731Labels = mixedMoment B node1767 node1767Labels := by
  calc
    mixedMoment B raw29731 raw29731Labels = mixedMoment B raw29731step0 raw29731step0Labels := by
      have hz : ∀ j, raw29731 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29731step0 = (fun i j => raw29731 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29731step0 raw29731; decide +kernel
      have hl : raw29731step0Labels = raw29731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29731 raw29731Labels permutation346 hz
    mixedMoment B raw29731step0 raw29731step0Labels = mixedMoment B raw29731step1 raw29731step1Labels := by
      have ha : raw29731step1 = (fun i j => raw29731step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29731step1 raw29731step0; decide +kernel
      have hl : raw29731step1Labels = raw29731step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29731step0 raw29731step0Labels permutation127 permutation3
    mixedMoment B raw29731step1 raw29731step1Labels = mixedMoment B raw29731step2 raw29731step2Labels := by
      have ha : raw29731step2 = -raw29731step1 := by apply Matrix.ext; change ∀ i j, raw29731step2 i j = -(raw29731step1 i j); unfold raw29731step2 raw29731step1; decide +kernel
      have hl : raw29731step2Labels = raw29731step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1767 node1767Labels := by rfl

def raw29732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw29732Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29732step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29732step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29732step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29732step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29732 raw29732Labels = mixedMoment B node1762 node1762Labels := by
  calc
    mixedMoment B raw29732 raw29732Labels = mixedMoment B raw29732step0 raw29732step0Labels := by
      have ha : raw29732step0 = (fun i j => raw29732 (permutation587 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29732step0 raw29732; decide +kernel
      have hl : raw29732step0Labels = raw29732Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29732 raw29732Labels permutation587 permutation3
    mixedMoment B raw29732step0 raw29732step0Labels = mixedMoment B raw29732step1 raw29732step1Labels := by
      have ha : raw29732step1 = -raw29732step0 := by apply Matrix.ext; change ∀ i j, raw29732step1 i j = -(raw29732step0 i j); unfold raw29732step1 raw29732step0; decide +kernel
      have hl : raw29732step1Labels = raw29732step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1762 node1762Labels := by rfl

def raw29733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw29733Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw29733step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw29733step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29733step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw29733step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29733 raw29733Labels = mixedMoment B node1778 node1778Labels := by
  calc
    mixedMoment B raw29733 raw29733Labels = mixedMoment B raw29733step0 raw29733step0Labels := by
      have hz : ∀ j, raw29733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29733step0 = (fun i j => raw29733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29733step0 raw29733; decide +kernel
      have hl : raw29733step0Labels = raw29733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29733 raw29733Labels permutation346 hz
    mixedMoment B raw29733step0 raw29733step0Labels = mixedMoment B raw29733step1 raw29733step1Labels := by
      have ha : raw29733step1 = (fun i j => raw29733step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29733step1 raw29733step0; decide +kernel
      have hl : raw29733step1Labels = raw29733step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29733step0 raw29733step0Labels permutation125 permutation3
    mixedMoment B raw29733step1 raw29733step1Labels = mixedMoment B raw29733step2 raw29733step2Labels := by
      have ha : raw29733step2 = -raw29733step1 := by apply Matrix.ext; change ∀ i j, raw29733step2 i j = -(raw29733step1 i j); unfold raw29733step2 raw29733step1; decide +kernel
      have hl : raw29733step2Labels = raw29733step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1778 node1778Labels := by rfl

def raw29734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw29734Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw29734step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29734step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29734step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29734step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29734 raw29734Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw29734 raw29734Labels = mixedMoment B raw29734step0 raw29734step0Labels := by
      have hz : ∀ j, raw29734 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29734step0 = (fun i j => raw29734 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29734step0 raw29734; decide +kernel
      have hl : raw29734step0Labels = raw29734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29734 raw29734Labels permutation346 hz
    mixedMoment B raw29734step0 raw29734step0Labels = mixedMoment B raw29734step1 raw29734step1Labels := by
      have ha : raw29734step1 = (fun i j => raw29734step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29734step1 raw29734step0; decide +kernel
      have hl : raw29734step1Labels = raw29734step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29734step0 raw29734step0Labels permutation127 permutation3
    mixedMoment B raw29734step1 raw29734step1Labels = mixedMoment B raw29734step2 raw29734step2Labels := by
      have ha : raw29734step2 = -raw29734step1 := by apply Matrix.ext; change ∀ i j, raw29734step2 i j = -(raw29734step1 i j); unfold raw29734step2 raw29734step1; decide +kernel
      have hl : raw29734step2Labels = raw29734step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2025 node2025Labels := by rfl

def raw29735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29735Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29735step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw29735step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29735step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw29735step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29735 raw29735Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw29735 raw29735Labels = mixedMoment B raw29735step0 raw29735step0Labels := by
      have hz : ∀ j, raw29735 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29735step0 = (fun i j => raw29735 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29735step0 raw29735; decide +kernel
      have hl : raw29735step0Labels = raw29735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29735 raw29735Labels permutation346 hz
    mixedMoment B raw29735step0 raw29735step0Labels = mixedMoment B raw29735step1 raw29735step1Labels := by
      have ha : raw29735step1 = (fun i j => raw29735step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29735step1 raw29735step0; decide +kernel
      have hl : raw29735step1Labels = raw29735step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29735step0 raw29735step0Labels permutation151 permutation2
    mixedMoment B raw29735step1 raw29735step1Labels = mixedMoment B raw29735step2 raw29735step2Labels := by
      have ha : raw29735step2 = -raw29735step1 := by apply Matrix.ext; change ∀ i j, raw29735step2 i j = -(raw29735step1 i j); unfold raw29735step2 raw29735step1; decide +kernel
      have hl : raw29735step2Labels = raw29735step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw29736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29736Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29736step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29736step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29736step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29736step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29736step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29736 raw29736Labels = mixedMoment B node4444 node4444Labels := by
  calc
    mixedMoment B raw29736 raw29736Labels = mixedMoment B raw29736step0 raw29736step0Labels := by
      have hz : ∀ j, raw29736 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29736step0 = (fun i j => raw29736 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29736step0 raw29736; decide +kernel
      have hl : raw29736step0Labels = raw29736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29736 raw29736Labels permutation346 hz
    mixedMoment B raw29736step0 raw29736step0Labels = mixedMoment B raw29736step1 raw29736step1Labels := by
      have ha : raw29736step1 = (fun i j => raw29736step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29736step1 raw29736step0; decide +kernel
      have hl : raw29736step1Labels = raw29736step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29736step0 raw29736step0Labels permutation32 permutation3
    mixedMoment B raw29736step1 raw29736step1Labels = mixedMoment B raw29736step2 raw29736step2Labels := by
      have ha : raw29736step2 = raw29736step1 := by apply Matrix.ext; unfold raw29736step2 raw29736step1; decide +kernel
      have hl : raw29736step1Labels = labelEmbedding6 ∘ raw29736step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29736step1 raw29736step1Labels raw29736step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4444 node4444Labels := by rfl

def raw29737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29737Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29737step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29737step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29737step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29737step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29737 raw29737Labels = mixedMoment B node5067 node5067Labels := by
  calc
    mixedMoment B raw29737 raw29737Labels = mixedMoment B raw29737step0 raw29737step0Labels := by
      have ha : raw29737step0 = (fun i j => raw29737 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29737step0 raw29737; decide +kernel
      have hl : raw29737step0Labels = raw29737Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29737 raw29737Labels permutation176 permutation3
    mixedMoment B raw29737step0 raw29737step0Labels = mixedMoment B raw29737step1 raw29737step1Labels := by
      have ha : raw29737step1 = raw29737step0 := by apply Matrix.ext; unfold raw29737step1 raw29737step0; decide +kernel
      have hl : raw29737step0Labels = labelEmbedding6 ∘ raw29737step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29737step0 raw29737step0Labels raw29737step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5067 node5067Labels := by rfl

def raw29738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29738Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29738step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29738step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29738step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29738step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29738 raw29738Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw29738 raw29738Labels = mixedMoment B raw29738step0 raw29738step0Labels := by
      have hz : ∀ j, raw29738 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29738step0 = (fun i j => raw29738 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29738step0 raw29738; decide +kernel
      have hl : raw29738step0Labels = raw29738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29738 raw29738Labels permutation346 hz
    mixedMoment B raw29738step0 raw29738step0Labels = mixedMoment B raw29738step1 raw29738step1Labels := by
      have ha : raw29738step1 = (fun i j => raw29738step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29738step1 raw29738step0; decide +kernel
      have hl : raw29738step1Labels = raw29738step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29738step0 raw29738step0Labels permutation38 permutation3
    mixedMoment B raw29738step1 raw29738step1Labels = mixedMoment B raw29738step2 raw29738step2Labels := by
      have ha : raw29738step2 = raw29738step1 := by apply Matrix.ext; unfold raw29738step2 raw29738step1; decide +kernel
      have hl : raw29738step1Labels = labelEmbedding6 ∘ raw29738step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29738step1 raw29738step1Labels raw29738step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw29739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29739Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29739step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw29739step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw29739step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29739 raw29739Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw29739 raw29739Labels = mixedMoment B raw29739step0 raw29739step0Labels := by
      have hz : ∀ j, raw29739 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29739step0 = (fun i j => raw29739 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29739step0 raw29739; decide +kernel
      have hl : raw29739step0Labels = raw29739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29739 raw29739Labels permutation346 hz
    mixedMoment B raw29739step0 raw29739step0Labels = mixedMoment B raw29739step1 raw29739step1Labels := by
      have ha : raw29739step1 = (fun i j => raw29739step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29739step1 raw29739step0; decide +kernel
      have hl : raw29739step1Labels = raw29739step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29739step0 raw29739step0Labels permutation33 permutation3
    mixedMoment B raw29739step1 raw29739step1Labels = mixedMoment B raw29739step2 raw29739step2Labels := by
      have ha : raw29739step2 = raw29739step1 := by apply Matrix.ext; unfold raw29739step2 raw29739step1; decide +kernel
      have hl : raw29739step1Labels = labelEmbedding6 ∘ raw29739step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29739step1 raw29739step1Labels raw29739step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw29740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29740Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29740step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29740step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29740step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29740 raw29740Labels = mixedMoment B node4332 node4332Labels := by
  calc
    mixedMoment B raw29740 raw29740Labels = mixedMoment B raw29740step0 raw29740step0Labels := by
      have ha : raw29740step0 = (fun i j => raw29740 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29740step0 raw29740; decide +kernel
      have hl : raw29740step0Labels = raw29740Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29740 raw29740Labels permutation158 permutation3
    mixedMoment B raw29740step0 raw29740step0Labels = mixedMoment B raw29740step1 raw29740step1Labels := by
      have ha : raw29740step1 = raw29740step0 := by apply Matrix.ext; unfold raw29740step1 raw29740step0; decide +kernel
      have hl : raw29740step0Labels = labelEmbedding6 ∘ raw29740step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29740step0 raw29740step0Labels raw29740step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4332 node4332Labels := by rfl

def raw29741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29741Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29741step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29741step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29741step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29741 raw29741Labels = mixedMoment B node4933 node4933Labels := by
  calc
    mixedMoment B raw29741 raw29741Labels = mixedMoment B raw29741step0 raw29741step0Labels := by
      have ha : raw29741step0 = (fun i j => raw29741 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29741step0 raw29741; decide +kernel
      have hl : raw29741step0Labels = raw29741Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29741 raw29741Labels permutation158 permutation3
    mixedMoment B raw29741step0 raw29741step0Labels = mixedMoment B raw29741step1 raw29741step1Labels := by
      have ha : raw29741step1 = raw29741step0 := by apply Matrix.ext; unfold raw29741step1 raw29741step0; decide +kernel
      have hl : raw29741step0Labels = labelEmbedding6 ∘ raw29741step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29741step0 raw29741step0Labels raw29741step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4933 node4933Labels := by rfl

def raw29742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29742Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29742step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29742step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29742step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29742 raw29742Labels = mixedMoment B node5117 node5117Labels := by
  calc
    mixedMoment B raw29742 raw29742Labels = mixedMoment B raw29742step0 raw29742step0Labels := by
      have ha : raw29742step0 = (fun i j => raw29742 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29742step0 raw29742; decide +kernel
      have hl : raw29742step0Labels = raw29742Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29742 raw29742Labels permutation158 permutation3
    mixedMoment B raw29742step0 raw29742step0Labels = mixedMoment B raw29742step1 raw29742step1Labels := by
      have ha : raw29742step1 = raw29742step0 := by apply Matrix.ext; unfold raw29742step1 raw29742step0; decide +kernel
      have hl : raw29742step0Labels = labelEmbedding6 ∘ raw29742step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29742step0 raw29742step0Labels raw29742step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5117 node5117Labels := by rfl

def raw29743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29743Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw29743step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29743step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw29743step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29743 raw29743Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw29743 raw29743Labels = mixedMoment B raw29743step0 raw29743step0Labels := by
      have ha : raw29743step0 = (fun i j => raw29743 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29743step0 raw29743; decide +kernel
      have hl : raw29743step0Labels = raw29743Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29743 raw29743Labels permutation162 permutation3
    mixedMoment B raw29743step0 raw29743step0Labels = mixedMoment B raw29743step1 raw29743step1Labels := by
      have ha : raw29743step1 = raw29743step0 := by apply Matrix.ext; unfold raw29743step1 raw29743step0; decide +kernel
      have hl : raw29743step0Labels = labelEmbedding6 ∘ raw29743step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29743step0 raw29743step0Labels raw29743step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

def raw29744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29744Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29744step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29744step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29744step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29744step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29744 raw29744Labels = mixedMoment B node4357 node4357Labels := by
  calc
    mixedMoment B raw29744 raw29744Labels = mixedMoment B raw29744step0 raw29744step0Labels := by
      have hz : ∀ j, raw29744 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29744step0 = (fun i j => raw29744 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29744step0 raw29744; decide +kernel
      have hl : raw29744step0Labels = raw29744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29744 raw29744Labels permutation346 hz
    mixedMoment B raw29744step0 raw29744step0Labels = mixedMoment B raw29744step1 raw29744step1Labels := by
      have ha : raw29744step1 = (fun i j => raw29744step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29744step1 raw29744step0; decide +kernel
      have hl : raw29744step1Labels = raw29744step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29744step0 raw29744step0Labels permutation32 permutation3
    mixedMoment B raw29744step1 raw29744step1Labels = mixedMoment B raw29744step2 raw29744step2Labels := by
      have ha : raw29744step2 = raw29744step1 := by apply Matrix.ext; unfold raw29744step2 raw29744step1; decide +kernel
      have hl : raw29744step1Labels = labelEmbedding6 ∘ raw29744step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29744step1 raw29744step1Labels raw29744step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4357 node4357Labels := by rfl

def raw29745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29745Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29745step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29745step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29745step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29745step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29745 raw29745Labels = mixedMoment B node4951 node4951Labels := by
  calc
    mixedMoment B raw29745 raw29745Labels = mixedMoment B raw29745step0 raw29745step0Labels := by
      have hz : ∀ j, raw29745 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29745step0 = (fun i j => raw29745 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29745step0 raw29745; decide +kernel
      have hl : raw29745step0Labels = raw29745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29745 raw29745Labels permutation346 hz
    mixedMoment B raw29745step0 raw29745step0Labels = mixedMoment B raw29745step1 raw29745step1Labels := by
      have ha : raw29745step1 = (fun i j => raw29745step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29745step1 raw29745step0; decide +kernel
      have hl : raw29745step1Labels = raw29745step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29745step0 raw29745step0Labels permutation32 permutation3
    mixedMoment B raw29745step1 raw29745step1Labels = mixedMoment B raw29745step2 raw29745step2Labels := by
      have ha : raw29745step2 = raw29745step1 := by apply Matrix.ext; unfold raw29745step2 raw29745step1; decide +kernel
      have hl : raw29745step1Labels = labelEmbedding6 ∘ raw29745step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29745step1 raw29745step1Labels raw29745step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4951 node4951Labels := by rfl

def raw29746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29746Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29746step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29746step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29746step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29746 raw29746Labels = mixedMoment B node5040 node5040Labels := by
  calc
    mixedMoment B raw29746 raw29746Labels = mixedMoment B raw29746step0 raw29746step0Labels := by
      have ha : raw29746step0 = (fun i j => raw29746 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29746step0 raw29746; decide +kernel
      have hl : raw29746step0Labels = raw29746Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29746 raw29746Labels permutation176 permutation3
    mixedMoment B raw29746step0 raw29746step0Labels = mixedMoment B raw29746step1 raw29746step1Labels := by
      have ha : raw29746step1 = raw29746step0 := by apply Matrix.ext; unfold raw29746step1 raw29746step0; decide +kernel
      have hl : raw29746step0Labels = labelEmbedding6 ∘ raw29746step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29746step0 raw29746step0Labels raw29746step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5040 node5040Labels := by rfl

def raw29747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29747Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29747step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw29747step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29747step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw29747step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29747 raw29747Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw29747 raw29747Labels = mixedMoment B raw29747step0 raw29747step0Labels := by
      have hz : ∀ j, raw29747 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29747step0 = (fun i j => raw29747 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29747step0 raw29747; decide +kernel
      have hl : raw29747step0Labels = raw29747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29747 raw29747Labels permutation346 hz
    mixedMoment B raw29747step0 raw29747step0Labels = mixedMoment B raw29747step1 raw29747step1Labels := by
      have ha : raw29747step1 = (fun i j => raw29747step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29747step1 raw29747step0; decide +kernel
      have hl : raw29747step1Labels = raw29747step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29747step0 raw29747step0Labels permutation36 permutation3
    mixedMoment B raw29747step1 raw29747step1Labels = mixedMoment B raw29747step2 raw29747step2Labels := by
      have ha : raw29747step2 = raw29747step1 := by apply Matrix.ext; unfold raw29747step2 raw29747step1; decide +kernel
      have hl : raw29747step1Labels = labelEmbedding6 ∘ raw29747step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29747step1 raw29747step1Labels raw29747step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5170 node5170Labels := by rfl

def raw29748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29748Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29748step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29748step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29748step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29748step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29748 raw29748Labels = mixedMoment B node4335 node4335Labels := by
  calc
    mixedMoment B raw29748 raw29748Labels = mixedMoment B raw29748step0 raw29748step0Labels := by
      have hz : ∀ j, raw29748 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29748step0 = (fun i j => raw29748 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29748step0 raw29748; decide +kernel
      have hl : raw29748step0Labels = raw29748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29748 raw29748Labels permutation346 hz
    mixedMoment B raw29748step0 raw29748step0Labels = mixedMoment B raw29748step1 raw29748step1Labels := by
      have ha : raw29748step1 = (fun i j => raw29748step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29748step1 raw29748step0; decide +kernel
      have hl : raw29748step1Labels = raw29748step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29748step0 raw29748step0Labels permutation33 permutation3
    mixedMoment B raw29748step1 raw29748step1Labels = mixedMoment B raw29748step2 raw29748step2Labels := by
      have ha : raw29748step2 = raw29748step1 := by apply Matrix.ext; unfold raw29748step2 raw29748step1; decide +kernel
      have hl : raw29748step1Labels = labelEmbedding6 ∘ raw29748step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29748step1 raw29748step1Labels raw29748step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4335 node4335Labels := by rfl

def raw29749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29749Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29749step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29749step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw29749step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29749step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29749step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29749 raw29749Labels = mixedMoment B node4935 node4935Labels := by
  calc
    mixedMoment B raw29749 raw29749Labels = mixedMoment B raw29749step0 raw29749step0Labels := by
      have hz : ∀ j, raw29749 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29749step0 = (fun i j => raw29749 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29749step0 raw29749; decide +kernel
      have hl : raw29749step0Labels = raw29749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29749 raw29749Labels permutation346 hz
    mixedMoment B raw29749step0 raw29749step0Labels = mixedMoment B raw29749step1 raw29749step1Labels := by
      have ha : raw29749step1 = (fun i j => raw29749step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29749step1 raw29749step0; decide +kernel
      have hl : raw29749step1Labels = raw29749step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29749step0 raw29749step0Labels permutation127 permutation2
    mixedMoment B raw29749step1 raw29749step1Labels = mixedMoment B raw29749step2 raw29749step2Labels := by
      have ha : raw29749step2 = -raw29749step1 := by apply Matrix.ext; change ∀ i j, raw29749step2 i j = -(raw29749step1 i j); unfold raw29749step2 raw29749step1; decide +kernel
      have hl : raw29749step2Labels = raw29749step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4935 node4935Labels := by rfl

def raw29750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29750Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw29750step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29750step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw29750step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29750 raw29750Labels = mixedMoment B node4930 node4930Labels := by
  calc
    mixedMoment B raw29750 raw29750Labels = mixedMoment B raw29750step0 raw29750step0Labels := by
      have ha : raw29750step0 = (fun i j => raw29750 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29750step0 raw29750; decide +kernel
      have hl : raw29750step0Labels = raw29750Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29750 raw29750Labels permutation589 permutation2
    mixedMoment B raw29750step0 raw29750step0Labels = mixedMoment B raw29750step1 raw29750step1Labels := by
      have ha : raw29750step1 = -raw29750step0 := by apply Matrix.ext; change ∀ i j, raw29750step1 i j = -(raw29750step0 i j); unfold raw29750step1 raw29750step0; decide +kernel
      have hl : raw29750step1Labels = raw29750step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4930 node4930Labels := by rfl

def raw29751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29751Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29751step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29751step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29751step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29751 raw29751Labels = mixedMoment B node4948 node4948Labels := by
  calc
    mixedMoment B raw29751 raw29751Labels = mixedMoment B raw29751step0 raw29751step0Labels := by
      have hz : ∀ j, raw29751 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29751step0 = (fun i j => raw29751 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29751step0 raw29751; decide +kernel
      have hl : raw29751step0Labels = raw29751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29751 raw29751Labels permutation346 hz
    mixedMoment B raw29751step0 raw29751step0Labels = mixedMoment B raw29751step1 raw29751step1Labels := by
      have ha : raw29751step1 = (fun i j => raw29751step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29751step1 raw29751step0; decide +kernel
      have hl : raw29751step1Labels = raw29751step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29751step0 raw29751step0Labels permutation125 permutation2
    mixedMoment B raw29751step1 raw29751step1Labels = mixedMoment B raw29751step2 raw29751step2Labels := by
      have ha : raw29751step2 = -raw29751step1 := by apply Matrix.ext; change ∀ i j, raw29751step2 i j = -(raw29751step1 i j); unfold raw29751step2 raw29751step1; decide +kernel
      have hl : raw29751step2Labels = raw29751step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4948 node4948Labels := by rfl

def raw29752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw29752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw29752step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29752step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29752step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29752step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29752 raw29752Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw29752 raw29752Labels = mixedMoment B raw29752step0 raw29752step0Labels := by
      have hz : ∀ j, raw29752 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29752step0 = (fun i j => raw29752 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29752step0 raw29752; decide +kernel
      have hl : raw29752step0Labels = raw29752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29752 raw29752Labels permutation346 hz
    mixedMoment B raw29752step0 raw29752step0Labels = mixedMoment B raw29752step1 raw29752step1Labels := by
      have ha : raw29752step1 = (fun i j => raw29752step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29752step1 raw29752step0; decide +kernel
      have hl : raw29752step1Labels = raw29752step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29752step0 raw29752step0Labels permutation127 permutation2
    mixedMoment B raw29752step1 raw29752step1Labels = mixedMoment B raw29752step2 raw29752step2Labels := by
      have ha : raw29752step2 = -raw29752step1 := by apply Matrix.ext; change ∀ i j, raw29752step2 i j = -(raw29752step1 i j); unfold raw29752step2 raw29752step1; decide +kernel
      have hl : raw29752step2Labels = raw29752step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw29753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29753Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29753step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29753step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw29753step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29753step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw29753step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29753 raw29753Labels = mixedMoment B node4334 node4334Labels := by
  calc
    mixedMoment B raw29753 raw29753Labels = mixedMoment B raw29753step0 raw29753step0Labels := by
      have hz : ∀ j, raw29753 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29753step0 = (fun i j => raw29753 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29753step0 raw29753; decide +kernel
      have hl : raw29753step0Labels = raw29753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29753 raw29753Labels permutation346 hz
    mixedMoment B raw29753step0 raw29753step0Labels = mixedMoment B raw29753step1 raw29753step1Labels := by
      have ha : raw29753step1 = (fun i j => raw29753step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29753step1 raw29753step0; decide +kernel
      have hl : raw29753step1Labels = raw29753step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29753step0 raw29753step0Labels permutation32 permutation3
    mixedMoment B raw29753step1 raw29753step1Labels = mixedMoment B raw29753step2 raw29753step2Labels := by
      have ha : raw29753step2 = raw29753step1 := by apply Matrix.ext; unfold raw29753step2 raw29753step1; decide +kernel
      have hl : raw29753step1Labels = labelEmbedding6 ∘ raw29753step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29753step1 raw29753step1Labels raw29753step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4334 node4334Labels := by rfl

def raw29754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29754Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29754step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw29754step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29754step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw29754step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29754 raw29754Labels = mixedMoment B node4934 node4934Labels := by
  calc
    mixedMoment B raw29754 raw29754Labels = mixedMoment B raw29754step0 raw29754step0Labels := by
      have hz : ∀ j, raw29754 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29754step0 = (fun i j => raw29754 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29754step0 raw29754; decide +kernel
      have hl : raw29754step0Labels = raw29754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29754 raw29754Labels permutation346 hz
    mixedMoment B raw29754step0 raw29754step0Labels = mixedMoment B raw29754step1 raw29754step1Labels := by
      have ha : raw29754step1 = (fun i j => raw29754step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29754step1 raw29754step0; decide +kernel
      have hl : raw29754step1Labels = raw29754step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29754step0 raw29754step0Labels permutation32 permutation3
    mixedMoment B raw29754step1 raw29754step1Labels = mixedMoment B raw29754step2 raw29754step2Labels := by
      have ha : raw29754step2 = raw29754step1 := by apply Matrix.ext; unfold raw29754step2 raw29754step1; decide +kernel
      have hl : raw29754step1Labels = labelEmbedding6 ∘ raw29754step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29754step1 raw29754step1Labels raw29754step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4934 node4934Labels := by rfl

def raw29755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29755Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29755step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29755step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29755step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29755step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29755step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29755 raw29755Labels = mixedMoment B node4954 node4954Labels := by
  calc
    mixedMoment B raw29755 raw29755Labels = mixedMoment B raw29755step0 raw29755step0Labels := by
      have ha : raw29755step0 = (fun i j => raw29755 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29755step0 raw29755; decide +kernel
      have hl : raw29755step0Labels = raw29755Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29755 raw29755Labels permutation686 permutation3
    mixedMoment B raw29755step0 raw29755step0Labels = mixedMoment B raw29755step1 raw29755step1Labels := by
      have ha : raw29755step1 = -raw29755step0 := by apply Matrix.ext; change ∀ i j, raw29755step1 i j = -(raw29755step0 i j); unfold raw29755step1 raw29755step0; decide +kernel
      have hl : raw29755step1Labels = raw29755step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29755step1 raw29755step1Labels = mixedMoment B raw29755step2 raw29755step2Labels := by
      have ha : raw29755step2 = raw29755step1 := by apply Matrix.ext; unfold raw29755step2 raw29755step1; decide +kernel
      have hl : raw29755step1Labels = labelEmbedding6 ∘ raw29755step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29755step1 raw29755step1Labels raw29755step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4954 node4954Labels := by rfl

def raw29756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29756Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29756step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw29756step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29756step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw29756step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw29756step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw29756step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29756 raw29756Labels = mixedMoment B node4970 node4970Labels := by
  calc
    mixedMoment B raw29756 raw29756Labels = mixedMoment B raw29756step0 raw29756step0Labels := by
      have hz : ∀ j, raw29756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29756step0 = (fun i j => raw29756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29756step0 raw29756; decide +kernel
      have hl : raw29756step0Labels = raw29756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29756 raw29756Labels permutation346 hz
    mixedMoment B raw29756step0 raw29756step0Labels = mixedMoment B raw29756step1 raw29756step1Labels := by
      have ha : raw29756step1 = (fun i j => raw29756step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29756step1 raw29756step0; decide +kernel
      have hl : raw29756step1Labels = raw29756step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29756step0 raw29756step0Labels permutation149 permutation3
    mixedMoment B raw29756step1 raw29756step1Labels = mixedMoment B raw29756step2 raw29756step2Labels := by
      have ha : raw29756step2 = -raw29756step1 := by apply Matrix.ext; change ∀ i j, raw29756step2 i j = -(raw29756step1 i j); unfold raw29756step2 raw29756step1; decide +kernel
      have hl : raw29756step2Labels = raw29756step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29756step2 raw29756step2Labels = mixedMoment B raw29756step3 raw29756step3Labels := by
      have ha : raw29756step3 = raw29756step2 := by apply Matrix.ext; unfold raw29756step3 raw29756step2; decide +kernel
      have hl : raw29756step2Labels = labelEmbedding6 ∘ raw29756step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29756step2 raw29756step2Labels raw29756step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4970 node4970Labels := by rfl

def raw29757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29757Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29757step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29757step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29757 raw29757Labels = mixedMoment B node3926 node3926Labels := by
  calc
    mixedMoment B raw29757 raw29757Labels = mixedMoment B raw29757step0 raw29757step0Labels := by
      have hz : ∀ j, raw29757 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29757step0 = (fun i j => raw29757 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29757step0 raw29757; decide +kernel
      have hl : raw29757step0Labels = raw29757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29757 raw29757Labels permutation346 hz
    mixedMoment B raw29757step0 raw29757step0Labels = mixedMoment B raw29757step1 raw29757step1Labels := by
      have ha : raw29757step1 = (fun i j => raw29757step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29757step1 raw29757step0; decide +kernel
      have hl : raw29757step1Labels = raw29757step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29757step0 raw29757step0Labels permutation32 permutation3
    _ = mixedMoment B node3926 node3926Labels := by rfl

def raw29758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29758Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw29758step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29758step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29758step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29758 raw29758Labels = mixedMoment B node3936 node3936Labels := by
  calc
    mixedMoment B raw29758 raw29758Labels = mixedMoment B raw29758step0 raw29758step0Labels := by
      have ha : raw29758step0 = (fun i j => raw29758 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29758step0 raw29758; decide +kernel
      have hl : raw29758step0Labels = raw29758Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29758 raw29758Labels permutation686 permutation3
    mixedMoment B raw29758step0 raw29758step0Labels = mixedMoment B raw29758step1 raw29758step1Labels := by
      have ha : raw29758step1 = -raw29758step0 := by apply Matrix.ext; change ∀ i j, raw29758step1 i j = -(raw29758step0 i j); unfold raw29758step1 raw29758step0; decide +kernel
      have hl : raw29758step1Labels = raw29758step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3936 node3936Labels := by rfl

def raw29759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29759Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29759step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw29759step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29759step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw29759step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29759 raw29759Labels = mixedMoment B node3940 node3940Labels := by
  calc
    mixedMoment B raw29759 raw29759Labels = mixedMoment B raw29759step0 raw29759step0Labels := by
      have hz : ∀ j, raw29759 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29759step0 = (fun i j => raw29759 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29759step0 raw29759; decide +kernel
      have hl : raw29759step0Labels = raw29759Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29759 raw29759Labels permutation346 hz
    mixedMoment B raw29759step0 raw29759step0Labels = mixedMoment B raw29759step1 raw29759step1Labels := by
      have ha : raw29759step1 = (fun i j => raw29759step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29759step1 raw29759step0; decide +kernel
      have hl : raw29759step1Labels = raw29759step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29759step0 raw29759step0Labels permutation149 permutation3
    mixedMoment B raw29759step1 raw29759step1Labels = mixedMoment B raw29759step2 raw29759step2Labels := by
      have ha : raw29759step2 = -raw29759step1 := by apply Matrix.ext; change ∀ i j, raw29759step2 i j = -(raw29759step1 i j); unfold raw29759step2 raw29759step1; decide +kernel
      have hl : raw29759step2Labels = raw29759step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3940 node3940Labels := by rfl

def raw29760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29760Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29760step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw29760step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29760 raw29760Labels = mixedMoment B node3995 node3995Labels := by
  calc
    mixedMoment B raw29760 raw29760Labels = mixedMoment B raw29760step0 raw29760step0Labels := by
      have hz : ∀ j, raw29760 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29760step0 = (fun i j => raw29760 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29760step0 raw29760; decide +kernel
      have hl : raw29760step0Labels = raw29760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29760 raw29760Labels permutation346 hz
    mixedMoment B raw29760step0 raw29760step0Labels = mixedMoment B raw29760step1 raw29760step1Labels := by
      have ha : raw29760step1 = (fun i j => raw29760step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29760step1 raw29760step0; decide +kernel
      have hl : raw29760step1Labels = raw29760step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29760step0 raw29760step0Labels permutation32 permutation3
    _ = mixedMoment B node3995 node3995Labels := by rfl

def raw29761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29761Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29761step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw29761step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29761 raw29761Labels = mixedMoment B node3996 node3996Labels := by
  calc
    mixedMoment B raw29761 raw29761Labels = mixedMoment B raw29761step0 raw29761step0Labels := by
      have hz : ∀ j, raw29761 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29761step0 = (fun i j => raw29761 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29761step0 raw29761; decide +kernel
      have hl : raw29761step0Labels = raw29761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29761 raw29761Labels permutation346 hz
    mixedMoment B raw29761step0 raw29761step0Labels = mixedMoment B raw29761step1 raw29761step1Labels := by
      have ha : raw29761step1 = (fun i j => raw29761step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29761step1 raw29761step0; decide +kernel
      have hl : raw29761step1Labels = raw29761step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29761step0 raw29761step0Labels permutation33 permutation3
    _ = mixedMoment B node3996 node3996Labels := by rfl

def raw29762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29762Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29762step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29762step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29762 raw29762Labels = mixedMoment B node1026 node1026Labels := by
  calc
    mixedMoment B raw29762 raw29762Labels = mixedMoment B raw29762step0 raw29762step0Labels := by
      have hz : ∀ j, raw29762 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29762step0 = (fun i j => raw29762 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29762step0 raw29762; decide +kernel
      have hl : raw29762step0Labels = raw29762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29762 raw29762Labels permutation346 hz
    mixedMoment B raw29762step0 raw29762step0Labels = mixedMoment B raw29762step1 raw29762step1Labels := by
      have ha : raw29762step1 = (fun i j => raw29762step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29762step1 raw29762step0; decide +kernel
      have hl : raw29762step1Labels = raw29762step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29762step0 raw29762step0Labels permutation32 permutation3
    _ = mixedMoment B node1026 node1026Labels := by rfl

def raw29763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29763Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29763step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29763 raw29763Labels = mixedMoment B node2473 node2473Labels := by
  calc
    mixedMoment B raw29763 raw29763Labels = mixedMoment B raw29763step0 raw29763step0Labels := by
      have ha : raw29763step0 = (fun i j => raw29763 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29763step0 raw29763; decide +kernel
      have hl : raw29763step0Labels = raw29763Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29763 raw29763Labels permutation176 permutation3
    _ = mixedMoment B node2473 node2473Labels := by rfl

def raw29764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29764Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29764step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29764step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29764 raw29764Labels = mixedMoment B node2576 node2576Labels := by
  calc
    mixedMoment B raw29764 raw29764Labels = mixedMoment B raw29764step0 raw29764step0Labels := by
      have hz : ∀ j, raw29764 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29764step0 = (fun i j => raw29764 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29764step0 raw29764; decide +kernel
      have hl : raw29764step0Labels = raw29764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29764 raw29764Labels permutation346 hz
    mixedMoment B raw29764step0 raw29764step0Labels = mixedMoment B raw29764step1 raw29764step1Labels := by
      have ha : raw29764step1 = (fun i j => raw29764step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29764step1 raw29764step0; decide +kernel
      have hl : raw29764step1Labels = raw29764step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29764step0 raw29764step0Labels permutation38 permutation3
    _ = mixedMoment B node2576 node2576Labels := by rfl

def raw29765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29765Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29765step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw29765step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29765 raw29765Labels = mixedMoment B node2751 node2751Labels := by
  calc
    mixedMoment B raw29765 raw29765Labels = mixedMoment B raw29765step0 raw29765step0Labels := by
      have hz : ∀ j, raw29765 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29765step0 = (fun i j => raw29765 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29765step0 raw29765; decide +kernel
      have hl : raw29765step0Labels = raw29765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29765 raw29765Labels permutation346 hz
    mixedMoment B raw29765step0 raw29765step0Labels = mixedMoment B raw29765step1 raw29765step1Labels := by
      have ha : raw29765step1 = (fun i j => raw29765step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29765step1 raw29765step0; decide +kernel
      have hl : raw29765step1Labels = raw29765step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29765step0 raw29765step0Labels permutation32 permutation3
    _ = mixedMoment B node2751 node2751Labels := by rfl

def raw29766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29766Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29766step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw29766step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29766 raw29766Labels = mixedMoment B node2753 node2753Labels := by
  calc
    mixedMoment B raw29766 raw29766Labels = mixedMoment B raw29766step0 raw29766step0Labels := by
      have hz : ∀ j, raw29766 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29766step0 = (fun i j => raw29766 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29766step0 raw29766; decide +kernel
      have hl : raw29766step0Labels = raw29766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29766 raw29766Labels permutation346 hz
    mixedMoment B raw29766step0 raw29766step0Labels = mixedMoment B raw29766step1 raw29766step1Labels := by
      have ha : raw29766step1 = (fun i j => raw29766step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29766step1 raw29766step0; decide +kernel
      have hl : raw29766step1Labels = raw29766step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29766step0 raw29766step0Labels permutation33 permutation3
    _ = mixedMoment B node2753 node2753Labels := by rfl

def raw29767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29767Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29767step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29767step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29767 raw29767Labels = mixedMoment B node910 node910Labels := by
  calc
    mixedMoment B raw29767 raw29767Labels = mixedMoment B raw29767step0 raw29767step0Labels := by
      have ha : raw29767step0 = (fun i j => raw29767 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29767step0 raw29767; decide +kernel
      have hl : raw29767step0Labels = raw29767Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29767 raw29767Labels permutation158 permutation3
    _ = mixedMoment B node910 node910Labels := by rfl

def raw29768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29768Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29768step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29768 raw29768Labels = mixedMoment B node2324 node2324Labels := by
  calc
    mixedMoment B raw29768 raw29768Labels = mixedMoment B raw29768step0 raw29768step0Labels := by
      have ha : raw29768step0 = (fun i j => raw29768 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29768step0 raw29768; decide +kernel
      have hl : raw29768step0Labels = raw29768Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29768 raw29768Labels permutation158 permutation3
    _ = mixedMoment B node2324 node2324Labels := by rfl

def raw29769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29769Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29769step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29769 raw29769Labels = mixedMoment B node2530 node2530Labels := by
  calc
    mixedMoment B raw29769 raw29769Labels = mixedMoment B raw29769step0 raw29769step0Labels := by
      have ha : raw29769step0 = (fun i j => raw29769 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29769step0 raw29769; decide +kernel
      have hl : raw29769step0Labels = raw29769Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29769 raw29769Labels permutation158 permutation3
    _ = mixedMoment B node2530 node2530Labels := by rfl

def raw29770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29770Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw29770step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29770 raw29770Labels = mixedMoment B node2567 node2567Labels := by
  calc
    mixedMoment B raw29770 raw29770Labels = mixedMoment B raw29770step0 raw29770step0Labels := by
      have ha : raw29770step0 = (fun i j => raw29770 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29770step0 raw29770; decide +kernel
      have hl : raw29770step0Labels = raw29770Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29770 raw29770Labels permutation160 permutation3
    _ = mixedMoment B node2567 node2567Labels := by rfl

def raw29771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29771Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw29771step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29771 raw29771Labels = mixedMoment B node2570 node2570Labels := by
  calc
    mixedMoment B raw29771 raw29771Labels = mixedMoment B raw29771step0 raw29771step0Labels := by
      have ha : raw29771step0 = (fun i j => raw29771 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29771step0 raw29771; decide +kernel
      have hl : raw29771step0Labels = raw29771Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29771 raw29771Labels permutation162 permutation3
    _ = mixedMoment B node2570 node2570Labels := by rfl

def raw29772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29772Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29772step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29772step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29772 raw29772Labels = mixedMoment B node935 node935Labels := by
  calc
    mixedMoment B raw29772 raw29772Labels = mixedMoment B raw29772step0 raw29772step0Labels := by
      have hz : ∀ j, raw29772 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29772step0 = (fun i j => raw29772 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29772step0 raw29772; decide +kernel
      have hl : raw29772step0Labels = raw29772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29772 raw29772Labels permutation346 hz
    mixedMoment B raw29772step0 raw29772step0Labels = mixedMoment B raw29772step1 raw29772step1Labels := by
      have ha : raw29772step1 = (fun i j => raw29772step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29772step1 raw29772step0; decide +kernel
      have hl : raw29772step1Labels = raw29772step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29772step0 raw29772step0Labels permutation32 permutation3
    _ = mixedMoment B node935 node935Labels := by rfl

def raw29773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29773Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29773step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29773step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29773step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29773 raw29773Labels = mixedMoment B node2343 node2343Labels := by
  calc
    mixedMoment B raw29773 raw29773Labels = mixedMoment B raw29773step0 raw29773step0Labels := by
      have hz : ∀ j, raw29773 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29773step0 = (fun i j => raw29773 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29773step0 raw29773; decide +kernel
      have hl : raw29773step0Labels = raw29773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29773 raw29773Labels permutation346 hz
    mixedMoment B raw29773step0 raw29773step0Labels = mixedMoment B raw29773step1 raw29773step1Labels := by
      have ha : raw29773step1 = (fun i j => raw29773step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29773step1 raw29773step0; decide +kernel
      have hl : raw29773step1Labels = raw29773step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29773step0 raw29773step0Labels permutation32 permutation3
    _ = mixedMoment B node2343 node2343Labels := by rfl

def raw29774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29774Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29774step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29774 raw29774Labels = mixedMoment B node2433 node2433Labels := by
  calc
    mixedMoment B raw29774 raw29774Labels = mixedMoment B raw29774step0 raw29774step0Labels := by
      have ha : raw29774step0 = (fun i j => raw29774 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29774step0 raw29774; decide +kernel
      have hl : raw29774step0Labels = raw29774Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29774 raw29774Labels permutation176 permutation3
    _ = mixedMoment B node2433 node2433Labels := by rfl

def raw29775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29775Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29775step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29775step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29775 raw29775Labels = mixedMoment B node2591 node2591Labels := by
  calc
    mixedMoment B raw29775 raw29775Labels = mixedMoment B raw29775step0 raw29775step0Labels := by
      have hz : ∀ j, raw29775 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29775step0 = (fun i j => raw29775 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29775step0 raw29775; decide +kernel
      have hl : raw29775step0Labels = raw29775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29775 raw29775Labels permutation346 hz
    mixedMoment B raw29775step0 raw29775step0Labels = mixedMoment B raw29775step1 raw29775step1Labels := by
      have ha : raw29775step1 = (fun i j => raw29775step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29775step1 raw29775step0; decide +kernel
      have hl : raw29775step1Labels = raw29775step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29775step0 raw29775step0Labels permutation34 permutation3
    _ = mixedMoment B node2591 node2591Labels := by rfl

def raw29776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29776Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29776step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29776step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw29776step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29776 raw29776Labels = mixedMoment B node2596 node2596Labels := by
  calc
    mixedMoment B raw29776 raw29776Labels = mixedMoment B raw29776step0 raw29776step0Labels := by
      have hz : ∀ j, raw29776 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29776step0 = (fun i j => raw29776 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29776step0 raw29776; decide +kernel
      have hl : raw29776step0Labels = raw29776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29776 raw29776Labels permutation346 hz
    mixedMoment B raw29776step0 raw29776step0Labels = mixedMoment B raw29776step1 raw29776step1Labels := by
      have ha : raw29776step1 = (fun i j => raw29776step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29776step1 raw29776step0; decide +kernel
      have hl : raw29776step1Labels = raw29776step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29776step0 raw29776step0Labels permutation36 permutation3
    _ = mixedMoment B node2596 node2596Labels := by rfl

def raw29777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29777Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29777step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29777step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29777 raw29777Labels = mixedMoment B node913 node913Labels := by
  calc
    mixedMoment B raw29777 raw29777Labels = mixedMoment B raw29777step0 raw29777step0Labels := by
      have hz : ∀ j, raw29777 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29777step0 = (fun i j => raw29777 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29777step0 raw29777; decide +kernel
      have hl : raw29777step0Labels = raw29777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29777 raw29777Labels permutation346 hz
    mixedMoment B raw29777step0 raw29777step0Labels = mixedMoment B raw29777step1 raw29777step1Labels := by
      have ha : raw29777step1 = (fun i j => raw29777step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29777step1 raw29777step0; decide +kernel
      have hl : raw29777step1Labels = raw29777step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29777step0 raw29777step0Labels permutation33 permutation3
    _ = mixedMoment B node913 node913Labels := by rfl

def raw29778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29778Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29778step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29778step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29778step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29778 raw29778Labels = mixedMoment B node2326 node2326Labels := by
  calc
    mixedMoment B raw29778 raw29778Labels = mixedMoment B raw29778step0 raw29778step0Labels := by
      have hz : ∀ j, raw29778 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29778step0 = (fun i j => raw29778 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29778step0 raw29778; decide +kernel
      have hl : raw29778step0Labels = raw29778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29778 raw29778Labels permutation346 hz
    mixedMoment B raw29778step0 raw29778step0Labels = mixedMoment B raw29778step1 raw29778step1Labels := by
      have ha : raw29778step1 = (fun i j => raw29778step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29778step1 raw29778step0; decide +kernel
      have hl : raw29778step1Labels = raw29778step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29778step0 raw29778step0Labels permutation33 permutation3
    _ = mixedMoment B node2326 node2326Labels := by rfl

def raw29779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29779Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29779step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29779step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29779 raw29779Labels = mixedMoment B node2422 node2422Labels := by
  calc
    mixedMoment B raw29779 raw29779Labels = mixedMoment B raw29779step0 raw29779step0Labels := by
      have ha : raw29779step0 = (fun i j => raw29779 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29779step0 raw29779; decide +kernel
      have hl : raw29779step0Labels = raw29779Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29779 raw29779Labels permutation177 permutation3
    _ = mixedMoment B node2422 node2422Labels := by rfl

def raw29780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29780Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29780step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw29780step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29780 raw29780Labels = mixedMoment B node2531 node2531Labels := by
  calc
    mixedMoment B raw29780 raw29780Labels = mixedMoment B raw29780step0 raw29780step0Labels := by
      have hz : ∀ j, raw29780 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29780step0 = (fun i j => raw29780 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29780step0 raw29780; decide +kernel
      have hl : raw29780step0Labels = raw29780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29780 raw29780Labels permutation346 hz
    mixedMoment B raw29780step0 raw29780step0Labels = mixedMoment B raw29780step1 raw29780step1Labels := by
      have ha : raw29780step1 = (fun i j => raw29780step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29780step1 raw29780step0; decide +kernel
      have hl : raw29780step1Labels = raw29780step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29780step0 raw29780step0Labels permutation33 permutation3
    _ = mixedMoment B node2531 node2531Labels := by rfl

def raw29781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw29781Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw29781step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29781step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw29781step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29781 raw29781Labels = mixedMoment B node2572 node2572Labels := by
  calc
    mixedMoment B raw29781 raw29781Labels = mixedMoment B raw29781step0 raw29781step0Labels := by
      have hz : ∀ j, raw29781 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29781step0 = (fun i j => raw29781 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29781step0 raw29781; decide +kernel
      have hl : raw29781step0Labels = raw29781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29781 raw29781Labels permutation346 hz
    mixedMoment B raw29781step0 raw29781step0Labels = mixedMoment B raw29781step1 raw29781step1Labels := by
      have ha : raw29781step1 = (fun i j => raw29781step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29781step1 raw29781step0; decide +kernel
      have hl : raw29781step1Labels = raw29781step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29781step0 raw29781step0Labels permutation33 permutation3
    _ = mixedMoment B node2572 node2572Labels := by rfl

def raw29782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29782Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29782step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29782step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw29782step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29782 raw29782Labels = mixedMoment B node912 node912Labels := by
  calc
    mixedMoment B raw29782 raw29782Labels = mixedMoment B raw29782step0 raw29782step0Labels := by
      have hz : ∀ j, raw29782 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29782step0 = (fun i j => raw29782 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29782step0 raw29782; decide +kernel
      have hl : raw29782step0Labels = raw29782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29782 raw29782Labels permutation346 hz
    mixedMoment B raw29782step0 raw29782step0Labels = mixedMoment B raw29782step1 raw29782step1Labels := by
      have ha : raw29782step1 = (fun i j => raw29782step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29782step1 raw29782step0; decide +kernel
      have hl : raw29782step1Labels = raw29782step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29782step0 raw29782step0Labels permutation32 permutation3
    _ = mixedMoment B node912 node912Labels := by rfl

def raw29783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29783Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29783step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw29783step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29783 raw29783Labels = mixedMoment B node2325 node2325Labels := by
  calc
    mixedMoment B raw29783 raw29783Labels = mixedMoment B raw29783step0 raw29783step0Labels := by
      have hz : ∀ j, raw29783 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29783step0 = (fun i j => raw29783 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29783step0 raw29783; decide +kernel
      have hl : raw29783step0Labels = raw29783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29783 raw29783Labels permutation346 hz
    mixedMoment B raw29783step0 raw29783step0Labels = mixedMoment B raw29783step1 raw29783step1Labels := by
      have ha : raw29783step1 = (fun i j => raw29783step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29783step1 raw29783step0; decide +kernel
      have hl : raw29783step1Labels = raw29783step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29783step0 raw29783step0Labels permutation32 permutation3
    _ = mixedMoment B node2325 node2325Labels := by rfl

def raw29784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29784Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29784step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29784step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29784step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29784step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29784 raw29784Labels = mixedMoment B node2347 node2347Labels := by
  calc
    mixedMoment B raw29784 raw29784Labels = mixedMoment B raw29784step0 raw29784step0Labels := by
      have ha : raw29784step0 = (fun i j => raw29784 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29784step0 raw29784; decide +kernel
      have hl : raw29784step0Labels = raw29784Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29784 raw29784Labels permutation686 permutation3
    mixedMoment B raw29784step0 raw29784step0Labels = mixedMoment B raw29784step1 raw29784step1Labels := by
      have ha : raw29784step1 = -raw29784step0 := by apply Matrix.ext; change ∀ i j, raw29784step1 i j = -(raw29784step0 i j); unfold raw29784step1 raw29784step0; decide +kernel
      have hl : raw29784step1Labels = raw29784step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2347 node2347Labels := by rfl

def raw29785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29785Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29785step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw29785step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29785step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw29785step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29785 raw29785Labels = mixedMoment B node2357 node2357Labels := by
  calc
    mixedMoment B raw29785 raw29785Labels = mixedMoment B raw29785step0 raw29785step0Labels := by
      have hz : ∀ j, raw29785 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29785step0 = (fun i j => raw29785 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29785step0 raw29785; decide +kernel
      have hl : raw29785step0Labels = raw29785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29785 raw29785Labels permutation346 hz
    mixedMoment B raw29785step0 raw29785step0Labels = mixedMoment B raw29785step1 raw29785step1Labels := by
      have ha : raw29785step1 = (fun i j => raw29785step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29785step1 raw29785step0; decide +kernel
      have hl : raw29785step1Labels = raw29785step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29785step0 raw29785step0Labels permutation149 permutation3
    mixedMoment B raw29785step1 raw29785step1Labels = mixedMoment B raw29785step2 raw29785step2Labels := by
      have ha : raw29785step2 = -raw29785step1 := by apply Matrix.ext; change ∀ i j, raw29785step2 i j = -(raw29785step1 i j); unfold raw29785step2 raw29785step1; decide +kernel
      have hl : raw29785step2Labels = raw29785step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2357 node2357Labels := by rfl

def raw29786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw29786Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw29786step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29786step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw29786step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29786 raw29786Labels = mixedMoment B node2569 node2569Labels := by
  calc
    mixedMoment B raw29786 raw29786Labels = mixedMoment B raw29786step0 raw29786step0Labels := by
      have hz : ∀ j, raw29786 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29786step0 = (fun i j => raw29786 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29786step0 raw29786; decide +kernel
      have hl : raw29786step0Labels = raw29786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29786 raw29786Labels permutation346 hz
    mixedMoment B raw29786step0 raw29786step0Labels = mixedMoment B raw29786step1 raw29786step1Labels := by
      have ha : raw29786step1 = (fun i j => raw29786step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw29786step1 raw29786step0; decide +kernel
      have hl : raw29786step1Labels = raw29786step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29786step0 raw29786step0Labels permutation32 permutation3
    _ = mixedMoment B node2569 node2569Labels := by rfl

def raw29787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29787Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29787step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29787step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw29787step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29787step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw29787step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29787 raw29787Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw29787 raw29787Labels = mixedMoment B raw29787step0 raw29787step0Labels := by
      have hz : ∀ j, raw29787 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29787step0 = (fun i j => raw29787 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29787step0 raw29787; decide +kernel
      have hl : raw29787step0Labels = raw29787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29787 raw29787Labels permutation346 hz
    mixedMoment B raw29787step0 raw29787step0Labels = mixedMoment B raw29787step1 raw29787step1Labels := by
      have ha : raw29787step1 = (fun i j => raw29787step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29787step1 raw29787step0; decide +kernel
      have hl : raw29787step1Labels = raw29787step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29787step0 raw29787step0Labels permutation127 permutation7
    mixedMoment B raw29787step1 raw29787step1Labels = mixedMoment B raw29787step2 raw29787step2Labels := by
      have ha : raw29787step2 = raw29787step1 := by apply Matrix.ext; unfold raw29787step2 raw29787step1; decide +kernel
      have hl : raw29787step1Labels = labelEmbedding1 ∘ raw29787step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29787step1 raw29787step1Labels raw29787step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3961 node3961Labels := by rfl

def raw29788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29788Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29788step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw29788step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29788step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw29788step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29788step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw29788step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29788 raw29788Labels = mixedMoment B node1736 node1736Labels := by
  calc
    mixedMoment B raw29788 raw29788Labels = mixedMoment B raw29788step0 raw29788step0Labels := by
      have hz : ∀ j, raw29788 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29788step0 = (fun i j => raw29788 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29788step0 raw29788; decide +kernel
      have hl : raw29788step0Labels = raw29788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29788 raw29788Labels permutation346 hz
    mixedMoment B raw29788step0 raw29788step0Labels = mixedMoment B raw29788step1 raw29788step1Labels := by
      have ha : raw29788step1 = (fun i j => raw29788step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29788step1 raw29788step0; decide +kernel
      have hl : raw29788step1Labels = raw29788step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29788step0 raw29788step0Labels permutation44 permutation5
    mixedMoment B raw29788step1 raw29788step1Labels = mixedMoment B raw29788step2 raw29788step2Labels := by
      have ha : raw29788step2 = -raw29788step1 := by apply Matrix.ext; change ∀ i j, raw29788step2 i j = -(raw29788step1 i j); unfold raw29788step2 raw29788step1; decide +kernel
      have hl : raw29788step2Labels = raw29788step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29788step2 raw29788step2Labels = mixedMoment B raw29788step3 raw29788step3Labels := by
      have ha : raw29788step3 = raw29788step2 := by apply Matrix.ext; unfold raw29788step3 raw29788step2; decide +kernel
      have hl : raw29788step2Labels = labelEmbedding1 ∘ raw29788step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29788step2 raw29788step2Labels raw29788step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1736 node1736Labels := by rfl

def raw29789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29789Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw29789step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29789step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw29789step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29789step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw29789step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29789 raw29789Labels = mixedMoment B node3476 node3476Labels := by
  calc
    mixedMoment B raw29789 raw29789Labels = mixedMoment B raw29789step0 raw29789step0Labels := by
      have ha : raw29789step0 = (fun i j => raw29789 (permutation188 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29789step0 raw29789; decide +kernel
      have hl : raw29789step0Labels = raw29789Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29789 raw29789Labels permutation188 permutation5
    mixedMoment B raw29789step0 raw29789step0Labels = mixedMoment B raw29789step1 raw29789step1Labels := by
      have ha : raw29789step1 = -raw29789step0 := by apply Matrix.ext; change ∀ i j, raw29789step1 i j = -(raw29789step0 i j); unfold raw29789step1 raw29789step0; decide +kernel
      have hl : raw29789step1Labels = raw29789step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29789step1 raw29789step1Labels = mixedMoment B raw29789step2 raw29789step2Labels := by
      have ha : raw29789step2 = raw29789step1 := by apply Matrix.ext; unfold raw29789step2 raw29789step1; decide +kernel
      have hl : raw29789step1Labels = labelEmbedding1 ∘ raw29789step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29789step1 raw29789step1Labels raw29789step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3476 node3476Labels := by rfl

def raw29790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29790Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29790step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29790step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw29790step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29790step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw29790step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29790step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw29790step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29790 raw29790Labels = mixedMoment B node3612 node3612Labels := by
  calc
    mixedMoment B raw29790 raw29790Labels = mixedMoment B raw29790step0 raw29790step0Labels := by
      have hz : ∀ j, raw29790 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29790step0 = (fun i j => raw29790 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29790step0 raw29790; decide +kernel
      have hl : raw29790step0Labels = raw29790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29790 raw29790Labels permutation346 hz
    mixedMoment B raw29790step0 raw29790step0Labels = mixedMoment B raw29790step1 raw29790step1Labels := by
      have ha : raw29790step1 = (fun i j => raw29790step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29790step1 raw29790step0; decide +kernel
      have hl : raw29790step1Labels = raw29790step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29790step0 raw29790step0Labels permutation40 permutation5
    mixedMoment B raw29790step1 raw29790step1Labels = mixedMoment B raw29790step2 raw29790step2Labels := by
      have ha : raw29790step2 = -raw29790step1 := by apply Matrix.ext; change ∀ i j, raw29790step2 i j = -(raw29790step1 i j); unfold raw29790step2 raw29790step1; decide +kernel
      have hl : raw29790step2Labels = raw29790step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29790step2 raw29790step2Labels = mixedMoment B raw29790step3 raw29790step3Labels := by
      have ha : raw29790step3 = raw29790step2 := by apply Matrix.ext; unfold raw29790step3 raw29790step2; decide +kernel
      have hl : raw29790step2Labels = labelEmbedding1 ∘ raw29790step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29790step2 raw29790step2Labels raw29790step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3612 node3612Labels := by rfl

def raw29791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29791Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29791step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw29791step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29791step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw29791step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29791step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw29791step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29791 raw29791Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw29791 raw29791Labels = mixedMoment B raw29791step0 raw29791step0Labels := by
      have hz : ∀ j, raw29791 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29791step0 = (fun i j => raw29791 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29791step0 raw29791; decide +kernel
      have hl : raw29791step0Labels = raw29791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29791 raw29791Labels permutation346 hz
    mixedMoment B raw29791step0 raw29791step0Labels = mixedMoment B raw29791step1 raw29791step1Labels := by
      have ha : raw29791step1 = (fun i j => raw29791step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29791step1 raw29791step0; decide +kernel
      have hl : raw29791step1Labels = raw29791step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29791step0 raw29791step0Labels permutation54 permutation5
    mixedMoment B raw29791step1 raw29791step1Labels = mixedMoment B raw29791step2 raw29791step2Labels := by
      have ha : raw29791step2 = -raw29791step1 := by apply Matrix.ext; change ∀ i j, raw29791step2 i j = -(raw29791step1 i j); unfold raw29791step2 raw29791step1; decide +kernel
      have hl : raw29791step2Labels = raw29791step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29791step2 raw29791step2Labels = mixedMoment B raw29791step3 raw29791step3Labels := by
      have ha : raw29791step3 = raw29791step2 := by apply Matrix.ext; unfold raw29791step3 raw29791step2; decide +kernel
      have hl : raw29791step2Labels = labelEmbedding1 ∘ raw29791step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29791step2 raw29791step2Labels raw29791step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3625 node3625Labels := by rfl

def raw29792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29792Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29792step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw29792step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29792step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw29792step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29792step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw29792step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29792 raw29792Labels = mixedMoment B node1678 node1678Labels := by
  calc
    mixedMoment B raw29792 raw29792Labels = mixedMoment B raw29792step0 raw29792step0Labels := by
      have ha : raw29792step0 = (fun i j => raw29792 (permutation166 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29792step0 raw29792; decide +kernel
      have hl : raw29792step0Labels = raw29792Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29792 raw29792Labels permutation166 permutation5
    mixedMoment B raw29792step0 raw29792step0Labels = mixedMoment B raw29792step1 raw29792step1Labels := by
      have ha : raw29792step1 = -raw29792step0 := by apply Matrix.ext; change ∀ i j, raw29792step1 i j = -(raw29792step0 i j); unfold raw29792step1 raw29792step0; decide +kernel
      have hl : raw29792step1Labels = raw29792step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29792step1 raw29792step1Labels = mixedMoment B raw29792step2 raw29792step2Labels := by
      have ha : raw29792step2 = raw29792step1 := by apply Matrix.ext; unfold raw29792step2 raw29792step1; decide +kernel
      have hl : raw29792step1Labels = labelEmbedding1 ∘ raw29792step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29792step1 raw29792step1Labels raw29792step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1678 node1678Labels := by rfl

def raw29793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29793Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw29793step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29793step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw29793step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29793step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw29793step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29793 raw29793Labels = mixedMoment B node3414 node3414Labels := by
  calc
    mixedMoment B raw29793 raw29793Labels = mixedMoment B raw29793step0 raw29793step0Labels := by
      have ha : raw29793step0 = (fun i j => raw29793 (permutation166 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29793step0 raw29793; decide +kernel
      have hl : raw29793step0Labels = raw29793Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29793 raw29793Labels permutation166 permutation5
    mixedMoment B raw29793step0 raw29793step0Labels = mixedMoment B raw29793step1 raw29793step1Labels := by
      have ha : raw29793step1 = -raw29793step0 := by apply Matrix.ext; change ∀ i j, raw29793step1 i j = -(raw29793step0 i j); unfold raw29793step1 raw29793step0; decide +kernel
      have hl : raw29793step1Labels = raw29793step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29793step1 raw29793step1Labels = mixedMoment B raw29793step2 raw29793step2Labels := by
      have ha : raw29793step2 = raw29793step1 := by apply Matrix.ext; unfold raw29793step2 raw29793step1; decide +kernel
      have hl : raw29793step1Labels = labelEmbedding1 ∘ raw29793step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29793step1 raw29793step1Labels raw29793step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3414 node3414Labels := by rfl

def raw29794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29794Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29794step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, -1, 2]]
def raw29794step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29794step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw29794step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29794step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw29794step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29794 raw29794Labels = mixedMoment B node3599 node3599Labels := by
  calc
    mixedMoment B raw29794 raw29794Labels = mixedMoment B raw29794step0 raw29794step0Labels := by
      have ha : raw29794step0 = (fun i j => raw29794 (permutation160 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29794step0 raw29794; decide +kernel
      have hl : raw29794step0Labels = raw29794Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29794 raw29794Labels permutation160 permutation5
    mixedMoment B raw29794step0 raw29794step0Labels = mixedMoment B raw29794step1 raw29794step1Labels := by
      have ha : raw29794step1 = -raw29794step0 := by apply Matrix.ext; change ∀ i j, raw29794step1 i j = -(raw29794step0 i j); unfold raw29794step1 raw29794step0; decide +kernel
      have hl : raw29794step1Labels = raw29794step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29794step1 raw29794step1Labels = mixedMoment B raw29794step2 raw29794step2Labels := by
      have ha : raw29794step2 = raw29794step1 := by apply Matrix.ext; unfold raw29794step2 raw29794step1; decide +kernel
      have hl : raw29794step1Labels = labelEmbedding1 ∘ raw29794step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29794step1 raw29794step1Labels raw29794step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3599 node3599Labels := by rfl

def raw29795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29795Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29795step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw29795step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29795step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw29795step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29795step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw29795step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29795 raw29795Labels = mixedMoment B node3605 node3605Labels := by
  calc
    mixedMoment B raw29795 raw29795Labels = mixedMoment B raw29795step0 raw29795step0Labels := by
      have ha : raw29795step0 = (fun i j => raw29795 (permutation175 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29795step0 raw29795; decide +kernel
      have hl : raw29795step0Labels = raw29795Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29795 raw29795Labels permutation175 permutation5
    mixedMoment B raw29795step0 raw29795step0Labels = mixedMoment B raw29795step1 raw29795step1Labels := by
      have ha : raw29795step1 = -raw29795step0 := by apply Matrix.ext; change ∀ i j, raw29795step1 i j = -(raw29795step0 i j); unfold raw29795step1 raw29795step0; decide +kernel
      have hl : raw29795step1Labels = raw29795step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29795step1 raw29795step1Labels = mixedMoment B raw29795step2 raw29795step2Labels := by
      have ha : raw29795step2 = raw29795step1 := by apply Matrix.ext; unfold raw29795step2 raw29795step1; decide +kernel
      have hl : raw29795step1Labels = labelEmbedding1 ∘ raw29795step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29795step1 raw29795step1Labels raw29795step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3605 node3605Labels := by rfl

def raw29796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29796Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29796step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29796step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw29796step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29796step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw29796step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29796step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw29796step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29796 raw29796Labels = mixedMoment B node1682 node1682Labels := by
  calc
    mixedMoment B raw29796 raw29796Labels = mixedMoment B raw29796step0 raw29796step0Labels := by
      have hz : ∀ j, raw29796 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29796step0 = (fun i j => raw29796 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29796step0 raw29796; decide +kernel
      have hl : raw29796step0Labels = raw29796Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29796 raw29796Labels permutation346 hz
    mixedMoment B raw29796step0 raw29796step0Labels = mixedMoment B raw29796step1 raw29796step1Labels := by
      have ha : raw29796step1 = (fun i j => raw29796step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29796step1 raw29796step0; decide +kernel
      have hl : raw29796step1Labels = raw29796step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29796step0 raw29796step0Labels permutation35 permutation5
    mixedMoment B raw29796step1 raw29796step1Labels = mixedMoment B raw29796step2 raw29796step2Labels := by
      have ha : raw29796step2 = -raw29796step1 := by apply Matrix.ext; change ∀ i j, raw29796step2 i j = -(raw29796step1 i j); unfold raw29796step2 raw29796step1; decide +kernel
      have hl : raw29796step2Labels = raw29796step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29796step2 raw29796step2Labels = mixedMoment B raw29796step3 raw29796step3Labels := by
      have ha : raw29796step3 = raw29796step2 := by apply Matrix.ext; unfold raw29796step3 raw29796step2; decide +kernel
      have hl : raw29796step2Labels = labelEmbedding1 ∘ raw29796step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29796step2 raw29796step2Labels raw29796step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1682 node1682Labels := by rfl

def raw29797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29797Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29797step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw29797step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29797step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw29797step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29797step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw29797step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29797 raw29797Labels = mixedMoment B node3418 node3418Labels := by
  calc
    mixedMoment B raw29797 raw29797Labels = mixedMoment B raw29797step0 raw29797step0Labels := by
      have hz : ∀ j, raw29797 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29797step0 = (fun i j => raw29797 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29797step0 raw29797; decide +kernel
      have hl : raw29797step0Labels = raw29797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29797 raw29797Labels permutation346 hz
    mixedMoment B raw29797step0 raw29797step0Labels = mixedMoment B raw29797step1 raw29797step1Labels := by
      have ha : raw29797step1 = (fun i j => raw29797step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29797step1 raw29797step0; decide +kernel
      have hl : raw29797step1Labels = raw29797step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29797step0 raw29797step0Labels permutation35 permutation5
    mixedMoment B raw29797step1 raw29797step1Labels = mixedMoment B raw29797step2 raw29797step2Labels := by
      have ha : raw29797step2 = -raw29797step1 := by apply Matrix.ext; change ∀ i j, raw29797step2 i j = -(raw29797step1 i j); unfold raw29797step2 raw29797step1; decide +kernel
      have hl : raw29797step2Labels = raw29797step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29797step2 raw29797step2Labels = mixedMoment B raw29797step3 raw29797step3Labels := by
      have ha : raw29797step3 = raw29797step2 := by apply Matrix.ext; unfold raw29797step3 raw29797step2; decide +kernel
      have hl : raw29797step2Labels = labelEmbedding1 ∘ raw29797step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29797step2 raw29797step2Labels raw29797step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3418 node3418Labels := by rfl

def raw29798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29798Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw29798step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29798step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw29798step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29798step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw29798step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29798 raw29798Labels = mixedMoment B node3454 node3454Labels := by
  calc
    mixedMoment B raw29798 raw29798Labels = mixedMoment B raw29798step0 raw29798step0Labels := by
      have ha : raw29798step0 = (fun i j => raw29798 (permutation179 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29798step0 raw29798; decide +kernel
      have hl : raw29798step0Labels = raw29798Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29798 raw29798Labels permutation179 permutation5
    mixedMoment B raw29798step0 raw29798step0Labels = mixedMoment B raw29798step1 raw29798step1Labels := by
      have ha : raw29798step1 = -raw29798step0 := by apply Matrix.ext; change ∀ i j, raw29798step1 i j = -(raw29798step0 i j); unfold raw29798step1 raw29798step0; decide +kernel
      have hl : raw29798step1Labels = raw29798step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29798step1 raw29798step1Labels = mixedMoment B raw29798step2 raw29798step2Labels := by
      have ha : raw29798step2 = raw29798step1 := by apply Matrix.ext; unfold raw29798step2 raw29798step1; decide +kernel
      have hl : raw29798step1Labels = labelEmbedding1 ∘ raw29798step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29798step1 raw29798step1Labels raw29798step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3454 node3454Labels := by rfl

def raw29799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29799Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29799step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 1, 1]]
def raw29799step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw29799step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29799step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw29799step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29799 raw29799Labels = mixedMoment B node3606 node3606Labels := by
  calc
    mixedMoment B raw29799 raw29799Labels = mixedMoment B raw29799step0 raw29799step0Labels := by
      have hz : ∀ j, raw29799 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29799step0 = (fun i j => raw29799 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29799step0 raw29799; decide +kernel
      have hl : raw29799step0Labels = raw29799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29799 raw29799Labels permutation346 hz
    mixedMoment B raw29799step0 raw29799step0Labels = mixedMoment B raw29799step1 raw29799step1Labels := by
      have ha : raw29799step1 = (fun i j => raw29799step0 (permutation37 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29799step1 raw29799step0; decide +kernel
      have hl : raw29799step1Labels = raw29799step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29799step0 raw29799step0Labels permutation37 permutation5
    mixedMoment B raw29799step1 raw29799step1Labels = mixedMoment B raw29799step2 raw29799step2Labels := by
      have ha : raw29799step2 = -raw29799step1 := by apply Matrix.ext; change ∀ i j, raw29799step2 i j = -(raw29799step1 i j); unfold raw29799step2 raw29799step1; decide +kernel
      have hl : raw29799step2Labels = raw29799step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29799step2 raw29799step2Labels = mixedMoment B raw29799step3 raw29799step3Labels := by
      have ha : raw29799step3 = raw29799step2 := by apply Matrix.ext; unfold raw29799step3 raw29799step2; decide +kernel
      have hl : raw29799step2Labels = labelEmbedding1 ∘ raw29799step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29799step2 raw29799step2Labels raw29799step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3606 node3606Labels := by rfl

def raw29800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29800Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29800step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw29800step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29800step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw29800step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29800step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw29800step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29800 raw29800Labels = mixedMoment B node1689 node1689Labels := by
  calc
    mixedMoment B raw29800 raw29800Labels = mixedMoment B raw29800step0 raw29800step0Labels := by
      have hz : ∀ j, raw29800 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29800step0 = (fun i j => raw29800 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29800step0 raw29800; decide +kernel
      have hl : raw29800step0Labels = raw29800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29800 raw29800Labels permutation346 hz
    mixedMoment B raw29800step0 raw29800step0Labels = mixedMoment B raw29800step1 raw29800step1Labels := by
      have ha : raw29800step1 = (fun i j => raw29800step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29800step1 raw29800step0; decide +kernel
      have hl : raw29800step1Labels = raw29800step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29800step0 raw29800step0Labels permutation33 permutation5
    mixedMoment B raw29800step1 raw29800step1Labels = mixedMoment B raw29800step2 raw29800step2Labels := by
      have ha : raw29800step2 = -raw29800step1 := by apply Matrix.ext; change ∀ i j, raw29800step2 i j = -(raw29800step1 i j); unfold raw29800step2 raw29800step1; decide +kernel
      have hl : raw29800step2Labels = raw29800step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29800step2 raw29800step2Labels = mixedMoment B raw29800step3 raw29800step3Labels := by
      have ha : raw29800step3 = raw29800step2 := by apply Matrix.ext; unfold raw29800step3 raw29800step2; decide +kernel
      have hl : raw29800step2Labels = labelEmbedding1 ∘ raw29800step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29800step2 raw29800step2Labels raw29800step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1689 node1689Labels := by rfl

def raw29801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29801Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29801step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29801step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw29801step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29801step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw29801step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29801step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw29801step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29801 raw29801Labels = mixedMoment B node3419 node3419Labels := by
  calc
    mixedMoment B raw29801 raw29801Labels = mixedMoment B raw29801step0 raw29801step0Labels := by
      have hz : ∀ j, raw29801 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29801step0 = (fun i j => raw29801 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29801step0 raw29801; decide +kernel
      have hl : raw29801step0Labels = raw29801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29801 raw29801Labels permutation346 hz
    mixedMoment B raw29801step0 raw29801step0Labels = mixedMoment B raw29801step1 raw29801step1Labels := by
      have ha : raw29801step1 = (fun i j => raw29801step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29801step1 raw29801step0; decide +kernel
      have hl : raw29801step1Labels = raw29801step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29801step0 raw29801step0Labels permutation33 permutation5
    mixedMoment B raw29801step1 raw29801step1Labels = mixedMoment B raw29801step2 raw29801step2Labels := by
      have ha : raw29801step2 = -raw29801step1 := by apply Matrix.ext; change ∀ i j, raw29801step2 i j = -(raw29801step1 i j); unfold raw29801step2 raw29801step1; decide +kernel
      have hl : raw29801step2Labels = raw29801step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29801step2 raw29801step2Labels = mixedMoment B raw29801step3 raw29801step3Labels := by
      have ha : raw29801step3 = raw29801step2 := by apply Matrix.ext; unfold raw29801step3 raw29801step2; decide +kernel
      have hl : raw29801step2Labels = labelEmbedding1 ∘ raw29801step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29801step2 raw29801step2Labels raw29801step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3419 node3419Labels := by rfl

def raw29802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29802Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw29802step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29802step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw29802step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29802 raw29802Labels = mixedMoment B node3408 node3408Labels := by
  calc
    mixedMoment B raw29802 raw29802Labels = mixedMoment B raw29802step0 raw29802step0Labels := by
      have ha : raw29802step0 = (fun i j => raw29802 (permutation584 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29802step0 raw29802; decide +kernel
      have hl : raw29802step0Labels = raw29802Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29802 raw29802Labels permutation584 permutation7
    mixedMoment B raw29802step0 raw29802step0Labels = mixedMoment B raw29802step1 raw29802step1Labels := by
      have ha : raw29802step1 = raw29802step0 := by apply Matrix.ext; unfold raw29802step1 raw29802step0; decide +kernel
      have hl : raw29802step0Labels = labelEmbedding1 ∘ raw29802step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29802step0 raw29802step0Labels raw29802step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3408 node3408Labels := by rfl

def raw29803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29803Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29803step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29803step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw29803step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29803step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw29803step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29803 raw29803Labels = mixedMoment B node3420 node3420Labels := by
  calc
    mixedMoment B raw29803 raw29803Labels = mixedMoment B raw29803step0 raw29803step0Labels := by
      have hz : ∀ j, raw29803 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29803step0 = (fun i j => raw29803 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29803step0 raw29803; decide +kernel
      have hl : raw29803step0Labels = raw29803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29803 raw29803Labels permutation346 hz
    mixedMoment B raw29803step0 raw29803step0Labels = mixedMoment B raw29803step1 raw29803step1Labels := by
      have ha : raw29803step1 = (fun i j => raw29803step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29803step1 raw29803step0; decide +kernel
      have hl : raw29803step1Labels = raw29803step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29803step0 raw29803step0Labels permutation125 permutation7
    mixedMoment B raw29803step1 raw29803step1Labels = mixedMoment B raw29803step2 raw29803step2Labels := by
      have ha : raw29803step2 = raw29803step1 := by apply Matrix.ext; unfold raw29803step2 raw29803step1; decide +kernel
      have hl : raw29803step1Labels = labelEmbedding1 ∘ raw29803step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29803step1 raw29803step1Labels raw29803step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3420 node3420Labels := by rfl

def raw29804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw29804Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw29804step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw29804step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29804step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw29804step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29804 raw29804Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw29804 raw29804Labels = mixedMoment B raw29804step0 raw29804step0Labels := by
      have hz : ∀ j, raw29804 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29804step0 = (fun i j => raw29804 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29804step0 raw29804; decide +kernel
      have hl : raw29804step0Labels = raw29804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29804 raw29804Labels permutation346 hz
    mixedMoment B raw29804step0 raw29804step0Labels = mixedMoment B raw29804step1 raw29804step1Labels := by
      have ha : raw29804step1 = (fun i j => raw29804step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29804step1 raw29804step0; decide +kernel
      have hl : raw29804step1Labels = raw29804step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29804step0 raw29804step0Labels permutation127 permutation7
    mixedMoment B raw29804step1 raw29804step1Labels = mixedMoment B raw29804step2 raw29804step2Labels := by
      have ha : raw29804step2 = raw29804step1 := by apply Matrix.ext; unfold raw29804step2 raw29804step1; decide +kernel
      have hl : raw29804step1Labels = labelEmbedding1 ∘ raw29804step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29804step1 raw29804step1Labels raw29804step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3481 node3481Labels := by rfl

def raw29805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29805Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29805step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29805step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw29805step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29805step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw29805step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29805step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw29805step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29805 raw29805Labels = mixedMoment B node1679 node1679Labels := by
  calc
    mixedMoment B raw29805 raw29805Labels = mixedMoment B raw29805step0 raw29805step0Labels := by
      have hz : ∀ j, raw29805 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29805step0 = (fun i j => raw29805 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29805step0 raw29805; decide +kernel
      have hl : raw29805step0Labels = raw29805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29805 raw29805Labels permutation346 hz
    mixedMoment B raw29805step0 raw29805step0Labels = mixedMoment B raw29805step1 raw29805step1Labels := by
      have ha : raw29805step1 = (fun i j => raw29805step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29805step1 raw29805step0; decide +kernel
      have hl : raw29805step1Labels = raw29805step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29805step0 raw29805step0Labels permutation34 permutation5
    mixedMoment B raw29805step1 raw29805step1Labels = mixedMoment B raw29805step2 raw29805step2Labels := by
      have ha : raw29805step2 = -raw29805step1 := by apply Matrix.ext; change ∀ i j, raw29805step2 i j = -(raw29805step1 i j); unfold raw29805step2 raw29805step1; decide +kernel
      have hl : raw29805step2Labels = raw29805step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29805step2 raw29805step2Labels = mixedMoment B raw29805step3 raw29805step3Labels := by
      have ha : raw29805step3 = raw29805step2 := by apply Matrix.ext; unfold raw29805step3 raw29805step2; decide +kernel
      have hl : raw29805step2Labels = labelEmbedding1 ∘ raw29805step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29805step2 raw29805step2Labels raw29805step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1679 node1679Labels := by rfl

def raw29806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29806Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29806step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw29806step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29806step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw29806step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29806step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw29806step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29806 raw29806Labels = mixedMoment B node3415 node3415Labels := by
  calc
    mixedMoment B raw29806 raw29806Labels = mixedMoment B raw29806step0 raw29806step0Labels := by
      have hz : ∀ j, raw29806 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29806step0 = (fun i j => raw29806 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29806step0 raw29806; decide +kernel
      have hl : raw29806step0Labels = raw29806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29806 raw29806Labels permutation346 hz
    mixedMoment B raw29806step0 raw29806step0Labels = mixedMoment B raw29806step1 raw29806step1Labels := by
      have ha : raw29806step1 = (fun i j => raw29806step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29806step1 raw29806step0; decide +kernel
      have hl : raw29806step1Labels = raw29806step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29806step0 raw29806step0Labels permutation34 permutation5
    mixedMoment B raw29806step1 raw29806step1Labels = mixedMoment B raw29806step2 raw29806step2Labels := by
      have ha : raw29806step2 = -raw29806step1 := by apply Matrix.ext; change ∀ i j, raw29806step2 i j = -(raw29806step1 i j); unfold raw29806step2 raw29806step1; decide +kernel
      have hl : raw29806step2Labels = raw29806step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29806step2 raw29806step2Labels = mixedMoment B raw29806step3 raw29806step3Labels := by
      have ha : raw29806step3 = raw29806step2 := by apply Matrix.ext; unfold raw29806step3 raw29806step2; decide +kernel
      have hl : raw29806step2Labels = labelEmbedding1 ∘ raw29806step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29806step2 raw29806step2Labels raw29806step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3415 node3415Labels := by rfl

def raw29807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29807Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29807step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw29807step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29807step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw29807step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29807step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw29807step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29807 raw29807Labels = mixedMoment B node3452 node3452Labels := by
  calc
    mixedMoment B raw29807 raw29807Labels = mixedMoment B raw29807step0 raw29807step0Labels := by
      have ha : raw29807step0 = (fun i j => raw29807 (permutation178 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29807step0 raw29807; decide +kernel
      have hl : raw29807step0Labels = raw29807Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29807 raw29807Labels permutation178 permutation5
    mixedMoment B raw29807step0 raw29807step0Labels = mixedMoment B raw29807step1 raw29807step1Labels := by
      have ha : raw29807step1 = -raw29807step0 := by apply Matrix.ext; change ∀ i j, raw29807step1 i j = -(raw29807step0 i j); unfold raw29807step1 raw29807step0; decide +kernel
      have hl : raw29807step1Labels = raw29807step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29807step1 raw29807step1Labels = mixedMoment B raw29807step2 raw29807step2Labels := by
      have ha : raw29807step2 = raw29807step1 := by apply Matrix.ext; unfold raw29807step2 raw29807step1; decide +kernel
      have hl : raw29807step1Labels = labelEmbedding1 ∘ raw29807step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29807step1 raw29807step1Labels raw29807step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3452 node3452Labels := by rfl

def raw29808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29808Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29808step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]
def raw29808step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29808step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]
def raw29808step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29808 raw29808Labels = mixedMoment B node3588 node3588Labels := by
  calc
    mixedMoment B raw29808 raw29808Labels = mixedMoment B raw29808step0 raw29808step0Labels := by
      have hz : ∀ j, raw29808 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29808step0 = (fun i j => raw29808 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29808step0 raw29808; decide +kernel
      have hl : raw29808step0Labels = raw29808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29808 raw29808Labels permutation346 hz
    mixedMoment B raw29808step0 raw29808step0Labels = mixedMoment B raw29808step1 raw29808step1Labels := by
      have ha : raw29808step1 = (fun i j => raw29808step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw29808step1 raw29808step0; decide +kernel
      have hl : raw29808step1Labels = raw29808step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29808step0 raw29808step0Labels permutation149 permutation5
    mixedMoment B raw29808step1 raw29808step1Labels = mixedMoment B raw29808step2 raw29808step2Labels := by
      have ha : raw29808step2 = raw29808step1 := by apply Matrix.ext; unfold raw29808step2 raw29808step1; decide +kernel
      have hl : raw29808step1Labels = labelEmbedding1 ∘ raw29808step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29808step1 raw29808step1Labels raw29808step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3588 node3588Labels := by rfl

def raw29809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29809Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29809step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw29809step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29809step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw29809step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29809 raw29809Labels = mixedMoment B node3694 node3694Labels := by
  calc
    mixedMoment B raw29809 raw29809Labels = mixedMoment B raw29809step0 raw29809step0Labels := by
      have hz : ∀ j, raw29809 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29809step0 = (fun i j => raw29809 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29809step0 raw29809; decide +kernel
      have hl : raw29809step0Labels = raw29809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29809 raw29809Labels permutation346 hz
    mixedMoment B raw29809step0 raw29809step0Labels = mixedMoment B raw29809step1 raw29809step1Labels := by
      have ha : raw29809step1 = (fun i j => raw29809step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29809step1 raw29809step0; decide +kernel
      have hl : raw29809step1Labels = raw29809step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29809step0 raw29809step0Labels permutation126 permutation2
    mixedMoment B raw29809step1 raw29809step1Labels = mixedMoment B raw29809step2 raw29809step2Labels := by
      have ha : raw29809step2 = -raw29809step1 := by apply Matrix.ext; change ∀ i j, raw29809step2 i j = -(raw29809step1 i j); unfold raw29809step2 raw29809step1; decide +kernel
      have hl : raw29809step2Labels = raw29809step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3694 node3694Labels := by rfl

def raw29810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29810Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29810step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29810step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29810 raw29810Labels = mixedMoment B node2822 node2822Labels := by
  calc
    mixedMoment B raw29810 raw29810Labels = mixedMoment B raw29810step0 raw29810step0Labels := by
      have ha : raw29810step0 = (fun i j => raw29810 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29810step0 raw29810; decide +kernel
      have hl : raw29810step0Labels = raw29810Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29810 raw29810Labels permutation159 permutation2
    _ = mixedMoment B node2822 node2822Labels := by rfl

def raw29811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29811Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29811step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29811step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29811 raw29811Labels = mixedMoment B node2827 node2827Labels := by
  calc
    mixedMoment B raw29811 raw29811Labels = mixedMoment B raw29811step0 raw29811step0Labels := by
      have hz : ∀ j, raw29811 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29811step0 = (fun i j => raw29811 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29811step0 raw29811; decide +kernel
      have hl : raw29811step0Labels = raw29811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29811 raw29811Labels permutation346 hz
    mixedMoment B raw29811step0 raw29811step0Labels = mixedMoment B raw29811step1 raw29811step1Labels := by
      have ha : raw29811step1 = (fun i j => raw29811step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29811step1 raw29811step0; decide +kernel
      have hl : raw29811step1Labels = raw29811step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29811step0 raw29811step0Labels permutation33 permutation2
    _ = mixedMoment B node2827 node2827Labels := by rfl

def raw29812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29812Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29812step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw29812step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29812step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw29812step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29812 raw29812Labels = mixedMoment B node2326 node2326Labels := by
  calc
    mixedMoment B raw29812 raw29812Labels = mixedMoment B raw29812step0 raw29812step0Labels := by
      have hz : ∀ j, raw29812 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29812step0 = (fun i j => raw29812 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29812step0 raw29812; decide +kernel
      have hl : raw29812step0Labels = raw29812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29812 raw29812Labels permutation346 hz
    mixedMoment B raw29812step0 raw29812step0Labels = mixedMoment B raw29812step1 raw29812step1Labels := by
      have ha : raw29812step1 = (fun i j => raw29812step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29812step1 raw29812step0; decide +kernel
      have hl : raw29812step1Labels = raw29812step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29812step0 raw29812step0Labels permutation127 permutation2
    mixedMoment B raw29812step1 raw29812step1Labels = mixedMoment B raw29812step2 raw29812step2Labels := by
      have ha : raw29812step2 = -raw29812step1 := by apply Matrix.ext; change ∀ i j, raw29812step2 i j = -(raw29812step1 i j); unfold raw29812step2 raw29812step1; decide +kernel
      have hl : raw29812step2Labels = raw29812step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2326 node2326Labels := by rfl

def raw29813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29813Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29813step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29813step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29813 raw29813Labels = mixedMoment B node1328 node1328Labels := by
  calc
    mixedMoment B raw29813 raw29813Labels = mixedMoment B raw29813step0 raw29813step0Labels := by
      have ha : raw29813step0 = (fun i j => raw29813 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29813step0 raw29813; decide +kernel
      have hl : raw29813step0Labels = raw29813Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29813 raw29813Labels permutation159 permutation2
    _ = mixedMoment B node1328 node1328Labels := by rfl

def raw29814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29814Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29814step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29814step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29814 raw29814Labels = mixedMoment B node2893 node2893Labels := by
  calc
    mixedMoment B raw29814 raw29814Labels = mixedMoment B raw29814step0 raw29814step0Labels := by
      have ha : raw29814step0 = (fun i j => raw29814 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29814step0 raw29814; decide +kernel
      have hl : raw29814step0Labels = raw29814Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29814 raw29814Labels permutation159 permutation2
    _ = mixedMoment B node2893 node2893Labels := by rfl

def raw29815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29815Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29815step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw29815step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29815 raw29815Labels = mixedMoment B node2925 node2925Labels := by
  calc
    mixedMoment B raw29815 raw29815Labels = mixedMoment B raw29815step0 raw29815step0Labels := by
      have ha : raw29815step0 = (fun i j => raw29815 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29815step0 raw29815; decide +kernel
      have hl : raw29815step0Labels = raw29815Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29815 raw29815Labels permutation158 permutation2
    _ = mixedMoment B node2925 node2925Labels := by rfl

def raw29816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29816Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29816step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29816step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29816 raw29816Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw29816 raw29816Labels = mixedMoment B raw29816step0 raw29816step0Labels := by
      have ha : raw29816step0 = (fun i j => raw29816 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29816step0 raw29816; decide +kernel
      have hl : raw29816step0Labels = raw29816Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29816 raw29816Labels permutation159 permutation2
    _ = mixedMoment B node2924 node2924Labels := by rfl

def raw29817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29817Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29817step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29817step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29817 raw29817Labels = mixedMoment B node1338 node1338Labels := by
  calc
    mixedMoment B raw29817 raw29817Labels = mixedMoment B raw29817step0 raw29817step0Labels := by
      have hz : ∀ j, raw29817 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29817step0 = (fun i j => raw29817 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29817step0 raw29817; decide +kernel
      have hl : raw29817step0Labels = raw29817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29817 raw29817Labels permutation346 hz
    mixedMoment B raw29817step0 raw29817step0Labels = mixedMoment B raw29817step1 raw29817step1Labels := by
      have ha : raw29817step1 = (fun i j => raw29817step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29817step1 raw29817step0; decide +kernel
      have hl : raw29817step1Labels = raw29817step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29817step0 raw29817step0Labels permutation33 permutation2
    _ = mixedMoment B node1338 node1338Labels := by rfl

def raw29818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29818Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29818step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29818step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29818 raw29818Labels = mixedMoment B node2900 node2900Labels := by
  calc
    mixedMoment B raw29818 raw29818Labels = mixedMoment B raw29818step0 raw29818step0Labels := by
      have ha : raw29818step0 = (fun i j => raw29818 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29818step0 raw29818; decide +kernel
      have hl : raw29818step0Labels = raw29818Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29818 raw29818Labels permutation153 permutation2
    _ = mixedMoment B node2900 node2900Labels := by rfl

def raw29819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29819Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw29819step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29819 raw29819Labels = mixedMoment B node2955 node2955Labels := by
  calc
    mixedMoment B raw29819 raw29819Labels = mixedMoment B raw29819step0 raw29819step0Labels := by
      have hz : ∀ j, raw29819 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29819step0 = (fun i j => raw29819 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29819step0 raw29819; decide +kernel
      have hl : raw29819step0Labels = raw29819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29819 raw29819Labels permutation346 hz
    _ = mixedMoment B node2955 node2955Labels := by rfl

def raw29820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29820Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw29820step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29820step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29820 raw29820Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw29820 raw29820Labels = mixedMoment B raw29820step0 raw29820step0Labels := by
      have hz : ∀ j, raw29820 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29820step0 = (fun i j => raw29820 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29820step0 raw29820; decide +kernel
      have hl : raw29820step0Labels = raw29820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29820 raw29820Labels permutation346 hz
    mixedMoment B raw29820step0 raw29820step0Labels = mixedMoment B raw29820step1 raw29820step1Labels := by
      have ha : raw29820step1 = (fun i j => raw29820step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29820step1 raw29820step0; decide +kernel
      have hl : raw29820step1Labels = raw29820step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29820step0 raw29820step0Labels permutation33 permutation2
    _ = mixedMoment B node2954 node2954Labels := by rfl

def raw29821 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29821step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29821step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29821step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29821step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29821step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29821 raw29821Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw29821 raw29821Labels = mixedMoment B raw29821step0 raw29821step0Labels := by
      have hz : ∀ j, raw29821 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29821step0 = (fun i j => raw29821 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29821step0 raw29821; decide +kernel
      have hl : raw29821step0Labels = raw29821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29821 raw29821Labels permutation346 hz
    mixedMoment B raw29821step0 raw29821step0Labels = mixedMoment B raw29821step1 raw29821step1Labels := by
      have ha : raw29821step1 = (fun i j => raw29821step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29821step1 raw29821step0; decide +kernel
      have hl : raw29821step1Labels = raw29821step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29821step0 raw29821step0Labels permutation33 permutation7
    mixedMoment B raw29821step1 raw29821step1Labels = mixedMoment B raw29821step2 raw29821step2Labels := by
      have ha : raw29821step2 = raw29821step1 := by apply Matrix.ext; unfold raw29821step2 raw29821step1; decide +kernel
      have hl : raw29821step1Labels = labelEmbedding10 ∘ raw29821step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29821step1 raw29821step1Labels raw29821step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

def raw29822 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29822Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw29822step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29822step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw29822step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29822 raw29822Labels = mixedMoment B node5050 node5050Labels := by
  calc
    mixedMoment B raw29822 raw29822Labels = mixedMoment B raw29822step0 raw29822step0Labels := by
      have ha : raw29822step0 = (fun i j => raw29822 (permutation159 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29822step0 raw29822; decide +kernel
      have hl : raw29822step0Labels = raw29822Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29822 raw29822Labels permutation159 permutation7
    mixedMoment B raw29822step0 raw29822step0Labels = mixedMoment B raw29822step1 raw29822step1Labels := by
      have ha : raw29822step1 = raw29822step0 := by apply Matrix.ext; unfold raw29822step1 raw29822step0; decide +kernel
      have hl : raw29822step0Labels = labelEmbedding10 ∘ raw29822step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29822step0 raw29822step0Labels raw29822step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5050 node5050Labels := by rfl

def raw29823 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29823Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29823step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29823step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw29823step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29823 raw29823Labels = mixedMoment B node5014 node5014Labels := by
  calc
    mixedMoment B raw29823 raw29823Labels = mixedMoment B raw29823step0 raw29823step0Labels := by
      have hz : ∀ j, raw29823 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29823step0 = (fun i j => raw29823 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29823step0 raw29823; decide +kernel
      have hl : raw29823step0Labels = raw29823Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29823 raw29823Labels permutation346 hz
    mixedMoment B raw29823step0 raw29823step0Labels = mixedMoment B raw29823step1 raw29823step1Labels := by
      have ha : raw29823step1 = (fun i j => raw29823step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29823step1 raw29823step0; decide +kernel
      have hl : raw29823step1Labels = raw29823step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29823step0 raw29823step0Labels permutation127 permutation2
    _ = mixedMoment B node5014 node5014Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
