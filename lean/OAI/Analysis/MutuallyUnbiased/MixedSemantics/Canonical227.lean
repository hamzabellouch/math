import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw29056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw29056Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw29056step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29056 raw29056Labels = mixedMoment B node2693 node2693Labels := by
  calc
    mixedMoment B raw29056 raw29056Labels = mixedMoment B raw29056step0 raw29056step0Labels := by
      have ha : raw29056step0 = (fun i j => raw29056 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29056step0 raw29056; decide +kernel
      have hl : raw29056step0Labels = raw29056Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29056 raw29056Labels permutation158 permutation2
    _ = mixedMoment B node2693 node2693Labels := by rfl

def raw29057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw29057Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29057 raw29057Labels = mixedMoment B node2476 node2476Labels := by
  calc
    _ = mixedMoment B node2476 node2476Labels := by rfl

def raw29058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29058Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw29058step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29058 raw29058Labels = mixedMoment B node2451 node2451Labels := by
  calc
    mixedMoment B raw29058 raw29058Labels = mixedMoment B raw29058step0 raw29058step0Labels := by
      have ha : raw29058step0 = (fun i j => raw29058 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29058step0 raw29058; decide +kernel
      have hl : raw29058step0Labels = raw29058Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29058 raw29058Labels permutation158 permutation2
    _ = mixedMoment B node2451 node2451Labels := by rfl

def raw29059 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw29059Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29059step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw29059step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29059 raw29059Labels = mixedMoment B node1996 node1996Labels := by
  calc
    mixedMoment B raw29059 raw29059Labels = mixedMoment B raw29059step0 raw29059step0Labels := by
      have ha : raw29059step0 = (fun i j => raw29059 (permutation646 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29059step0 raw29059; decide +kernel
      have hl : raw29059step0Labels = raw29059Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29059 raw29059Labels permutation646 permutation4
    _ = mixedMoment B node1996 node1996Labels := by rfl

def raw29060 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw29060Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29060step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw29060step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29060 raw29060Labels = mixedMoment B node1986 node1986Labels := by
  calc
    mixedMoment B raw29060 raw29060Labels = mixedMoment B raw29060step0 raw29060step0Labels := by
      have ha : raw29060step0 = (fun i j => raw29060 (permutation644 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29060step0 raw29060; decide +kernel
      have hl : raw29060step0Labels = raw29060Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29060 raw29060Labels permutation644 permutation4
    _ = mixedMoment B node1986 node1986Labels := by rfl

def raw29061 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw29061Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29061step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29061step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29061 raw29061Labels = mixedMoment B node1784 node1784Labels := by
  calc
    mixedMoment B raw29061 raw29061Labels = mixedMoment B raw29061step0 raw29061step0Labels := by
      have ha : raw29061step0 = (fun i j => raw29061 (permutation646 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29061step0 raw29061; decide +kernel
      have hl : raw29061step0Labels = raw29061Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29061 raw29061Labels permutation646 permutation4
    _ = mixedMoment B node1784 node1784Labels := by rfl

def raw29062 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw29062Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29062step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29062step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29062 raw29062Labels = mixedMoment B node898 node898Labels := by
  calc
    mixedMoment B raw29062 raw29062Labels = mixedMoment B raw29062step0 raw29062step0Labels := by
      have ha : raw29062step0 = (fun i j => raw29062 (permutation646 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29062step0 raw29062; decide +kernel
      have hl : raw29062step0Labels = raw29062Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29062 raw29062Labels permutation646 permutation4
    _ = mixedMoment B node898 node898Labels := by rfl

def raw29063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29063Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29063step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29063step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw29063step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29063step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw29063step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29063step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29063step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29063 raw29063Labels = mixedMoment B node4846 node4846Labels := by
  calc
    mixedMoment B raw29063 raw29063Labels = mixedMoment B raw29063step0 raw29063step0Labels := by
      have hz : ∀ j, raw29063 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29063step0 = (fun i j => raw29063 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29063step0 raw29063; decide +kernel
      have hl : raw29063step0Labels = raw29063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29063 raw29063Labels permutation434 hz
    mixedMoment B raw29063step0 raw29063step0Labels = mixedMoment B raw29063step1 raw29063step1Labels := by
      have hz : ∀ j, raw29063step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29063step1 = (fun i j => raw29063step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29063step1 raw29063step0; decide +kernel
      have hl : raw29063step1Labels = raw29063step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29063step0 raw29063step0Labels permutation80 hz
    mixedMoment B raw29063step1 raw29063step1Labels = mixedMoment B raw29063step2 raw29063step2Labels := by
      have ha : raw29063step2 = (fun i j => raw29063step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29063step2 raw29063step1; decide +kernel
      have hl : raw29063step2Labels = raw29063step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29063step1 raw29063step1Labels permutation31 permutation2
    mixedMoment B raw29063step2 raw29063step2Labels = mixedMoment B raw29063step3 raw29063step3Labels := by
      have ha : raw29063step3 = -raw29063step2 := by apply Matrix.ext; change ∀ i j, raw29063step3 i j = -(raw29063step2 i j); unfold raw29063step3 raw29063step2; decide +kernel
      have hl : raw29063step3Labels = raw29063step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4846 node4846Labels := by rfl

def raw29064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29064Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29064step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29064step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw29064step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29064step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29064step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29064 raw29064Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw29064 raw29064Labels = mixedMoment B raw29064step0 raw29064step0Labels := by
      have hz : ∀ j, raw29064 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29064step0 = (fun i j => raw29064 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29064step0 raw29064; decide +kernel
      have hl : raw29064step0Labels = raw29064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29064 raw29064Labels permutation434 hz
    mixedMoment B raw29064step0 raw29064step0Labels = mixedMoment B raw29064step1 raw29064step1Labels := by
      have ha : raw29064step1 = (fun i j => raw29064step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29064step1 raw29064step0; decide +kernel
      have hl : raw29064step1Labels = raw29064step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29064step0 raw29064step0Labels permutation151 permutation2
    mixedMoment B raw29064step1 raw29064step1Labels = mixedMoment B raw29064step2 raw29064step2Labels := by
      have ha : raw29064step2 = -raw29064step1 := by apply Matrix.ext; change ∀ i j, raw29064step2 i j = -(raw29064step1 i j); unfold raw29064step2 raw29064step1; decide +kernel
      have hl : raw29064step2Labels = raw29064step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4834 node4834Labels := by rfl

def raw29065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29065Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29065step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw29065step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29065step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29065step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29065 raw29065Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw29065 raw29065Labels = mixedMoment B raw29065step0 raw29065step0Labels := by
      have hz : ∀ j, raw29065 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29065step0 = (fun i j => raw29065 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29065step0 raw29065; decide +kernel
      have hl : raw29065step0Labels = raw29065Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29065 raw29065Labels permutation346 hz
    mixedMoment B raw29065step0 raw29065step0Labels = mixedMoment B raw29065step1 raw29065step1Labels := by
      have ha : raw29065step1 = (fun i j => raw29065step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29065step1 raw29065step0; decide +kernel
      have hl : raw29065step1Labels = raw29065step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29065step0 raw29065step0Labels permutation151 permutation2
    mixedMoment B raw29065step1 raw29065step1Labels = mixedMoment B raw29065step2 raw29065step2Labels := by
      have ha : raw29065step2 = -raw29065step1 := by apply Matrix.ext; change ∀ i j, raw29065step2 i j = -(raw29065step1 i j); unfold raw29065step2 raw29065step1; decide +kernel
      have hl : raw29065step2Labels = raw29065step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4834 node4834Labels := by rfl

def raw29066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29066Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29066step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29066step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![3, 0, -3]]
def raw29066step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29066step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![3, 0, -3]]
def raw29066step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29066step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw29066step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw29066step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw29066step4Labels : Fin 2 → Fin 3 := ![0, 2]

def raw29066step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw29066step5Labels : Fin 2 → Fin 3 := ![0, 2]

def raw29066step6 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw29066step6Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29066 raw29066Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw29066 raw29066Labels = mixedMoment B raw29066step0 raw29066step0Labels := by
      have hz : ∀ j, raw29066 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29066step0 = (fun i j => raw29066 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29066step0 raw29066; decide +kernel
      have hl : raw29066step0Labels = raw29066Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29066 raw29066Labels permutation520 hz
    mixedMoment B raw29066step0 raw29066step0Labels = mixedMoment B raw29066step1 raw29066step1Labels := by
      have hz : ∀ j, raw29066step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29066step1 = (fun i j => raw29066step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29066step1 raw29066step0; decide +kernel
      have hl : raw29066step1Labels = raw29066step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29066step0 raw29066step0Labels permutation104 hz
    mixedMoment B raw29066step1 raw29066step1Labels = mixedMoment B raw29066step2 raw29066step2Labels := by
      have hz : ∀ j, raw29066step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw29066step2 = (fun i j => raw29066step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw29066step2 raw29066step1; decide +kernel
      have hl : raw29066step2Labels = raw29066step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29066step1 raw29066step1Labels permutation20 hz
    mixedMoment B raw29066step2 raw29066step2Labels = mixedMoment B raw29066step3 raw29066step3Labels := by
      have hz : ∀ i, raw29066step2 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw29066step3 = (fun i j => raw29066step2 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw29066step3 raw29066step2; decide +kernel
      have hl : raw29066step3Labels = (fun j => raw29066step2Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw29066step2 raw29066step2Labels permutation4 hz
    mixedMoment B raw29066step3 raw29066step3Labels = mixedMoment B raw29066step4 raw29066step4Labels := by
      have ha : raw29066step4 = (fun i j => raw29066step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29066step4 raw29066step3; decide +kernel
      have hl : raw29066step4Labels = raw29066step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29066step3 raw29066step3Labels permutation7 permutation0
    mixedMoment B raw29066step4 raw29066step4Labels = mixedMoment B raw29066step5 raw29066step5Labels := by
      have ha : raw29066step5 = -raw29066step4 := by apply Matrix.ext; change ∀ i j, raw29066step5 i j = -(raw29066step4 i j); unfold raw29066step5 raw29066step4; decide +kernel
      have hl : raw29066step5Labels = raw29066step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29066step5 raw29066step5Labels = mixedMoment B raw29066step6 raw29066step6Labels := by
      have ha : raw29066step6 = raw29066step5 := by apply Matrix.ext; unfold raw29066step6 raw29066step5; decide +kernel
      have hl : raw29066step5Labels = labelEmbedding2 ∘ raw29066step6Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29066step5 raw29066step5Labels raw29066step6Labels labelEmbedding2 hl
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw29067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29067Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29067step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29067step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw29067step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29067step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29067step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29067step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29067step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29067 raw29067Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw29067 raw29067Labels = mixedMoment B raw29067step0 raw29067step0Labels := by
      have hz : ∀ j, raw29067 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29067step0 = (fun i j => raw29067 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29067step0 raw29067; decide +kernel
      have hl : raw29067step0Labels = raw29067Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29067 raw29067Labels permutation434 hz
    mixedMoment B raw29067step0 raw29067step0Labels = mixedMoment B raw29067step1 raw29067step1Labels := by
      have hz : ∀ j, raw29067step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29067step1 = (fun i j => raw29067step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29067step1 raw29067step0; decide +kernel
      have hl : raw29067step1Labels = raw29067step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29067step0 raw29067step0Labels permutation80 hz
    mixedMoment B raw29067step1 raw29067step1Labels = mixedMoment B raw29067step2 raw29067step2Labels := by
      have ha : raw29067step2 = (fun i j => raw29067step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29067step2 raw29067step1; decide +kernel
      have hl : raw29067step2Labels = raw29067step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29067step1 raw29067step1Labels permutation31 permutation7
    mixedMoment B raw29067step2 raw29067step2Labels = mixedMoment B raw29067step3 raw29067step3Labels := by
      have ha : raw29067step3 = raw29067step2 := by apply Matrix.ext; unfold raw29067step3 raw29067step2; decide +kernel
      have hl : raw29067step2Labels = labelEmbedding10 ∘ raw29067step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29067step2 raw29067step2Labels raw29067step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5274 node5274Labels := by rfl

def raw29068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29068Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29068step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29068step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw29068step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29068 raw29068Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw29068 raw29068Labels = mixedMoment B raw29068step0 raw29068step0Labels := by
      have hz : ∀ j, raw29068 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29068step0 = (fun i j => raw29068 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29068step0 raw29068; decide +kernel
      have hl : raw29068step0Labels = raw29068Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29068 raw29068Labels permutation434 hz
    mixedMoment B raw29068step0 raw29068step0Labels = mixedMoment B raw29068step1 raw29068step1Labels := by
      have hz : ∀ j, raw29068step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29068step1 = (fun i j => raw29068step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29068step1 raw29068step0; decide +kernel
      have hl : raw29068step1Labels = raw29068step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29068step0 raw29068step0Labels permutation80 hz
    _ = mixedMoment B node4605 node4605Labels := by rfl

def raw29069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29069Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29069step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29069step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw29069step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29069step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw29069step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29069 raw29069Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw29069 raw29069Labels = mixedMoment B raw29069step0 raw29069step0Labels := by
      have hz : ∀ j, raw29069 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29069step0 = (fun i j => raw29069 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29069step0 raw29069; decide +kernel
      have hl : raw29069step0Labels = raw29069Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29069 raw29069Labels permutation434 hz
    mixedMoment B raw29069step0 raw29069step0Labels = mixedMoment B raw29069step1 raw29069step1Labels := by
      have ha : raw29069step1 = (fun i j => raw29069step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29069step1 raw29069step0; decide +kernel
      have hl : raw29069step1Labels = raw29069step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29069step0 raw29069step0Labels permutation149 permutation2
    mixedMoment B raw29069step1 raw29069step1Labels = mixedMoment B raw29069step2 raw29069step2Labels := by
      have ha : raw29069step2 = -raw29069step1 := by apply Matrix.ext; change ∀ i j, raw29069step2 i j = -(raw29069step1 i j); unfold raw29069step2 raw29069step1; decide +kernel
      have hl : raw29069step2Labels = raw29069step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4804 node4804Labels := by rfl

def raw29070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29070Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29070step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw29070step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29070step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw29070step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29070 raw29070Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw29070 raw29070Labels = mixedMoment B raw29070step0 raw29070step0Labels := by
      have hz : ∀ j, raw29070 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29070step0 = (fun i j => raw29070 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29070step0 raw29070; decide +kernel
      have hl : raw29070step0Labels = raw29070Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29070 raw29070Labels permutation346 hz
    mixedMoment B raw29070step0 raw29070step0Labels = mixedMoment B raw29070step1 raw29070step1Labels := by
      have ha : raw29070step1 = (fun i j => raw29070step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29070step1 raw29070step0; decide +kernel
      have hl : raw29070step1Labels = raw29070step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29070step0 raw29070step0Labels permutation149 permutation2
    mixedMoment B raw29070step1 raw29070step1Labels = mixedMoment B raw29070step2 raw29070step2Labels := by
      have ha : raw29070step2 = -raw29070step1 := by apply Matrix.ext; change ∀ i j, raw29070step2 i j = -(raw29070step1 i j); unfold raw29070step2 raw29070step1; decide +kernel
      have hl : raw29070step2Labels = raw29070step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4804 node4804Labels := by rfl

def raw29071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29071Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29071step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29071step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw29071step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29071step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![3, 0, -3]]
def raw29071step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29071step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw29071step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29071step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw29071step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29071 raw29071Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw29071 raw29071Labels = mixedMoment B raw29071step0 raw29071step0Labels := by
      have hz : ∀ j, raw29071 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29071step0 = (fun i j => raw29071 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29071step0 raw29071; decide +kernel
      have hl : raw29071step0Labels = raw29071Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29071 raw29071Labels permutation520 hz
    mixedMoment B raw29071step0 raw29071step0Labels = mixedMoment B raw29071step1 raw29071step1Labels := by
      have hz : ∀ j, raw29071step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29071step1 = (fun i j => raw29071step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29071step1 raw29071step0; decide +kernel
      have hl : raw29071step1Labels = raw29071step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29071step0 raw29071step0Labels permutation104 hz
    mixedMoment B raw29071step1 raw29071step1Labels = mixedMoment B raw29071step2 raw29071step2Labels := by
      have hz : ∀ j, raw29071step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw29071step2 = (fun i j => raw29071step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw29071step2 raw29071step1; decide +kernel
      have hl : raw29071step2Labels = raw29071step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29071step1 raw29071step1Labels permutation20 hz
    mixedMoment B raw29071step2 raw29071step2Labels = mixedMoment B raw29071step3 raw29071step3Labels := by
      have ha : raw29071step3 = (fun i j => raw29071step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29071step3 raw29071step2; decide +kernel
      have hl : raw29071step3Labels = raw29071step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29071step2 raw29071step2Labels permutation7 permutation2
    mixedMoment B raw29071step3 raw29071step3Labels = mixedMoment B raw29071step4 raw29071step4Labels := by
      have ha : raw29071step4 = -raw29071step3 := by apply Matrix.ext; change ∀ i j, raw29071step4 i j = -(raw29071step3 i j); unfold raw29071step4 raw29071step3; decide +kernel
      have hl : raw29071step4Labels = raw29071step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4897 node4897Labels := by rfl

def raw29072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29072Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29072step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29072step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw29072step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29072 raw29072Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw29072 raw29072Labels = mixedMoment B raw29072step0 raw29072step0Labels := by
      have hz : ∀ j, raw29072 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29072step0 = (fun i j => raw29072 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29072step0 raw29072; decide +kernel
      have hl : raw29072step0Labels = raw29072Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29072 raw29072Labels permutation434 hz
    mixedMoment B raw29072step0 raw29072step0Labels = mixedMoment B raw29072step1 raw29072step1Labels := by
      have hz : ∀ j, raw29072step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29072step1 = (fun i j => raw29072step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29072step1 raw29072step0; decide +kernel
      have hl : raw29072step1Labels = raw29072step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29072step0 raw29072step0Labels permutation80 hz
    _ = mixedMoment B node5272 node5272Labels := by rfl

def raw29073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29073Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29073step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29073 raw29073Labels = mixedMoment B node4543 node4543Labels := by
  calc
    mixedMoment B raw29073 raw29073Labels = mixedMoment B raw29073step0 raw29073step0Labels := by
      have hz : ∀ j, raw29073 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29073step0 = (fun i j => raw29073 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29073step0 raw29073; decide +kernel
      have hl : raw29073step0Labels = raw29073Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29073 raw29073Labels permutation434 hz
    _ = mixedMoment B node4543 node4543Labels := by rfl

def raw29074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29074Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29074step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw29074step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29074step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw29074step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29074 raw29074Labels = mixedMoment B node4769 node4769Labels := by
  calc
    mixedMoment B raw29074 raw29074Labels = mixedMoment B raw29074step0 raw29074step0Labels := by
      have hz : ∀ j, raw29074 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29074step0 = (fun i j => raw29074 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29074step0 raw29074; decide +kernel
      have hl : raw29074step0Labels = raw29074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29074 raw29074Labels permutation434 hz
    mixedMoment B raw29074step0 raw29074step0Labels = mixedMoment B raw29074step1 raw29074step1Labels := by
      have ha : raw29074step1 = (fun i j => raw29074step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29074step1 raw29074step0; decide +kernel
      have hl : raw29074step1Labels = raw29074step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29074step0 raw29074step0Labels permutation145 permutation2
    mixedMoment B raw29074step1 raw29074step1Labels = mixedMoment B raw29074step2 raw29074step2Labels := by
      have ha : raw29074step2 = -raw29074step1 := by apply Matrix.ext; change ∀ i j, raw29074step2 i j = -(raw29074step1 i j); unfold raw29074step2 raw29074step1; decide +kernel
      have hl : raw29074step2Labels = raw29074step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4769 node4769Labels := by rfl

def raw29075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29075Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29075step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29075step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29075step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29075 raw29075Labels = mixedMoment B node4760 node4760Labels := by
  calc
    mixedMoment B raw29075 raw29075Labels = mixedMoment B raw29075step0 raw29075step0Labels := by
      have ha : raw29075step0 = (fun i j => raw29075 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29075step0 raw29075; decide +kernel
      have hl : raw29075step0Labels = raw29075Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29075 raw29075Labels permutation646 permutation2
    mixedMoment B raw29075step0 raw29075step0Labels = mixedMoment B raw29075step1 raw29075step1Labels := by
      have ha : raw29075step1 = -raw29075step0 := by apply Matrix.ext; change ∀ i j, raw29075step1 i j = -(raw29075step0 i j); unfold raw29075step1 raw29075step0; decide +kernel
      have hl : raw29075step1Labels = raw29075step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4760 node4760Labels := by rfl

def raw29076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29076Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29076step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29076step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw29076step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29076step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29076step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29076step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29076step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29076 raw29076Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw29076 raw29076Labels = mixedMoment B raw29076step0 raw29076step0Labels := by
      have hz : ∀ j, raw29076 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29076step0 = (fun i j => raw29076 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29076step0 raw29076; decide +kernel
      have hl : raw29076step0Labels = raw29076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29076 raw29076Labels permutation520 hz
    mixedMoment B raw29076step0 raw29076step0Labels = mixedMoment B raw29076step1 raw29076step1Labels := by
      have hz : ∀ j, raw29076step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29076step1 = (fun i j => raw29076step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29076step1 raw29076step0; decide +kernel
      have hl : raw29076step1Labels = raw29076step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29076step0 raw29076step0Labels permutation104 hz
    mixedMoment B raw29076step1 raw29076step1Labels = mixedMoment B raw29076step2 raw29076step2Labels := by
      have ha : raw29076step2 = (fun i j => raw29076step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29076step2 raw29076step1; decide +kernel
      have hl : raw29076step2Labels = raw29076step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29076step1 raw29076step1Labels permutation31 permutation2
    mixedMoment B raw29076step2 raw29076step2Labels = mixedMoment B raw29076step3 raw29076step3Labels := by
      have ha : raw29076step3 = -raw29076step2 := by apply Matrix.ext; change ∀ i j, raw29076step3 i j = -(raw29076step2 i j); unfold raw29076step3 raw29076step2; decide +kernel
      have hl : raw29076step3Labels = raw29076step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4841 node4841Labels := by rfl

def raw29077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29077Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29077step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29077 raw29077Labels = mixedMoment B node5099 node5099Labels := by
  calc
    mixedMoment B raw29077 raw29077Labels = mixedMoment B raw29077step0 raw29077step0Labels := by
      have hz : ∀ j, raw29077 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29077step0 = (fun i j => raw29077 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29077step0 raw29077; decide +kernel
      have hl : raw29077step0Labels = raw29077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29077 raw29077Labels permutation434 hz
    _ = mixedMoment B node5099 node5099Labels := by rfl

def raw29078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29078Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29078step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29078 raw29078Labels = mixedMoment B node4543 node4543Labels := by
  calc
    mixedMoment B raw29078 raw29078Labels = mixedMoment B raw29078step0 raw29078step0Labels := by
      have hz : ∀ j, raw29078 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29078step0 = (fun i j => raw29078 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29078step0 raw29078; decide +kernel
      have hl : raw29078step0Labels = raw29078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29078 raw29078Labels permutation346 hz
    _ = mixedMoment B node4543 node4543Labels := by rfl

def raw29079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29079Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29079step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29079step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw29079step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29079step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw29079step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29079 raw29079Labels = mixedMoment B node4769 node4769Labels := by
  calc
    mixedMoment B raw29079 raw29079Labels = mixedMoment B raw29079step0 raw29079step0Labels := by
      have hz : ∀ j, raw29079 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29079step0 = (fun i j => raw29079 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29079step0 raw29079; decide +kernel
      have hl : raw29079step0Labels = raw29079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29079 raw29079Labels permutation346 hz
    mixedMoment B raw29079step0 raw29079step0Labels = mixedMoment B raw29079step1 raw29079step1Labels := by
      have ha : raw29079step1 = (fun i j => raw29079step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29079step1 raw29079step0; decide +kernel
      have hl : raw29079step1Labels = raw29079step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29079step0 raw29079step0Labels permutation145 permutation2
    mixedMoment B raw29079step1 raw29079step1Labels = mixedMoment B raw29079step2 raw29079step2Labels := by
      have ha : raw29079step2 = -raw29079step1 := by apply Matrix.ext; change ∀ i j, raw29079step2 i j = -(raw29079step1 i j); unfold raw29079step2 raw29079step1; decide +kernel
      have hl : raw29079step2Labels = raw29079step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4769 node4769Labels := by rfl

def raw29080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29080step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29080step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29080step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29080 raw29080Labels = mixedMoment B node4760 node4760Labels := by
  calc
    mixedMoment B raw29080 raw29080Labels = mixedMoment B raw29080step0 raw29080step0Labels := by
      have ha : raw29080step0 = (fun i j => raw29080 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29080step0 raw29080; decide +kernel
      have hl : raw29080step0Labels = raw29080Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29080 raw29080Labels permutation664 permutation2
    mixedMoment B raw29080step0 raw29080step0Labels = mixedMoment B raw29080step1 raw29080step1Labels := by
      have ha : raw29080step1 = -raw29080step0 := by apply Matrix.ext; change ∀ i j, raw29080step1 i j = -(raw29080step0 i j); unfold raw29080step1 raw29080step0; decide +kernel
      have hl : raw29080step1Labels = raw29080step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4760 node4760Labels := by rfl

def raw29081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29081Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29081step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29081step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw29081step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29081step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29081step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29081step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29081step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29081 raw29081Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw29081 raw29081Labels = mixedMoment B raw29081step0 raw29081step0Labels := by
      have hz : ∀ j, raw29081 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29081step0 = (fun i j => raw29081 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29081step0 raw29081; decide +kernel
      have hl : raw29081step0Labels = raw29081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29081 raw29081Labels permutation520 hz
    mixedMoment B raw29081step0 raw29081step0Labels = mixedMoment B raw29081step1 raw29081step1Labels := by
      have hz : ∀ j, raw29081step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29081step1 = (fun i j => raw29081step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29081step1 raw29081step0; decide +kernel
      have hl : raw29081step1Labels = raw29081step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29081step0 raw29081step0Labels permutation80 hz
    mixedMoment B raw29081step1 raw29081step1Labels = mixedMoment B raw29081step2 raw29081step2Labels := by
      have ha : raw29081step2 = (fun i j => raw29081step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29081step2 raw29081step1; decide +kernel
      have hl : raw29081step2Labels = raw29081step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29081step1 raw29081step1Labels permutation31 permutation2
    mixedMoment B raw29081step2 raw29081step2Labels = mixedMoment B raw29081step3 raw29081step3Labels := by
      have ha : raw29081step3 = -raw29081step2 := by apply Matrix.ext; change ∀ i j, raw29081step3 i j = -(raw29081step2 i j); unfold raw29081step3 raw29081step2; decide +kernel
      have hl : raw29081step3Labels = raw29081step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4841 node4841Labels := by rfl

def raw29082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29082Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29082step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29082 raw29082Labels = mixedMoment B node5099 node5099Labels := by
  calc
    mixedMoment B raw29082 raw29082Labels = mixedMoment B raw29082step0 raw29082step0Labels := by
      have hz : ∀ j, raw29082 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29082step0 = (fun i j => raw29082 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29082step0 raw29082; decide +kernel
      have hl : raw29082step0Labels = raw29082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29082 raw29082Labels permutation346 hz
    _ = mixedMoment B node5099 node5099Labels := by rfl

def raw29083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29083Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29083step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29083step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw29083step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29083 raw29083Labels = mixedMoment B node4557 node4557Labels := by
  calc
    mixedMoment B raw29083 raw29083Labels = mixedMoment B raw29083step0 raw29083step0Labels := by
      have hz : ∀ j, raw29083 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29083step0 = (fun i j => raw29083 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29083step0 raw29083; decide +kernel
      have hl : raw29083step0Labels = raw29083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29083 raw29083Labels permutation434 hz
    mixedMoment B raw29083step0 raw29083step0Labels = mixedMoment B raw29083step1 raw29083step1Labels := by
      have hz : ∀ j, raw29083step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29083step1 = (fun i j => raw29083step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29083step1 raw29083step0; decide +kernel
      have hl : raw29083step1Labels = raw29083step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29083step0 raw29083step0Labels permutation80 hz
    _ = mixedMoment B node4557 node4557Labels := by rfl

def raw29084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29084Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29084step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29084step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw29084step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29084step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw29084step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29084step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw29084step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29084 raw29084Labels = mixedMoment B node4692 node4692Labels := by
  calc
    mixedMoment B raw29084 raw29084Labels = mixedMoment B raw29084step0 raw29084step0Labels := by
      have hz : ∀ j, raw29084 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29084step0 = (fun i j => raw29084 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29084step0 raw29084; decide +kernel
      have hl : raw29084step0Labels = raw29084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29084 raw29084Labels permutation434 hz
    mixedMoment B raw29084step0 raw29084step0Labels = mixedMoment B raw29084step1 raw29084step1Labels := by
      have hz : ∀ j, raw29084step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29084step1 = (fun i j => raw29084step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29084step1 raw29084step0; decide +kernel
      have hl : raw29084step1Labels = raw29084step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29084step0 raw29084step0Labels permutation80 hz
    mixedMoment B raw29084step1 raw29084step1Labels = mixedMoment B raw29084step2 raw29084step2Labels := by
      have ha : raw29084step2 = (fun i j => raw29084step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29084step2 raw29084step1; decide +kernel
      have hl : raw29084step2Labels = raw29084step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29084step1 raw29084step1Labels permutation31 permutation2
    mixedMoment B raw29084step2 raw29084step2Labels = mixedMoment B raw29084step3 raw29084step3Labels := by
      have ha : raw29084step3 = -raw29084step2 := by apply Matrix.ext; change ∀ i j, raw29084step3 i j = -(raw29084step2 i j); unfold raw29084step3 raw29084step2; decide +kernel
      have hl : raw29084step3Labels = raw29084step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4692 node4692Labels := by rfl

def raw29085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29085step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29085step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29085step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29085step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29085step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29085 raw29085Labels = mixedMoment B node4681 node4681Labels := by
  calc
    mixedMoment B raw29085 raw29085Labels = mixedMoment B raw29085step0 raw29085step0Labels := by
      have hz : ∀ j, raw29085 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29085step0 = (fun i j => raw29085 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29085step0 raw29085; decide +kernel
      have hl : raw29085step0Labels = raw29085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29085 raw29085Labels permutation434 hz
    mixedMoment B raw29085step0 raw29085step0Labels = mixedMoment B raw29085step1 raw29085step1Labels := by
      have ha : raw29085step1 = (fun i j => raw29085step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29085step1 raw29085step0; decide +kernel
      have hl : raw29085step1Labels = raw29085step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29085step0 raw29085step0Labels permutation151 permutation2
    mixedMoment B raw29085step1 raw29085step1Labels = mixedMoment B raw29085step2 raw29085step2Labels := by
      have ha : raw29085step2 = -raw29085step1 := by apply Matrix.ext; change ∀ i j, raw29085step2 i j = -(raw29085step1 i j); unfold raw29085step2 raw29085step1; decide +kernel
      have hl : raw29085step2Labels = raw29085step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4681 node4681Labels := by rfl

def raw29086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29086step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29086step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29086step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29086step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29086 raw29086Labels = mixedMoment B node4681 node4681Labels := by
  calc
    mixedMoment B raw29086 raw29086Labels = mixedMoment B raw29086step0 raw29086step0Labels := by
      have hz : ∀ j, raw29086 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29086step0 = (fun i j => raw29086 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29086step0 raw29086; decide +kernel
      have hl : raw29086step0Labels = raw29086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29086 raw29086Labels permutation346 hz
    mixedMoment B raw29086step0 raw29086step0Labels = mixedMoment B raw29086step1 raw29086step1Labels := by
      have ha : raw29086step1 = (fun i j => raw29086step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29086step1 raw29086step0; decide +kernel
      have hl : raw29086step1Labels = raw29086step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29086step0 raw29086step0Labels permutation151 permutation2
    mixedMoment B raw29086step1 raw29086step1Labels = mixedMoment B raw29086step2 raw29086step2Labels := by
      have ha : raw29086step2 = -raw29086step1 := by apply Matrix.ext; change ∀ i j, raw29086step2 i j = -(raw29086step1 i j); unfold raw29086step2 raw29086step1; decide +kernel
      have hl : raw29086step2Labels = raw29086step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4681 node4681Labels := by rfl

def raw29087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29087step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29087step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29087step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29087 raw29087Labels = mixedMoment B node5110 node5110Labels := by
  calc
    mixedMoment B raw29087 raw29087Labels = mixedMoment B raw29087step0 raw29087step0Labels := by
      have hz : ∀ j, raw29087 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29087step0 = (fun i j => raw29087 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29087step0 raw29087; decide +kernel
      have hl : raw29087step0Labels = raw29087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29087 raw29087Labels permutation434 hz
    mixedMoment B raw29087step0 raw29087step0Labels = mixedMoment B raw29087step1 raw29087step1Labels := by
      have hz : ∀ j, raw29087step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29087step1 = (fun i j => raw29087step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29087step1 raw29087step0; decide +kernel
      have hl : raw29087step1Labels = raw29087step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29087step0 raw29087step0Labels permutation80 hz
    _ = mixedMoment B node5110 node5110Labels := by rfl

def raw29088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29088step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw29088step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29088step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw29088step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29088step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw29088step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29088 raw29088Labels = mixedMoment B node4356 node4356Labels := by
  calc
    mixedMoment B raw29088 raw29088Labels = mixedMoment B raw29088step0 raw29088step0Labels := by
      have hz : ∀ j, raw29088 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29088step0 = (fun i j => raw29088 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29088step0 raw29088; decide +kernel
      have hl : raw29088step0Labels = raw29088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29088 raw29088Labels permutation434 hz
    mixedMoment B raw29088step0 raw29088step0Labels = mixedMoment B raw29088step1 raw29088step1Labels := by
      have hz : ∀ j, raw29088step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29088step1 = (fun i j => raw29088step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29088step1 raw29088step0; decide +kernel
      have hl : raw29088step1Labels = raw29088step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29088step0 raw29088step0Labels permutation80 hz
    mixedMoment B raw29088step1 raw29088step1Labels = mixedMoment B raw29088step2 raw29088step2Labels := by
      have ha : raw29088step2 = (fun i j => raw29088step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29088step2 raw29088step1; decide +kernel
      have hl : raw29088step2Labels = raw29088step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29088step1 raw29088step1Labels permutation31 permutation2
    mixedMoment B raw29088step2 raw29088step2Labels = mixedMoment B raw29088step3 raw29088step3Labels := by
      have ha : raw29088step3 = -raw29088step2 := by apply Matrix.ext; change ∀ i j, raw29088step3 i j = -(raw29088step2 i j); unfold raw29088step3 raw29088step2; decide +kernel
      have hl : raw29088step3Labels = raw29088step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4356 node4356Labels := by rfl

def raw29089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29089step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw29089step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29089step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw29089step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29089step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw29089step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29089 raw29089Labels = mixedMoment B node4360 node4360Labels := by
  calc
    mixedMoment B raw29089 raw29089Labels = mixedMoment B raw29089step0 raw29089step0Labels := by
      have hz : ∀ j, raw29089 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29089step0 = (fun i j => raw29089 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29089step0 raw29089; decide +kernel
      have hl : raw29089step0Labels = raw29089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29089 raw29089Labels permutation434 hz
    mixedMoment B raw29089step0 raw29089step0Labels = mixedMoment B raw29089step1 raw29089step1Labels := by
      have hz : ∀ j, raw29089step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29089step1 = (fun i j => raw29089step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29089step1 raw29089step0; decide +kernel
      have hl : raw29089step1Labels = raw29089step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29089step0 raw29089step0Labels permutation80 hz
    mixedMoment B raw29089step1 raw29089step1Labels = mixedMoment B raw29089step2 raw29089step2Labels := by
      have ha : raw29089step2 = (fun i j => raw29089step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29089step2 raw29089step1; decide +kernel
      have hl : raw29089step2Labels = raw29089step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29089step1 raw29089step1Labels permutation31 permutation2
    mixedMoment B raw29089step2 raw29089step2Labels = mixedMoment B raw29089step3 raw29089step3Labels := by
      have ha : raw29089step3 = -raw29089step2 := by apply Matrix.ext; change ∀ i j, raw29089step3 i j = -(raw29089step2 i j); unfold raw29089step3 raw29089step2; decide +kernel
      have hl : raw29089step3Labels = raw29089step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4360 node4360Labels := by rfl

def raw29090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29090step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29090step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29090step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29090step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29090 raw29090Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw29090 raw29090Labels = mixedMoment B raw29090step0 raw29090step0Labels := by
      have hz : ∀ j, raw29090 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29090step0 = (fun i j => raw29090 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29090step0 raw29090; decide +kernel
      have hl : raw29090step0Labels = raw29090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29090 raw29090Labels permutation434 hz
    mixedMoment B raw29090step0 raw29090step0Labels = mixedMoment B raw29090step1 raw29090step1Labels := by
      have ha : raw29090step1 = (fun i j => raw29090step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29090step1 raw29090step0; decide +kernel
      have hl : raw29090step1Labels = raw29090step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29090step0 raw29090step0Labels permutation151 permutation2
    mixedMoment B raw29090step1 raw29090step1Labels = mixedMoment B raw29090step2 raw29090step2Labels := by
      have ha : raw29090step2 = -raw29090step1 := by apply Matrix.ext; change ∀ i j, raw29090step2 i j = -(raw29090step1 i j); unfold raw29090step2 raw29090step1; decide +kernel
      have hl : raw29090step2Labels = raw29090step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4346 node4346Labels := by rfl

def raw29091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29091step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29091step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29091step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29091step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29091step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29091 raw29091Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw29091 raw29091Labels = mixedMoment B raw29091step0 raw29091step0Labels := by
      have hz : ∀ j, raw29091 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29091step0 = (fun i j => raw29091 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29091step0 raw29091; decide +kernel
      have hl : raw29091step0Labels = raw29091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29091 raw29091Labels permutation346 hz
    mixedMoment B raw29091step0 raw29091step0Labels = mixedMoment B raw29091step1 raw29091step1Labels := by
      have ha : raw29091step1 = (fun i j => raw29091step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29091step1 raw29091step0; decide +kernel
      have hl : raw29091step1Labels = raw29091step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29091step0 raw29091step0Labels permutation151 permutation2
    mixedMoment B raw29091step1 raw29091step1Labels = mixedMoment B raw29091step2 raw29091step2Labels := by
      have ha : raw29091step2 = -raw29091step1 := by apply Matrix.ext; change ∀ i j, raw29091step2 i j = -(raw29091step1 i j); unfold raw29091step2 raw29091step1; decide +kernel
      have hl : raw29091step2Labels = raw29091step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4346 node4346Labels := by rfl

def raw29092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw29092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw29092step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29092step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![4, -1, -3]]
def raw29092step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29092step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![4, -1, -3]]
def raw29092step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29092step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 0, 1], ![-3, 1, 2]]
def raw29092step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29092step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw29092step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29092 raw29092Labels = mixedMoment B node4505 node4505Labels := by
  calc
    mixedMoment B raw29092 raw29092Labels = mixedMoment B raw29092step0 raw29092step0Labels := by
      have hz : ∀ j, raw29092 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29092step0 = (fun i j => raw29092 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29092step0 raw29092; decide +kernel
      have hl : raw29092step0Labels = raw29092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29092 raw29092Labels permutation520 hz
    mixedMoment B raw29092step0 raw29092step0Labels = mixedMoment B raw29092step1 raw29092step1Labels := by
      have hz : ∀ j, raw29092step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29092step1 = (fun i j => raw29092step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29092step1 raw29092step0; decide +kernel
      have hl : raw29092step1Labels = raw29092step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29092step0 raw29092step0Labels permutation104 hz
    mixedMoment B raw29092step1 raw29092step1Labels = mixedMoment B raw29092step2 raw29092step2Labels := by
      have hz : ∀ j, raw29092step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw29092step2 = (fun i j => raw29092step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw29092step2 raw29092step1; decide +kernel
      have hl : raw29092step2Labels = raw29092step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29092step1 raw29092step1Labels permutation20 hz
    mixedMoment B raw29092step2 raw29092step2Labels = mixedMoment B raw29092step3 raw29092step3Labels := by
      have ha : raw29092step3 = (fun i j => raw29092step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29092step3 raw29092step2; decide +kernel
      have hl : raw29092step3Labels = raw29092step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29092step2 raw29092step2Labels permutation7 permutation2
    mixedMoment B raw29092step3 raw29092step3Labels = mixedMoment B raw29092step4 raw29092step4Labels := by
      have ha : raw29092step4 = -raw29092step3 := by apply Matrix.ext; change ∀ i j, raw29092step4 i j = -(raw29092step3 i j); unfold raw29092step4 raw29092step3; decide +kernel
      have hl : raw29092step4Labels = raw29092step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4505 node4505Labels := by rfl

def raw29093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29093Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29093step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29093step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw29093step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29093step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29093step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29093step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29093step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29093 raw29093Labels = mixedMoment B node2229 node2229Labels := by
  calc
    mixedMoment B raw29093 raw29093Labels = mixedMoment B raw29093step0 raw29093step0Labels := by
      have hz : ∀ j, raw29093 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29093step0 = (fun i j => raw29093 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29093step0 raw29093; decide +kernel
      have hl : raw29093step0Labels = raw29093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29093 raw29093Labels permutation434 hz
    mixedMoment B raw29093step0 raw29093step0Labels = mixedMoment B raw29093step1 raw29093step1Labels := by
      have hz : ∀ j, raw29093step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29093step1 = (fun i j => raw29093step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29093step1 raw29093step0; decide +kernel
      have hl : raw29093step1Labels = raw29093step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29093step0 raw29093step0Labels permutation80 hz
    mixedMoment B raw29093step1 raw29093step1Labels = mixedMoment B raw29093step2 raw29093step2Labels := by
      have ha : raw29093step2 = (fun i j => raw29093step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29093step2 raw29093step1; decide +kernel
      have hl : raw29093step2Labels = raw29093step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29093step1 raw29093step1Labels permutation31 permutation7
    mixedMoment B raw29093step2 raw29093step2Labels = mixedMoment B raw29093step3 raw29093step3Labels := by
      have ha : raw29093step3 = raw29093step2 := by apply Matrix.ext; unfold raw29093step3 raw29093step2; decide +kernel
      have hl : raw29093step2Labels = labelEmbedding1 ∘ raw29093step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29093step2 raw29093step2Labels raw29093step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2229 node2229Labels := by rfl

def raw29094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29094Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29094step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29094step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29094step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29094step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29094step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29094 raw29094Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw29094 raw29094Labels = mixedMoment B raw29094step0 raw29094step0Labels := by
      have hz : ∀ j, raw29094 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29094step0 = (fun i j => raw29094 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29094step0 raw29094; decide +kernel
      have hl : raw29094step0Labels = raw29094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29094 raw29094Labels permutation434 hz
    mixedMoment B raw29094step0 raw29094step0Labels = mixedMoment B raw29094step1 raw29094step1Labels := by
      have ha : raw29094step1 = (fun i j => raw29094step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29094step1 raw29094step0; decide +kernel
      have hl : raw29094step1Labels = raw29094step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29094step0 raw29094step0Labels permutation151 permutation7
    mixedMoment B raw29094step1 raw29094step1Labels = mixedMoment B raw29094step2 raw29094step2Labels := by
      have ha : raw29094step2 = raw29094step1 := by apply Matrix.ext; unfold raw29094step2 raw29094step1; decide +kernel
      have hl : raw29094step1Labels = labelEmbedding1 ∘ raw29094step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29094step1 raw29094step1Labels raw29094step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2205 node2205Labels := by rfl

def raw29095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29095Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29095step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29095step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29095step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29095step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29095step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29095 raw29095Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw29095 raw29095Labels = mixedMoment B raw29095step0 raw29095step0Labels := by
      have hz : ∀ j, raw29095 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29095step0 = (fun i j => raw29095 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29095step0 raw29095; decide +kernel
      have hl : raw29095step0Labels = raw29095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29095 raw29095Labels permutation346 hz
    mixedMoment B raw29095step0 raw29095step0Labels = mixedMoment B raw29095step1 raw29095step1Labels := by
      have ha : raw29095step1 = (fun i j => raw29095step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29095step1 raw29095step0; decide +kernel
      have hl : raw29095step1Labels = raw29095step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29095step0 raw29095step0Labels permutation151 permutation7
    mixedMoment B raw29095step1 raw29095step1Labels = mixedMoment B raw29095step2 raw29095step2Labels := by
      have ha : raw29095step2 = raw29095step1 := by apply Matrix.ext; unfold raw29095step2 raw29095step1; decide +kernel
      have hl : raw29095step1Labels = labelEmbedding1 ∘ raw29095step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29095step1 raw29095step1Labels raw29095step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2205 node2205Labels := by rfl

def raw29096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29096Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29096step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29096step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![3, 0, -3]]
def raw29096step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29096step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![3, 0, -3]]
def raw29096step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29096step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw29096step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29096step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw29096step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29096step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw29096step5Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29096 raw29096Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw29096 raw29096Labels = mixedMoment B raw29096step0 raw29096step0Labels := by
      have hz : ∀ j, raw29096 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29096step0 = (fun i j => raw29096 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29096step0 raw29096; decide +kernel
      have hl : raw29096step0Labels = raw29096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29096 raw29096Labels permutation520 hz
    mixedMoment B raw29096step0 raw29096step0Labels = mixedMoment B raw29096step1 raw29096step1Labels := by
      have hz : ∀ j, raw29096step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29096step1 = (fun i j => raw29096step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29096step1 raw29096step0; decide +kernel
      have hl : raw29096step1Labels = raw29096step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29096step0 raw29096step0Labels permutation104 hz
    mixedMoment B raw29096step1 raw29096step1Labels = mixedMoment B raw29096step2 raw29096step2Labels := by
      have hz : ∀ j, raw29096step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw29096step2 = (fun i j => raw29096step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw29096step2 raw29096step1; decide +kernel
      have hl : raw29096step2Labels = raw29096step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29096step1 raw29096step1Labels permutation20 hz
    mixedMoment B raw29096step2 raw29096step2Labels = mixedMoment B raw29096step3 raw29096step3Labels := by
      have hz : ∀ i, raw29096step2 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw29096step3 = (fun i j => raw29096step2 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw29096step3 raw29096step2; decide +kernel
      have hl : raw29096step3Labels = (fun j => raw29096step2Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw29096step2 raw29096step2Labels permutation4 hz
    mixedMoment B raw29096step3 raw29096step3Labels = mixedMoment B raw29096step4 raw29096step4Labels := by
      have ha : raw29096step4 = (fun i j => raw29096step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29096step4 raw29096step3; decide +kernel
      have hl : raw29096step4Labels = raw29096step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29096step3 raw29096step3Labels permutation7 permutation0
    mixedMoment B raw29096step4 raw29096step4Labels = mixedMoment B raw29096step5 raw29096step5Labels := by
      have ha : raw29096step5 = -raw29096step4 := by apply Matrix.ext; change ∀ i j, raw29096step5 i j = -(raw29096step4 i j); unfold raw29096step5 raw29096step4; decide +kernel
      have hl : raw29096step5Labels = raw29096step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw29097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29097Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29097step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29097step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw29097step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29097step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29097step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29097step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29097step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29097 raw29097Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw29097 raw29097Labels = mixedMoment B raw29097step0 raw29097step0Labels := by
      have hz : ∀ j, raw29097 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29097step0 = (fun i j => raw29097 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29097step0 raw29097; decide +kernel
      have hl : raw29097step0Labels = raw29097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29097 raw29097Labels permutation434 hz
    mixedMoment B raw29097step0 raw29097step0Labels = mixedMoment B raw29097step1 raw29097step1Labels := by
      have hz : ∀ j, raw29097step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29097step1 = (fun i j => raw29097step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29097step1 raw29097step0; decide +kernel
      have hl : raw29097step1Labels = raw29097step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29097step0 raw29097step0Labels permutation80 hz
    mixedMoment B raw29097step1 raw29097step1Labels = mixedMoment B raw29097step2 raw29097step2Labels := by
      have ha : raw29097step2 = (fun i j => raw29097step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29097step2 raw29097step1; decide +kernel
      have hl : raw29097step2Labels = raw29097step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29097step1 raw29097step1Labels permutation31 permutation7
    mixedMoment B raw29097step2 raw29097step2Labels = mixedMoment B raw29097step3 raw29097step3Labels := by
      have ha : raw29097step3 = raw29097step2 := by apply Matrix.ext; unfold raw29097step3 raw29097step2; decide +kernel
      have hl : raw29097step2Labels = labelEmbedding1 ∘ raw29097step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29097step2 raw29097step2Labels raw29097step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2742 node2742Labels := by rfl

def raw29098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29098Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29098step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29098step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw29098step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29098step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw29098step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29098step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw29098step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29098 raw29098Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw29098 raw29098Labels = mixedMoment B raw29098step0 raw29098step0Labels := by
      have hz : ∀ j, raw29098 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29098step0 = (fun i j => raw29098 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29098step0 raw29098; decide +kernel
      have hl : raw29098step0Labels = raw29098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29098 raw29098Labels permutation434 hz
    mixedMoment B raw29098step0 raw29098step0Labels = mixedMoment B raw29098step1 raw29098step1Labels := by
      have hz : ∀ j, raw29098step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29098step1 = (fun i j => raw29098step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29098step1 raw29098step0; decide +kernel
      have hl : raw29098step1Labels = raw29098step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29098step0 raw29098step0Labels permutation80 hz
    mixedMoment B raw29098step1 raw29098step1Labels = mixedMoment B raw29098step2 raw29098step2Labels := by
      have ha : raw29098step2 = (fun i j => raw29098step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29098step2 raw29098step1; decide +kernel
      have hl : raw29098step2Labels = raw29098step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29098step1 raw29098step1Labels permutation31 permutation7
    mixedMoment B raw29098step2 raw29098step2Labels = mixedMoment B raw29098step3 raw29098step3Labels := by
      have ha : raw29098step3 = raw29098step2 := by apply Matrix.ext; unfold raw29098step3 raw29098step2; decide +kernel
      have hl : raw29098step2Labels = labelEmbedding1 ∘ raw29098step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29098step2 raw29098step2Labels raw29098step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2226 node2226Labels := by rfl

def raw29099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29099Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29099step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw29099step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29099step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw29099step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29099 raw29099Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw29099 raw29099Labels = mixedMoment B raw29099step0 raw29099step0Labels := by
      have hz : ∀ j, raw29099 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29099step0 = (fun i j => raw29099 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29099step0 raw29099; decide +kernel
      have hl : raw29099step0Labels = raw29099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29099 raw29099Labels permutation434 hz
    mixedMoment B raw29099step0 raw29099step0Labels = mixedMoment B raw29099step1 raw29099step1Labels := by
      have ha : raw29099step1 = (fun i j => raw29099step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29099step1 raw29099step0; decide +kernel
      have hl : raw29099step1Labels = raw29099step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29099step0 raw29099step0Labels permutation151 permutation7
    mixedMoment B raw29099step1 raw29099step1Labels = mixedMoment B raw29099step2 raw29099step2Labels := by
      have ha : raw29099step2 = raw29099step1 := by apply Matrix.ext; unfold raw29099step2 raw29099step1; decide +kernel
      have hl : raw29099step1Labels = labelEmbedding1 ∘ raw29099step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29099step1 raw29099step1Labels raw29099step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

def raw29100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29100Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29100step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw29100step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29100step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw29100step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29100 raw29100Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw29100 raw29100Labels = mixedMoment B raw29100step0 raw29100step0Labels := by
      have hz : ∀ j, raw29100 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29100step0 = (fun i j => raw29100 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29100step0 raw29100; decide +kernel
      have hl : raw29100step0Labels = raw29100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29100 raw29100Labels permutation346 hz
    mixedMoment B raw29100step0 raw29100step0Labels = mixedMoment B raw29100step1 raw29100step1Labels := by
      have ha : raw29100step1 = (fun i j => raw29100step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29100step1 raw29100step0; decide +kernel
      have hl : raw29100step1Labels = raw29100step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29100step0 raw29100step0Labels permutation151 permutation7
    mixedMoment B raw29100step1 raw29100step1Labels = mixedMoment B raw29100step2 raw29100step2Labels := by
      have ha : raw29100step2 = raw29100step1 := by apply Matrix.ext; unfold raw29100step2 raw29100step1; decide +kernel
      have hl : raw29100step1Labels = labelEmbedding1 ∘ raw29100step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29100step1 raw29100step1Labels raw29100step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

def raw29101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29101Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29101step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29101step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw29101step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29101step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![3, 0, -3]]
def raw29101step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29101step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw29101step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29101step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw29101step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29101 raw29101Labels = mixedMoment B node2292 node2292Labels := by
  calc
    mixedMoment B raw29101 raw29101Labels = mixedMoment B raw29101step0 raw29101step0Labels := by
      have hz : ∀ j, raw29101 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29101step0 = (fun i j => raw29101 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29101step0 raw29101; decide +kernel
      have hl : raw29101step0Labels = raw29101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29101 raw29101Labels permutation520 hz
    mixedMoment B raw29101step0 raw29101step0Labels = mixedMoment B raw29101step1 raw29101step1Labels := by
      have hz : ∀ j, raw29101step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29101step1 = (fun i j => raw29101step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29101step1 raw29101step0; decide +kernel
      have hl : raw29101step1Labels = raw29101step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29101step0 raw29101step0Labels permutation104 hz
    mixedMoment B raw29101step1 raw29101step1Labels = mixedMoment B raw29101step2 raw29101step2Labels := by
      have hz : ∀ j, raw29101step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw29101step2 = (fun i j => raw29101step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw29101step2 raw29101step1; decide +kernel
      have hl : raw29101step2Labels = raw29101step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29101step1 raw29101step1Labels permutation20 hz
    mixedMoment B raw29101step2 raw29101step2Labels = mixedMoment B raw29101step3 raw29101step3Labels := by
      have ha : raw29101step3 = (fun i j => raw29101step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29101step3 raw29101step2; decide +kernel
      have hl : raw29101step3Labels = raw29101step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29101step2 raw29101step2Labels permutation7 permutation7
    mixedMoment B raw29101step3 raw29101step3Labels = mixedMoment B raw29101step4 raw29101step4Labels := by
      have ha : raw29101step4 = raw29101step3 := by apply Matrix.ext; unfold raw29101step4 raw29101step3; decide +kernel
      have hl : raw29101step3Labels = labelEmbedding1 ∘ raw29101step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29101step3 raw29101step3Labels raw29101step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2292 node2292Labels := by rfl

def raw29102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29102Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29102step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29102step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw29102step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29102step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw29102step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29102step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw29102step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29102 raw29102Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw29102 raw29102Labels = mixedMoment B raw29102step0 raw29102step0Labels := by
      have hz : ∀ j, raw29102 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29102step0 = (fun i j => raw29102 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29102step0 raw29102; decide +kernel
      have hl : raw29102step0Labels = raw29102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29102 raw29102Labels permutation434 hz
    mixedMoment B raw29102step0 raw29102step0Labels = mixedMoment B raw29102step1 raw29102step1Labels := by
      have hz : ∀ j, raw29102step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29102step1 = (fun i j => raw29102step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29102step1 raw29102step0; decide +kernel
      have hl : raw29102step1Labels = raw29102step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29102step0 raw29102step0Labels permutation80 hz
    mixedMoment B raw29102step1 raw29102step1Labels = mixedMoment B raw29102step2 raw29102step2Labels := by
      have ha : raw29102step2 = (fun i j => raw29102step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29102step2 raw29102step1; decide +kernel
      have hl : raw29102step2Labels = raw29102step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29102step1 raw29102step1Labels permutation31 permutation7
    mixedMoment B raw29102step2 raw29102step2Labels = mixedMoment B raw29102step3 raw29102step3Labels := by
      have ha : raw29102step3 = raw29102step2 := by apply Matrix.ext; unfold raw29102step3 raw29102step2; decide +kernel
      have hl : raw29102step2Labels = labelEmbedding1 ∘ raw29102step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29102step2 raw29102step2Labels raw29102step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

def raw29103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29103Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29103step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw29103step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29103step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw29103step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29103 raw29103Labels = mixedMoment B node2184 node2184Labels := by
  calc
    mixedMoment B raw29103 raw29103Labels = mixedMoment B raw29103step0 raw29103step0Labels := by
      have hz : ∀ j, raw29103 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29103step0 = (fun i j => raw29103 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29103step0 raw29103; decide +kernel
      have hl : raw29103step0Labels = raw29103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29103 raw29103Labels permutation434 hz
    mixedMoment B raw29103step0 raw29103step0Labels = mixedMoment B raw29103step1 raw29103step1Labels := by
      have ha : raw29103step1 = (fun i j => raw29103step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29103step1 raw29103step0; decide +kernel
      have hl : raw29103step1Labels = raw29103step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29103step0 raw29103step0Labels permutation145 permutation7
    mixedMoment B raw29103step1 raw29103step1Labels = mixedMoment B raw29103step2 raw29103step2Labels := by
      have ha : raw29103step2 = raw29103step1 := by apply Matrix.ext; unfold raw29103step2 raw29103step1; decide +kernel
      have hl : raw29103step1Labels = labelEmbedding1 ∘ raw29103step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29103step1 raw29103step1Labels raw29103step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2184 node2184Labels := by rfl

def raw29104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29104Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29104step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29104step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw29104step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29104step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw29104step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29104 raw29104Labels = mixedMoment B node2185 node2185Labels := by
  calc
    mixedMoment B raw29104 raw29104Labels = mixedMoment B raw29104step0 raw29104step0Labels := by
      have hz : ∀ j, raw29104 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29104step0 = (fun i j => raw29104 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29104step0 raw29104; decide +kernel
      have hl : raw29104step0Labels = raw29104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29104 raw29104Labels permutation434 hz
    mixedMoment B raw29104step0 raw29104step0Labels = mixedMoment B raw29104step1 raw29104step1Labels := by
      have ha : raw29104step1 = (fun i j => raw29104step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29104step1 raw29104step0; decide +kernel
      have hl : raw29104step1Labels = raw29104step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29104step0 raw29104step0Labels permutation145 permutation7
    mixedMoment B raw29104step1 raw29104step1Labels = mixedMoment B raw29104step2 raw29104step2Labels := by
      have ha : raw29104step2 = raw29104step1 := by apply Matrix.ext; unfold raw29104step2 raw29104step1; decide +kernel
      have hl : raw29104step1Labels = labelEmbedding1 ∘ raw29104step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29104step1 raw29104step1Labels raw29104step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2185 node2185Labels := by rfl

def raw29105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29105Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29105step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29105step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29105step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29105step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29105 raw29105Labels = mixedMoment B node2173 node2173Labels := by
  calc
    mixedMoment B raw29105 raw29105Labels = mixedMoment B raw29105step0 raw29105step0Labels := by
      have ha : raw29105step0 = (fun i j => raw29105 (permutation646 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29105step0 raw29105; decide +kernel
      have hl : raw29105step0Labels = raw29105Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29105 raw29105Labels permutation646 permutation7
    mixedMoment B raw29105step0 raw29105step0Labels = mixedMoment B raw29105step1 raw29105step1Labels := by
      have ha : raw29105step1 = raw29105step0 := by apply Matrix.ext; unfold raw29105step1 raw29105step0; decide +kernel
      have hl : raw29105step0Labels = labelEmbedding1 ∘ raw29105step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29105step0 raw29105step0Labels raw29105step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2173 node2173Labels := by rfl

def raw29106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29106Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29106step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29106step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw29106step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29106step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29106step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29106step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29106step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29106 raw29106Labels = mixedMoment B node2228 node2228Labels := by
  calc
    mixedMoment B raw29106 raw29106Labels = mixedMoment B raw29106step0 raw29106step0Labels := by
      have hz : ∀ j, raw29106 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29106step0 = (fun i j => raw29106 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29106step0 raw29106; decide +kernel
      have hl : raw29106step0Labels = raw29106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29106 raw29106Labels permutation520 hz
    mixedMoment B raw29106step0 raw29106step0Labels = mixedMoment B raw29106step1 raw29106step1Labels := by
      have hz : ∀ j, raw29106step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29106step1 = (fun i j => raw29106step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29106step1 raw29106step0; decide +kernel
      have hl : raw29106step1Labels = raw29106step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29106step0 raw29106step0Labels permutation104 hz
    mixedMoment B raw29106step1 raw29106step1Labels = mixedMoment B raw29106step2 raw29106step2Labels := by
      have ha : raw29106step2 = (fun i j => raw29106step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29106step2 raw29106step1; decide +kernel
      have hl : raw29106step2Labels = raw29106step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29106step1 raw29106step1Labels permutation31 permutation7
    mixedMoment B raw29106step2 raw29106step2Labels = mixedMoment B raw29106step3 raw29106step3Labels := by
      have ha : raw29106step3 = raw29106step2 := by apply Matrix.ext; unfold raw29106step3 raw29106step2; decide +kernel
      have hl : raw29106step2Labels = labelEmbedding1 ∘ raw29106step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29106step2 raw29106step2Labels raw29106step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2228 node2228Labels := by rfl

def raw29107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29107Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29107step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29107step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29107step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29107step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29107 raw29107Labels = mixedMoment B node2704 node2704Labels := by
  calc
    mixedMoment B raw29107 raw29107Labels = mixedMoment B raw29107step0 raw29107step0Labels := by
      have hz : ∀ j, raw29107 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29107step0 = (fun i j => raw29107 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29107step0 raw29107; decide +kernel
      have hl : raw29107step0Labels = raw29107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29107 raw29107Labels permutation434 hz
    mixedMoment B raw29107step0 raw29107step0Labels = mixedMoment B raw29107step1 raw29107step1Labels := by
      have ha : raw29107step1 = (fun i j => raw29107step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29107step1 raw29107step0; decide +kernel
      have hl : raw29107step1Labels = raw29107step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29107step0 raw29107step0Labels permutation145 permutation7
    mixedMoment B raw29107step1 raw29107step1Labels = mixedMoment B raw29107step2 raw29107step2Labels := by
      have ha : raw29107step2 = raw29107step1 := by apply Matrix.ext; unfold raw29107step2 raw29107step1; decide +kernel
      have hl : raw29107step1Labels = labelEmbedding1 ∘ raw29107step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29107step1 raw29107step1Labels raw29107step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2704 node2704Labels := by rfl

def raw29108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29108Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29108step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw29108step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29108step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw29108step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29108 raw29108Labels = mixedMoment B node2184 node2184Labels := by
  calc
    mixedMoment B raw29108 raw29108Labels = mixedMoment B raw29108step0 raw29108step0Labels := by
      have hz : ∀ j, raw29108 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29108step0 = (fun i j => raw29108 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29108step0 raw29108; decide +kernel
      have hl : raw29108step0Labels = raw29108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29108 raw29108Labels permutation346 hz
    mixedMoment B raw29108step0 raw29108step0Labels = mixedMoment B raw29108step1 raw29108step1Labels := by
      have ha : raw29108step1 = (fun i j => raw29108step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29108step1 raw29108step0; decide +kernel
      have hl : raw29108step1Labels = raw29108step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29108step0 raw29108step0Labels permutation145 permutation7
    mixedMoment B raw29108step1 raw29108step1Labels = mixedMoment B raw29108step2 raw29108step2Labels := by
      have ha : raw29108step2 = raw29108step1 := by apply Matrix.ext; unfold raw29108step2 raw29108step1; decide +kernel
      have hl : raw29108step1Labels = labelEmbedding1 ∘ raw29108step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29108step1 raw29108step1Labels raw29108step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2184 node2184Labels := by rfl

def raw29109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29109Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29109step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw29109step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29109step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw29109step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29109 raw29109Labels = mixedMoment B node2185 node2185Labels := by
  calc
    mixedMoment B raw29109 raw29109Labels = mixedMoment B raw29109step0 raw29109step0Labels := by
      have hz : ∀ j, raw29109 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29109step0 = (fun i j => raw29109 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29109step0 raw29109; decide +kernel
      have hl : raw29109step0Labels = raw29109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29109 raw29109Labels permutation346 hz
    mixedMoment B raw29109step0 raw29109step0Labels = mixedMoment B raw29109step1 raw29109step1Labels := by
      have ha : raw29109step1 = (fun i j => raw29109step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29109step1 raw29109step0; decide +kernel
      have hl : raw29109step1Labels = raw29109step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29109step0 raw29109step0Labels permutation145 permutation7
    mixedMoment B raw29109step1 raw29109step1Labels = mixedMoment B raw29109step2 raw29109step2Labels := by
      have ha : raw29109step2 = raw29109step1 := by apply Matrix.ext; unfold raw29109step2 raw29109step1; decide +kernel
      have hl : raw29109step1Labels = labelEmbedding1 ∘ raw29109step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29109step1 raw29109step1Labels raw29109step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2185 node2185Labels := by rfl

def raw29110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29110Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29110step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29110step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29110step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29110step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29110 raw29110Labels = mixedMoment B node2173 node2173Labels := by
  calc
    mixedMoment B raw29110 raw29110Labels = mixedMoment B raw29110step0 raw29110step0Labels := by
      have ha : raw29110step0 = (fun i j => raw29110 (permutation664 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29110step0 raw29110; decide +kernel
      have hl : raw29110step0Labels = raw29110Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29110 raw29110Labels permutation664 permutation7
    mixedMoment B raw29110step0 raw29110step0Labels = mixedMoment B raw29110step1 raw29110step1Labels := by
      have ha : raw29110step1 = raw29110step0 := by apply Matrix.ext; unfold raw29110step1 raw29110step0; decide +kernel
      have hl : raw29110step0Labels = labelEmbedding1 ∘ raw29110step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29110step0 raw29110step0Labels raw29110step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2173 node2173Labels := by rfl

def raw29111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29111Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29111step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29111step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw29111step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29111step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29111step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29111step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29111step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29111 raw29111Labels = mixedMoment B node2228 node2228Labels := by
  calc
    mixedMoment B raw29111 raw29111Labels = mixedMoment B raw29111step0 raw29111step0Labels := by
      have hz : ∀ j, raw29111 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29111step0 = (fun i j => raw29111 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29111step0 raw29111; decide +kernel
      have hl : raw29111step0Labels = raw29111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29111 raw29111Labels permutation520 hz
    mixedMoment B raw29111step0 raw29111step0Labels = mixedMoment B raw29111step1 raw29111step1Labels := by
      have hz : ∀ j, raw29111step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29111step1 = (fun i j => raw29111step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29111step1 raw29111step0; decide +kernel
      have hl : raw29111step1Labels = raw29111step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29111step0 raw29111step0Labels permutation80 hz
    mixedMoment B raw29111step1 raw29111step1Labels = mixedMoment B raw29111step2 raw29111step2Labels := by
      have ha : raw29111step2 = (fun i j => raw29111step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29111step2 raw29111step1; decide +kernel
      have hl : raw29111step2Labels = raw29111step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29111step1 raw29111step1Labels permutation31 permutation7
    mixedMoment B raw29111step2 raw29111step2Labels = mixedMoment B raw29111step3 raw29111step3Labels := by
      have ha : raw29111step3 = raw29111step2 := by apply Matrix.ext; unfold raw29111step3 raw29111step2; decide +kernel
      have hl : raw29111step2Labels = labelEmbedding1 ∘ raw29111step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29111step2 raw29111step2Labels raw29111step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2228 node2228Labels := by rfl

def raw29112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29112Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29112step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29112step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29112step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29112step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29112 raw29112Labels = mixedMoment B node2704 node2704Labels := by
  calc
    mixedMoment B raw29112 raw29112Labels = mixedMoment B raw29112step0 raw29112step0Labels := by
      have hz : ∀ j, raw29112 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29112step0 = (fun i j => raw29112 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29112step0 raw29112; decide +kernel
      have hl : raw29112step0Labels = raw29112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29112 raw29112Labels permutation346 hz
    mixedMoment B raw29112step0 raw29112step0Labels = mixedMoment B raw29112step1 raw29112step1Labels := by
      have ha : raw29112step1 = (fun i j => raw29112step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29112step1 raw29112step0; decide +kernel
      have hl : raw29112step1Labels = raw29112step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29112step0 raw29112step0Labels permutation145 permutation7
    mixedMoment B raw29112step1 raw29112step1Labels = mixedMoment B raw29112step2 raw29112step2Labels := by
      have ha : raw29112step2 = raw29112step1 := by apply Matrix.ext; unfold raw29112step2 raw29112step1; decide +kernel
      have hl : raw29112step1Labels = labelEmbedding1 ∘ raw29112step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29112step1 raw29112step1Labels raw29112step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2704 node2704Labels := by rfl

def raw29113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29113Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29113step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29113step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw29113step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29113step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![2, 2, -4]]
def raw29113step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29113step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![2, 2, -4]]
def raw29113step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29113 raw29113Labels = mixedMoment B node2167 node2167Labels := by
  calc
    mixedMoment B raw29113 raw29113Labels = mixedMoment B raw29113step0 raw29113step0Labels := by
      have hz : ∀ j, raw29113 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29113step0 = (fun i j => raw29113 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29113step0 raw29113; decide +kernel
      have hl : raw29113step0Labels = raw29113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29113 raw29113Labels permutation434 hz
    mixedMoment B raw29113step0 raw29113step0Labels = mixedMoment B raw29113step1 raw29113step1Labels := by
      have hz : ∀ j, raw29113step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29113step1 = (fun i j => raw29113step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29113step1 raw29113step0; decide +kernel
      have hl : raw29113step1Labels = raw29113step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29113step0 raw29113step0Labels permutation80 hz
    mixedMoment B raw29113step1 raw29113step1Labels = mixedMoment B raw29113step2 raw29113step2Labels := by
      have ha : raw29113step2 = (fun i j => raw29113step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29113step2 raw29113step1; decide +kernel
      have hl : raw29113step2Labels = raw29113step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29113step1 raw29113step1Labels permutation31 permutation7
    mixedMoment B raw29113step2 raw29113step2Labels = mixedMoment B raw29113step3 raw29113step3Labels := by
      have ha : raw29113step3 = raw29113step2 := by apply Matrix.ext; unfold raw29113step3 raw29113step2; decide +kernel
      have hl : raw29113step2Labels = labelEmbedding1 ∘ raw29113step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29113step2 raw29113step2Labels raw29113step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2167 node2167Labels := by rfl

def raw29114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29114Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29114step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29114step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw29114step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29114step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]
def raw29114step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29114step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]
def raw29114step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29114 raw29114Labels = mixedMoment B node2168 node2168Labels := by
  calc
    mixedMoment B raw29114 raw29114Labels = mixedMoment B raw29114step0 raw29114step0Labels := by
      have hz : ∀ j, raw29114 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29114step0 = (fun i j => raw29114 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29114step0 raw29114; decide +kernel
      have hl : raw29114step0Labels = raw29114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29114 raw29114Labels permutation434 hz
    mixedMoment B raw29114step0 raw29114step0Labels = mixedMoment B raw29114step1 raw29114step1Labels := by
      have hz : ∀ j, raw29114step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29114step1 = (fun i j => raw29114step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29114step1 raw29114step0; decide +kernel
      have hl : raw29114step1Labels = raw29114step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29114step0 raw29114step0Labels permutation80 hz
    mixedMoment B raw29114step1 raw29114step1Labels = mixedMoment B raw29114step2 raw29114step2Labels := by
      have ha : raw29114step2 = (fun i j => raw29114step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29114step2 raw29114step1; decide +kernel
      have hl : raw29114step2Labels = raw29114step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29114step1 raw29114step1Labels permutation31 permutation7
    mixedMoment B raw29114step2 raw29114step2Labels = mixedMoment B raw29114step3 raw29114step3Labels := by
      have ha : raw29114step3 = raw29114step2 := by apply Matrix.ext; unfold raw29114step3 raw29114step2; decide +kernel
      have hl : raw29114step2Labels = labelEmbedding1 ∘ raw29114step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29114step2 raw29114step2Labels raw29114step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2168 node2168Labels := by rfl

def raw29115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29115Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29115step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29115step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29115step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29115step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29115 raw29115Labels = mixedMoment B node2151 node2151Labels := by
  calc
    mixedMoment B raw29115 raw29115Labels = mixedMoment B raw29115step0 raw29115step0Labels := by
      have hz : ∀ j, raw29115 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29115step0 = (fun i j => raw29115 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29115step0 raw29115; decide +kernel
      have hl : raw29115step0Labels = raw29115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29115 raw29115Labels permutation434 hz
    mixedMoment B raw29115step0 raw29115step0Labels = mixedMoment B raw29115step1 raw29115step1Labels := by
      have ha : raw29115step1 = (fun i j => raw29115step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29115step1 raw29115step0; decide +kernel
      have hl : raw29115step1Labels = raw29115step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29115step0 raw29115step0Labels permutation151 permutation7
    mixedMoment B raw29115step1 raw29115step1Labels = mixedMoment B raw29115step2 raw29115step2Labels := by
      have ha : raw29115step2 = raw29115step1 := by apply Matrix.ext; unfold raw29115step2 raw29115step1; decide +kernel
      have hl : raw29115step1Labels = labelEmbedding1 ∘ raw29115step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29115step1 raw29115step1Labels raw29115step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2151 node2151Labels := by rfl

def raw29116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29116Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29116step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29116step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29116step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29116step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29116 raw29116Labels = mixedMoment B node2151 node2151Labels := by
  calc
    mixedMoment B raw29116 raw29116Labels = mixedMoment B raw29116step0 raw29116step0Labels := by
      have hz : ∀ j, raw29116 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29116step0 = (fun i j => raw29116 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29116step0 raw29116; decide +kernel
      have hl : raw29116step0Labels = raw29116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29116 raw29116Labels permutation346 hz
    mixedMoment B raw29116step0 raw29116step0Labels = mixedMoment B raw29116step1 raw29116step1Labels := by
      have ha : raw29116step1 = (fun i j => raw29116step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29116step1 raw29116step0; decide +kernel
      have hl : raw29116step1Labels = raw29116step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29116step0 raw29116step0Labels permutation151 permutation7
    mixedMoment B raw29116step1 raw29116step1Labels = mixedMoment B raw29116step2 raw29116step2Labels := by
      have ha : raw29116step2 = raw29116step1 := by apply Matrix.ext; unfold raw29116step2 raw29116step1; decide +kernel
      have hl : raw29116step1Labels = labelEmbedding1 ∘ raw29116step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29116step1 raw29116step1Labels raw29116step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2151 node2151Labels := by rfl

def raw29117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29117Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29117step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29117step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29117step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29117step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw29117step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29117step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw29117step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29117 raw29117Labels = mixedMoment B node2685 node2685Labels := by
  calc
    mixedMoment B raw29117 raw29117Labels = mixedMoment B raw29117step0 raw29117step0Labels := by
      have hz : ∀ j, raw29117 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29117step0 = (fun i j => raw29117 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29117step0 raw29117; decide +kernel
      have hl : raw29117step0Labels = raw29117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29117 raw29117Labels permutation434 hz
    mixedMoment B raw29117step0 raw29117step0Labels = mixedMoment B raw29117step1 raw29117step1Labels := by
      have hz : ∀ j, raw29117step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29117step1 = (fun i j => raw29117step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29117step1 raw29117step0; decide +kernel
      have hl : raw29117step1Labels = raw29117step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29117step0 raw29117step0Labels permutation80 hz
    mixedMoment B raw29117step1 raw29117step1Labels = mixedMoment B raw29117step2 raw29117step2Labels := by
      have ha : raw29117step2 = (fun i j => raw29117step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29117step2 raw29117step1; decide +kernel
      have hl : raw29117step2Labels = raw29117step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29117step1 raw29117step1Labels permutation31 permutation7
    mixedMoment B raw29117step2 raw29117step2Labels = mixedMoment B raw29117step3 raw29117step3Labels := by
      have ha : raw29117step3 = raw29117step2 := by apply Matrix.ext; unfold raw29117step3 raw29117step2; decide +kernel
      have hl : raw29117step2Labels = labelEmbedding1 ∘ raw29117step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29117step2 raw29117step2Labels raw29117step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2685 node2685Labels := by rfl

def raw29118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29118Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29118step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29118step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw29118step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29118step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw29118step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29118step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw29118step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29118 raw29118Labels = mixedMoment B node1692 node1692Labels := by
  calc
    mixedMoment B raw29118 raw29118Labels = mixedMoment B raw29118step0 raw29118step0Labels := by
      have hz : ∀ j, raw29118 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29118step0 = (fun i j => raw29118 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29118step0 raw29118; decide +kernel
      have hl : raw29118step0Labels = raw29118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29118 raw29118Labels permutation434 hz
    mixedMoment B raw29118step0 raw29118step0Labels = mixedMoment B raw29118step1 raw29118step1Labels := by
      have hz : ∀ j, raw29118step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29118step1 = (fun i j => raw29118step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29118step1 raw29118step0; decide +kernel
      have hl : raw29118step1Labels = raw29118step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29118step0 raw29118step0Labels permutation80 hz
    mixedMoment B raw29118step1 raw29118step1Labels = mixedMoment B raw29118step2 raw29118step2Labels := by
      have ha : raw29118step2 = (fun i j => raw29118step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29118step2 raw29118step1; decide +kernel
      have hl : raw29118step2Labels = raw29118step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29118step1 raw29118step1Labels permutation31 permutation7
    mixedMoment B raw29118step2 raw29118step2Labels = mixedMoment B raw29118step3 raw29118step3Labels := by
      have ha : raw29118step3 = raw29118step2 := by apply Matrix.ext; unfold raw29118step3 raw29118step2; decide +kernel
      have hl : raw29118step2Labels = labelEmbedding1 ∘ raw29118step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29118step2 raw29118step2Labels raw29118step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1692 node1692Labels := by rfl

def raw29119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29119Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29119step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29119step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw29119step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29119step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw29119step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29119step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw29119step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29119 raw29119Labels = mixedMoment B node1693 node1693Labels := by
  calc
    mixedMoment B raw29119 raw29119Labels = mixedMoment B raw29119step0 raw29119step0Labels := by
      have hz : ∀ j, raw29119 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29119step0 = (fun i j => raw29119 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29119step0 raw29119; decide +kernel
      have hl : raw29119step0Labels = raw29119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29119 raw29119Labels permutation434 hz
    mixedMoment B raw29119step0 raw29119step0Labels = mixedMoment B raw29119step1 raw29119step1Labels := by
      have hz : ∀ j, raw29119step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29119step1 = (fun i j => raw29119step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29119step1 raw29119step0; decide +kernel
      have hl : raw29119step1Labels = raw29119step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29119step0 raw29119step0Labels permutation80 hz
    mixedMoment B raw29119step1 raw29119step1Labels = mixedMoment B raw29119step2 raw29119step2Labels := by
      have ha : raw29119step2 = (fun i j => raw29119step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29119step2 raw29119step1; decide +kernel
      have hl : raw29119step2Labels = raw29119step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29119step1 raw29119step1Labels permutation31 permutation7
    mixedMoment B raw29119step2 raw29119step2Labels = mixedMoment B raw29119step3 raw29119step3Labels := by
      have ha : raw29119step3 = raw29119step2 := by apply Matrix.ext; unfold raw29119step3 raw29119step2; decide +kernel
      have hl : raw29119step2Labels = labelEmbedding1 ∘ raw29119step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29119step2 raw29119step2Labels raw29119step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1693 node1693Labels := by rfl

def raw29120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29120Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29120step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29120step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29120step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29120step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29120step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29120 raw29120Labels = mixedMoment B node1674 node1674Labels := by
  calc
    mixedMoment B raw29120 raw29120Labels = mixedMoment B raw29120step0 raw29120step0Labels := by
      have hz : ∀ j, raw29120 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29120step0 = (fun i j => raw29120 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29120step0 raw29120; decide +kernel
      have hl : raw29120step0Labels = raw29120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29120 raw29120Labels permutation434 hz
    mixedMoment B raw29120step0 raw29120step0Labels = mixedMoment B raw29120step1 raw29120step1Labels := by
      have ha : raw29120step1 = (fun i j => raw29120step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29120step1 raw29120step0; decide +kernel
      have hl : raw29120step1Labels = raw29120step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29120step0 raw29120step0Labels permutation151 permutation7
    mixedMoment B raw29120step1 raw29120step1Labels = mixedMoment B raw29120step2 raw29120step2Labels := by
      have ha : raw29120step2 = raw29120step1 := by apply Matrix.ext; unfold raw29120step2 raw29120step1; decide +kernel
      have hl : raw29120step1Labels = labelEmbedding1 ∘ raw29120step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29120step1 raw29120step1Labels raw29120step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1674 node1674Labels := by rfl

def raw29121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29121Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29121step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29121step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29121step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw29121step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29121 raw29121Labels = mixedMoment B node1674 node1674Labels := by
  calc
    mixedMoment B raw29121 raw29121Labels = mixedMoment B raw29121step0 raw29121step0Labels := by
      have hz : ∀ j, raw29121 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29121step0 = (fun i j => raw29121 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29121step0 raw29121; decide +kernel
      have hl : raw29121step0Labels = raw29121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29121 raw29121Labels permutation346 hz
    mixedMoment B raw29121step0 raw29121step0Labels = mixedMoment B raw29121step1 raw29121step1Labels := by
      have ha : raw29121step1 = (fun i j => raw29121step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29121step1 raw29121step0; decide +kernel
      have hl : raw29121step1Labels = raw29121step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29121step0 raw29121step0Labels permutation151 permutation7
    mixedMoment B raw29121step1 raw29121step1Labels = mixedMoment B raw29121step2 raw29121step2Labels := by
      have ha : raw29121step2 = raw29121step1 := by apply Matrix.ext; unfold raw29121step2 raw29121step1; decide +kernel
      have hl : raw29121step1Labels = labelEmbedding1 ∘ raw29121step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29121step1 raw29121step1Labels raw29121step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1674 node1674Labels := by rfl

def raw29122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw29122Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw29122step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29122step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![4, -1, -3]]
def raw29122step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29122step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![4, -1, -3]]
def raw29122step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29122step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![2, 1, -3]]
def raw29122step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29122step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![2, 1, -3]]
def raw29122step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29122 raw29122Labels = mixedMoment B node1754 node1754Labels := by
  calc
    mixedMoment B raw29122 raw29122Labels = mixedMoment B raw29122step0 raw29122step0Labels := by
      have hz : ∀ j, raw29122 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29122step0 = (fun i j => raw29122 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29122step0 raw29122; decide +kernel
      have hl : raw29122step0Labels = raw29122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29122 raw29122Labels permutation520 hz
    mixedMoment B raw29122step0 raw29122step0Labels = mixedMoment B raw29122step1 raw29122step1Labels := by
      have hz : ∀ j, raw29122step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29122step1 = (fun i j => raw29122step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29122step1 raw29122step0; decide +kernel
      have hl : raw29122step1Labels = raw29122step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29122step0 raw29122step0Labels permutation104 hz
    mixedMoment B raw29122step1 raw29122step1Labels = mixedMoment B raw29122step2 raw29122step2Labels := by
      have hz : ∀ j, raw29122step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw29122step2 = (fun i j => raw29122step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw29122step2 raw29122step1; decide +kernel
      have hl : raw29122step2Labels = raw29122step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29122step1 raw29122step1Labels permutation20 hz
    mixedMoment B raw29122step2 raw29122step2Labels = mixedMoment B raw29122step3 raw29122step3Labels := by
      have ha : raw29122step3 = (fun i j => raw29122step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29122step3 raw29122step2; decide +kernel
      have hl : raw29122step3Labels = raw29122step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29122step2 raw29122step2Labels permutation7 permutation7
    mixedMoment B raw29122step3 raw29122step3Labels = mixedMoment B raw29122step4 raw29122step4Labels := by
      have ha : raw29122step4 = raw29122step3 := by apply Matrix.ext; unfold raw29122step4 raw29122step3; decide +kernel
      have hl : raw29122step3Labels = labelEmbedding1 ∘ raw29122step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29122step3 raw29122step3Labels raw29122step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1754 node1754Labels := by rfl

def raw29123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29123Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29123step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29123step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29123step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29123step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29123 raw29123Labels = mixedMoment B node2385 node2385Labels := by
  calc
    mixedMoment B raw29123 raw29123Labels = mixedMoment B raw29123step0 raw29123step0Labels := by
      have hz : ∀ j, raw29123 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29123step0 = (fun i j => raw29123 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29123step0 raw29123; decide +kernel
      have hl : raw29123step0Labels = raw29123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29123 raw29123Labels permutation346 hz
    mixedMoment B raw29123step0 raw29123step0Labels = mixedMoment B raw29123step1 raw29123step1Labels := by
      have ha : raw29123step1 = (fun i j => raw29123step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29123step1 raw29123step0; decide +kernel
      have hl : raw29123step1Labels = raw29123step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29123step0 raw29123step0Labels permutation151 permutation2
    mixedMoment B raw29123step1 raw29123step1Labels = mixedMoment B raw29123step2 raw29123step2Labels := by
      have ha : raw29123step2 = -raw29123step1 := by apply Matrix.ext; change ∀ i j, raw29123step2 i j = -(raw29123step1 i j); unfold raw29123step2 raw29123step1; decide +kernel
      have hl : raw29123step2Labels = raw29123step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2385 node2385Labels := by rfl

def raw29124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29124Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29124step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw29124step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29124step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw29124step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29124 raw29124Labels = mixedMoment B node2388 node2388Labels := by
  calc
    mixedMoment B raw29124 raw29124Labels = mixedMoment B raw29124step0 raw29124step0Labels := by
      have hz : ∀ j, raw29124 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29124step0 = (fun i j => raw29124 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29124step0 raw29124; decide +kernel
      have hl : raw29124step0Labels = raw29124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29124 raw29124Labels permutation346 hz
    mixedMoment B raw29124step0 raw29124step0Labels = mixedMoment B raw29124step1 raw29124step1Labels := by
      have ha : raw29124step1 = (fun i j => raw29124step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29124step1 raw29124step0; decide +kernel
      have hl : raw29124step1Labels = raw29124step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29124step0 raw29124step0Labels permutation151 permutation2
    mixedMoment B raw29124step1 raw29124step1Labels = mixedMoment B raw29124step2 raw29124step2Labels := by
      have ha : raw29124step2 = -raw29124step1 := by apply Matrix.ext; change ∀ i j, raw29124step2 i j = -(raw29124step1 i j); unfold raw29124step2 raw29124step1; decide +kernel
      have hl : raw29124step2Labels = raw29124step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2388 node2388Labels := by rfl

def raw29125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29125Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw29125step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29125step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29125step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29125 raw29125Labels = mixedMoment B node2382 node2382Labels := by
  calc
    mixedMoment B raw29125 raw29125Labels = mixedMoment B raw29125step0 raw29125step0Labels := by
      have ha : raw29125step0 = (fun i j => raw29125 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29125step0 raw29125; decide +kernel
      have hl : raw29125step0Labels = raw29125Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29125 raw29125Labels permutation688 permutation2
    mixedMoment B raw29125step0 raw29125step0Labels = mixedMoment B raw29125step1 raw29125step1Labels := by
      have ha : raw29125step1 = -raw29125step0 := by apply Matrix.ext; change ∀ i j, raw29125step1 i j = -(raw29125step0 i j); unfold raw29125step1 raw29125step0; decide +kernel
      have hl : raw29125step1Labels = raw29125step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2382 node2382Labels := by rfl

def raw29126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29126Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29126step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw29126step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29126step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29126step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29126 raw29126Labels = mixedMoment B node2403 node2403Labels := by
  calc
    mixedMoment B raw29126 raw29126Labels = mixedMoment B raw29126step0 raw29126step0Labels := by
      have hz : ∀ j, raw29126 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29126step0 = (fun i j => raw29126 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29126step0 raw29126; decide +kernel
      have hl : raw29126step0Labels = raw29126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29126 raw29126Labels permutation346 hz
    mixedMoment B raw29126step0 raw29126step0Labels = mixedMoment B raw29126step1 raw29126step1Labels := by
      have ha : raw29126step1 = (fun i j => raw29126step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29126step1 raw29126step0; decide +kernel
      have hl : raw29126step1Labels = raw29126step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29126step0 raw29126step0Labels permutation149 permutation2
    mixedMoment B raw29126step1 raw29126step1Labels = mixedMoment B raw29126step2 raw29126step2Labels := by
      have ha : raw29126step2 = -raw29126step1 := by apply Matrix.ext; change ∀ i j, raw29126step2 i j = -(raw29126step1 i j); unfold raw29126step2 raw29126step1; decide +kernel
      have hl : raw29126step2Labels = raw29126step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2403 node2403Labels := by rfl

def raw29127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw29127Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw29127step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw29127step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29127step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29127step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29127 raw29127Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw29127 raw29127Labels = mixedMoment B raw29127step0 raw29127step0Labels := by
      have hz : ∀ j, raw29127 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29127step0 = (fun i j => raw29127 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29127step0 raw29127; decide +kernel
      have hl : raw29127step0Labels = raw29127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29127 raw29127Labels permutation346 hz
    mixedMoment B raw29127step0 raw29127step0Labels = mixedMoment B raw29127step1 raw29127step1Labels := by
      have ha : raw29127step1 = (fun i j => raw29127step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29127step1 raw29127step0; decide +kernel
      have hl : raw29127step1Labels = raw29127step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29127step0 raw29127step0Labels permutation151 permutation2
    mixedMoment B raw29127step1 raw29127step1Labels = mixedMoment B raw29127step2 raw29127step2Labels := by
      have ha : raw29127step2 = -raw29127step1 := by apply Matrix.ext; change ∀ i j, raw29127step2 i j = -(raw29127step1 i j); unfold raw29127step2 raw29127step1; decide +kernel
      have hl : raw29127step2Labels = raw29127step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2672 node2672Labels := by rfl

def raw29128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29128Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29128step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29128step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw29128step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29128step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29128step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29128 raw29128Labels = mixedMoment B node3766 node3766Labels := by
  calc
    mixedMoment B raw29128 raw29128Labels = mixedMoment B raw29128step0 raw29128step0Labels := by
      have hz : ∀ j, raw29128 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29128step0 = (fun i j => raw29128 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29128step0 raw29128; decide +kernel
      have hl : raw29128step0Labels = raw29128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29128 raw29128Labels permutation346 hz
    mixedMoment B raw29128step0 raw29128step0Labels = mixedMoment B raw29128step1 raw29128step1Labels := by
      have ha : raw29128step1 = (fun i j => raw29128step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29128step1 raw29128step0; decide +kernel
      have hl : raw29128step1Labels = raw29128step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29128step0 raw29128step0Labels permutation151 permutation2
    mixedMoment B raw29128step1 raw29128step1Labels = mixedMoment B raw29128step2 raw29128step2Labels := by
      have ha : raw29128step2 = -raw29128step1 := by apply Matrix.ext; change ∀ i j, raw29128step2 i j = -(raw29128step1 i j); unfold raw29128step2 raw29128step1; decide +kernel
      have hl : raw29128step2Labels = raw29128step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3766 node3766Labels := by rfl

def raw29129 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![-1, 1], ![2, -2], ![2, -2]]
def raw29129Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29129step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]
def raw29129step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29129step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw29129step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29129step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw29129step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29129 raw29129Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw29129 raw29129Labels = mixedMoment B raw29129step0 raw29129step0Labels := by
      have hz : ∀ j, raw29129 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29129step0 = (fun i j => raw29129 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29129step0 raw29129; decide +kernel
      have hl : raw29129step0Labels = raw29129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29129 raw29129Labels permutation346 hz
    mixedMoment B raw29129step0 raw29129step0Labels = mixedMoment B raw29129step1 raw29129step1Labels := by
      have ha : raw29129step1 = (fun i j => raw29129step0 (permutation125 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29129step1 raw29129step0; decide +kernel
      have hl : raw29129step1Labels = raw29129step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29129step0 raw29129step0Labels permutation125 permutation0
    mixedMoment B raw29129step1 raw29129step1Labels = mixedMoment B raw29129step2 raw29129step2Labels := by
      have ha : raw29129step2 = -raw29129step1 := by apply Matrix.ext; change ∀ i j, raw29129step2 i j = -(raw29129step1 i j); unfold raw29129step2 raw29129step1; decide +kernel
      have hl : raw29129step2Labels = raw29129step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw29130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29130Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29130step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29130step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29130step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29130step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29130 raw29130Labels = mixedMoment B node2385 node2385Labels := by
  calc
    mixedMoment B raw29130 raw29130Labels = mixedMoment B raw29130step0 raw29130step0Labels := by
      have hz : ∀ j, raw29130 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29130step0 = (fun i j => raw29130 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29130step0 raw29130; decide +kernel
      have hl : raw29130step0Labels = raw29130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29130 raw29130Labels permutation346 hz
    mixedMoment B raw29130step0 raw29130step0Labels = mixedMoment B raw29130step1 raw29130step1Labels := by
      have ha : raw29130step1 = (fun i j => raw29130step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29130step1 raw29130step0; decide +kernel
      have hl : raw29130step1Labels = raw29130step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29130step0 raw29130step0Labels permutation149 permutation2
    mixedMoment B raw29130step1 raw29130step1Labels = mixedMoment B raw29130step2 raw29130step2Labels := by
      have ha : raw29130step2 = -raw29130step1 := by apply Matrix.ext; change ∀ i j, raw29130step2 i j = -(raw29130step1 i j); unfold raw29130step2 raw29130step1; decide +kernel
      have hl : raw29130step2Labels = raw29130step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2385 node2385Labels := by rfl

def raw29131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29131Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29131step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29131step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29131step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29131step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29131 raw29131Labels = mixedMoment B node2371 node2371Labels := by
  calc
    mixedMoment B raw29131 raw29131Labels = mixedMoment B raw29131step0 raw29131step0Labels := by
      have ha : raw29131step0 = (fun i j => raw29131 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29131step0 raw29131; decide +kernel
      have hl : raw29131step0Labels = raw29131Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29131 raw29131Labels permutation680 permutation2
    mixedMoment B raw29131step0 raw29131step0Labels = mixedMoment B raw29131step1 raw29131step1Labels := by
      have ha : raw29131step1 = -raw29131step0 := by apply Matrix.ext; change ∀ i j, raw29131step1 i j = -(raw29131step0 i j); unfold raw29131step1 raw29131step0; decide +kernel
      have hl : raw29131step1Labels = raw29131step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2371 node2371Labels := by rfl

def raw29132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def raw29132Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def raw29132step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29132step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29132step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29132step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29132step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29132 raw29132Labels = mixedMoment B node2309 node2309Labels := by
  calc
    mixedMoment B raw29132 raw29132Labels = mixedMoment B raw29132step0 raw29132step0Labels := by
      have hz : ∀ j, raw29132 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29132step0 = (fun i j => raw29132 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29132step0 raw29132; decide +kernel
      have hl : raw29132step0Labels = raw29132Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29132 raw29132Labels permutation346 hz
    mixedMoment B raw29132step0 raw29132step0Labels = mixedMoment B raw29132step1 raw29132step1Labels := by
      have ha : raw29132step1 = (fun i j => raw29132step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29132step1 raw29132step0; decide +kernel
      have hl : raw29132step1Labels = raw29132step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29132step0 raw29132step0Labels permutation149 permutation2
    mixedMoment B raw29132step1 raw29132step1Labels = mixedMoment B raw29132step2 raw29132step2Labels := by
      have ha : raw29132step2 = -raw29132step1 := by apply Matrix.ext; change ∀ i j, raw29132step2 i j = -(raw29132step1 i j); unfold raw29132step2 raw29132step1; decide +kernel
      have hl : raw29132step2Labels = raw29132step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2309 node2309Labels := by rfl

def raw29133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw29133Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw29133step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29133step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29133step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29133step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29133step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29133 raw29133Labels = mixedMoment B node1101 node1101Labels := by
  calc
    mixedMoment B raw29133 raw29133Labels = mixedMoment B raw29133step0 raw29133step0Labels := by
      have hz : ∀ j, raw29133 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29133step0 = (fun i j => raw29133 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29133step0 raw29133; decide +kernel
      have hl : raw29133step0Labels = raw29133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29133 raw29133Labels permutation346 hz
    mixedMoment B raw29133step0 raw29133step0Labels = mixedMoment B raw29133step1 raw29133step1Labels := by
      have ha : raw29133step1 = (fun i j => raw29133step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29133step1 raw29133step0; decide +kernel
      have hl : raw29133step1Labels = raw29133step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29133step0 raw29133step0Labels permutation149 permutation2
    mixedMoment B raw29133step1 raw29133step1Labels = mixedMoment B raw29133step2 raw29133step2Labels := by
      have ha : raw29133step2 = -raw29133step1 := by apply Matrix.ext; change ∀ i j, raw29133step2 i j = -(raw29133step1 i j); unfold raw29133step2 raw29133step1; decide +kernel
      have hl : raw29133step2Labels = raw29133step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1101 node1101Labels := by rfl

def raw29134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw29134Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw29134step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29134 raw29134Labels = mixedMoment B node1110 node1110Labels := by
  calc
    mixedMoment B raw29134 raw29134Labels = mixedMoment B raw29134step0 raw29134step0Labels := by
      have hz : ∀ j, raw29134 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29134step0 = (fun i j => raw29134 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29134step0 raw29134; decide +kernel
      have hl : raw29134step0Labels = raw29134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29134 raw29134Labels permutation346 hz
    _ = mixedMoment B node1110 node1110Labels := by rfl

def raw29135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw29135Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw29135step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw29135step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29135step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw29135step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29135 raw29135Labels = mixedMoment B node2300 node2300Labels := by
  calc
    mixedMoment B raw29135 raw29135Labels = mixedMoment B raw29135step0 raw29135step0Labels := by
      have hz : ∀ j, raw29135 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29135step0 = (fun i j => raw29135 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29135step0 raw29135; decide +kernel
      have hl : raw29135step0Labels = raw29135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29135 raw29135Labels permutation346 hz
    mixedMoment B raw29135step0 raw29135step0Labels = mixedMoment B raw29135step1 raw29135step1Labels := by
      have ha : raw29135step1 = (fun i j => raw29135step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29135step1 raw29135step0; decide +kernel
      have hl : raw29135step1Labels = raw29135step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29135step0 raw29135step0Labels permutation151 permutation2
    mixedMoment B raw29135step1 raw29135step1Labels = mixedMoment B raw29135step2 raw29135step2Labels := by
      have ha : raw29135step2 = -raw29135step1 := by apply Matrix.ext; change ∀ i j, raw29135step2 i j = -(raw29135step1 i j); unfold raw29135step2 raw29135step1; decide +kernel
      have hl : raw29135step2Labels = raw29135step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2300 node2300Labels := by rfl

def raw29136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw29136Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29136step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29136step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29136 raw29136Labels = mixedMoment B node2295 node2295Labels := by
  calc
    mixedMoment B raw29136 raw29136Labels = mixedMoment B raw29136step0 raw29136step0Labels := by
      have ha : raw29136step0 = (fun i j => raw29136 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29136step0 raw29136; decide +kernel
      have hl : raw29136step0Labels = raw29136Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29136 raw29136Labels permutation688 permutation2
    mixedMoment B raw29136step0 raw29136step0Labels = mixedMoment B raw29136step1 raw29136step1Labels := by
      have ha : raw29136step1 = -raw29136step0 := by apply Matrix.ext; change ∀ i j, raw29136step1 i j = -(raw29136step0 i j); unfold raw29136step1 raw29136step0; decide +kernel
      have hl : raw29136step1Labels = raw29136step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2295 node2295Labels := by rfl

def raw29137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29137Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29137step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29137 raw29137Labels = mixedMoment B node2468 node2468Labels := by
  calc
    mixedMoment B raw29137 raw29137Labels = mixedMoment B raw29137step0 raw29137step0Labels := by
      have hz : ∀ j, raw29137 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29137step0 = (fun i j => raw29137 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29137step0 raw29137; decide +kernel
      have hl : raw29137step0Labels = raw29137Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29137 raw29137Labels permutation346 hz
    _ = mixedMoment B node2468 node2468Labels := by rfl

def raw29138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29138Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29138step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29138 raw29138Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw29138 raw29138Labels = mixedMoment B raw29138step0 raw29138step0Labels := by
      have hz : ∀ j, raw29138 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29138step0 = (fun i j => raw29138 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29138step0 raw29138; decide +kernel
      have hl : raw29138step0Labels = raw29138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29138 raw29138Labels permutation346 hz
    _ = mixedMoment B node2705 node2705Labels := by rfl

def raw29139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29139Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29139step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw29139step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29139 raw29139Labels = mixedMoment B node2459 node2459Labels := by
  calc
    mixedMoment B raw29139 raw29139Labels = mixedMoment B raw29139step0 raw29139step0Labels := by
      have ha : raw29139step0 = (fun i j => raw29139 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29139step0 raw29139; decide +kernel
      have hl : raw29139step0Labels = raw29139Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29139 raw29139Labels permutation158 permutation2
    _ = mixedMoment B node2459 node2459Labels := by rfl

def raw29140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29140Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29140step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29140 raw29140Labels = mixedMoment B node2505 node2505Labels := by
  calc
    mixedMoment B raw29140 raw29140Labels = mixedMoment B raw29140step0 raw29140step0Labels := by
      have hz : ∀ j, raw29140 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29140step0 = (fun i j => raw29140 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29140step0 raw29140; decide +kernel
      have hl : raw29140step0Labels = raw29140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29140 raw29140Labels permutation346 hz
    _ = mixedMoment B node2505 node2505Labels := by rfl

def raw29141 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw29141Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw29141step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29141step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw29141step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29141 raw29141Labels = mixedMoment B node3353 node3353Labels := by
  calc
    mixedMoment B raw29141 raw29141Labels = mixedMoment B raw29141step0 raw29141step0Labels := by
      have hz : ∀ j, raw29141 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29141step0 = (fun i j => raw29141 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29141step0 raw29141; decide +kernel
      have hl : raw29141step0Labels = raw29141Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29141 raw29141Labels permutation346 hz
    mixedMoment B raw29141step0 raw29141step0Labels = mixedMoment B raw29141step1 raw29141step1Labels := by
      have ha : raw29141step1 = (fun i j => raw29141step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29141step1 raw29141step0; decide +kernel
      have hl : raw29141step1Labels = raw29141step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29141step0 raw29141step0Labels permutation151 permutation4
    _ = mixedMoment B node3353 node3353Labels := by rfl

def raw29142 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw29142Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw29142step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![-2, -1, 3]]
def raw29142step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29142step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw29142step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29142 raw29142Labels = mixedMoment B node2006 node2006Labels := by
  calc
    mixedMoment B raw29142 raw29142Labels = mixedMoment B raw29142step0 raw29142step0Labels := by
      have hz : ∀ j, raw29142 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29142step0 = (fun i j => raw29142 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29142step0 raw29142; decide +kernel
      have hl : raw29142step0Labels = raw29142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29142 raw29142Labels permutation346 hz
    mixedMoment B raw29142step0 raw29142step0Labels = mixedMoment B raw29142step1 raw29142step1Labels := by
      have ha : raw29142step1 = (fun i j => raw29142step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29142step1 raw29142step0; decide +kernel
      have hl : raw29142step1Labels = raw29142step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29142step0 raw29142step0Labels permutation38 permutation4
    mixedMoment B raw29142step1 raw29142step1Labels = mixedMoment B raw29142step2 raw29142step2Labels := by
      have ha : raw29142step2 = -raw29142step1 := by apply Matrix.ext; change ∀ i j, raw29142step2 i j = -(raw29142step1 i j); unfold raw29142step2 raw29142step1; decide +kernel
      have hl : raw29142step2Labels = raw29142step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2006 node2006Labels := by rfl

def raw29143 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw29143Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw29143step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29143step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -2, 1], ![-1, -2, 3]]
def raw29143step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29143step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-2, 1, 1], ![-2, -1, 3]]
def raw29143step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29143step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![2, -1, -1], ![2, 1, -3]]
def raw29143step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29143 raw29143Labels = mixedMoment B node1953 node1953Labels := by
  calc
    mixedMoment B raw29143 raw29143Labels = mixedMoment B raw29143step0 raw29143step0Labels := by
      have hz : ∀ j, raw29143 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29143step0 = (fun i j => raw29143 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29143step0 raw29143; decide +kernel
      have hl : raw29143step0Labels = raw29143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29143 raw29143Labels permutation434 hz
    mixedMoment B raw29143step0 raw29143step0Labels = mixedMoment B raw29143step1 raw29143step1Labels := by
      have hz : ∀ j, raw29143step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29143step1 = (fun i j => raw29143step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29143step1 raw29143step0; decide +kernel
      have hl : raw29143step1Labels = raw29143step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29143step0 raw29143step0Labels permutation80 hz
    mixedMoment B raw29143step1 raw29143step1Labels = mixedMoment B raw29143step2 raw29143step2Labels := by
      have ha : raw29143step2 = (fun i j => raw29143step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29143step2 raw29143step1; decide +kernel
      have hl : raw29143step2Labels = raw29143step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29143step1 raw29143step1Labels permutation8 permutation4
    mixedMoment B raw29143step2 raw29143step2Labels = mixedMoment B raw29143step3 raw29143step3Labels := by
      have ha : raw29143step3 = -raw29143step2 := by apply Matrix.ext; change ∀ i j, raw29143step3 i j = -(raw29143step2 i j); unfold raw29143step3 raw29143step2; decide +kernel
      have hl : raw29143step3Labels = raw29143step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1953 node1953Labels := by rfl

def raw29144 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw29144Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw29144step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-2, -1, 3], ![-3, 2, 1]]
def raw29144step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29144step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw29144step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29144 raw29144Labels = mixedMoment B node1873 node1873Labels := by
  calc
    mixedMoment B raw29144 raw29144Labels = mixedMoment B raw29144step0 raw29144step0Labels := by
      have hz : ∀ j, raw29144 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29144step0 = (fun i j => raw29144 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29144step0 raw29144; decide +kernel
      have hl : raw29144step0Labels = raw29144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29144 raw29144Labels permutation346 hz
    mixedMoment B raw29144step0 raw29144step0Labels = mixedMoment B raw29144step1 raw29144step1Labels := by
      have ha : raw29144step1 = (fun i j => raw29144step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29144step1 raw29144step0; decide +kernel
      have hl : raw29144step1Labels = raw29144step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29144step0 raw29144step0Labels permutation33 permutation4
    mixedMoment B raw29144step1 raw29144step1Labels = mixedMoment B raw29144step2 raw29144step2Labels := by
      have ha : raw29144step2 = -raw29144step1 := by apply Matrix.ext; change ∀ i j, raw29144step2 i j = -(raw29144step1 i j); unfold raw29144step2 raw29144step1; decide +kernel
      have hl : raw29144step2Labels = raw29144step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1873 node1873Labels := by rfl

def raw29145 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw29145Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw29145step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29145step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29145step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29145 raw29145Labels = mixedMoment B node1772 node1772Labels := by
  calc
    mixedMoment B raw29145 raw29145Labels = mixedMoment B raw29145step0 raw29145step0Labels := by
      have hz : ∀ j, raw29145 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29145step0 = (fun i j => raw29145 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29145step0 raw29145; decide +kernel
      have hl : raw29145step0Labels = raw29145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29145 raw29145Labels permutation346 hz
    mixedMoment B raw29145step0 raw29145step0Labels = mixedMoment B raw29145step1 raw29145step1Labels := by
      have ha : raw29145step1 = (fun i j => raw29145step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29145step1 raw29145step0; decide +kernel
      have hl : raw29145step1Labels = raw29145step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29145step0 raw29145step0Labels permutation151 permutation4
    _ = mixedMoment B node1772 node1772Labels := by rfl

def raw29146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29146step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw29146step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29146step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw29146step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29146 raw29146Labels = mixedMoment B node4745 node4745Labels := by
  calc
    mixedMoment B raw29146 raw29146Labels = mixedMoment B raw29146step0 raw29146step0Labels := by
      have hz : ∀ j, raw29146 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29146step0 = (fun i j => raw29146 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29146step0 raw29146; decide +kernel
      have hl : raw29146step0Labels = raw29146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29146 raw29146Labels permutation346 hz
    mixedMoment B raw29146step0 raw29146step0Labels = mixedMoment B raw29146step1 raw29146step1Labels := by
      have ha : raw29146step1 = (fun i j => raw29146step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29146step1 raw29146step0; decide +kernel
      have hl : raw29146step1Labels = raw29146step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29146step0 raw29146step0Labels permutation151 permutation2
    mixedMoment B raw29146step1 raw29146step1Labels = mixedMoment B raw29146step2 raw29146step2Labels := by
      have ha : raw29146step2 = -raw29146step1 := by apply Matrix.ext; change ∀ i j, raw29146step2 i j = -(raw29146step1 i j); unfold raw29146step2 raw29146step1; decide +kernel
      have hl : raw29146step2Labels = raw29146step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4745 node4745Labels := by rfl

def raw29147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29147step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw29147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29147step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29147step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29147 raw29147Labels = mixedMoment B node4736 node4736Labels := by
  calc
    mixedMoment B raw29147 raw29147Labels = mixedMoment B raw29147step0 raw29147step0Labels := by
      have ha : raw29147step0 = (fun i j => raw29147 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29147step0 raw29147; decide +kernel
      have hl : raw29147step0Labels = raw29147Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29147 raw29147Labels permutation688 permutation2
    mixedMoment B raw29147step0 raw29147step0Labels = mixedMoment B raw29147step1 raw29147step1Labels := by
      have ha : raw29147step1 = -raw29147step0 := by apply Matrix.ext; change ∀ i j, raw29147step1 i j = -(raw29147step0 i j); unfold raw29147step1 raw29147step0; decide +kernel
      have hl : raw29147step1Labels = raw29147step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4736 node4736Labels := by rfl

def raw29148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29148step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![3, -3]]
def raw29148step1Labels : Fin 2 → Fin 3 := ![0, 2]

def raw29148step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw29148step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw29148step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw29148step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw29148step4 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw29148step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29148 raw29148Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw29148 raw29148Labels = mixedMoment B raw29148step0 raw29148step0Labels := by
      have hz : ∀ j, raw29148 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29148step0 = (fun i j => raw29148 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29148step0 raw29148; decide +kernel
      have hl : raw29148step0Labels = raw29148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29148 raw29148Labels permutation346 hz
    mixedMoment B raw29148step0 raw29148step0Labels = mixedMoment B raw29148step1 raw29148step1Labels := by
      have hz : ∀ i, raw29148step0 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw29148step1 = (fun i j => raw29148step0 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw29148step1 raw29148step0; decide +kernel
      have hl : raw29148step1Labels = (fun j => raw29148step0Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw29148step0 raw29148step0Labels permutation4 hz
    mixedMoment B raw29148step1 raw29148step1Labels = mixedMoment B raw29148step2 raw29148step2Labels := by
      have ha : raw29148step2 = (fun i j => raw29148step1 (permutation149 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29148step2 raw29148step1; decide +kernel
      have hl : raw29148step2Labels = raw29148step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29148step1 raw29148step1Labels permutation149 permutation0
    mixedMoment B raw29148step2 raw29148step2Labels = mixedMoment B raw29148step3 raw29148step3Labels := by
      have ha : raw29148step3 = -raw29148step2 := by apply Matrix.ext; change ∀ i j, raw29148step3 i j = -(raw29148step2 i j); unfold raw29148step3 raw29148step2; decide +kernel
      have hl : raw29148step3Labels = raw29148step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29148step3 raw29148step3Labels = mixedMoment B raw29148step4 raw29148step4Labels := by
      have ha : raw29148step4 = raw29148step3 := by apply Matrix.ext; unfold raw29148step4 raw29148step3; decide +kernel
      have hl : raw29148step3Labels = labelEmbedding2 ∘ raw29148step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29148step3 raw29148step3Labels raw29148step4Labels labelEmbedding2 hl
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw29149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29149step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29149step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29149step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29149step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29149step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29149 raw29149Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw29149 raw29149Labels = mixedMoment B raw29149step0 raw29149step0Labels := by
      have hz : ∀ j, raw29149 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29149step0 = (fun i j => raw29149 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29149step0 raw29149; decide +kernel
      have hl : raw29149step0Labels = raw29149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29149 raw29149Labels permutation346 hz
    mixedMoment B raw29149step0 raw29149step0Labels = mixedMoment B raw29149step1 raw29149step1Labels := by
      have ha : raw29149step1 = (fun i j => raw29149step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29149step1 raw29149step0; decide +kernel
      have hl : raw29149step1Labels = raw29149step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29149step0 raw29149step0Labels permutation151 permutation7
    mixedMoment B raw29149step1 raw29149step1Labels = mixedMoment B raw29149step2 raw29149step2Labels := by
      have ha : raw29149step2 = raw29149step1 := by apply Matrix.ext; unfold raw29149step2 raw29149step1; decide +kernel
      have hl : raw29149step1Labels = labelEmbedding10 ∘ raw29149step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29149step1 raw29149step1Labels raw29149step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4834 node4834Labels := by rfl

def raw29150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29150step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29150step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29150step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29150 raw29150Labels = mixedMoment B node5101 node5101Labels := by
  calc
    mixedMoment B raw29150 raw29150Labels = mixedMoment B raw29150step0 raw29150step0Labels := by
      have hz : ∀ j, raw29150 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29150step0 = (fun i j => raw29150 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29150step0 raw29150; decide +kernel
      have hl : raw29150step0Labels = raw29150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29150 raw29150Labels permutation346 hz
    mixedMoment B raw29150step0 raw29150step0Labels = mixedMoment B raw29150step1 raw29150step1Labels := by
      have ha : raw29150step1 = (fun i j => raw29150step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29150step1 raw29150step0; decide +kernel
      have hl : raw29150step1Labels = raw29150step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29150step0 raw29150step0Labels permutation151 permutation7
    mixedMoment B raw29150step1 raw29150step1Labels = mixedMoment B raw29150step2 raw29150step2Labels := by
      have ha : raw29150step2 = raw29150step1 := by apply Matrix.ext; unfold raw29150step2 raw29150step1; decide +kernel
      have hl : raw29150step1Labels = labelEmbedding10 ∘ raw29150step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29150step1 raw29150step1Labels raw29150step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5101 node5101Labels := by rfl

def raw29151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29151step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29151 raw29151Labels = mixedMoment B node4583 node4583Labels := by
  calc
    mixedMoment B raw29151 raw29151Labels = mixedMoment B raw29151step0 raw29151step0Labels := by
      have hz : ∀ j, raw29151 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29151step0 = (fun i j => raw29151 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29151step0 raw29151; decide +kernel
      have hl : raw29151step0Labels = raw29151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29151 raw29151Labels permutation346 hz
    _ = mixedMoment B node4583 node4583Labels := by rfl

def raw29152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29152step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw29152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29152step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw29152step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29152 raw29152Labels = mixedMoment B node4728 node4728Labels := by
  calc
    mixedMoment B raw29152 raw29152Labels = mixedMoment B raw29152step0 raw29152step0Labels := by
      have ha : raw29152step0 = (fun i j => raw29152 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29152step0 raw29152; decide +kernel
      have hl : raw29152step0Labels = raw29152Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29152 raw29152Labels permutation676 permutation2
    mixedMoment B raw29152step0 raw29152step0Labels = mixedMoment B raw29152step1 raw29152step1Labels := by
      have ha : raw29152step1 = -raw29152step0 := by apply Matrix.ext; change ∀ i j, raw29152step1 i j = -(raw29152step0 i j); unfold raw29152step1 raw29152step0; decide +kernel
      have hl : raw29152step1Labels = raw29152step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4728 node4728Labels := by rfl

def raw29153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29153step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29153step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29153step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29153step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29153 raw29153Labels = mixedMoment B node4741 node4741Labels := by
  calc
    mixedMoment B raw29153 raw29153Labels = mixedMoment B raw29153step0 raw29153step0Labels := by
      have hz : ∀ j, raw29153 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29153step0 = (fun i j => raw29153 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29153step0 raw29153; decide +kernel
      have hl : raw29153step0Labels = raw29153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29153 raw29153Labels permutation346 hz
    mixedMoment B raw29153step0 raw29153step0Labels = mixedMoment B raw29153step1 raw29153step1Labels := by
      have ha : raw29153step1 = (fun i j => raw29153step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29153step1 raw29153step0; decide +kernel
      have hl : raw29153step1Labels = raw29153step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29153step0 raw29153step0Labels permutation149 permutation2
    mixedMoment B raw29153step1 raw29153step1Labels = mixedMoment B raw29153step2 raw29153step2Labels := by
      have ha : raw29153step2 = -raw29153step1 := by apply Matrix.ext; change ∀ i j, raw29153step2 i j = -(raw29153step1 i j); unfold raw29153step2 raw29153step1; decide +kernel
      have hl : raw29153step2Labels = raw29153step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4741 node4741Labels := by rfl

def raw29154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29154step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29154step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29154step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29154step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29154step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29154 raw29154Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw29154 raw29154Labels = mixedMoment B raw29154step0 raw29154step0Labels := by
      have hz : ∀ j, raw29154 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29154step0 = (fun i j => raw29154 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29154step0 raw29154; decide +kernel
      have hl : raw29154step0Labels = raw29154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29154 raw29154Labels permutation346 hz
    mixedMoment B raw29154step0 raw29154step0Labels = mixedMoment B raw29154step1 raw29154step1Labels := by
      have ha : raw29154step1 = (fun i j => raw29154step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29154step1 raw29154step0; decide +kernel
      have hl : raw29154step1Labels = raw29154step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29154step0 raw29154step0Labels permutation149 permutation7
    mixedMoment B raw29154step1 raw29154step1Labels = mixedMoment B raw29154step2 raw29154step2Labels := by
      have ha : raw29154step2 = raw29154step1 := by apply Matrix.ext; unfold raw29154step2 raw29154step1; decide +kernel
      have hl : raw29154step1Labels = labelEmbedding10 ∘ raw29154step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29154step1 raw29154step1Labels raw29154step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4832 node4832Labels := by rfl

def raw29155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29155step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29155step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29155step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29155step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29155step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29155 raw29155Labels = mixedMoment B node5099 node5099Labels := by
  calc
    mixedMoment B raw29155 raw29155Labels = mixedMoment B raw29155step0 raw29155step0Labels := by
      have hz : ∀ j, raw29155 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29155step0 = (fun i j => raw29155 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29155step0 raw29155; decide +kernel
      have hl : raw29155step0Labels = raw29155Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29155 raw29155Labels permutation346 hz
    mixedMoment B raw29155step0 raw29155step0Labels = mixedMoment B raw29155step1 raw29155step1Labels := by
      have ha : raw29155step1 = (fun i j => raw29155step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29155step1 raw29155step0; decide +kernel
      have hl : raw29155step1Labels = raw29155step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29155step0 raw29155step0Labels permutation149 permutation7
    mixedMoment B raw29155step1 raw29155step1Labels = mixedMoment B raw29155step2 raw29155step2Labels := by
      have ha : raw29155step2 = raw29155step1 := by apply Matrix.ext; unfold raw29155step2 raw29155step1; decide +kernel
      have hl : raw29155step1Labels = labelEmbedding10 ∘ raw29155step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29155step1 raw29155step1Labels raw29155step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5099 node5099Labels := by rfl

def raw29156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29156step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29156step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29156 raw29156Labels = mixedMoment B node4521 node4521Labels := by
  calc
    mixedMoment B raw29156 raw29156Labels = mixedMoment B raw29156step0 raw29156step0Labels := by
      have ha : raw29156step0 = (fun i j => raw29156 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29156step0 raw29156; decide +kernel
      have hl : raw29156step0Labels = raw29156Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29156 raw29156Labels permutation158 permutation2
    _ = mixedMoment B node4521 node4521Labels := by rfl

def raw29157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29157step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw29157step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29157step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw29157step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29157 raw29157Labels = mixedMoment B node4706 node4706Labels := by
  calc
    mixedMoment B raw29157 raw29157Labels = mixedMoment B raw29157step0 raw29157step0Labels := by
      have ha : raw29157step0 = (fun i j => raw29157 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29157step0 raw29157; decide +kernel
      have hl : raw29157step0Labels = raw29157Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29157 raw29157Labels permutation682 permutation2
    mixedMoment B raw29157step0 raw29157step0Labels = mixedMoment B raw29157step1 raw29157step1Labels := by
      have ha : raw29157step1 = -raw29157step0 := by apply Matrix.ext; change ∀ i j, raw29157step1 i j = -(raw29157step0 i j); unfold raw29157step1 raw29157step0; decide +kernel
      have hl : raw29157step1Labels = raw29157step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4706 node4706Labels := by rfl

def raw29158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29158step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29158step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29158step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29158step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29158 raw29158Labels = mixedMoment B node4712 node4712Labels := by
  calc
    mixedMoment B raw29158 raw29158Labels = mixedMoment B raw29158step0 raw29158step0Labels := by
      have ha : raw29158step0 = (fun i j => raw29158 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29158step0 raw29158; decide +kernel
      have hl : raw29158step0Labels = raw29158Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29158 raw29158Labels permutation680 permutation2
    mixedMoment B raw29158step0 raw29158step0Labels = mixedMoment B raw29158step1 raw29158step1Labels := by
      have ha : raw29158step1 = -raw29158step0 := by apply Matrix.ext; change ∀ i j, raw29158step1 i j = -(raw29158step0 i j); unfold raw29158step1 raw29158step0; decide +kernel
      have hl : raw29158step1Labels = raw29158step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4712 node4712Labels := by rfl

def raw29159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29159step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29159step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29159step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29159step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29159 raw29159Labels = mixedMoment B node4779 node4779Labels := by
  calc
    mixedMoment B raw29159 raw29159Labels = mixedMoment B raw29159step0 raw29159step0Labels := by
      have ha : raw29159step0 = (fun i j => raw29159 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29159step0 raw29159; decide +kernel
      have hl : raw29159step0Labels = raw29159Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29159 raw29159Labels permutation646 permutation2
    mixedMoment B raw29159step0 raw29159step0Labels = mixedMoment B raw29159step1 raw29159step1Labels := by
      have ha : raw29159step1 = -raw29159step0 := by apply Matrix.ext; change ∀ i j, raw29159step1 i j = -(raw29159step0 i j); unfold raw29159step1 raw29159step0; decide +kernel
      have hl : raw29159step1Labels = raw29159step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4779 node4779Labels := by rfl

def raw29160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29160Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29160step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw29160step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29160 raw29160Labels = mixedMoment B node5055 node5055Labels := by
  calc
    mixedMoment B raw29160 raw29160Labels = mixedMoment B raw29160step0 raw29160step0Labels := by
      have ha : raw29160step0 = (fun i j => raw29160 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29160step0 raw29160; decide +kernel
      have hl : raw29160step0Labels = raw29160Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29160 raw29160Labels permutation158 permutation2
    _ = mixedMoment B node5055 node5055Labels := by rfl

def raw29161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29161Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29161step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29161 raw29161Labels = mixedMoment B node4538 node4538Labels := by
  calc
    mixedMoment B raw29161 raw29161Labels = mixedMoment B raw29161step0 raw29161step0Labels := by
      have hz : ∀ j, raw29161 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29161step0 = (fun i j => raw29161 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29161step0 raw29161; decide +kernel
      have hl : raw29161step0Labels = raw29161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29161 raw29161Labels permutation346 hz
    _ = mixedMoment B node4538 node4538Labels := by rfl

def raw29162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29162Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29162step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw29162step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29162step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw29162step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29162 raw29162Labels = mixedMoment B node4726 node4726Labels := by
  calc
    mixedMoment B raw29162 raw29162Labels = mixedMoment B raw29162step0 raw29162step0Labels := by
      have hz : ∀ j, raw29162 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29162step0 = (fun i j => raw29162 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29162step0 raw29162; decide +kernel
      have hl : raw29162step0Labels = raw29162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29162 raw29162Labels permutation346 hz
    mixedMoment B raw29162step0 raw29162step0Labels = mixedMoment B raw29162step1 raw29162step1Labels := by
      have ha : raw29162step1 = (fun i j => raw29162step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29162step1 raw29162step0; decide +kernel
      have hl : raw29162step1Labels = raw29162step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29162step0 raw29162step0Labels permutation151 permutation2
    mixedMoment B raw29162step1 raw29162step1Labels = mixedMoment B raw29162step2 raw29162step2Labels := by
      have ha : raw29162step2 = -raw29162step1 := by apply Matrix.ext; change ∀ i j, raw29162step2 i j = -(raw29162step1 i j); unfold raw29162step2 raw29162step1; decide +kernel
      have hl : raw29162step2Labels = raw29162step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4726 node4726Labels := by rfl

def raw29163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29163Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29163step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29163step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29163step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29163step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29163 raw29163Labels = mixedMoment B node4721 node4721Labels := by
  calc
    mixedMoment B raw29163 raw29163Labels = mixedMoment B raw29163step0 raw29163step0Labels := by
      have ha : raw29163step0 = (fun i j => raw29163 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29163step0 raw29163; decide +kernel
      have hl : raw29163step0Labels = raw29163Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29163 raw29163Labels permutation688 permutation2
    mixedMoment B raw29163step0 raw29163step0Labels = mixedMoment B raw29163step1 raw29163step1Labels := by
      have ha : raw29163step1 = -raw29163step0 := by apply Matrix.ext; change ∀ i j, raw29163step1 i j = -(raw29163step0 i j); unfold raw29163step1 raw29163step0; decide +kernel
      have hl : raw29163step1Labels = raw29163step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4721 node4721Labels := by rfl

def raw29164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29164Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29164step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29164step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29164step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29164step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29164 raw29164Labels = mixedMoment B node4827 node4827Labels := by
  calc
    mixedMoment B raw29164 raw29164Labels = mixedMoment B raw29164step0 raw29164step0Labels := by
      have hz : ∀ j, raw29164 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29164step0 = (fun i j => raw29164 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29164step0 raw29164; decide +kernel
      have hl : raw29164step0Labels = raw29164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29164 raw29164Labels permutation346 hz
    mixedMoment B raw29164step0 raw29164step0Labels = mixedMoment B raw29164step1 raw29164step1Labels := by
      have ha : raw29164step1 = (fun i j => raw29164step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29164step1 raw29164step0; decide +kernel
      have hl : raw29164step1Labels = raw29164step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29164step0 raw29164step0Labels permutation151 permutation7
    mixedMoment B raw29164step1 raw29164step1Labels = mixedMoment B raw29164step2 raw29164step2Labels := by
      have ha : raw29164step2 = raw29164step1 := by apply Matrix.ext; unfold raw29164step2 raw29164step1; decide +kernel
      have hl : raw29164step1Labels = labelEmbedding10 ∘ raw29164step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29164step1 raw29164step1Labels raw29164step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4827 node4827Labels := by rfl

def raw29165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29165Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29165step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29165 raw29165Labels = mixedMoment B node5094 node5094Labels := by
  calc
    mixedMoment B raw29165 raw29165Labels = mixedMoment B raw29165step0 raw29165step0Labels := by
      have hz : ∀ j, raw29165 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29165step0 = (fun i j => raw29165 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29165step0 raw29165; decide +kernel
      have hl : raw29165step0Labels = raw29165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29165 raw29165Labels permutation346 hz
    _ = mixedMoment B node5094 node5094Labels := by rfl

def raw29166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29166Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29166step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29166 raw29166Labels = mixedMoment B node4525 node4525Labels := by
  calc
    mixedMoment B raw29166 raw29166Labels = mixedMoment B raw29166step0 raw29166step0Labels := by
      have hz : ∀ j, raw29166 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29166step0 = (fun i j => raw29166 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29166step0 raw29166; decide +kernel
      have hl : raw29166step0Labels = raw29166Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29166 raw29166Labels permutation346 hz
    _ = mixedMoment B node4525 node4525Labels := by rfl

def raw29167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29167Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29167step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw29167step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29167step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw29167step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29167 raw29167Labels = mixedMoment B node4637 node4637Labels := by
  calc
    mixedMoment B raw29167 raw29167Labels = mixedMoment B raw29167step0 raw29167step0Labels := by
      have hz : ∀ j, raw29167 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29167step0 = (fun i j => raw29167 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29167step0 raw29167; decide +kernel
      have hl : raw29167step0Labels = raw29167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29167 raw29167Labels permutation346 hz
    mixedMoment B raw29167step0 raw29167step0Labels = mixedMoment B raw29167step1 raw29167step1Labels := by
      have ha : raw29167step1 = (fun i j => raw29167step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29167step1 raw29167step0; decide +kernel
      have hl : raw29167step1Labels = raw29167step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29167step0 raw29167step0Labels permutation151 permutation2
    mixedMoment B raw29167step1 raw29167step1Labels = mixedMoment B raw29167step2 raw29167step2Labels := by
      have ha : raw29167step2 = -raw29167step1 := by apply Matrix.ext; change ∀ i j, raw29167step2 i j = -(raw29167step1 i j); unfold raw29167step2 raw29167step1; decide +kernel
      have hl : raw29167step2Labels = raw29167step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4637 node4637Labels := by rfl

def raw29168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29168Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29168step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29168step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29168step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29168step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29168 raw29168Labels = mixedMoment B node4631 node4631Labels := by
  calc
    mixedMoment B raw29168 raw29168Labels = mixedMoment B raw29168step0 raw29168step0Labels := by
      have ha : raw29168step0 = (fun i j => raw29168 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29168step0 raw29168; decide +kernel
      have hl : raw29168step0Labels = raw29168Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29168 raw29168Labels permutation688 permutation2
    mixedMoment B raw29168step0 raw29168step0Labels = mixedMoment B raw29168step1 raw29168step1Labels := by
      have ha : raw29168step1 = -raw29168step0 := by apply Matrix.ext; change ∀ i j, raw29168step1 i j = -(raw29168step0 i j); unfold raw29168step1 raw29168step0; decide +kernel
      have hl : raw29168step1Labels = raw29168step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4631 node4631Labels := by rfl

def raw29169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29169Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29169step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29169step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29169step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29169step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29169 raw29169Labels = mixedMoment B node4649 node4649Labels := by
  calc
    mixedMoment B raw29169 raw29169Labels = mixedMoment B raw29169step0 raw29169step0Labels := by
      have hz : ∀ j, raw29169 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29169step0 = (fun i j => raw29169 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29169step0 raw29169; decide +kernel
      have hl : raw29169step0Labels = raw29169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29169 raw29169Labels permutation346 hz
    mixedMoment B raw29169step0 raw29169step0Labels = mixedMoment B raw29169step1 raw29169step1Labels := by
      have ha : raw29169step1 = (fun i j => raw29169step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29169step1 raw29169step0; decide +kernel
      have hl : raw29169step1Labels = raw29169step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29169step0 raw29169step0Labels permutation149 permutation2
    mixedMoment B raw29169step1 raw29169step1Labels = mixedMoment B raw29169step2 raw29169step2Labels := by
      have ha : raw29169step2 = -raw29169step1 := by apply Matrix.ext; change ∀ i j, raw29169step2 i j = -(raw29169step1 i j); unfold raw29169step2 raw29169step1; decide +kernel
      have hl : raw29169step2Labels = raw29169step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4649 node4649Labels := by rfl

def raw29170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw29170Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw29170step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw29170step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29170step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw29170step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29170 raw29170Labels = mixedMoment B node5014 node5014Labels := by
  calc
    mixedMoment B raw29170 raw29170Labels = mixedMoment B raw29170step0 raw29170step0Labels := by
      have hz : ∀ j, raw29170 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29170step0 = (fun i j => raw29170 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29170step0 raw29170; decide +kernel
      have hl : raw29170step0Labels = raw29170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29170 raw29170Labels permutation346 hz
    mixedMoment B raw29170step0 raw29170step0Labels = mixedMoment B raw29170step1 raw29170step1Labels := by
      have ha : raw29170step1 = (fun i j => raw29170step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29170step1 raw29170step0; decide +kernel
      have hl : raw29170step1Labels = raw29170step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29170step0 raw29170step0Labels permutation151 permutation7
    mixedMoment B raw29170step1 raw29170step1Labels = mixedMoment B raw29170step2 raw29170step2Labels := by
      have ha : raw29170step2 = raw29170step1 := by apply Matrix.ext; unfold raw29170step2 raw29170step1; decide +kernel
      have hl : raw29170step1Labels = labelEmbedding10 ∘ raw29170step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29170step1 raw29170step1Labels raw29170step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5014 node5014Labels := by rfl

def raw29171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29171Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29171step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw29171step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29171step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw29171step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29171 raw29171Labels = mixedMoment B node4293 node4293Labels := by
  calc
    mixedMoment B raw29171 raw29171Labels = mixedMoment B raw29171step0 raw29171step0Labels := by
      have hz : ∀ j, raw29171 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29171step0 = (fun i j => raw29171 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29171step0 raw29171; decide +kernel
      have hl : raw29171step0Labels = raw29171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29171 raw29171Labels permutation346 hz
    mixedMoment B raw29171step0 raw29171step0Labels = mixedMoment B raw29171step1 raw29171step1Labels := by
      have ha : raw29171step1 = (fun i j => raw29171step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29171step1 raw29171step0; decide +kernel
      have hl : raw29171step1Labels = raw29171step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29171step0 raw29171step0Labels permutation151 permutation2
    mixedMoment B raw29171step1 raw29171step1Labels = mixedMoment B raw29171step2 raw29171step2Labels := by
      have ha : raw29171step2 = -raw29171step1 := by apply Matrix.ext; change ∀ i j, raw29171step2 i j = -(raw29171step1 i j); unfold raw29171step2 raw29171step1; decide +kernel
      have hl : raw29171step2Labels = raw29171step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4293 node4293Labels := by rfl

def raw29172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29172Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29172step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw29172step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29172step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw29172step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29172 raw29172Labels = mixedMoment B node4295 node4295Labels := by
  calc
    mixedMoment B raw29172 raw29172Labels = mixedMoment B raw29172step0 raw29172step0Labels := by
      have hz : ∀ j, raw29172 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29172step0 = (fun i j => raw29172 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29172step0 raw29172; decide +kernel
      have hl : raw29172step0Labels = raw29172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29172 raw29172Labels permutation346 hz
    mixedMoment B raw29172step0 raw29172step0Labels = mixedMoment B raw29172step1 raw29172step1Labels := by
      have ha : raw29172step1 = (fun i j => raw29172step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29172step1 raw29172step0; decide +kernel
      have hl : raw29172step1Labels = raw29172step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29172step0 raw29172step0Labels permutation151 permutation2
    mixedMoment B raw29172step1 raw29172step1Labels = mixedMoment B raw29172step2 raw29172step2Labels := by
      have ha : raw29172step2 = -raw29172step1 := by apply Matrix.ext; change ∀ i j, raw29172step2 i j = -(raw29172step1 i j); unfold raw29172step2 raw29172step1; decide +kernel
      have hl : raw29172step2Labels = raw29172step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4295 node4295Labels := by rfl

def raw29173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29173Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29173step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29173step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29173step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29173 raw29173Labels = mixedMoment B node4287 node4287Labels := by
  calc
    mixedMoment B raw29173 raw29173Labels = mixedMoment B raw29173step0 raw29173step0Labels := by
      have ha : raw29173step0 = (fun i j => raw29173 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29173step0 raw29173; decide +kernel
      have hl : raw29173step0Labels = raw29173Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29173 raw29173Labels permutation688 permutation2
    mixedMoment B raw29173step0 raw29173step0Labels = mixedMoment B raw29173step1 raw29173step1Labels := by
      have ha : raw29173step1 = -raw29173step0 := by apply Matrix.ext; change ∀ i j, raw29173step1 i j = -(raw29173step0 i j); unfold raw29173step1 raw29173step0; decide +kernel
      have hl : raw29173step1Labels = raw29173step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4287 node4287Labels := by rfl

def raw29174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29174Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29174step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29174step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29174step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29174step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29174 raw29174Labels = mixedMoment B node4308 node4308Labels := by
  calc
    mixedMoment B raw29174 raw29174Labels = mixedMoment B raw29174step0 raw29174step0Labels := by
      have hz : ∀ j, raw29174 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29174step0 = (fun i j => raw29174 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29174step0 raw29174; decide +kernel
      have hl : raw29174step0Labels = raw29174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29174 raw29174Labels permutation346 hz
    mixedMoment B raw29174step0 raw29174step0Labels = mixedMoment B raw29174step1 raw29174step1Labels := by
      have ha : raw29174step1 = (fun i j => raw29174step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29174step1 raw29174step0; decide +kernel
      have hl : raw29174step1Labels = raw29174step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29174step0 raw29174step0Labels permutation149 permutation2
    mixedMoment B raw29174step1 raw29174step1Labels = mixedMoment B raw29174step2 raw29174step2Labels := by
      have ha : raw29174step2 = -raw29174step1 := by apply Matrix.ext; change ∀ i j, raw29174step2 i j = -(raw29174step1 i j); unfold raw29174step2 raw29174step1; decide +kernel
      have hl : raw29174step2Labels = raw29174step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4308 node4308Labels := by rfl

def raw29175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw29175Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw29175step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29175step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29175step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29175step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29175 raw29175Labels = mixedMoment B node4401 node4401Labels := by
  calc
    mixedMoment B raw29175 raw29175Labels = mixedMoment B raw29175step0 raw29175step0Labels := by
      have hz : ∀ j, raw29175 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29175step0 = (fun i j => raw29175 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29175step0 raw29175; decide +kernel
      have hl : raw29175step0Labels = raw29175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29175 raw29175Labels permutation346 hz
    mixedMoment B raw29175step0 raw29175step0Labels = mixedMoment B raw29175step1 raw29175step1Labels := by
      have ha : raw29175step1 = (fun i j => raw29175step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29175step1 raw29175step0; decide +kernel
      have hl : raw29175step1Labels = raw29175step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29175step0 raw29175step0Labels permutation151 permutation2
    mixedMoment B raw29175step1 raw29175step1Labels = mixedMoment B raw29175step2 raw29175step2Labels := by
      have ha : raw29175step2 = -raw29175step1 := by apply Matrix.ext; change ∀ i j, raw29175step2 i j = -(raw29175step1 i j); unfold raw29175step2 raw29175step1; decide +kernel
      have hl : raw29175step2Labels = raw29175step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4401 node4401Labels := by rfl

def raw29176 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29176Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29176step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29176step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw29176step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29176step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw29176step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29176step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw29176step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29176 raw29176Labels = mixedMoment B node4742 node4742Labels := by
  calc
    mixedMoment B raw29176 raw29176Labels = mixedMoment B raw29176step0 raw29176step0Labels := by
      have hz : ∀ j, raw29176 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29176step0 = (fun i j => raw29176 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29176step0 raw29176; decide +kernel
      have hl : raw29176step0Labels = raw29176Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29176 raw29176Labels permutation346 hz
    mixedMoment B raw29176step0 raw29176step0Labels = mixedMoment B raw29176step1 raw29176step1Labels := by
      have ha : raw29176step1 = (fun i j => raw29176step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29176step1 raw29176step0; decide +kernel
      have hl : raw29176step1Labels = raw29176step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29176step0 raw29176step0Labels permutation151 permutation6
    mixedMoment B raw29176step1 raw29176step1Labels = mixedMoment B raw29176step2 raw29176step2Labels := by
      have ha : raw29176step2 = -raw29176step1 := by apply Matrix.ext; change ∀ i j, raw29176step2 i j = -(raw29176step1 i j); unfold raw29176step2 raw29176step1; decide +kernel
      have hl : raw29176step2Labels = raw29176step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29176step2 raw29176step2Labels = mixedMoment B raw29176step3 raw29176step3Labels := by
      have ha : raw29176step3 = raw29176step2 := by apply Matrix.ext; unfold raw29176step3 raw29176step2; decide +kernel
      have hl : raw29176step2Labels = labelEmbedding9 ∘ raw29176step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29176step2 raw29176step2Labels raw29176step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4742 node4742Labels := by rfl

def raw29177 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29177Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29177step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw29177step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29177step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29177step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29177step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw29177step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29177 raw29177Labels = mixedMoment B node4729 node4729Labels := by
  calc
    mixedMoment B raw29177 raw29177Labels = mixedMoment B raw29177step0 raw29177step0Labels := by
      have ha : raw29177step0 = (fun i j => raw29177 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29177step0 raw29177; decide +kernel
      have hl : raw29177step0Labels = raw29177Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29177 raw29177Labels permutation682 permutation6
    mixedMoment B raw29177step0 raw29177step0Labels = mixedMoment B raw29177step1 raw29177step1Labels := by
      have ha : raw29177step1 = -raw29177step0 := by apply Matrix.ext; change ∀ i j, raw29177step1 i j = -(raw29177step0 i j); unfold raw29177step1 raw29177step0; decide +kernel
      have hl : raw29177step1Labels = raw29177step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29177step1 raw29177step1Labels = mixedMoment B raw29177step2 raw29177step2Labels := by
      have ha : raw29177step2 = raw29177step1 := by apply Matrix.ext; unfold raw29177step2 raw29177step1; decide +kernel
      have hl : raw29177step1Labels = labelEmbedding9 ∘ raw29177step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29177step1 raw29177step1Labels raw29177step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4729 node4729Labels := by rfl

def raw29178 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29178Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-2, 2, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29178step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw29178step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29178step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw29178step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29178step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw29178step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29178 raw29178Labels = mixedMoment B node4747 node4747Labels := by
  calc
    mixedMoment B raw29178 raw29178Labels = mixedMoment B raw29178step0 raw29178step0Labels := by
      have hz : ∀ j, raw29178 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29178step0 = (fun i j => raw29178 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29178step0 raw29178; decide +kernel
      have hl : raw29178step0Labels = raw29178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29178 raw29178Labels permutation346 hz
    mixedMoment B raw29178step0 raw29178step0Labels = mixedMoment B raw29178step1 raw29178step1Labels := by
      have ha : raw29178step1 = (fun i j => raw29178step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29178step1 raw29178step0; decide +kernel
      have hl : raw29178step1Labels = raw29178step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29178step0 raw29178step0Labels permutation151 permutation6
    mixedMoment B raw29178step1 raw29178step1Labels = mixedMoment B raw29178step2 raw29178step2Labels := by
      have ha : raw29178step2 = -raw29178step1 := by apply Matrix.ext; change ∀ i j, raw29178step2 i j = -(raw29178step1 i j); unfold raw29178step2 raw29178step1; decide +kernel
      have hl : raw29178step2Labels = raw29178step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29178step2 raw29178step2Labels = mixedMoment B raw29178step3 raw29178step3Labels := by
      have ha : raw29178step3 = raw29178step2 := by apply Matrix.ext; unfold raw29178step3 raw29178step2; decide +kernel
      have hl : raw29178step2Labels = labelEmbedding9 ∘ raw29178step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29178step2 raw29178step2Labels raw29178step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4747 node4747Labels := by rfl

def raw29179 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29179Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29179step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29179step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29179step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29179 raw29179Labels = mixedMoment B node4708 node4708Labels := by
  calc
    mixedMoment B raw29179 raw29179Labels = mixedMoment B raw29179step0 raw29179step0Labels := by
      have ha : raw29179step0 = (fun i j => raw29179 (permutation682 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29179step0 raw29179; decide +kernel
      have hl : raw29179step0Labels = raw29179Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29179 raw29179Labels permutation682 permutation4
    mixedMoment B raw29179step0 raw29179step0Labels = mixedMoment B raw29179step1 raw29179step1Labels := by
      have ha : raw29179step1 = raw29179step0 := by apply Matrix.ext; unfold raw29179step1 raw29179step0; decide +kernel
      have hl : raw29179step0Labels = labelEmbedding7 ∘ raw29179step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29179step0 raw29179step0Labels raw29179step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4708 node4708Labels := by rfl

def raw29180 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29180Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29180step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29180step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29180step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29180step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29180 raw29180Labels = mixedMoment B node4710 node4710Labels := by
  calc
    mixedMoment B raw29180 raw29180Labels = mixedMoment B raw29180step0 raw29180step0Labels := by
      have ha : raw29180step0 = (fun i j => raw29180 (permutation682 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29180step0 raw29180; decide +kernel
      have hl : raw29180step0Labels = raw29180Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29180 raw29180Labels permutation682 permutation4
    mixedMoment B raw29180step0 raw29180step0Labels = mixedMoment B raw29180step1 raw29180step1Labels := by
      have ha : raw29180step1 = raw29180step0 := by apply Matrix.ext; unfold raw29180step1 raw29180step0; decide +kernel
      have hl : raw29180step0Labels = labelEmbedding7 ∘ raw29180step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29180step0 raw29180step0Labels raw29180step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4710 node4710Labels := by rfl

def raw29181 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29181Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29181step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw29181step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29181step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw29181step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29181 raw29181Labels = mixedMoment B node4714 node4714Labels := by
  calc
    mixedMoment B raw29181 raw29181Labels = mixedMoment B raw29181step0 raw29181step0Labels := by
      have ha : raw29181step0 = (fun i j => raw29181 (permutation680 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29181step0 raw29181; decide +kernel
      have hl : raw29181step0Labels = raw29181Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29181 raw29181Labels permutation680 permutation4
    mixedMoment B raw29181step0 raw29181step0Labels = mixedMoment B raw29181step1 raw29181step1Labels := by
      have ha : raw29181step1 = raw29181step0 := by apply Matrix.ext; unfold raw29181step1 raw29181step0; decide +kernel
      have hl : raw29181step0Labels = labelEmbedding7 ∘ raw29181step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29181step0 raw29181step0Labels raw29181step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4714 node4714Labels := by rfl

def raw29182 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29182Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29182step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29182step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, -1, 1], ![0, -3, 3]]
def raw29182step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29182step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-3, 3]]
def raw29182step2Labels : Fin 2 → Fin 3 := ![1, 2]

def raw29182step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw29182step3Labels : Fin 2 → Fin 3 := ![1, 2]

def raw29182step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw29182step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29182 raw29182Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw29182 raw29182Labels = mixedMoment B raw29182step0 raw29182step0Labels := by
      have hz : ∀ j, raw29182 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29182step0 = (fun i j => raw29182 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29182step0 raw29182; decide +kernel
      have hl : raw29182step0Labels = raw29182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29182 raw29182Labels permutation434 hz
    mixedMoment B raw29182step0 raw29182step0Labels = mixedMoment B raw29182step1 raw29182step1Labels := by
      have hz : ∀ j, raw29182step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29182step1 = (fun i j => raw29182step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29182step1 raw29182step0; decide +kernel
      have hl : raw29182step1Labels = raw29182step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29182step0 raw29182step0Labels permutation80 hz
    mixedMoment B raw29182step1 raw29182step1Labels = mixedMoment B raw29182step2 raw29182step2Labels := by
      have hz : ∀ i, raw29182step1 i (permutation2 0) = 0 := by decide +kernel
      have ha : raw29182step2 = (fun i j => raw29182step1 i (permutation2 j.succ)) := by apply Matrix.ext; unfold raw29182step2 raw29182step1; decide +kernel
      have hl : raw29182step2Labels = (fun j => raw29182step1Labels (permutation2 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw29182step1 raw29182step1Labels permutation2 hz
    mixedMoment B raw29182step2 raw29182step2Labels = mixedMoment B raw29182step3 raw29182step3Labels := by
      have ha : raw29182step3 = (fun i j => raw29182step2 (permutation31 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29182step3 raw29182step2; decide +kernel
      have hl : raw29182step3Labels = raw29182step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29182step2 raw29182step2Labels permutation31 permutation0
    mixedMoment B raw29182step3 raw29182step3Labels = mixedMoment B raw29182step4 raw29182step4Labels := by
      have ha : raw29182step4 = raw29182step3 := by apply Matrix.ext; unfold raw29182step4 raw29182step3; decide +kernel
      have hl : raw29182step3Labels = labelEmbedding3 ∘ raw29182step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29182step3 raw29182step3Labels raw29182step4Labels labelEmbedding3 hl
    _ = mixedMoment B node4081 node4081Labels := by rfl

def raw29183 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29183Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29183step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29183step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, -1, 1], ![0, -3, 3]]
def raw29183step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29183step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw29183step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29183step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29183step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29183step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29183step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29183 raw29183Labels = mixedMoment B node4753 node4753Labels := by
  calc
    mixedMoment B raw29183 raw29183Labels = mixedMoment B raw29183step0 raw29183step0Labels := by
      have hz : ∀ j, raw29183 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29183step0 = (fun i j => raw29183 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29183step0 raw29183; decide +kernel
      have hl : raw29183step0Labels = raw29183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29183 raw29183Labels permutation434 hz
    mixedMoment B raw29183step0 raw29183step0Labels = mixedMoment B raw29183step1 raw29183step1Labels := by
      have hz : ∀ j, raw29183step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29183step1 = (fun i j => raw29183step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29183step1 raw29183step0; decide +kernel
      have hl : raw29183step1Labels = raw29183step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29183step0 raw29183step0Labels permutation80 hz
    mixedMoment B raw29183step1 raw29183step1Labels = mixedMoment B raw29183step2 raw29183step2Labels := by
      have ha : raw29183step2 = (fun i j => raw29183step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29183step2 raw29183step1; decide +kernel
      have hl : raw29183step2Labels = raw29183step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29183step1 raw29183step1Labels permutation31 permutation6
    mixedMoment B raw29183step2 raw29183step2Labels = mixedMoment B raw29183step3 raw29183step3Labels := by
      have ha : raw29183step3 = -raw29183step2 := by apply Matrix.ext; change ∀ i j, raw29183step3 i j = -(raw29183step2 i j); unfold raw29183step3 raw29183step2; decide +kernel
      have hl : raw29183step3Labels = raw29183step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29183step3 raw29183step3Labels = mixedMoment B raw29183step4 raw29183step4Labels := by
      have ha : raw29183step4 = raw29183step3 := by apply Matrix.ext; unfold raw29183step4 raw29183step3; decide +kernel
      have hl : raw29183step3Labels = labelEmbedding9 ∘ raw29183step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29183step3 raw29183step3Labels raw29183step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4753 node4753Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
