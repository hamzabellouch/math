import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw42624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw42624Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw42624step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw42624step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42624step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42624step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42624step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42624step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42624 raw42624Labels = mixedMoment B node1522 node1522Labels := by
  calc
    mixedMoment B raw42624 raw42624Labels = mixedMoment B raw42624step0 raw42624step0Labels := by
      have hz : ∀ j, raw42624 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42624step0 = (fun i j => raw42624 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42624step0 raw42624; decide +kernel
      have hl : raw42624step0Labels = raw42624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42624 raw42624Labels permutation346 hz
    mixedMoment B raw42624step0 raw42624step0Labels = mixedMoment B raw42624step1 raw42624step1Labels := by
      have ha : raw42624step1 = (fun i j => raw42624step0 (permutation133 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42624step1 raw42624step0; decide +kernel
      have hl : raw42624step1Labels = raw42624step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42624step0 raw42624step0Labels permutation133 permutation4
    mixedMoment B raw42624step1 raw42624step1Labels = mixedMoment B raw42624step2 raw42624step2Labels := by
      have ha : raw42624step2 = -raw42624step1 := by apply Matrix.ext; change ∀ i j, raw42624step2 i j = -(raw42624step1 i j); unfold raw42624step2 raw42624step1; decide +kernel
      have hl : raw42624step2Labels = raw42624step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42624step2 raw42624step2Labels = mixedMoment B raw42624step3 raw42624step3Labels := by
      have ha : raw42624step3 = raw42624step2 := by apply Matrix.ext; unfold raw42624step3 raw42624step2; decide +kernel
      have hl : raw42624step2Labels = labelEmbedding1 ∘ raw42624step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42624step2 raw42624step2Labels raw42624step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1522 node1522Labels := by rfl

def raw42625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw42625Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw42625step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw42625step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42625 raw42625Labels = mixedMoment B node4158 node4158Labels := by
  calc
    mixedMoment B raw42625 raw42625Labels = mixedMoment B raw42625step0 raw42625step0Labels := by
      have hz : ∀ j, raw42625 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42625step0 = (fun i j => raw42625 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42625step0 raw42625; decide +kernel
      have hl : raw42625step0Labels = raw42625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42625 raw42625Labels permutation346 hz
    mixedMoment B raw42625step0 raw42625step0Labels = mixedMoment B raw42625step1 raw42625step1Labels := by
      have ha : raw42625step1 = (fun i j => raw42625step0 (permutation150 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42625step1 raw42625step0; decide +kernel
      have hl : raw42625step1Labels = raw42625step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42625step0 raw42625step0Labels permutation150 permutation6
    _ = mixedMoment B node4158 node4158Labels := by rfl

def raw42626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw42626Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw42626step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw42626step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42626step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw42626step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42626step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw42626step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42626 raw42626Labels = mixedMoment B node1682 node1682Labels := by
  calc
    mixedMoment B raw42626 raw42626Labels = mixedMoment B raw42626step0 raw42626step0Labels := by
      have hz : ∀ j, raw42626 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42626step0 = (fun i j => raw42626 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42626step0 raw42626; decide +kernel
      have hl : raw42626step0Labels = raw42626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42626 raw42626Labels permutation346 hz
    mixedMoment B raw42626step0 raw42626step0Labels = mixedMoment B raw42626step1 raw42626step1Labels := by
      have ha : raw42626step1 = (fun i j => raw42626step0 (permutation92 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42626step1 raw42626step0; decide +kernel
      have hl : raw42626step1Labels = raw42626step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42626step0 raw42626step0Labels permutation92 permutation4
    mixedMoment B raw42626step1 raw42626step1Labels = mixedMoment B raw42626step2 raw42626step2Labels := by
      have ha : raw42626step2 = -raw42626step1 := by apply Matrix.ext; change ∀ i j, raw42626step2 i j = -(raw42626step1 i j); unfold raw42626step2 raw42626step1; decide +kernel
      have hl : raw42626step2Labels = raw42626step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42626step2 raw42626step2Labels = mixedMoment B raw42626step3 raw42626step3Labels := by
      have ha : raw42626step3 = raw42626step2 := by apply Matrix.ext; unfold raw42626step3 raw42626step2; decide +kernel
      have hl : raw42626step2Labels = labelEmbedding1 ∘ raw42626step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42626step2 raw42626step2Labels raw42626step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1682 node1682Labels := by rfl

def raw42627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw42627Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw42627step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42627step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw42627step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42627 raw42627Labels = mixedMoment B node4357 node4357Labels := by
  calc
    mixedMoment B raw42627 raw42627Labels = mixedMoment B raw42627step0 raw42627step0Labels := by
      have hz : ∀ j, raw42627 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42627step0 = (fun i j => raw42627 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42627step0 raw42627; decide +kernel
      have hl : raw42627step0Labels = raw42627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42627 raw42627Labels permutation346 hz
    mixedMoment B raw42627step0 raw42627step0Labels = mixedMoment B raw42627step1 raw42627step1Labels := by
      have ha : raw42627step1 = (fun i j => raw42627step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42627step1 raw42627step0; decide +kernel
      have hl : raw42627step1Labels = raw42627step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42627step0 raw42627step0Labels permutation96 permutation6
    _ = mixedMoment B node4357 node4357Labels := by rfl

def raw42628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw42628Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw42628step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42628step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw42628step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42628step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42628step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42628step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42628step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42628 raw42628Labels = mixedMoment B node1736 node1736Labels := by
  calc
    mixedMoment B raw42628 raw42628Labels = mixedMoment B raw42628step0 raw42628step0Labels := by
      have hz : ∀ j, raw42628 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42628step0 = (fun i j => raw42628 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42628step0 raw42628; decide +kernel
      have hl : raw42628step0Labels = raw42628Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42628 raw42628Labels permutation346 hz
    mixedMoment B raw42628step0 raw42628step0Labels = mixedMoment B raw42628step1 raw42628step1Labels := by
      have ha : raw42628step1 = (fun i j => raw42628step0 (permutation83 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42628step1 raw42628step0; decide +kernel
      have hl : raw42628step1Labels = raw42628step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42628step0 raw42628step0Labels permutation83 permutation4
    mixedMoment B raw42628step1 raw42628step1Labels = mixedMoment B raw42628step2 raw42628step2Labels := by
      have ha : raw42628step2 = -raw42628step1 := by apply Matrix.ext; change ∀ i j, raw42628step2 i j = -(raw42628step1 i j); unfold raw42628step2 raw42628step1; decide +kernel
      have hl : raw42628step2Labels = raw42628step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42628step2 raw42628step2Labels = mixedMoment B raw42628step3 raw42628step3Labels := by
      have ha : raw42628step3 = raw42628step2 := by apply Matrix.ext; unfold raw42628step3 raw42628step2; decide +kernel
      have hl : raw42628step2Labels = labelEmbedding1 ∘ raw42628step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42628step2 raw42628step2Labels raw42628step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1736 node1736Labels := by rfl

def raw42629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw42629Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw42629step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42629step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw42629step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42629 raw42629Labels = mixedMoment B node4444 node4444Labels := by
  calc
    mixedMoment B raw42629 raw42629Labels = mixedMoment B raw42629step0 raw42629step0Labels := by
      have hz : ∀ j, raw42629 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42629step0 = (fun i j => raw42629 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42629step0 raw42629; decide +kernel
      have hl : raw42629step0Labels = raw42629Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42629 raw42629Labels permutation346 hz
    mixedMoment B raw42629step0 raw42629step0Labels = mixedMoment B raw42629step1 raw42629step1Labels := by
      have ha : raw42629step1 = (fun i j => raw42629step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42629step1 raw42629step0; decide +kernel
      have hl : raw42629step1Labels = raw42629step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42629step0 raw42629step0Labels permutation96 permutation6
    _ = mixedMoment B node4444 node4444Labels := by rfl

def raw42630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw42630Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw42630step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw42630step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42630step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw42630step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42630step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw42630step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42630 raw42630Labels = mixedMoment B node3418 node3418Labels := by
  calc
    mixedMoment B raw42630 raw42630Labels = mixedMoment B raw42630step0 raw42630step0Labels := by
      have hz : ∀ j, raw42630 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42630step0 = (fun i j => raw42630 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42630step0 raw42630; decide +kernel
      have hl : raw42630step0Labels = raw42630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42630 raw42630Labels permutation346 hz
    mixedMoment B raw42630step0 raw42630step0Labels = mixedMoment B raw42630step1 raw42630step1Labels := by
      have ha : raw42630step1 = (fun i j => raw42630step0 (permutation92 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42630step1 raw42630step0; decide +kernel
      have hl : raw42630step1Labels = raw42630step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42630step0 raw42630step0Labels permutation92 permutation4
    mixedMoment B raw42630step1 raw42630step1Labels = mixedMoment B raw42630step2 raw42630step2Labels := by
      have ha : raw42630step2 = -raw42630step1 := by apply Matrix.ext; change ∀ i j, raw42630step2 i j = -(raw42630step1 i j); unfold raw42630step2 raw42630step1; decide +kernel
      have hl : raw42630step2Labels = raw42630step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42630step2 raw42630step2Labels = mixedMoment B raw42630step3 raw42630step3Labels := by
      have ha : raw42630step3 = raw42630step2 := by apply Matrix.ext; unfold raw42630step3 raw42630step2; decide +kernel
      have hl : raw42630step2Labels = labelEmbedding1 ∘ raw42630step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42630step2 raw42630step2Labels raw42630step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3418 node3418Labels := by rfl

def raw42631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw42631Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw42631step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42631step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw42631step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42631 raw42631Labels = mixedMoment B node4951 node4951Labels := by
  calc
    mixedMoment B raw42631 raw42631Labels = mixedMoment B raw42631step0 raw42631step0Labels := by
      have hz : ∀ j, raw42631 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42631step0 = (fun i j => raw42631 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42631step0 raw42631; decide +kernel
      have hl : raw42631step0Labels = raw42631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42631 raw42631Labels permutation346 hz
    mixedMoment B raw42631step0 raw42631step0Labels = mixedMoment B raw42631step1 raw42631step1Labels := by
      have ha : raw42631step1 = (fun i j => raw42631step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42631step1 raw42631step0; decide +kernel
      have hl : raw42631step1Labels = raw42631step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42631step0 raw42631step0Labels permutation96 permutation6
    _ = mixedMoment B node4951 node4951Labels := by rfl

def raw42632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42632Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw42632step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42632step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42632step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42632step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42632step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42632 raw42632Labels = mixedMoment B node1678 node1678Labels := by
  calc
    mixedMoment B raw42632 raw42632Labels = mixedMoment B raw42632step0 raw42632step0Labels := by
      have ha : raw42632step0 = (fun i j => raw42632 (permutation488 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42632step0 raw42632; decide +kernel
      have hl : raw42632step0Labels = raw42632Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42632 raw42632Labels permutation488 permutation4
    mixedMoment B raw42632step0 raw42632step0Labels = mixedMoment B raw42632step1 raw42632step1Labels := by
      have ha : raw42632step1 = -raw42632step0 := by apply Matrix.ext; change ∀ i j, raw42632step1 i j = -(raw42632step0 i j); unfold raw42632step1 raw42632step0; decide +kernel
      have hl : raw42632step1Labels = raw42632step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42632step1 raw42632step1Labels = mixedMoment B raw42632step2 raw42632step2Labels := by
      have ha : raw42632step2 = raw42632step1 := by apply Matrix.ext; unfold raw42632step2 raw42632step1; decide +kernel
      have hl : raw42632step1Labels = labelEmbedding1 ∘ raw42632step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42632step1 raw42632step1Labels raw42632step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1678 node1678Labels := by rfl

def raw42633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42633Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42633step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw42633step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42633 raw42633Labels = mixedMoment B node4332 node4332Labels := by
  calc
    mixedMoment B raw42633 raw42633Labels = mixedMoment B raw42633step0 raw42633step0Labels := by
      have ha : raw42633step0 = (fun i j => raw42633 (permutation503 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42633step0 raw42633; decide +kernel
      have hl : raw42633step0Labels = raw42633Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42633 raw42633Labels permutation503 permutation6
    _ = mixedMoment B node4332 node4332Labels := by rfl

def raw42634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42634Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42634step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw42634step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42634step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42634step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42634step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42634step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42634 raw42634Labels = mixedMoment B node3414 node3414Labels := by
  calc
    mixedMoment B raw42634 raw42634Labels = mixedMoment B raw42634step0 raw42634step0Labels := by
      have ha : raw42634step0 = (fun i j => raw42634 (permutation488 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42634step0 raw42634; decide +kernel
      have hl : raw42634step0Labels = raw42634Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42634 raw42634Labels permutation488 permutation4
    mixedMoment B raw42634step0 raw42634step0Labels = mixedMoment B raw42634step1 raw42634step1Labels := by
      have ha : raw42634step1 = -raw42634step0 := by apply Matrix.ext; change ∀ i j, raw42634step1 i j = -(raw42634step0 i j); unfold raw42634step1 raw42634step0; decide +kernel
      have hl : raw42634step1Labels = raw42634step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42634step1 raw42634step1Labels = mixedMoment B raw42634step2 raw42634step2Labels := by
      have ha : raw42634step2 = raw42634step1 := by apply Matrix.ext; unfold raw42634step2 raw42634step1; decide +kernel
      have hl : raw42634step1Labels = labelEmbedding1 ∘ raw42634step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42634step1 raw42634step1Labels raw42634step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3414 node3414Labels := by rfl

def raw42635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42635Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42635step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw42635step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42635 raw42635Labels = mixedMoment B node4933 node4933Labels := by
  calc
    mixedMoment B raw42635 raw42635Labels = mixedMoment B raw42635step0 raw42635step0Labels := by
      have ha : raw42635step0 = (fun i j => raw42635 (permutation503 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42635step0 raw42635; decide +kernel
      have hl : raw42635step0Labels = raw42635Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42635 raw42635Labels permutation503 permutation6
    _ = mixedMoment B node4933 node4933Labels := by rfl

def raw42636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42636Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw42636step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42636step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw42636step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42636step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42636step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42636step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42636step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42636 raw42636Labels = mixedMoment B node2155 node2155Labels := by
  calc
    mixedMoment B raw42636 raw42636Labels = mixedMoment B raw42636step0 raw42636step0Labels := by
      have hz : ∀ j, raw42636 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42636step0 = (fun i j => raw42636 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42636step0 raw42636; decide +kernel
      have hl : raw42636step0Labels = raw42636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42636 raw42636Labels permutation434 hz
    mixedMoment B raw42636step0 raw42636step0Labels = mixedMoment B raw42636step1 raw42636step1Labels := by
      have ha : raw42636step1 = (fun i j => raw42636step0 (permutation99 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42636step1 raw42636step0; decide +kernel
      have hl : raw42636step1Labels = raw42636step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42636step0 raw42636step0Labels permutation99 permutation4
    mixedMoment B raw42636step1 raw42636step1Labels = mixedMoment B raw42636step2 raw42636step2Labels := by
      have ha : raw42636step2 = -raw42636step1 := by apply Matrix.ext; change ∀ i j, raw42636step2 i j = -(raw42636step1 i j); unfold raw42636step2 raw42636step1; decide +kernel
      have hl : raw42636step2Labels = raw42636step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42636step2 raw42636step2Labels = mixedMoment B raw42636step3 raw42636step3Labels := by
      have ha : raw42636step3 = raw42636step2 := by apply Matrix.ext; unfold raw42636step3 raw42636step2; decide +kernel
      have hl : raw42636step2Labels = labelEmbedding1 ∘ raw42636step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42636step2 raw42636step2Labels raw42636step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2155 node2155Labels := by rfl

def raw42637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42637Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw42637step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw42637step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42637 raw42637Labels = mixedMoment B node4669 node4669Labels := by
  calc
    mixedMoment B raw42637 raw42637Labels = mixedMoment B raw42637step0 raw42637step0Labels := by
      have hz : ∀ j, raw42637 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42637step0 = (fun i j => raw42637 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42637step0 raw42637; decide +kernel
      have hl : raw42637step0Labels = raw42637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42637 raw42637Labels permutation434 hz
    mixedMoment B raw42637step0 raw42637step0Labels = mixedMoment B raw42637step1 raw42637step1Labels := by
      have ha : raw42637step1 = (fun i j => raw42637step0 (permutation102 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42637step1 raw42637step0; decide +kernel
      have hl : raw42637step1Labels = raw42637step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42637step0 raw42637step0Labels permutation102 permutation6
    _ = mixedMoment B node4669 node4669Labels := by rfl

def raw42638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42638Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42638step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw42638step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42638step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42638step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42638step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42638step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42638 raw42638Labels = mixedMoment B node2176 node2176Labels := by
  calc
    mixedMoment B raw42638 raw42638Labels = mixedMoment B raw42638step0 raw42638step0Labels := by
      have ha : raw42638step0 = (fun i j => raw42638 (permutation390 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42638step0 raw42638; decide +kernel
      have hl : raw42638step0Labels = raw42638Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42638 raw42638Labels permutation390 permutation4
    mixedMoment B raw42638step0 raw42638step0Labels = mixedMoment B raw42638step1 raw42638step1Labels := by
      have ha : raw42638step1 = -raw42638step0 := by apply Matrix.ext; change ∀ i j, raw42638step1 i j = -(raw42638step0 i j); unfold raw42638step1 raw42638step0; decide +kernel
      have hl : raw42638step1Labels = raw42638step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42638step1 raw42638step1Labels = mixedMoment B raw42638step2 raw42638step2Labels := by
      have ha : raw42638step2 = raw42638step1 := by apply Matrix.ext; unfold raw42638step2 raw42638step1; decide +kernel
      have hl : raw42638step1Labels = labelEmbedding1 ∘ raw42638step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42638step1 raw42638step1Labels raw42638step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2176 node2176Labels := by rfl

def raw42639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42639Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42639step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw42639step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42639 raw42639Labels = mixedMoment B node4756 node4756Labels := by
  calc
    mixedMoment B raw42639 raw42639Labels = mixedMoment B raw42639step0 raw42639step0Labels := by
      have ha : raw42639step0 = (fun i j => raw42639 (permutation393 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42639step0 raw42639; decide +kernel
      have hl : raw42639step0Labels = raw42639Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42639 raw42639Labels permutation393 permutation6
    _ = mixedMoment B node4756 node4756Labels := by rfl

def raw42640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42640Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42640step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw42640step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42640step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw42640step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42640 raw42640Labels = mixedMoment B node3509 node3509Labels := by
  calc
    mixedMoment B raw42640 raw42640Labels = mixedMoment B raw42640step0 raw42640step0Labels := by
      have ha : raw42640step0 = (fun i j => raw42640 (permutation325 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42640step0 raw42640; decide +kernel
      have hl : raw42640step0Labels = raw42640Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42640 raw42640Labels permutation325 permutation4
    mixedMoment B raw42640step0 raw42640step0Labels = mixedMoment B raw42640step1 raw42640step1Labels := by
      have ha : raw42640step1 = raw42640step0 := by apply Matrix.ext; unfold raw42640step1 raw42640step0; decide +kernel
      have hl : raw42640step0Labels = labelEmbedding1 ∘ raw42640step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42640step0 raw42640step0Labels raw42640step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3509 node3509Labels := by rfl

def raw42641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42641Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42641step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw42641step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42641step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw42641step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42641 raw42641Labels = mixedMoment B node4957 node4957Labels := by
  calc
    mixedMoment B raw42641 raw42641Labels = mixedMoment B raw42641step0 raw42641step0Labels := by
      have ha : raw42641step0 = (fun i j => raw42641 (permutation280 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42641step0 raw42641; decide +kernel
      have hl : raw42641step0Labels = raw42641Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42641 raw42641Labels permutation280 permutation6
    mixedMoment B raw42641step0 raw42641step0Labels = mixedMoment B raw42641step1 raw42641step1Labels := by
      have ha : raw42641step1 = -raw42641step0 := by apply Matrix.ext; change ∀ i j, raw42641step1 i j = -(raw42641step0 i j); unfold raw42641step1 raw42641step0; decide +kernel
      have hl : raw42641step1Labels = raw42641step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4957 node4957Labels := by rfl

def raw42642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42642Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42642step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![-1, -2, 3], ![-2, 0, 2]]
def raw42642step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42642step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw42642step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42642step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw42642step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42642 raw42642Labels = mixedMoment B node3512 node3512Labels := by
  calc
    mixedMoment B raw42642 raw42642Labels = mixedMoment B raw42642step0 raw42642step0Labels := by
      have hz : ∀ j, raw42642 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42642step0 = (fun i j => raw42642 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42642step0 raw42642; decide +kernel
      have hl : raw42642step0Labels = raw42642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42642 raw42642Labels permutation434 hz
    mixedMoment B raw42642step0 raw42642step0Labels = mixedMoment B raw42642step1 raw42642step1Labels := by
      have ha : raw42642step1 = (fun i j => raw42642step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42642step1 raw42642step0; decide +kernel
      have hl : raw42642step1Labels = raw42642step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42642step0 raw42642step0Labels permutation151 permutation2
    mixedMoment B raw42642step1 raw42642step1Labels = mixedMoment B raw42642step2 raw42642step2Labels := by
      have ha : raw42642step2 = -raw42642step1 := by apply Matrix.ext; change ∀ i j, raw42642step2 i j = -(raw42642step1 i j); unfold raw42642step2 raw42642step1; decide +kernel
      have hl : raw42642step2Labels = raw42642step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42642step2 raw42642step2Labels = mixedMoment B raw42642step3 raw42642step3Labels := by
      have ha : raw42642step3 = raw42642step2 := by apply Matrix.ext; unfold raw42642step3 raw42642step2; decide +kernel
      have hl : raw42642step2Labels = labelEmbedding1 ∘ raw42642step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42642step2 raw42642step2Labels raw42642step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3512 node3512Labels := by rfl

def raw42643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42643Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42643step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42643step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw42643step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42643step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw42643step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42643 raw42643Labels = mixedMoment B node4959 node4959Labels := by
  calc
    mixedMoment B raw42643 raw42643Labels = mixedMoment B raw42643step0 raw42643step0Labels := by
      have hz : ∀ j, raw42643 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42643step0 = (fun i j => raw42643 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42643step0 raw42643; decide +kernel
      have hl : raw42643step0Labels = raw42643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42643 raw42643Labels permutation434 hz
    mixedMoment B raw42643step0 raw42643step0Labels = mixedMoment B raw42643step1 raw42643step1Labels := by
      have ha : raw42643step1 = (fun i j => raw42643step0 (permutation58 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42643step1 raw42643step0; decide +kernel
      have hl : raw42643step1Labels = raw42643step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42643step0 raw42643step0Labels permutation58 permutation6
    mixedMoment B raw42643step1 raw42643step1Labels = mixedMoment B raw42643step2 raw42643step2Labels := by
      have ha : raw42643step2 = -raw42643step1 := by apply Matrix.ext; change ∀ i j, raw42643step2 i j = -(raw42643step1 i j); unfold raw42643step2 raw42643step1; decide +kernel
      have hl : raw42643step2Labels = raw42643step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4959 node4959Labels := by rfl

def raw42644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42644Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw42644step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42644step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw42644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42644 raw42644Labels = mixedMoment B node3508 node3508Labels := by
  calc
    mixedMoment B raw42644 raw42644Labels = mixedMoment B raw42644step0 raw42644step0Labels := by
      have ha : raw42644step0 = (fun i j => raw42644 (permutation338 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42644step0 raw42644; decide +kernel
      have hl : raw42644step0Labels = raw42644Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42644 raw42644Labels permutation338 permutation4
    mixedMoment B raw42644step0 raw42644step0Labels = mixedMoment B raw42644step1 raw42644step1Labels := by
      have ha : raw42644step1 = raw42644step0 := by apply Matrix.ext; unfold raw42644step1 raw42644step0; decide +kernel
      have hl : raw42644step0Labels = labelEmbedding1 ∘ raw42644step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42644step0 raw42644step0Labels raw42644step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3508 node3508Labels := by rfl

def raw42645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42645Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42645step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw42645step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42645step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw42645step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42645 raw42645Labels = mixedMoment B node4955 node4955Labels := by
  calc
    mixedMoment B raw42645 raw42645Labels = mixedMoment B raw42645step0 raw42645step0Labels := by
      have ha : raw42645step0 = (fun i j => raw42645 (permutation288 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42645step0 raw42645; decide +kernel
      have hl : raw42645step0Labels = raw42645Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42645 raw42645Labels permutation288 permutation6
    mixedMoment B raw42645step0 raw42645step0Labels = mixedMoment B raw42645step1 raw42645step1Labels := by
      have ha : raw42645step1 = -raw42645step0 := by apply Matrix.ext; change ∀ i j, raw42645step1 i j = -(raw42645step0 i j); unfold raw42645step1 raw42645step0; decide +kernel
      have hl : raw42645step1Labels = raw42645step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4955 node4955Labels := by rfl

def raw42646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42646Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw42646step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42646step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw42646step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42646 raw42646Labels = mixedMoment B node3510 node3510Labels := by
  calc
    mixedMoment B raw42646 raw42646Labels = mixedMoment B raw42646step0 raw42646step0Labels := by
      have ha : raw42646step0 = (fun i j => raw42646 (permutation322 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42646step0 raw42646; decide +kernel
      have hl : raw42646step0Labels = raw42646Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42646 raw42646Labels permutation322 permutation4
    mixedMoment B raw42646step0 raw42646step0Labels = mixedMoment B raw42646step1 raw42646step1Labels := by
      have ha : raw42646step1 = raw42646step0 := by apply Matrix.ext; unfold raw42646step1 raw42646step0; decide +kernel
      have hl : raw42646step0Labels = labelEmbedding1 ∘ raw42646step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42646step0 raw42646step0Labels raw42646step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3510 node3510Labels := by rfl

def raw42647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42647Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42647step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw42647step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42647step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw42647step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42647 raw42647Labels = mixedMoment B node4956 node4956Labels := by
  calc
    mixedMoment B raw42647 raw42647Labels = mixedMoment B raw42647step0 raw42647step0Labels := by
      have ha : raw42647step0 = (fun i j => raw42647 (permutation277 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42647step0 raw42647; decide +kernel
      have hl : raw42647step0Labels = raw42647Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42647 raw42647Labels permutation277 permutation6
    mixedMoment B raw42647step0 raw42647step0Labels = mixedMoment B raw42647step1 raw42647step1Labels := by
      have ha : raw42647step1 = -raw42647step0 := by apply Matrix.ext; change ∀ i j, raw42647step1 i j = -(raw42647step0 i j); unfold raw42647step1 raw42647step0; decide +kernel
      have hl : raw42647step1Labels = raw42647step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4956 node4956Labels := by rfl

def raw42648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42648Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw42648step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42648step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw42648step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42648step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42648step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42648step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42648step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42648 raw42648Labels = mixedMoment B node3268 node3268Labels := by
  calc
    mixedMoment B raw42648 raw42648Labels = mixedMoment B raw42648step0 raw42648step0Labels := by
      have hz : ∀ j, raw42648 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42648step0 = (fun i j => raw42648 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42648step0 raw42648; decide +kernel
      have hl : raw42648step0Labels = raw42648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42648 raw42648Labels permutation434 hz
    mixedMoment B raw42648step0 raw42648step0Labels = mixedMoment B raw42648step1 raw42648step1Labels := by
      have ha : raw42648step1 = (fun i j => raw42648step0 (permutation141 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42648step1 raw42648step0; decide +kernel
      have hl : raw42648step1Labels = raw42648step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42648step0 raw42648step0Labels permutation141 permutation4
    mixedMoment B raw42648step1 raw42648step1Labels = mixedMoment B raw42648step2 raw42648step2Labels := by
      have ha : raw42648step2 = -raw42648step1 := by apply Matrix.ext; change ∀ i j, raw42648step2 i j = -(raw42648step1 i j); unfold raw42648step2 raw42648step1; decide +kernel
      have hl : raw42648step2Labels = raw42648step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42648step2 raw42648step2Labels = mixedMoment B raw42648step3 raw42648step3Labels := by
      have ha : raw42648step3 = raw42648step2 := by apply Matrix.ext; unfold raw42648step3 raw42648step2; decide +kernel
      have hl : raw42648step2Labels = labelEmbedding1 ∘ raw42648step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42648step2 raw42648step2Labels raw42648step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3268 node3268Labels := by rfl

def raw42649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42649Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw42649step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw42649step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42649 raw42649Labels = mixedMoment B node4534 node4534Labels := by
  calc
    mixedMoment B raw42649 raw42649Labels = mixedMoment B raw42649step0 raw42649step0Labels := by
      have hz : ∀ j, raw42649 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42649step0 = (fun i j => raw42649 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42649step0 raw42649; decide +kernel
      have hl : raw42649step0Labels = raw42649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42649 raw42649Labels permutation434 hz
    mixedMoment B raw42649step0 raw42649step0Labels = mixedMoment B raw42649step1 raw42649step1Labels := by
      have ha : raw42649step1 = (fun i j => raw42649step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42649step1 raw42649step0; decide +kernel
      have hl : raw42649step1Labels = raw42649step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42649step0 raw42649step0Labels permutation144 permutation6
    _ = mixedMoment B node4534 node4534Labels := by rfl

def raw42650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42650Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw42650step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42650step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42650step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42650step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42650step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42650 raw42650Labels = mixedMoment B node3452 node3452Labels := by
  calc
    mixedMoment B raw42650 raw42650Labels = mixedMoment B raw42650step0 raw42650step0Labels := by
      have ha : raw42650step0 = (fun i j => raw42650 (permutation476 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42650step0 raw42650; decide +kernel
      have hl : raw42650step0Labels = raw42650Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42650 raw42650Labels permutation476 permutation4
    mixedMoment B raw42650step0 raw42650step0Labels = mixedMoment B raw42650step1 raw42650step1Labels := by
      have ha : raw42650step1 = -raw42650step0 := by apply Matrix.ext; change ∀ i j, raw42650step1 i j = -(raw42650step0 i j); unfold raw42650step1 raw42650step0; decide +kernel
      have hl : raw42650step1Labels = raw42650step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42650step1 raw42650step1Labels = mixedMoment B raw42650step2 raw42650step2Labels := by
      have ha : raw42650step2 = raw42650step1 := by apply Matrix.ext; unfold raw42650step2 raw42650step1; decide +kernel
      have hl : raw42650step1Labels = labelEmbedding1 ∘ raw42650step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42650step1 raw42650step1Labels raw42650step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3452 node3452Labels := by rfl

def raw42651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42651Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw42651step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42651step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw42651step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42651 raw42651Labels = mixedMoment B node4954 node4954Labels := by
  calc
    mixedMoment B raw42651 raw42651Labels = mixedMoment B raw42651step0 raw42651step0Labels := by
      have ha : raw42651step0 = (fun i j => raw42651 (permutation287 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42651step0 raw42651; decide +kernel
      have hl : raw42651step0Labels = raw42651Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42651 raw42651Labels permutation287 permutation6
    mixedMoment B raw42651step0 raw42651step0Labels = mixedMoment B raw42651step1 raw42651step1Labels := by
      have ha : raw42651step1 = -raw42651step0 := by apply Matrix.ext; change ∀ i j, raw42651step1 i j = -(raw42651step0 i j); unfold raw42651step1 raw42651step0; decide +kernel
      have hl : raw42651step1Labels = raw42651step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4954 node4954Labels := by rfl

def raw42652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw42652Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42652step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw42652step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42652step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw42652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42652 raw42652Labels = mixedMoment B node3511 node3511Labels := by
  calc
    mixedMoment B raw42652 raw42652Labels = mixedMoment B raw42652step0 raw42652step0Labels := by
      have ha : raw42652step0 = (fun i j => raw42652 (permutation333 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42652step0 raw42652; decide +kernel
      have hl : raw42652step0Labels = raw42652Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42652 raw42652Labels permutation333 permutation4
    mixedMoment B raw42652step0 raw42652step0Labels = mixedMoment B raw42652step1 raw42652step1Labels := by
      have ha : raw42652step1 = raw42652step0 := by apply Matrix.ext; unfold raw42652step1 raw42652step0; decide +kernel
      have hl : raw42652step0Labels = labelEmbedding1 ∘ raw42652step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42652step0 raw42652step0Labels raw42652step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3511 node3511Labels := by rfl

def raw42653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw42653Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw42653step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42653step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw42653step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42653 raw42653Labels = mixedMoment B node4958 node4958Labels := by
  calc
    mixedMoment B raw42653 raw42653Labels = mixedMoment B raw42653step0 raw42653step0Labels := by
      have ha : raw42653step0 = (fun i j => raw42653 (permutation283 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42653step0 raw42653; decide +kernel
      have hl : raw42653step0Labels = raw42653Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42653 raw42653Labels permutation283 permutation6
    mixedMoment B raw42653step0 raw42653step0Labels = mixedMoment B raw42653step1 raw42653step1Labels := by
      have ha : raw42653step1 = -raw42653step0 := by apply Matrix.ext; change ∀ i j, raw42653step1 i j = -(raw42653step0 i j); unfold raw42653step1 raw42653step0; decide +kernel
      have hl : raw42653step1Labels = raw42653step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4958 node4958Labels := by rfl

def raw42654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw42654Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw42654step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42654step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![1, -1, 0], ![2, 3, -5]]
def raw42654step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42654step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw42654step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42654step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42654step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42654step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42654step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42654 raw42654Labels = mixedMoment B node1523 node1523Labels := by
  calc
    mixedMoment B raw42654 raw42654Labels = mixedMoment B raw42654step0 raw42654step0Labels := by
      have hz : ∀ j, raw42654 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42654step0 = (fun i j => raw42654 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42654step0 raw42654; decide +kernel
      have hl : raw42654step0Labels = raw42654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42654 raw42654Labels permutation434 hz
    mixedMoment B raw42654step0 raw42654step0Labels = mixedMoment B raw42654step1 raw42654step1Labels := by
      have hz : ∀ j, raw42654step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42654step1 = (fun i j => raw42654step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42654step1 raw42654step0; decide +kernel
      have hl : raw42654step1Labels = raw42654step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42654step0 raw42654step0Labels permutation80 hz
    mixedMoment B raw42654step1 raw42654step1Labels = mixedMoment B raw42654step2 raw42654step2Labels := by
      have ha : raw42654step2 = (fun i j => raw42654step1 (permutation27 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42654step2 raw42654step1; decide +kernel
      have hl : raw42654step2Labels = raw42654step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42654step1 raw42654step1Labels permutation27 permutation4
    mixedMoment B raw42654step2 raw42654step2Labels = mixedMoment B raw42654step3 raw42654step3Labels := by
      have ha : raw42654step3 = -raw42654step2 := by apply Matrix.ext; change ∀ i j, raw42654step3 i j = -(raw42654step2 i j); unfold raw42654step3 raw42654step2; decide +kernel
      have hl : raw42654step3Labels = raw42654step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42654step3 raw42654step3Labels = mixedMoment B raw42654step4 raw42654step4Labels := by
      have ha : raw42654step4 = raw42654step3 := by apply Matrix.ext; unfold raw42654step4 raw42654step3; decide +kernel
      have hl : raw42654step3Labels = labelEmbedding1 ∘ raw42654step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42654step3 raw42654step3Labels raw42654step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1523 node1523Labels := by rfl

def raw42655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw42655Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw42655step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42655step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![1, -1, 0], ![2, 3, -5]]
def raw42655step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42655step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw42655step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42655 raw42655Labels = mixedMoment B node4160 node4160Labels := by
  calc
    mixedMoment B raw42655 raw42655Labels = mixedMoment B raw42655step0 raw42655step0Labels := by
      have hz : ∀ j, raw42655 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42655step0 = (fun i j => raw42655 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42655step0 raw42655; decide +kernel
      have hl : raw42655step0Labels = raw42655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42655 raw42655Labels permutation434 hz
    mixedMoment B raw42655step0 raw42655step0Labels = mixedMoment B raw42655step1 raw42655step1Labels := by
      have hz : ∀ j, raw42655step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42655step1 = (fun i j => raw42655step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42655step1 raw42655step0; decide +kernel
      have hl : raw42655step1Labels = raw42655step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42655step0 raw42655step0Labels permutation80 hz
    mixedMoment B raw42655step1 raw42655step1Labels = mixedMoment B raw42655step2 raw42655step2Labels := by
      have ha : raw42655step2 = (fun i j => raw42655step1 (permutation30 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42655step2 raw42655step1; decide +kernel
      have hl : raw42655step2Labels = raw42655step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42655step1 raw42655step1Labels permutation30 permutation6
    _ = mixedMoment B node4160 node4160Labels := by rfl

def raw42656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42656Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42656step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42656step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw42656step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42656step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42656step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42656step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42656step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42656 raw42656Labels = mixedMoment B node1679 node1679Labels := by
  calc
    mixedMoment B raw42656 raw42656Labels = mixedMoment B raw42656step0 raw42656step0Labels := by
      have hz : ∀ j, raw42656 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42656step0 = (fun i j => raw42656 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42656step0 raw42656; decide +kernel
      have hl : raw42656step0Labels = raw42656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42656 raw42656Labels permutation346 hz
    mixedMoment B raw42656step0 raw42656step0Labels = mixedMoment B raw42656step1 raw42656step1Labels := by
      have ha : raw42656step1 = (fun i j => raw42656step0 (permutation93 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42656step1 raw42656step0; decide +kernel
      have hl : raw42656step1Labels = raw42656step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42656step0 raw42656step0Labels permutation93 permutation4
    mixedMoment B raw42656step1 raw42656step1Labels = mixedMoment B raw42656step2 raw42656step2Labels := by
      have ha : raw42656step2 = -raw42656step1 := by apply Matrix.ext; change ∀ i j, raw42656step2 i j = -(raw42656step1 i j); unfold raw42656step2 raw42656step1; decide +kernel
      have hl : raw42656step2Labels = raw42656step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42656step2 raw42656step2Labels = mixedMoment B raw42656step3 raw42656step3Labels := by
      have ha : raw42656step3 = raw42656step2 := by apply Matrix.ext; unfold raw42656step3 raw42656step2; decide +kernel
      have hl : raw42656step2Labels = labelEmbedding1 ∘ raw42656step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42656step2 raw42656step2Labels raw42656step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1679 node1679Labels := by rfl

def raw42657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 0, 0], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42657Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42657step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw42657step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42657 raw42657Labels = mixedMoment B node4334 node4334Labels := by
  calc
    mixedMoment B raw42657 raw42657Labels = mixedMoment B raw42657step0 raw42657step0Labels := by
      have hz : ∀ j, raw42657 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42657step0 = (fun i j => raw42657 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42657step0 raw42657; decide +kernel
      have hl : raw42657step0Labels = raw42657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42657 raw42657Labels permutation346 hz
    mixedMoment B raw42657step0 raw42657step0Labels = mixedMoment B raw42657step1 raw42657step1Labels := by
      have ha : raw42657step1 = (fun i j => raw42657step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42657step1 raw42657step0; decide +kernel
      have hl : raw42657step1Labels = raw42657step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42657step0 raw42657step0Labels permutation96 permutation6
    _ = mixedMoment B node4334 node4334Labels := by rfl

def raw42658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42658Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42658step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw42658step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42658step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42658step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42658step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw42658step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42658 raw42658Labels = mixedMoment B node3415 node3415Labels := by
  calc
    mixedMoment B raw42658 raw42658Labels = mixedMoment B raw42658step0 raw42658step0Labels := by
      have hz : ∀ j, raw42658 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42658step0 = (fun i j => raw42658 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42658step0 raw42658; decide +kernel
      have hl : raw42658step0Labels = raw42658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42658 raw42658Labels permutation346 hz
    mixedMoment B raw42658step0 raw42658step0Labels = mixedMoment B raw42658step1 raw42658step1Labels := by
      have ha : raw42658step1 = (fun i j => raw42658step0 (permutation93 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42658step1 raw42658step0; decide +kernel
      have hl : raw42658step1Labels = raw42658step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42658step0 raw42658step0Labels permutation93 permutation4
    mixedMoment B raw42658step1 raw42658step1Labels = mixedMoment B raw42658step2 raw42658step2Labels := by
      have ha : raw42658step2 = -raw42658step1 := by apply Matrix.ext; change ∀ i j, raw42658step2 i j = -(raw42658step1 i j); unfold raw42658step2 raw42658step1; decide +kernel
      have hl : raw42658step2Labels = raw42658step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42658step2 raw42658step2Labels = mixedMoment B raw42658step3 raw42658step3Labels := by
      have ha : raw42658step3 = raw42658step2 := by apply Matrix.ext; unfold raw42658step3 raw42658step2; decide +kernel
      have hl : raw42658step2Labels = labelEmbedding1 ∘ raw42658step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42658step2 raw42658step2Labels raw42658step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3415 node3415Labels := by rfl

def raw42659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42659Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42659step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42659step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw42659step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42659 raw42659Labels = mixedMoment B node4934 node4934Labels := by
  calc
    mixedMoment B raw42659 raw42659Labels = mixedMoment B raw42659step0 raw42659step0Labels := by
      have hz : ∀ j, raw42659 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42659step0 = (fun i j => raw42659 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42659step0 raw42659; decide +kernel
      have hl : raw42659step0Labels = raw42659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42659 raw42659Labels permutation346 hz
    mixedMoment B raw42659step0 raw42659step0Labels = mixedMoment B raw42659step1 raw42659step1Labels := by
      have ha : raw42659step1 = (fun i j => raw42659step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42659step1 raw42659step0; decide +kernel
      have hl : raw42659step1Labels = raw42659step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42659step0 raw42659step0Labels permutation96 permutation6
    _ = mixedMoment B node4934 node4934Labels := by rfl

def raw42660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42660Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42660step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42660step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42660step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42660step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -2, 3], ![-2, 2, 0]]
def raw42660step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42660step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42660step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42660step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42660step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42660 raw42660Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw42660 raw42660Labels = mixedMoment B raw42660step0 raw42660step0Labels := by
      have hz : ∀ j, raw42660 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42660step0 = (fun i j => raw42660 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42660step0 raw42660; decide +kernel
      have hl : raw42660step0Labels = raw42660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42660 raw42660Labels permutation434 hz
    mixedMoment B raw42660step0 raw42660step0Labels = mixedMoment B raw42660step1 raw42660step1Labels := by
      have hz : ∀ j, raw42660step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42660step1 = (fun i j => raw42660step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42660step1 raw42660step0; decide +kernel
      have hl : raw42660step1Labels = raw42660step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42660step0 raw42660step0Labels permutation80 hz
    mixedMoment B raw42660step1 raw42660step1Labels = mixedMoment B raw42660step2 raw42660step2Labels := by
      have ha : raw42660step2 = (fun i j => raw42660step1 (permutation16 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42660step2 raw42660step1; decide +kernel
      have hl : raw42660step2Labels = raw42660step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42660step1 raw42660step1Labels permutation16 permutation4
    mixedMoment B raw42660step2 raw42660step2Labels = mixedMoment B raw42660step3 raw42660step3Labels := by
      have ha : raw42660step3 = -raw42660step2 := by apply Matrix.ext; change ∀ i j, raw42660step3 i j = -(raw42660step2 i j); unfold raw42660step3 raw42660step2; decide +kernel
      have hl : raw42660step3Labels = raw42660step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42660step3 raw42660step3Labels = mixedMoment B raw42660step4 raw42660step4Labels := by
      have ha : raw42660step4 = raw42660step3 := by apply Matrix.ext; unfold raw42660step4 raw42660step3; decide +kernel
      have hl : raw42660step3Labels = labelEmbedding1 ∘ raw42660step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42660step3 raw42660step3Labels raw42660step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2744 node2744Labels := by rfl

def raw42661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42661Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42661step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42661step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42661step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42661step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -2, 3], ![-2, 2, 0]]
def raw42661step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42661step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42661step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42661step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42661step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42661 raw42661Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw42661 raw42661Labels = mixedMoment B raw42661step0 raw42661step0Labels := by
      have hz : ∀ j, raw42661 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42661step0 = (fun i j => raw42661 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42661step0 raw42661; decide +kernel
      have hl : raw42661step0Labels = raw42661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42661 raw42661Labels permutation434 hz
    mixedMoment B raw42661step0 raw42661step0Labels = mixedMoment B raw42661step1 raw42661step1Labels := by
      have hz : ∀ j, raw42661step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42661step1 = (fun i j => raw42661step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42661step1 raw42661step0; decide +kernel
      have hl : raw42661step1Labels = raw42661step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42661step0 raw42661step0Labels permutation80 hz
    mixedMoment B raw42661step1 raw42661step1Labels = mixedMoment B raw42661step2 raw42661step2Labels := by
      have ha : raw42661step2 = (fun i j => raw42661step1 (permutation16 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42661step2 raw42661step1; decide +kernel
      have hl : raw42661step2Labels = raw42661step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42661step1 raw42661step1Labels permutation16 permutation4
    mixedMoment B raw42661step2 raw42661step2Labels = mixedMoment B raw42661step3 raw42661step3Labels := by
      have ha : raw42661step3 = -raw42661step2 := by apply Matrix.ext; change ∀ i j, raw42661step3 i j = -(raw42661step2 i j); unfold raw42661step3 raw42661step2; decide +kernel
      have hl : raw42661step3Labels = raw42661step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42661step3 raw42661step3Labels = mixedMoment B raw42661step4 raw42661step4Labels := by
      have ha : raw42661step4 = raw42661step3 := by apply Matrix.ext; unfold raw42661step4 raw42661step3; decide +kernel
      have hl : raw42661step3Labels = labelEmbedding10 ∘ raw42661step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42661step3 raw42661step3Labels raw42661step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

def raw42662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42662Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42662step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42662step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42662step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42662step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3]]
def raw42662step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42662step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw42662step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42662step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw42662step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42662 raw42662Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw42662 raw42662Labels = mixedMoment B raw42662step0 raw42662step0Labels := by
      have hz : ∀ j, raw42662 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42662step0 = (fun i j => raw42662 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42662step0 raw42662; decide +kernel
      have hl : raw42662step0Labels = raw42662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42662 raw42662Labels permutation434 hz
    mixedMoment B raw42662step0 raw42662step0Labels = mixedMoment B raw42662step1 raw42662step1Labels := by
      have hz : ∀ j, raw42662step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42662step1 = (fun i j => raw42662step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42662step1 raw42662step0; decide +kernel
      have hl : raw42662step1Labels = raw42662step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42662step0 raw42662step0Labels permutation80 hz
    mixedMoment B raw42662step1 raw42662step1Labels = mixedMoment B raw42662step2 raw42662step2Labels := by
      have ha : raw42662step2 = (fun i j => raw42662step1 (permutation19 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42662step2 raw42662step1; decide +kernel
      have hl : raw42662step2Labels = raw42662step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42662step1 raw42662step1Labels permutation19 permutation4
    mixedMoment B raw42662step2 raw42662step2Labels = mixedMoment B raw42662step3 raw42662step3Labels := by
      have ha : raw42662step3 = -raw42662step2 := by apply Matrix.ext; change ∀ i j, raw42662step3 i j = -(raw42662step2 i j); unfold raw42662step3 raw42662step2; decide +kernel
      have hl : raw42662step3Labels = raw42662step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42662step3 raw42662step3Labels = mixedMoment B raw42662step4 raw42662step4Labels := by
      have ha : raw42662step4 = raw42662step3 := by apply Matrix.ext; unfold raw42662step4 raw42662step3; decide +kernel
      have hl : raw42662step3Labels = labelEmbedding1 ∘ raw42662step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42662step3 raw42662step3Labels raw42662step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2781 node2781Labels := by rfl

def raw42663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42663Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42663step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42663step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42663step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42663step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw42663step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42663step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42663step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42663step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42663step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42663 raw42663Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw42663 raw42663Labels = mixedMoment B raw42663step0 raw42663step0Labels := by
      have hz : ∀ j, raw42663 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42663step0 = (fun i j => raw42663 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42663step0 raw42663; decide +kernel
      have hl : raw42663step0Labels = raw42663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42663 raw42663Labels permutation434 hz
    mixedMoment B raw42663step0 raw42663step0Labels = mixedMoment B raw42663step1 raw42663step1Labels := by
      have hz : ∀ j, raw42663step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42663step1 = (fun i j => raw42663step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42663step1 raw42663step0; decide +kernel
      have hl : raw42663step1Labels = raw42663step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42663step0 raw42663step0Labels permutation80 hz
    mixedMoment B raw42663step1 raw42663step1Labels = mixedMoment B raw42663step2 raw42663step2Labels := by
      have ha : raw42663step2 = (fun i j => raw42663step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42663step2 raw42663step1; decide +kernel
      have hl : raw42663step2Labels = raw42663step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42663step1 raw42663step1Labels permutation11 permutation7
    mixedMoment B raw42663step2 raw42663step2Labels = mixedMoment B raw42663step3 raw42663step3Labels := by
      have ha : raw42663step3 = -raw42663step2 := by apply Matrix.ext; change ∀ i j, raw42663step3 i j = -(raw42663step2 i j); unfold raw42663step3 raw42663step2; decide +kernel
      have hl : raw42663step3Labels = raw42663step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42663step3 raw42663step3Labels = mixedMoment B raw42663step4 raw42663step4Labels := by
      have ha : raw42663step4 = raw42663step3 := by apply Matrix.ext; unfold raw42663step4 raw42663step3; decide +kernel
      have hl : raw42663step3Labels = labelEmbedding6 ∘ raw42663step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42663step3 raw42663step3Labels raw42663step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw42664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42664Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42664step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42664step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, -2, 1], ![2, 0, -2]]
def raw42664step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42664step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, -2, 3], ![-2, 1, 1]]
def raw42664step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42664step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw42664step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42664step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw42664step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42664 raw42664Labels = mixedMoment B node2687 node2687Labels := by
  calc
    mixedMoment B raw42664 raw42664Labels = mixedMoment B raw42664step0 raw42664step0Labels := by
      have hz : ∀ j, raw42664 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42664step0 = (fun i j => raw42664 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42664step0 raw42664; decide +kernel
      have hl : raw42664step0Labels = raw42664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42664 raw42664Labels permutation434 hz
    mixedMoment B raw42664step0 raw42664step0Labels = mixedMoment B raw42664step1 raw42664step1Labels := by
      have hz : ∀ j, raw42664step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42664step1 = (fun i j => raw42664step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42664step1 raw42664step0; decide +kernel
      have hl : raw42664step1Labels = raw42664step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42664step0 raw42664step0Labels permutation80 hz
    mixedMoment B raw42664step1 raw42664step1Labels = mixedMoment B raw42664step2 raw42664step2Labels := by
      have ha : raw42664step2 = (fun i j => raw42664step1 (permutation18 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42664step2 raw42664step1; decide +kernel
      have hl : raw42664step2Labels = raw42664step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42664step1 raw42664step1Labels permutation18 permutation4
    mixedMoment B raw42664step2 raw42664step2Labels = mixedMoment B raw42664step3 raw42664step3Labels := by
      have ha : raw42664step3 = -raw42664step2 := by apply Matrix.ext; change ∀ i j, raw42664step3 i j = -(raw42664step2 i j); unfold raw42664step3 raw42664step2; decide +kernel
      have hl : raw42664step3Labels = raw42664step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42664step3 raw42664step3Labels = mixedMoment B raw42664step4 raw42664step4Labels := by
      have ha : raw42664step4 = raw42664step3 := by apply Matrix.ext; unfold raw42664step4 raw42664step3; decide +kernel
      have hl : raw42664step3Labels = labelEmbedding1 ∘ raw42664step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42664step3 raw42664step3Labels raw42664step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2687 node2687Labels := by rfl

def raw42665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42665Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42665step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42665step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, -2, 1], ![2, 0, -2]]
def raw42665step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42665step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw42665step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42665step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw42665step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42665step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw42665step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42665 raw42665Labels = mixedMoment B node5206 node5206Labels := by
  calc
    mixedMoment B raw42665 raw42665Labels = mixedMoment B raw42665step0 raw42665step0Labels := by
      have hz : ∀ j, raw42665 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42665step0 = (fun i j => raw42665 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42665step0 raw42665; decide +kernel
      have hl : raw42665step0Labels = raw42665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42665 raw42665Labels permutation434 hz
    mixedMoment B raw42665step0 raw42665step0Labels = mixedMoment B raw42665step1 raw42665step1Labels := by
      have hz : ∀ j, raw42665step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42665step1 = (fun i j => raw42665step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42665step1 raw42665step0; decide +kernel
      have hl : raw42665step1Labels = raw42665step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42665step0 raw42665step0Labels permutation80 hz
    mixedMoment B raw42665step1 raw42665step1Labels = mixedMoment B raw42665step2 raw42665step2Labels := by
      have ha : raw42665step2 = (fun i j => raw42665step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42665step2 raw42665step1; decide +kernel
      have hl : raw42665step2Labels = raw42665step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42665step1 raw42665step1Labels permutation10 permutation7
    mixedMoment B raw42665step2 raw42665step2Labels = mixedMoment B raw42665step3 raw42665step3Labels := by
      have ha : raw42665step3 = -raw42665step2 := by apply Matrix.ext; change ∀ i j, raw42665step3 i j = -(raw42665step2 i j); unfold raw42665step3 raw42665step2; decide +kernel
      have hl : raw42665step3Labels = raw42665step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42665step3 raw42665step3Labels = mixedMoment B raw42665step4 raw42665step4Labels := by
      have ha : raw42665step4 = raw42665step3 := by apply Matrix.ext; unfold raw42665step4 raw42665step3; decide +kernel
      have hl : raw42665step3Labels = labelEmbedding6 ∘ raw42665step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42665step3 raw42665step3Labels raw42665step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5206 node5206Labels := by rfl

def raw42666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42666Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42666step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw42666step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42666step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42666step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42666step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42666step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42666 raw42666Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw42666 raw42666Labels = mixedMoment B raw42666step0 raw42666step0Labels := by
      have hz : ∀ j, raw42666 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42666step0 = (fun i j => raw42666 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42666step0 raw42666; decide +kernel
      have hl : raw42666step0Labels = raw42666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42666 raw42666Labels permutation346 hz
    mixedMoment B raw42666step0 raw42666step0Labels = mixedMoment B raw42666step1 raw42666step1Labels := by
      have ha : raw42666step1 = (fun i j => raw42666step0 (permutation79 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42666step1 raw42666step0; decide +kernel
      have hl : raw42666step1Labels = raw42666step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42666step0 raw42666step0Labels permutation79 permutation4
    mixedMoment B raw42666step1 raw42666step1Labels = mixedMoment B raw42666step2 raw42666step2Labels := by
      have ha : raw42666step2 = -raw42666step1 := by apply Matrix.ext; change ∀ i j, raw42666step2 i j = -(raw42666step1 i j); unfold raw42666step2 raw42666step1; decide +kernel
      have hl : raw42666step2Labels = raw42666step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42666step2 raw42666step2Labels = mixedMoment B raw42666step3 raw42666step3Labels := by
      have ha : raw42666step3 = raw42666step2 := by apply Matrix.ext; unfold raw42666step3 raw42666step2; decide +kernel
      have hl : raw42666step2Labels = labelEmbedding1 ∘ raw42666step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42666step2 raw42666step2Labels raw42666step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2681 node2681Labels := by rfl

def raw42667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42667Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42667step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw42667step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42667step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw42667step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42667step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw42667step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42667 raw42667Labels = mixedMoment B node5151 node5151Labels := by
  calc
    mixedMoment B raw42667 raw42667Labels = mixedMoment B raw42667step0 raw42667step0Labels := by
      have hz : ∀ j, raw42667 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42667step0 = (fun i j => raw42667 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42667step0 raw42667; decide +kernel
      have hl : raw42667step0Labels = raw42667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42667 raw42667Labels permutation346 hz
    mixedMoment B raw42667step0 raw42667step0Labels = mixedMoment B raw42667step1 raw42667step1Labels := by
      have ha : raw42667step1 = (fun i j => raw42667step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42667step1 raw42667step0; decide +kernel
      have hl : raw42667step1Labels = raw42667step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42667step0 raw42667step0Labels permutation40 permutation7
    mixedMoment B raw42667step1 raw42667step1Labels = mixedMoment B raw42667step2 raw42667step2Labels := by
      have ha : raw42667step2 = -raw42667step1 := by apply Matrix.ext; change ∀ i j, raw42667step2 i j = -(raw42667step1 i j); unfold raw42667step2 raw42667step1; decide +kernel
      have hl : raw42667step2Labels = raw42667step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42667step2 raw42667step2Labels = mixedMoment B raw42667step3 raw42667step3Labels := by
      have ha : raw42667step3 = raw42667step2 := by apply Matrix.ext; unfold raw42667step3 raw42667step2; decide +kernel
      have hl : raw42667step2Labels = labelEmbedding6 ∘ raw42667step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42667step2 raw42667step2Labels raw42667step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5151 node5151Labels := by rfl

def raw42668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42668Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42668step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw42668step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42668step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw42668step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42668step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw42668step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42668 raw42668Labels = mixedMoment B node2706 node2706Labels := by
  calc
    mixedMoment B raw42668 raw42668Labels = mixedMoment B raw42668step0 raw42668step0Labels := by
      have hz : ∀ j, raw42668 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42668step0 = (fun i j => raw42668 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42668step0 raw42668; decide +kernel
      have hl : raw42668step0Labels = raw42668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42668 raw42668Labels permutation346 hz
    mixedMoment B raw42668step0 raw42668step0Labels = mixedMoment B raw42668step1 raw42668step1Labels := by
      have ha : raw42668step1 = (fun i j => raw42668step0 (permutation64 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42668step1 raw42668step0; decide +kernel
      have hl : raw42668step1Labels = raw42668step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42668step0 raw42668step0Labels permutation64 permutation4
    mixedMoment B raw42668step1 raw42668step1Labels = mixedMoment B raw42668step2 raw42668step2Labels := by
      have ha : raw42668step2 = -raw42668step1 := by apply Matrix.ext; change ∀ i j, raw42668step2 i j = -(raw42668step1 i j); unfold raw42668step2 raw42668step1; decide +kernel
      have hl : raw42668step2Labels = raw42668step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42668step2 raw42668step2Labels = mixedMoment B raw42668step3 raw42668step3Labels := by
      have ha : raw42668step3 = raw42668step2 := by apply Matrix.ext; unfold raw42668step3 raw42668step2; decide +kernel
      have hl : raw42668step2Labels = labelEmbedding1 ∘ raw42668step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42668step2 raw42668step2Labels raw42668step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2706 node2706Labels := by rfl

def raw42669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42669Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42669step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw42669step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42669step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42669step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42669step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42669 raw42669Labels = mixedMoment B node5205 node5205Labels := by
  calc
    mixedMoment B raw42669 raw42669Labels = mixedMoment B raw42669step0 raw42669step0Labels := by
      have hz : ∀ j, raw42669 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42669step0 = (fun i j => raw42669 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42669step0 raw42669; decide +kernel
      have hl : raw42669step0Labels = raw42669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42669 raw42669Labels permutation346 hz
    mixedMoment B raw42669step0 raw42669step0Labels = mixedMoment B raw42669step1 raw42669step1Labels := by
      have ha : raw42669step1 = (fun i j => raw42669step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42669step1 raw42669step0; decide +kernel
      have hl : raw42669step1Labels = raw42669step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42669step0 raw42669step0Labels permutation53 permutation7
    mixedMoment B raw42669step1 raw42669step1Labels = mixedMoment B raw42669step2 raw42669step2Labels := by
      have ha : raw42669step2 = -raw42669step1 := by apply Matrix.ext; change ∀ i j, raw42669step2 i j = -(raw42669step1 i j); unfold raw42669step2 raw42669step1; decide +kernel
      have hl : raw42669step2Labels = raw42669step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42669step2 raw42669step2Labels = mixedMoment B raw42669step3 raw42669step3Labels := by
      have ha : raw42669step3 = raw42669step2 := by apply Matrix.ext; unfold raw42669step3 raw42669step2; decide +kernel
      have hl : raw42669step2Labels = labelEmbedding6 ∘ raw42669step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42669step2 raw42669step2Labels raw42669step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5205 node5205Labels := by rfl

def raw42670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42670Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42670step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw42670step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42670step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw42670step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42670step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw42670step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42670 raw42670Labels = mixedMoment B node2738 node2738Labels := by
  calc
    mixedMoment B raw42670 raw42670Labels = mixedMoment B raw42670step0 raw42670step0Labels := by
      have hz : ∀ j, raw42670 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42670step0 = (fun i j => raw42670 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42670step0 raw42670; decide +kernel
      have hl : raw42670step0Labels = raw42670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42670 raw42670Labels permutation346 hz
    mixedMoment B raw42670step0 raw42670step0Labels = mixedMoment B raw42670step1 raw42670step1Labels := by
      have ha : raw42670step1 = (fun i j => raw42670step0 (permutation65 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42670step1 raw42670step0; decide +kernel
      have hl : raw42670step1Labels = raw42670step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42670step0 raw42670step0Labels permutation65 permutation4
    mixedMoment B raw42670step1 raw42670step1Labels = mixedMoment B raw42670step2 raw42670step2Labels := by
      have ha : raw42670step2 = -raw42670step1 := by apply Matrix.ext; change ∀ i j, raw42670step2 i j = -(raw42670step1 i j); unfold raw42670step2 raw42670step1; decide +kernel
      have hl : raw42670step2Labels = raw42670step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42670step2 raw42670step2Labels = mixedMoment B raw42670step3 raw42670step3Labels := by
      have ha : raw42670step3 = raw42670step2 := by apply Matrix.ext; unfold raw42670step3 raw42670step2; decide +kernel
      have hl : raw42670step2Labels = labelEmbedding1 ∘ raw42670step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42670step2 raw42670step2Labels raw42670step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2738 node2738Labels := by rfl

def raw42671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42671Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42671step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw42671step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42671step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw42671step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42671step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw42671step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42671 raw42671Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw42671 raw42671Labels = mixedMoment B raw42671step0 raw42671step0Labels := by
      have hz : ∀ j, raw42671 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42671step0 = (fun i j => raw42671 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42671step0 raw42671; decide +kernel
      have hl : raw42671step0Labels = raw42671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42671 raw42671Labels permutation346 hz
    mixedMoment B raw42671step0 raw42671step0Labels = mixedMoment B raw42671step1 raw42671step1Labels := by
      have ha : raw42671step1 = (fun i j => raw42671step0 (permutation65 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42671step1 raw42671step0; decide +kernel
      have hl : raw42671step1Labels = raw42671step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42671step0 raw42671step0Labels permutation65 permutation4
    mixedMoment B raw42671step1 raw42671step1Labels = mixedMoment B raw42671step2 raw42671step2Labels := by
      have ha : raw42671step2 = -raw42671step1 := by apply Matrix.ext; change ∀ i j, raw42671step2 i j = -(raw42671step1 i j); unfold raw42671step2 raw42671step1; decide +kernel
      have hl : raw42671step2Labels = raw42671step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42671step2 raw42671step2Labels = mixedMoment B raw42671step3 raw42671step3Labels := by
      have ha : raw42671step3 = raw42671step2 := by apply Matrix.ext; unfold raw42671step3 raw42671step2; decide +kernel
      have hl : raw42671step2Labels = labelEmbedding10 ∘ raw42671step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42671step2 raw42671step2Labels raw42671step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw42672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42672Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42672step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw42672step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42672step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42672step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42672step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42672step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42672 raw42672Labels = mixedMoment B node2700 node2700Labels := by
  calc
    mixedMoment B raw42672 raw42672Labels = mixedMoment B raw42672step0 raw42672step0Labels := by
      have ha : raw42672step0 = (fun i j => raw42672 (permutation317 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42672step0 raw42672; decide +kernel
      have hl : raw42672step0Labels = raw42672Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42672 raw42672Labels permutation317 permutation4
    mixedMoment B raw42672step0 raw42672step0Labels = mixedMoment B raw42672step1 raw42672step1Labels := by
      have ha : raw42672step1 = -raw42672step0 := by apply Matrix.ext; change ∀ i j, raw42672step1 i j = -(raw42672step0 i j); unfold raw42672step1 raw42672step0; decide +kernel
      have hl : raw42672step1Labels = raw42672step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42672step1 raw42672step1Labels = mixedMoment B raw42672step2 raw42672step2Labels := by
      have ha : raw42672step2 = raw42672step1 := by apply Matrix.ext; unfold raw42672step2 raw42672step1; decide +kernel
      have hl : raw42672step1Labels = labelEmbedding1 ∘ raw42672step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42672step1 raw42672step1Labels raw42672step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2700 node2700Labels := by rfl

def raw42673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42673Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42673step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw42673step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42673step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42673step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42673step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42673step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42673 raw42673Labels = mixedMoment B node5150 node5150Labels := by
  calc
    mixedMoment B raw42673 raw42673Labels = mixedMoment B raw42673step0 raw42673step0Labels := by
      have ha : raw42673step0 = (fun i j => raw42673 (permutation197 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42673step0 raw42673; decide +kernel
      have hl : raw42673step0Labels = raw42673Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42673 raw42673Labels permutation197 permutation7
    mixedMoment B raw42673step0 raw42673step0Labels = mixedMoment B raw42673step1 raw42673step1Labels := by
      have ha : raw42673step1 = -raw42673step0 := by apply Matrix.ext; change ∀ i j, raw42673step1 i j = -(raw42673step0 i j); unfold raw42673step1 raw42673step0; decide +kernel
      have hl : raw42673step1Labels = raw42673step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42673step1 raw42673step1Labels = mixedMoment B raw42673step2 raw42673step2Labels := by
      have ha : raw42673step2 = raw42673step1 := by apply Matrix.ext; unfold raw42673step2 raw42673step1; decide +kernel
      have hl : raw42673step1Labels = labelEmbedding6 ∘ raw42673step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42673step1 raw42673step1Labels raw42673step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5150 node5150Labels := by rfl

def raw42674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42674Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42674step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42674step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42674 raw42674Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw42674 raw42674Labels = mixedMoment B raw42674step0 raw42674step0Labels := by
      have hz : ∀ j, raw42674 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42674step0 = (fun i j => raw42674 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42674step0 raw42674; decide +kernel
      have hl : raw42674step0Labels = raw42674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42674 raw42674Labels permutation434 hz
    mixedMoment B raw42674step0 raw42674step0Labels = mixedMoment B raw42674step1 raw42674step1Labels := by
      have ha : raw42674step1 = raw42674step0 := by apply Matrix.ext; unfold raw42674step1 raw42674step0; decide +kernel
      have hl : raw42674step0Labels = labelEmbedding1 ∘ raw42674step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42674step0 raw42674step0Labels raw42674step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw42675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42675Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42675step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw42675step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42675step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42675step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42675step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42675step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42675 raw42675Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw42675 raw42675Labels = mixedMoment B raw42675step0 raw42675step0Labels := by
      have hz : ∀ j, raw42675 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42675step0 = (fun i j => raw42675 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42675step0 raw42675; decide +kernel
      have hl : raw42675step0Labels = raw42675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42675 raw42675Labels permutation434 hz
    mixedMoment B raw42675step0 raw42675step0Labels = mixedMoment B raw42675step1 raw42675step1Labels := by
      have ha : raw42675step1 = (fun i j => raw42675step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42675step1 raw42675step0; decide +kernel
      have hl : raw42675step1Labels = raw42675step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42675step0 raw42675step0Labels permutation50 permutation7
    mixedMoment B raw42675step1 raw42675step1Labels = mixedMoment B raw42675step2 raw42675step2Labels := by
      have ha : raw42675step2 = -raw42675step1 := by apply Matrix.ext; change ∀ i j, raw42675step2 i j = -(raw42675step1 i j); unfold raw42675step2 raw42675step1; decide +kernel
      have hl : raw42675step2Labels = raw42675step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42675step2 raw42675step2Labels = mixedMoment B raw42675step3 raw42675step3Labels := by
      have ha : raw42675step3 = raw42675step2 := by apply Matrix.ext; unfold raw42675step3 raw42675step2; decide +kernel
      have hl : raw42675step2Labels = labelEmbedding6 ∘ raw42675step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42675step2 raw42675step2Labels raw42675step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw42676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42676Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42676step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42676step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42676step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42676 raw42676Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw42676 raw42676Labels = mixedMoment B raw42676step0 raw42676step0Labels := by
      have hz : ∀ j, raw42676 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42676step0 = (fun i j => raw42676 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42676step0 raw42676; decide +kernel
      have hl : raw42676step0Labels = raw42676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42676 raw42676Labels permutation434 hz
    mixedMoment B raw42676step0 raw42676step0Labels = mixedMoment B raw42676step1 raw42676step1Labels := by
      have ha : raw42676step1 = raw42676step0 := by apply Matrix.ext; unfold raw42676step1 raw42676step0; decide +kernel
      have hl : raw42676step0Labels = labelEmbedding1 ∘ raw42676step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42676step0 raw42676step0Labels raw42676step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw42677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42677Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42677step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw42677step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42677step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42677step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42677step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42677step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42677 raw42677Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw42677 raw42677Labels = mixedMoment B raw42677step0 raw42677step0Labels := by
      have hz : ∀ j, raw42677 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42677step0 = (fun i j => raw42677 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42677step0 raw42677; decide +kernel
      have hl : raw42677step0Labels = raw42677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42677 raw42677Labels permutation434 hz
    mixedMoment B raw42677step0 raw42677step0Labels = mixedMoment B raw42677step1 raw42677step1Labels := by
      have ha : raw42677step1 = (fun i j => raw42677step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42677step1 raw42677step0; decide +kernel
      have hl : raw42677step1Labels = raw42677step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42677step0 raw42677step0Labels permutation44 permutation7
    mixedMoment B raw42677step1 raw42677step1Labels = mixedMoment B raw42677step2 raw42677step2Labels := by
      have ha : raw42677step2 = -raw42677step1 := by apply Matrix.ext; change ∀ i j, raw42677step2 i j = -(raw42677step1 i j); unfold raw42677step2 raw42677step1; decide +kernel
      have hl : raw42677step2Labels = raw42677step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42677step2 raw42677step2Labels = mixedMoment B raw42677step3 raw42677step3Labels := by
      have ha : raw42677step3 = raw42677step2 := by apply Matrix.ext; unfold raw42677step3 raw42677step2; decide +kernel
      have hl : raw42677step2Labels = labelEmbedding6 ∘ raw42677step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42677step2 raw42677step2Labels raw42677step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw42678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42678Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42678step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42678step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42678 raw42678Labels = mixedMoment B node3570 node3570Labels := by
  calc
    mixedMoment B raw42678 raw42678Labels = mixedMoment B raw42678step0 raw42678step0Labels := by
      have hz : ∀ j, raw42678 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42678step0 = (fun i j => raw42678 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42678step0 raw42678; decide +kernel
      have hl : raw42678step0Labels = raw42678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42678 raw42678Labels permutation434 hz
    mixedMoment B raw42678step0 raw42678step0Labels = mixedMoment B raw42678step1 raw42678step1Labels := by
      have ha : raw42678step1 = raw42678step0 := by apply Matrix.ext; unfold raw42678step1 raw42678step0; decide +kernel
      have hl : raw42678step0Labels = labelEmbedding1 ∘ raw42678step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42678step0 raw42678step0Labels raw42678step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3570 node3570Labels := by rfl

def raw42679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42679Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42679step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42679step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw42679step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42679step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42679step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42679step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42679step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42679 raw42679Labels = mixedMoment B node5198 node5198Labels := by
  calc
    mixedMoment B raw42679 raw42679Labels = mixedMoment B raw42679step0 raw42679step0Labels := by
      have hz : ∀ j, raw42679 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42679step0 = (fun i j => raw42679 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42679step0 raw42679; decide +kernel
      have hl : raw42679step0Labels = raw42679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42679 raw42679Labels permutation434 hz
    mixedMoment B raw42679step0 raw42679step0Labels = mixedMoment B raw42679step1 raw42679step1Labels := by
      have ha : raw42679step1 = (fun i j => raw42679step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42679step1 raw42679step0; decide +kernel
      have hl : raw42679step1Labels = raw42679step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42679step0 raw42679step0Labels permutation44 permutation7
    mixedMoment B raw42679step1 raw42679step1Labels = mixedMoment B raw42679step2 raw42679step2Labels := by
      have ha : raw42679step2 = -raw42679step1 := by apply Matrix.ext; change ∀ i j, raw42679step2 i j = -(raw42679step1 i j); unfold raw42679step2 raw42679step1; decide +kernel
      have hl : raw42679step2Labels = raw42679step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42679step2 raw42679step2Labels = mixedMoment B raw42679step3 raw42679step3Labels := by
      have ha : raw42679step3 = raw42679step2 := by apply Matrix.ext; unfold raw42679step3 raw42679step2; decide +kernel
      have hl : raw42679step2Labels = labelEmbedding6 ∘ raw42679step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42679step2 raw42679step2Labels raw42679step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5198 node5198Labels := by rfl

def raw42680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42680Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42680step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42680step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42680step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42680step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42680 raw42680Labels = mixedMoment B node3557 node3557Labels := by
  calc
    mixedMoment B raw42680 raw42680Labels = mixedMoment B raw42680step0 raw42680step0Labels := by
      have ha : raw42680step0 = (fun i j => raw42680 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42680step0 raw42680; decide +kernel
      have hl : raw42680step0Labels = raw42680Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42680 raw42680Labels permutation158 permutation2
    mixedMoment B raw42680step0 raw42680step0Labels = mixedMoment B raw42680step1 raw42680step1Labels := by
      have ha : raw42680step1 = raw42680step0 := by apply Matrix.ext; unfold raw42680step1 raw42680step0; decide +kernel
      have hl : raw42680step0Labels = labelEmbedding1 ∘ raw42680step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42680step0 raw42680step0Labels raw42680step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3557 node3557Labels := by rfl

def raw42681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42681Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42681step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw42681step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42681step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42681step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42681step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42681step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42681 raw42681Labels = mixedMoment B node5144 node5144Labels := by
  calc
    mixedMoment B raw42681 raw42681Labels = mixedMoment B raw42681step0 raw42681step0Labels := by
      have ha : raw42681step0 = (fun i j => raw42681 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42681step0 raw42681; decide +kernel
      have hl : raw42681step0Labels = raw42681Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42681 raw42681Labels permutation212 permutation7
    mixedMoment B raw42681step0 raw42681step0Labels = mixedMoment B raw42681step1 raw42681step1Labels := by
      have ha : raw42681step1 = -raw42681step0 := by apply Matrix.ext; change ∀ i j, raw42681step1 i j = -(raw42681step0 i j); unfold raw42681step1 raw42681step0; decide +kernel
      have hl : raw42681step1Labels = raw42681step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42681step1 raw42681step1Labels = mixedMoment B raw42681step2 raw42681step2Labels := by
      have ha : raw42681step2 = raw42681step1 := by apply Matrix.ext; unfold raw42681step2 raw42681step1; decide +kernel
      have hl : raw42681step1Labels = labelEmbedding6 ∘ raw42681step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42681step1 raw42681step1Labels raw42681step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5144 node5144Labels := by rfl

def raw42682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42682Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42682step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42682step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42682step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42682step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42682 raw42682Labels = mixedMoment B node3569 node3569Labels := by
  calc
    mixedMoment B raw42682 raw42682Labels = mixedMoment B raw42682step0 raw42682step0Labels := by
      have ha : raw42682step0 = (fun i j => raw42682 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42682step0 raw42682; decide +kernel
      have hl : raw42682step0Labels = raw42682Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42682 raw42682Labels permutation156 permutation2
    mixedMoment B raw42682step0 raw42682step0Labels = mixedMoment B raw42682step1 raw42682step1Labels := by
      have ha : raw42682step1 = raw42682step0 := by apply Matrix.ext; unfold raw42682step1 raw42682step0; decide +kernel
      have hl : raw42682step0Labels = labelEmbedding1 ∘ raw42682step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42682step0 raw42682step0Labels raw42682step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3569 node3569Labels := by rfl

def raw42683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42683Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42683step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw42683step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42683step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42683step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42683step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42683step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42683 raw42683Labels = mixedMoment B node5197 node5197Labels := by
  calc
    mixedMoment B raw42683 raw42683Labels = mixedMoment B raw42683step0 raw42683step0Labels := by
      have ha : raw42683step0 = (fun i j => raw42683 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42683step0 raw42683; decide +kernel
      have hl : raw42683step0Labels = raw42683Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42683 raw42683Labels permutation246 permutation7
    mixedMoment B raw42683step0 raw42683step0Labels = mixedMoment B raw42683step1 raw42683step1Labels := by
      have ha : raw42683step1 = -raw42683step0 := by apply Matrix.ext; change ∀ i j, raw42683step1 i j = -(raw42683step0 i j); unfold raw42683step1 raw42683step0; decide +kernel
      have hl : raw42683step1Labels = raw42683step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42683step1 raw42683step1Labels = mixedMoment B raw42683step2 raw42683step2Labels := by
      have ha : raw42683step2 = raw42683step1 := by apply Matrix.ext; unfold raw42683step2 raw42683step1; decide +kernel
      have hl : raw42683step1Labels = labelEmbedding6 ∘ raw42683step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42683step1 raw42683step1Labels raw42683step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5197 node5197Labels := by rfl

def raw42684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42684Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42684step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42684step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42684step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42684step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42684 raw42684Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw42684 raw42684Labels = mixedMoment B raw42684step0 raw42684step0Labels := by
      have ha : raw42684step0 = (fun i j => raw42684 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42684step0 raw42684; decide +kernel
      have hl : raw42684step0Labels = raw42684Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42684 raw42684Labels permutation155 permutation2
    mixedMoment B raw42684step0 raw42684step0Labels = mixedMoment B raw42684step1 raw42684step1Labels := by
      have ha : raw42684step1 = raw42684step0 := by apply Matrix.ext; unfold raw42684step1 raw42684step0; decide +kernel
      have hl : raw42684step0Labels = labelEmbedding1 ∘ raw42684step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42684step0 raw42684step0Labels raw42684step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3571 node3571Labels := by rfl

def raw42685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42685Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42685step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw42685step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42685step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42685step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42685step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42685step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42685 raw42685Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw42685 raw42685Labels = mixedMoment B raw42685step0 raw42685step0Labels := by
      have ha : raw42685step0 = (fun i j => raw42685 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42685step0 raw42685; decide +kernel
      have hl : raw42685step0Labels = raw42685Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42685 raw42685Labels permutation240 permutation7
    mixedMoment B raw42685step0 raw42685step0Labels = mixedMoment B raw42685step1 raw42685step1Labels := by
      have ha : raw42685step1 = -raw42685step0 := by apply Matrix.ext; change ∀ i j, raw42685step1 i j = -(raw42685step0 i j); unfold raw42685step1 raw42685step0; decide +kernel
      have hl : raw42685step1Labels = raw42685step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42685step1 raw42685step1Labels = mixedMoment B raw42685step2 raw42685step2Labels := by
      have ha : raw42685step2 = raw42685step1 := by apply Matrix.ext; unfold raw42685step2 raw42685step1; decide +kernel
      have hl : raw42685step1Labels = labelEmbedding6 ∘ raw42685step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42685step1 raw42685step1Labels raw42685step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw42686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42686Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42686step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42686step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42686step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42686step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42686step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42686 raw42686Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw42686 raw42686Labels = mixedMoment B raw42686step0 raw42686step0Labels := by
      have hz : ∀ j, raw42686 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42686step0 = (fun i j => raw42686 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42686step0 raw42686; decide +kernel
      have hl : raw42686step0Labels = raw42686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42686 raw42686Labels permutation434 hz
    mixedMoment B raw42686step0 raw42686step0Labels = mixedMoment B raw42686step1 raw42686step1Labels := by
      have hz : ∀ j, raw42686step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42686step1 = (fun i j => raw42686step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42686step1 raw42686step0; decide +kernel
      have hl : raw42686step1Labels = raw42686step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42686step0 raw42686step0Labels permutation80 hz
    mixedMoment B raw42686step1 raw42686step1Labels = mixedMoment B raw42686step2 raw42686step2Labels := by
      have ha : raw42686step2 = raw42686step1 := by apply Matrix.ext; unfold raw42686step2 raw42686step1; decide +kernel
      have hl : raw42686step1Labels = labelEmbedding1 ∘ raw42686step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42686step1 raw42686step1Labels raw42686step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3584 node3584Labels := by rfl

def raw42687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42687Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42687step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42687step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42687step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42687step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw42687step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42687step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42687step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42687step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42687step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42687 raw42687Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw42687 raw42687Labels = mixedMoment B raw42687step0 raw42687step0Labels := by
      have hz : ∀ j, raw42687 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42687step0 = (fun i j => raw42687 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42687step0 raw42687; decide +kernel
      have hl : raw42687step0Labels = raw42687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42687 raw42687Labels permutation434 hz
    mixedMoment B raw42687step0 raw42687step0Labels = mixedMoment B raw42687step1 raw42687step1Labels := by
      have hz : ∀ j, raw42687step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42687step1 = (fun i j => raw42687step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42687step1 raw42687step0; decide +kernel
      have hl : raw42687step1Labels = raw42687step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42687step0 raw42687step0Labels permutation80 hz
    mixedMoment B raw42687step1 raw42687step1Labels = mixedMoment B raw42687step2 raw42687step2Labels := by
      have ha : raw42687step2 = (fun i j => raw42687step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42687step2 raw42687step1; decide +kernel
      have hl : raw42687step2Labels = raw42687step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42687step1 raw42687step1Labels permutation12 permutation7
    mixedMoment B raw42687step2 raw42687step2Labels = mixedMoment B raw42687step3 raw42687step3Labels := by
      have ha : raw42687step3 = -raw42687step2 := by apply Matrix.ext; change ∀ i j, raw42687step3 i j = -(raw42687step2 i j); unfold raw42687step3 raw42687step2; decide +kernel
      have hl : raw42687step3Labels = raw42687step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42687step3 raw42687step3Labels = mixedMoment B raw42687step4 raw42687step4Labels := by
      have ha : raw42687step4 = raw42687step3 := by apply Matrix.ext; unfold raw42687step4 raw42687step3; decide +kernel
      have hl : raw42687step3Labels = labelEmbedding6 ∘ raw42687step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42687step3 raw42687step3Labels raw42687step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5300 node5300Labels := by rfl

def raw42688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw42688Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw42688step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42688step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]
def raw42688step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42688step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]
def raw42688step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42688 raw42688Labels = mixedMoment B node3579 node3579Labels := by
  calc
    mixedMoment B raw42688 raw42688Labels = mixedMoment B raw42688step0 raw42688step0Labels := by
      have hz : ∀ j, raw42688 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42688step0 = (fun i j => raw42688 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42688step0 raw42688; decide +kernel
      have hl : raw42688step0Labels = raw42688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42688 raw42688Labels permutation434 hz
    mixedMoment B raw42688step0 raw42688step0Labels = mixedMoment B raw42688step1 raw42688step1Labels := by
      have hz : ∀ j, raw42688step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42688step1 = (fun i j => raw42688step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42688step1 raw42688step0; decide +kernel
      have hl : raw42688step1Labels = raw42688step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42688step0 raw42688step0Labels permutation80 hz
    mixedMoment B raw42688step1 raw42688step1Labels = mixedMoment B raw42688step2 raw42688step2Labels := by
      have ha : raw42688step2 = raw42688step1 := by apply Matrix.ext; unfold raw42688step2 raw42688step1; decide +kernel
      have hl : raw42688step1Labels = labelEmbedding1 ∘ raw42688step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42688step1 raw42688step1Labels raw42688step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3579 node3579Labels := by rfl

def raw42689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw42689Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw42689step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42689step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![2, 1, -3]]
def raw42689step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42689step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw42689step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42689step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw42689step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42689 raw42689Labels = mixedMoment B node5201 node5201Labels := by
  calc
    mixedMoment B raw42689 raw42689Labels = mixedMoment B raw42689step0 raw42689step0Labels := by
      have hz : ∀ j, raw42689 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42689step0 = (fun i j => raw42689 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42689step0 raw42689; decide +kernel
      have hl : raw42689step0Labels = raw42689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42689 raw42689Labels permutation434 hz
    mixedMoment B raw42689step0 raw42689step0Labels = mixedMoment B raw42689step1 raw42689step1Labels := by
      have hz : ∀ j, raw42689step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42689step1 = (fun i j => raw42689step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42689step1 raw42689step0; decide +kernel
      have hl : raw42689step1Labels = raw42689step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42689step0 raw42689step0Labels permutation80 hz
    mixedMoment B raw42689step1 raw42689step1Labels = mixedMoment B raw42689step2 raw42689step2Labels := by
      have ha : raw42689step2 = (fun i j => raw42689step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42689step2 raw42689step1; decide +kernel
      have hl : raw42689step2Labels = raw42689step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42689step1 raw42689step1Labels permutation29 permutation7
    mixedMoment B raw42689step2 raw42689step2Labels = mixedMoment B raw42689step3 raw42689step3Labels := by
      have ha : raw42689step3 = raw42689step2 := by apply Matrix.ext; unfold raw42689step3 raw42689step2; decide +kernel
      have hl : raw42689step2Labels = labelEmbedding6 ∘ raw42689step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42689step2 raw42689step2Labels raw42689step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5201 node5201Labels := by rfl

def raw42690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42690Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42690step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw42690step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42690step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw42690step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42690step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw42690step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42690 raw42690Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw42690 raw42690Labels = mixedMoment B raw42690step0 raw42690step0Labels := by
      have hz : ∀ j, raw42690 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42690step0 = (fun i j => raw42690 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42690step0 raw42690; decide +kernel
      have hl : raw42690step0Labels = raw42690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42690 raw42690Labels permutation346 hz
    mixedMoment B raw42690step0 raw42690step0Labels = mixedMoment B raw42690step1 raw42690step1Labels := by
      have ha : raw42690step1 = (fun i j => raw42690step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42690step1 raw42690step0; decide +kernel
      have hl : raw42690step1Labels = raw42690step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42690step0 raw42690step0Labels permutation151 permutation2
    mixedMoment B raw42690step1 raw42690step1Labels = mixedMoment B raw42690step2 raw42690step2Labels := by
      have ha : raw42690step2 = -raw42690step1 := by apply Matrix.ext; change ∀ i j, raw42690step2 i j = -(raw42690step1 i j); unfold raw42690step2 raw42690step1; decide +kernel
      have hl : raw42690step2Labels = raw42690step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42690step2 raw42690step2Labels = mixedMoment B raw42690step3 raw42690step3Labels := by
      have ha : raw42690step3 = raw42690step2 := by apply Matrix.ext; unfold raw42690step3 raw42690step2; decide +kernel
      have hl : raw42690step2Labels = labelEmbedding1 ∘ raw42690step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42690step2 raw42690step2Labels raw42690step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3530 node3530Labels := by rfl

def raw42691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42691Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42691step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw42691step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42691step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw42691step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42691step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw42691step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42691 raw42691Labels = mixedMoment B node5147 node5147Labels := by
  calc
    mixedMoment B raw42691 raw42691Labels = mixedMoment B raw42691step0 raw42691step0Labels := by
      have hz : ∀ j, raw42691 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42691step0 = (fun i j => raw42691 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42691step0 raw42691; decide +kernel
      have hl : raw42691step0Labels = raw42691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42691 raw42691Labels permutation346 hz
    mixedMoment B raw42691step0 raw42691step0Labels = mixedMoment B raw42691step1 raw42691step1Labels := by
      have ha : raw42691step1 = (fun i j => raw42691step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42691step1 raw42691step0; decide +kernel
      have hl : raw42691step1Labels = raw42691step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42691step0 raw42691step0Labels permutation40 permutation7
    mixedMoment B raw42691step1 raw42691step1Labels = mixedMoment B raw42691step2 raw42691step2Labels := by
      have ha : raw42691step2 = -raw42691step1 := by apply Matrix.ext; change ∀ i j, raw42691step2 i j = -(raw42691step1 i j); unfold raw42691step2 raw42691step1; decide +kernel
      have hl : raw42691step2Labels = raw42691step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42691step2 raw42691step2Labels = mixedMoment B raw42691step3 raw42691step3Labels := by
      have ha : raw42691step3 = raw42691step2 := by apply Matrix.ext; unfold raw42691step3 raw42691step2; decide +kernel
      have hl : raw42691step2Labels = labelEmbedding6 ∘ raw42691step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42691step2 raw42691step2Labels raw42691step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5147 node5147Labels := by rfl

def raw42692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42692Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42692step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42692step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42692step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42692step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42692 raw42692Labels = mixedMoment B node3578 node3578Labels := by
  calc
    mixedMoment B raw42692 raw42692Labels = mixedMoment B raw42692step0 raw42692step0Labels := by
      have hz : ∀ j, raw42692 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42692step0 = (fun i j => raw42692 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42692step0 raw42692; decide +kernel
      have hl : raw42692step0Labels = raw42692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42692 raw42692Labels permutation346 hz
    mixedMoment B raw42692step0 raw42692step0Labels = mixedMoment B raw42692step1 raw42692step1Labels := by
      have ha : raw42692step1 = (fun i j => raw42692step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42692step1 raw42692step0; decide +kernel
      have hl : raw42692step1Labels = raw42692step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42692step0 raw42692step0Labels permutation37 permutation2
    mixedMoment B raw42692step1 raw42692step1Labels = mixedMoment B raw42692step2 raw42692step2Labels := by
      have ha : raw42692step2 = raw42692step1 := by apply Matrix.ext; unfold raw42692step2 raw42692step1; decide +kernel
      have hl : raw42692step1Labels = labelEmbedding1 ∘ raw42692step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42692step1 raw42692step1Labels raw42692step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3578 node3578Labels := by rfl

def raw42693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42693Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42693step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42693step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42693step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw42693step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42693step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw42693step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42693 raw42693Labels = mixedMoment B node5199 node5199Labels := by
  calc
    mixedMoment B raw42693 raw42693Labels = mixedMoment B raw42693step0 raw42693step0Labels := by
      have hz : ∀ j, raw42693 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42693step0 = (fun i j => raw42693 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42693step0 raw42693; decide +kernel
      have hl : raw42693step0Labels = raw42693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42693 raw42693Labels permutation346 hz
    mixedMoment B raw42693step0 raw42693step0Labels = mixedMoment B raw42693step1 raw42693step1Labels := by
      have ha : raw42693step1 = (fun i j => raw42693step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42693step1 raw42693step0; decide +kernel
      have hl : raw42693step1Labels = raw42693step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42693step0 raw42693step0Labels permutation51 permutation7
    mixedMoment B raw42693step1 raw42693step1Labels = mixedMoment B raw42693step2 raw42693step2Labels := by
      have ha : raw42693step2 = -raw42693step1 := by apply Matrix.ext; change ∀ i j, raw42693step2 i j = -(raw42693step1 i j); unfold raw42693step2 raw42693step1; decide +kernel
      have hl : raw42693step2Labels = raw42693step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42693step2 raw42693step2Labels = mixedMoment B raw42693step3 raw42693step3Labels := by
      have ha : raw42693step3 = raw42693step2 := by apply Matrix.ext; unfold raw42693step3 raw42693step2; decide +kernel
      have hl : raw42693step2Labels = labelEmbedding6 ∘ raw42693step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42693step2 raw42693step2Labels raw42693step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5199 node5199Labels := by rfl

def raw42694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw42694Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw42694step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42694step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42694step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42694step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42694 raw42694Labels = mixedMoment B node3580 node3580Labels := by
  calc
    mixedMoment B raw42694 raw42694Labels = mixedMoment B raw42694step0 raw42694step0Labels := by
      have hz : ∀ j, raw42694 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42694step0 = (fun i j => raw42694 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42694step0 raw42694; decide +kernel
      have hl : raw42694step0Labels = raw42694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42694 raw42694Labels permutation346 hz
    mixedMoment B raw42694step0 raw42694step0Labels = mixedMoment B raw42694step1 raw42694step1Labels := by
      have ha : raw42694step1 = (fun i j => raw42694step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42694step1 raw42694step0; decide +kernel
      have hl : raw42694step1Labels = raw42694step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42694step0 raw42694step0Labels permutation35 permutation2
    mixedMoment B raw42694step1 raw42694step1Labels = mixedMoment B raw42694step2 raw42694step2Labels := by
      have ha : raw42694step2 = raw42694step1 := by apply Matrix.ext; unfold raw42694step2 raw42694step1; decide +kernel
      have hl : raw42694step1Labels = labelEmbedding1 ∘ raw42694step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42694step1 raw42694step1Labels raw42694step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3580 node3580Labels := by rfl

def raw42695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw42695Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw42695step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42695step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42695step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42695step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42695step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42695step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42695 raw42695Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw42695 raw42695Labels = mixedMoment B raw42695step0 raw42695step0Labels := by
      have hz : ∀ j, raw42695 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42695step0 = (fun i j => raw42695 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42695step0 raw42695; decide +kernel
      have hl : raw42695step0Labels = raw42695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42695 raw42695Labels permutation346 hz
    mixedMoment B raw42695step0 raw42695step0Labels = mixedMoment B raw42695step1 raw42695step1Labels := by
      have ha : raw42695step1 = (fun i j => raw42695step0 (permutation48 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42695step1 raw42695step0; decide +kernel
      have hl : raw42695step1Labels = raw42695step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42695step0 raw42695step0Labels permutation48 permutation7
    mixedMoment B raw42695step1 raw42695step1Labels = mixedMoment B raw42695step2 raw42695step2Labels := by
      have ha : raw42695step2 = -raw42695step1 := by apply Matrix.ext; change ∀ i j, raw42695step2 i j = -(raw42695step1 i j); unfold raw42695step2 raw42695step1; decide +kernel
      have hl : raw42695step2Labels = raw42695step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42695step2 raw42695step2Labels = mixedMoment B raw42695step3 raw42695step3Labels := by
      have ha : raw42695step3 = raw42695step2 := by apply Matrix.ext; unfold raw42695step3 raw42695step2; decide +kernel
      have hl : raw42695step2Labels = labelEmbedding6 ∘ raw42695step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42695step2 raw42695step2Labels raw42695step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5282 node5282Labels := by rfl

def raw42696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42696Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42696step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42696step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42696step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42696 raw42696Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw42696 raw42696Labels = mixedMoment B raw42696step0 raw42696step0Labels := by
      have ha : raw42696step0 = (fun i j => raw42696 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42696step0 raw42696; decide +kernel
      have hl : raw42696step0Labels = raw42696Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42696 raw42696Labels permutation157 permutation2
    mixedMoment B raw42696step0 raw42696step0Labels = mixedMoment B raw42696step1 raw42696step1Labels := by
      have ha : raw42696step1 = raw42696step0 := by apply Matrix.ext; unfold raw42696step1 raw42696step0; decide +kernel
      have hl : raw42696step0Labels = labelEmbedding1 ∘ raw42696step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42696step0 raw42696step0Labels raw42696step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

def raw42697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42697Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42697step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42697step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42697step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw42697step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42697step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw42697step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42697 raw42697Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw42697 raw42697Labels = mixedMoment B raw42697step0 raw42697step0Labels := by
      have ha : raw42697step0 = (fun i j => raw42697 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42697step0 raw42697; decide +kernel
      have hl : raw42697step0Labels = raw42697Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42697 raw42697Labels permutation195 permutation7
    mixedMoment B raw42697step0 raw42697step0Labels = mixedMoment B raw42697step1 raw42697step1Labels := by
      have ha : raw42697step1 = -raw42697step0 := by apply Matrix.ext; change ∀ i j, raw42697step1 i j = -(raw42697step0 i j); unfold raw42697step1 raw42697step0; decide +kernel
      have hl : raw42697step1Labels = raw42697step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42697step1 raw42697step1Labels = mixedMoment B raw42697step2 raw42697step2Labels := by
      have ha : raw42697step2 = raw42697step1 := by apply Matrix.ext; unfold raw42697step2 raw42697step1; decide +kernel
      have hl : raw42697step1Labels = labelEmbedding6 ∘ raw42697step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42697step1 raw42697step1Labels raw42697step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5145 node5145Labels := by rfl

def raw42698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42698Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42698step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42698step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42698 raw42698Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw42698 raw42698Labels = mixedMoment B raw42698step0 raw42698step0Labels := by
      have hz : ∀ j, raw42698 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42698step0 = (fun i j => raw42698 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42698step0 raw42698; decide +kernel
      have hl : raw42698step0Labels = raw42698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42698 raw42698Labels permutation434 hz
    mixedMoment B raw42698step0 raw42698step0Labels = mixedMoment B raw42698step1 raw42698step1Labels := by
      have ha : raw42698step1 = raw42698step0 := by apply Matrix.ext; unfold raw42698step1 raw42698step0; decide +kernel
      have hl : raw42698step0Labels = labelEmbedding1 ∘ raw42698step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42698step0 raw42698step0Labels raw42698step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3541 node3541Labels := by rfl

def raw42699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42699Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42699step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw42699step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42699step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42699step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42699step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42699step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42699 raw42699Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw42699 raw42699Labels = mixedMoment B raw42699step0 raw42699step0Labels := by
      have hz : ∀ j, raw42699 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42699step0 = (fun i j => raw42699 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42699step0 raw42699; decide +kernel
      have hl : raw42699step0Labels = raw42699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42699 raw42699Labels permutation434 hz
    mixedMoment B raw42699step0 raw42699step0Labels = mixedMoment B raw42699step1 raw42699step1Labels := by
      have ha : raw42699step1 = (fun i j => raw42699step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42699step1 raw42699step0; decide +kernel
      have hl : raw42699step1Labels = raw42699step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42699step0 raw42699step0Labels permutation37 permutation7
    mixedMoment B raw42699step1 raw42699step1Labels = mixedMoment B raw42699step2 raw42699step2Labels := by
      have ha : raw42699step2 = -raw42699step1 := by apply Matrix.ext; change ∀ i j, raw42699step2 i j = -(raw42699step1 i j); unfold raw42699step2 raw42699step1; decide +kernel
      have hl : raw42699step2Labels = raw42699step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42699step2 raw42699step2Labels = mixedMoment B raw42699step3 raw42699step3Labels := by
      have ha : raw42699step3 = raw42699step2 := by apply Matrix.ext; unfold raw42699step3 raw42699step2; decide +kernel
      have hl : raw42699step2Labels = labelEmbedding6 ∘ raw42699step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42699step2 raw42699step2Labels raw42699step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw42700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42700Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42700step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42700step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42700 raw42700Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw42700 raw42700Labels = mixedMoment B raw42700step0 raw42700step0Labels := by
      have hz : ∀ j, raw42700 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42700step0 = (fun i j => raw42700 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42700step0 raw42700; decide +kernel
      have hl : raw42700step0Labels = raw42700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42700 raw42700Labels permutation434 hz
    mixedMoment B raw42700step0 raw42700step0Labels = mixedMoment B raw42700step1 raw42700step1Labels := by
      have ha : raw42700step1 = raw42700step0 := by apply Matrix.ext; unfold raw42700step1 raw42700step0; decide +kernel
      have hl : raw42700step0Labels = labelEmbedding1 ∘ raw42700step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42700step0 raw42700step0Labels raw42700step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

def raw42701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42701Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42701step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42701step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42701step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42701step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42701step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42701step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42701 raw42701Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw42701 raw42701Labels = mixedMoment B raw42701step0 raw42701step0Labels := by
      have hz : ∀ j, raw42701 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42701step0 = (fun i j => raw42701 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42701step0 raw42701; decide +kernel
      have hl : raw42701step0Labels = raw42701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42701 raw42701Labels permutation434 hz
    mixedMoment B raw42701step0 raw42701step0Labels = mixedMoment B raw42701step1 raw42701step1Labels := by
      have ha : raw42701step1 = (fun i j => raw42701step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42701step1 raw42701step0; decide +kernel
      have hl : raw42701step1Labels = raw42701step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42701step0 raw42701step0Labels permutation35 permutation7
    mixedMoment B raw42701step1 raw42701step1Labels = mixedMoment B raw42701step2 raw42701step2Labels := by
      have ha : raw42701step2 = -raw42701step1 := by apply Matrix.ext; change ∀ i j, raw42701step2 i j = -(raw42701step1 i j); unfold raw42701step2 raw42701step1; decide +kernel
      have hl : raw42701step2Labels = raw42701step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42701step2 raw42701step2Labels = mixedMoment B raw42701step3 raw42701step3Labels := by
      have ha : raw42701step3 = raw42701step2 := by apply Matrix.ext; unfold raw42701step3 raw42701step2; decide +kernel
      have hl : raw42701step2Labels = labelEmbedding6 ∘ raw42701step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42701step2 raw42701step2Labels raw42701step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw42702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42702Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw42702step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42702step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw42702step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42702 raw42702Labels = mixedMoment B node3538 node3538Labels := by
  calc
    mixedMoment B raw42702 raw42702Labels = mixedMoment B raw42702step0 raw42702step0Labels := by
      have hz : ∀ j, raw42702 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42702step0 = (fun i j => raw42702 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42702step0 raw42702; decide +kernel
      have hl : raw42702step0Labels = raw42702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42702 raw42702Labels permutation434 hz
    mixedMoment B raw42702step0 raw42702step0Labels = mixedMoment B raw42702step1 raw42702step1Labels := by
      have ha : raw42702step1 = raw42702step0 := by apply Matrix.ext; unfold raw42702step1 raw42702step0; decide +kernel
      have hl : raw42702step0Labels = labelEmbedding1 ∘ raw42702step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42702step0 raw42702step0Labels raw42702step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3538 node3538Labels := by rfl

def raw42703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42703Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw42703step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw42703step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42703step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw42703step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42703step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw42703step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42703 raw42703Labels = mixedMoment B node5188 node5188Labels := by
  calc
    mixedMoment B raw42703 raw42703Labels = mixedMoment B raw42703step0 raw42703step0Labels := by
      have hz : ∀ j, raw42703 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42703step0 = (fun i j => raw42703 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42703step0 raw42703; decide +kernel
      have hl : raw42703step0Labels = raw42703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42703 raw42703Labels permutation434 hz
    mixedMoment B raw42703step0 raw42703step0Labels = mixedMoment B raw42703step1 raw42703step1Labels := by
      have ha : raw42703step1 = (fun i j => raw42703step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42703step1 raw42703step0; decide +kernel
      have hl : raw42703step1Labels = raw42703step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42703step0 raw42703step0Labels permutation44 permutation7
    mixedMoment B raw42703step1 raw42703step1Labels = mixedMoment B raw42703step2 raw42703step2Labels := by
      have ha : raw42703step2 = -raw42703step1 := by apply Matrix.ext; change ∀ i j, raw42703step2 i j = -(raw42703step1 i j); unfold raw42703step2 raw42703step1; decide +kernel
      have hl : raw42703step2Labels = raw42703step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42703step2 raw42703step2Labels = mixedMoment B raw42703step3 raw42703step3Labels := by
      have ha : raw42703step3 = raw42703step2 := by apply Matrix.ext; unfold raw42703step3 raw42703step2; decide +kernel
      have hl : raw42703step2Labels = labelEmbedding6 ∘ raw42703step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42703step2 raw42703step2Labels raw42703step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5188 node5188Labels := by rfl

def raw42704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42704Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42704step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42704step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42704step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42704step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42704 raw42704Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw42704 raw42704Labels = mixedMoment B raw42704step0 raw42704step0Labels := by
      have ha : raw42704step0 = (fun i j => raw42704 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42704step0 raw42704; decide +kernel
      have hl : raw42704step0Labels = raw42704Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42704 raw42704Labels permutation158 permutation2
    mixedMoment B raw42704step0 raw42704step0Labels = mixedMoment B raw42704step1 raw42704step1Labels := by
      have ha : raw42704step1 = raw42704step0 := by apply Matrix.ext; unfold raw42704step1 raw42704step0; decide +kernel
      have hl : raw42704step0Labels = labelEmbedding1 ∘ raw42704step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42704step0 raw42704step0Labels raw42704step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

def raw42705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42705Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42705step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw42705step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42705step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw42705step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42705step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw42705step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42705 raw42705Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw42705 raw42705Labels = mixedMoment B raw42705step0 raw42705step0Labels := by
      have ha : raw42705step0 = (fun i j => raw42705 (permutation202 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42705step0 raw42705; decide +kernel
      have hl : raw42705step0Labels = raw42705Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42705 raw42705Labels permutation202 permutation7
    mixedMoment B raw42705step0 raw42705step0Labels = mixedMoment B raw42705step1 raw42705step1Labels := by
      have ha : raw42705step1 = -raw42705step0 := by apply Matrix.ext; change ∀ i j, raw42705step1 i j = -(raw42705step0 i j); unfold raw42705step1 raw42705step0; decide +kernel
      have hl : raw42705step1Labels = raw42705step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42705step1 raw42705step1Labels = mixedMoment B raw42705step2 raw42705step2Labels := by
      have ha : raw42705step2 = raw42705step1 := by apply Matrix.ext; unfold raw42705step2 raw42705step1; decide +kernel
      have hl : raw42705step1Labels = labelEmbedding6 ∘ raw42705step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42705step1 raw42705step1Labels raw42705step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5129 node5129Labels := by rfl

def raw42706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42706Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42706step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42706step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42706step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42706step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42706 raw42706Labels = mixedMoment B node3537 node3537Labels := by
  calc
    mixedMoment B raw42706 raw42706Labels = mixedMoment B raw42706step0 raw42706step0Labels := by
      have ha : raw42706step0 = (fun i j => raw42706 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42706step0 raw42706; decide +kernel
      have hl : raw42706step0Labels = raw42706Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42706 raw42706Labels permutation156 permutation2
    mixedMoment B raw42706step0 raw42706step0Labels = mixedMoment B raw42706step1 raw42706step1Labels := by
      have ha : raw42706step1 = raw42706step0 := by apply Matrix.ext; unfold raw42706step1 raw42706step0; decide +kernel
      have hl : raw42706step0Labels = labelEmbedding1 ∘ raw42706step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42706step0 raw42706step0Labels raw42706step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3537 node3537Labels := by rfl

def raw42707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42707Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42707step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42707step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42707step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42707step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42707step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42707step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42707 raw42707Labels = mixedMoment B node5187 node5187Labels := by
  calc
    mixedMoment B raw42707 raw42707Labels = mixedMoment B raw42707step0 raw42707step0Labels := by
      have ha : raw42707step0 = (fun i j => raw42707 (permutation249 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42707step0 raw42707; decide +kernel
      have hl : raw42707step0Labels = raw42707Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42707 raw42707Labels permutation249 permutation7
    mixedMoment B raw42707step0 raw42707step0Labels = mixedMoment B raw42707step1 raw42707step1Labels := by
      have ha : raw42707step1 = -raw42707step0 := by apply Matrix.ext; change ∀ i j, raw42707step1 i j = -(raw42707step0 i j); unfold raw42707step1 raw42707step0; decide +kernel
      have hl : raw42707step1Labels = raw42707step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42707step1 raw42707step1Labels = mixedMoment B raw42707step2 raw42707step2Labels := by
      have ha : raw42707step2 = raw42707step1 := by apply Matrix.ext; unfold raw42707step2 raw42707step1; decide +kernel
      have hl : raw42707step1Labels = labelEmbedding6 ∘ raw42707step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42707step1 raw42707step1Labels raw42707step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5187 node5187Labels := by rfl

def raw42708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42708Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42708step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42708step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42708step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42708step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42708 raw42708Labels = mixedMoment B node3539 node3539Labels := by
  calc
    mixedMoment B raw42708 raw42708Labels = mixedMoment B raw42708step0 raw42708step0Labels := by
      have ha : raw42708step0 = (fun i j => raw42708 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42708step0 raw42708; decide +kernel
      have hl : raw42708step0Labels = raw42708Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42708 raw42708Labels permutation155 permutation2
    mixedMoment B raw42708step0 raw42708step0Labels = mixedMoment B raw42708step1 raw42708step1Labels := by
      have ha : raw42708step1 = raw42708step0 := by apply Matrix.ext; unfold raw42708step1 raw42708step0; decide +kernel
      have hl : raw42708step0Labels = labelEmbedding1 ∘ raw42708step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42708step0 raw42708step0Labels raw42708step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3539 node3539Labels := by rfl

def raw42709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42709Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42709step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42709step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42709step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42709step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42709step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42709step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42709 raw42709Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw42709 raw42709Labels = mixedMoment B raw42709step0 raw42709step0Labels := by
      have ha : raw42709step0 = (fun i j => raw42709 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42709step0 raw42709; decide +kernel
      have hl : raw42709step0Labels = raw42709Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42709 raw42709Labels permutation169 permutation7
    mixedMoment B raw42709step0 raw42709step0Labels = mixedMoment B raw42709step1 raw42709step1Labels := by
      have ha : raw42709step1 = -raw42709step0 := by apply Matrix.ext; change ∀ i j, raw42709step1 i j = -(raw42709step0 i j); unfold raw42709step1 raw42709step0; decide +kernel
      have hl : raw42709step1Labels = raw42709step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42709step1 raw42709step1Labels = mixedMoment B raw42709step2 raw42709step2Labels := by
      have ha : raw42709step2 = raw42709step1 := by apply Matrix.ext; unfold raw42709step2 raw42709step1; decide +kernel
      have hl : raw42709step1Labels = labelEmbedding6 ∘ raw42709step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42709step1 raw42709step1Labels raw42709step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw42710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42710Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42710step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42710step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42710 raw42710Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw42710 raw42710Labels = mixedMoment B raw42710step0 raw42710step0Labels := by
      have ha : raw42710step0 = raw42710 := by apply Matrix.ext; unfold raw42710step0 raw42710; decide +kernel
      have hl : raw42710Labels = labelEmbedding1 ∘ raw42710step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42710 raw42710Labels raw42710step0Labels labelEmbedding1 hl
    _ = mixedMoment B node3526 node3526Labels := by rfl

def raw42711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42711Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42711step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw42711step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42711step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42711step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42711step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42711step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42711 raw42711Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw42711 raw42711Labels = mixedMoment B raw42711step0 raw42711step0Labels := by
      have ha : raw42711step0 = (fun i j => raw42711 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42711step0 raw42711; decide +kernel
      have hl : raw42711step0Labels = raw42711Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42711 raw42711Labels permutation170 permutation7
    mixedMoment B raw42711step0 raw42711step0Labels = mixedMoment B raw42711step1 raw42711step1Labels := by
      have ha : raw42711step1 = -raw42711step0 := by apply Matrix.ext; change ∀ i j, raw42711step1 i j = -(raw42711step0 i j); unfold raw42711step1 raw42711step0; decide +kernel
      have hl : raw42711step1Labels = raw42711step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42711step1 raw42711step1Labels = mixedMoment B raw42711step2 raw42711step2Labels := by
      have ha : raw42711step2 = raw42711step1 := by apply Matrix.ext; unfold raw42711step2 raw42711step1; decide +kernel
      have hl : raw42711step1Labels = labelEmbedding6 ∘ raw42711step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42711step1 raw42711step1Labels raw42711step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw42712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42712Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42712step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42712step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42712 raw42712Labels = mixedMoment B node3524 node3524Labels := by
  calc
    mixedMoment B raw42712 raw42712Labels = mixedMoment B raw42712step0 raw42712step0Labels := by
      have ha : raw42712step0 = raw42712 := by apply Matrix.ext; unfold raw42712step0 raw42712; decide +kernel
      have hl : raw42712Labels = labelEmbedding1 ∘ raw42712step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42712 raw42712Labels raw42712step0Labels labelEmbedding1 hl
    _ = mixedMoment B node3524 node3524Labels := by rfl

def raw42713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42713Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw42713step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42713step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42713step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42713step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42713step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42713 raw42713Labels = mixedMoment B node5184 node5184Labels := by
  calc
    mixedMoment B raw42713 raw42713Labels = mixedMoment B raw42713step0 raw42713step0Labels := by
      have ha : raw42713step0 = (fun i j => raw42713 (permutation224 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42713step0 raw42713; decide +kernel
      have hl : raw42713step0Labels = raw42713Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42713 raw42713Labels permutation224 permutation7
    mixedMoment B raw42713step0 raw42713step0Labels = mixedMoment B raw42713step1 raw42713step1Labels := by
      have ha : raw42713step1 = -raw42713step0 := by apply Matrix.ext; change ∀ i j, raw42713step1 i j = -(raw42713step0 i j); unfold raw42713step1 raw42713step0; decide +kernel
      have hl : raw42713step1Labels = raw42713step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42713step1 raw42713step1Labels = mixedMoment B raw42713step2 raw42713step2Labels := by
      have ha : raw42713step2 = raw42713step1 := by apply Matrix.ext; unfold raw42713step2 raw42713step1; decide +kernel
      have hl : raw42713step1Labels = labelEmbedding6 ∘ raw42713step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42713step1 raw42713step1Labels raw42713step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5184 node5184Labels := by rfl

def raw42714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42714Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42714step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42714step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42714 raw42714Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw42714 raw42714Labels = mixedMoment B raw42714step0 raw42714step0Labels := by
      have hz : ∀ j, raw42714 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42714step0 = (fun i j => raw42714 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42714step0 raw42714; decide +kernel
      have hl : raw42714step0Labels = raw42714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42714 raw42714Labels permutation434 hz
    mixedMoment B raw42714step0 raw42714step0Labels = mixedMoment B raw42714step1 raw42714step1Labels := by
      have ha : raw42714step1 = raw42714step0 := by apply Matrix.ext; unfold raw42714step1 raw42714step0; decide +kernel
      have hl : raw42714step0Labels = labelEmbedding1 ∘ raw42714step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42714step0 raw42714step0Labels raw42714step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw42715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42715Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42715step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw42715step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42715step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42715step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42715step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42715step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42715 raw42715Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw42715 raw42715Labels = mixedMoment B raw42715step0 raw42715step0Labels := by
      have hz : ∀ j, raw42715 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42715step0 = (fun i j => raw42715 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42715step0 raw42715; decide +kernel
      have hl : raw42715step0Labels = raw42715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42715 raw42715Labels permutation434 hz
    mixedMoment B raw42715step0 raw42715step0Labels = mixedMoment B raw42715step1 raw42715step1Labels := by
      have ha : raw42715step1 = (fun i j => raw42715step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42715step1 raw42715step0; decide +kernel
      have hl : raw42715step1Labels = raw42715step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42715step0 raw42715step0Labels permutation36 permutation7
    mixedMoment B raw42715step1 raw42715step1Labels = mixedMoment B raw42715step2 raw42715step2Labels := by
      have ha : raw42715step2 = -raw42715step1 := by apply Matrix.ext; change ∀ i j, raw42715step2 i j = -(raw42715step1 i j); unfold raw42715step2 raw42715step1; decide +kernel
      have hl : raw42715step2Labels = raw42715step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42715step2 raw42715step2Labels = mixedMoment B raw42715step3 raw42715step3Labels := by
      have ha : raw42715step3 = raw42715step2 := by apply Matrix.ext; unfold raw42715step3 raw42715step2; decide +kernel
      have hl : raw42715step2Labels = labelEmbedding6 ∘ raw42715step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42715step2 raw42715step2Labels raw42715step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw42716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw42716Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw42716step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw42716step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42716 raw42716Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw42716 raw42716Labels = mixedMoment B raw42716step0 raw42716step0Labels := by
      have hz : ∀ j, raw42716 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42716step0 = (fun i j => raw42716 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42716step0 raw42716; decide +kernel
      have hl : raw42716step0Labels = raw42716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42716 raw42716Labels permutation434 hz
    mixedMoment B raw42716step0 raw42716step0Labels = mixedMoment B raw42716step1 raw42716step1Labels := by
      have ha : raw42716step1 = raw42716step0 := by apply Matrix.ext; unfold raw42716step1 raw42716step0; decide +kernel
      have hl : raw42716step0Labels = labelEmbedding1 ∘ raw42716step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42716step0 raw42716step0Labels raw42716step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3530 node3530Labels := by rfl

def raw42717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw42717Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw42717step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw42717step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42717step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw42717step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42717 raw42717Labels = mixedMoment B node5147 node5147Labels := by
  calc
    mixedMoment B raw42717 raw42717Labels = mixedMoment B raw42717step0 raw42717step0Labels := by
      have hz : ∀ j, raw42717 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42717step0 = (fun i j => raw42717 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42717step0 raw42717; decide +kernel
      have hl : raw42717step0Labels = raw42717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42717 raw42717Labels permutation434 hz
    mixedMoment B raw42717step0 raw42717step0Labels = mixedMoment B raw42717step1 raw42717step1Labels := by
      have ha : raw42717step1 = (fun i j => raw42717step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42717step1 raw42717step0; decide +kernel
      have hl : raw42717step1Labels = raw42717step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42717step0 raw42717step0Labels permutation143 permutation7
    mixedMoment B raw42717step1 raw42717step1Labels = mixedMoment B raw42717step2 raw42717step2Labels := by
      have ha : raw42717step2 = raw42717step1 := by apply Matrix.ext; unfold raw42717step2 raw42717step1; decide +kernel
      have hl : raw42717step1Labels = labelEmbedding6 ∘ raw42717step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42717step1 raw42717step1Labels raw42717step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5147 node5147Labels := by rfl

def raw42718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw42718Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw42718step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42718step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw42718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42718step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw42718step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42718 raw42718Labels = mixedMoment B node3549 node3549Labels := by
  calc
    mixedMoment B raw42718 raw42718Labels = mixedMoment B raw42718step0 raw42718step0Labels := by
      have hz : ∀ j, raw42718 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42718step0 = (fun i j => raw42718 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42718step0 raw42718; decide +kernel
      have hl : raw42718step0Labels = raw42718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42718 raw42718Labels permutation434 hz
    mixedMoment B raw42718step0 raw42718step0Labels = mixedMoment B raw42718step1 raw42718step1Labels := by
      have hz : ∀ j, raw42718step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42718step1 = (fun i j => raw42718step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42718step1 raw42718step0; decide +kernel
      have hl : raw42718step1Labels = raw42718step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42718step0 raw42718step0Labels permutation80 hz
    mixedMoment B raw42718step1 raw42718step1Labels = mixedMoment B raw42718step2 raw42718step2Labels := by
      have ha : raw42718step2 = raw42718step1 := by apply Matrix.ext; unfold raw42718step2 raw42718step1; decide +kernel
      have hl : raw42718step1Labels = labelEmbedding1 ∘ raw42718step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42718step1 raw42718step1Labels raw42718step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3549 node3549Labels := by rfl

def raw42719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw42719Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw42719step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42719step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw42719step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42719step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw42719step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42719 raw42719Labels = mixedMoment B node5268 node5268Labels := by
  calc
    mixedMoment B raw42719 raw42719Labels = mixedMoment B raw42719step0 raw42719step0Labels := by
      have hz : ∀ j, raw42719 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42719step0 = (fun i j => raw42719 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42719step0 raw42719; decide +kernel
      have hl : raw42719step0Labels = raw42719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42719 raw42719Labels permutation434 hz
    mixedMoment B raw42719step0 raw42719step0Labels = mixedMoment B raw42719step1 raw42719step1Labels := by
      have hz : ∀ j, raw42719step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42719step1 = (fun i j => raw42719step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42719step1 raw42719step0; decide +kernel
      have hl : raw42719step1Labels = raw42719step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42719step0 raw42719step0Labels permutation80 hz
    mixedMoment B raw42719step1 raw42719step1Labels = mixedMoment B raw42719step2 raw42719step2Labels := by
      have ha : raw42719step2 = (fun i j => raw42719step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42719step2 raw42719step1; decide +kernel
      have hl : raw42719step2Labels = raw42719step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42719step1 raw42719step1Labels permutation23 permutation6
    _ = mixedMoment B node5268 node5268Labels := by rfl

def raw42720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw42720Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw42720step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42720step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 2, -4]]
def raw42720step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42720step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw42720step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42720step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw42720step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42720step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw42720step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42720 raw42720Labels = mixedMoment B node3302 node3302Labels := by
  calc
    mixedMoment B raw42720 raw42720Labels = mixedMoment B raw42720step0 raw42720step0Labels := by
      have hz : ∀ j, raw42720 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42720step0 = (fun i j => raw42720 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42720step0 raw42720; decide +kernel
      have hl : raw42720step0Labels = raw42720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42720 raw42720Labels permutation434 hz
    mixedMoment B raw42720step0 raw42720step0Labels = mixedMoment B raw42720step1 raw42720step1Labels := by
      have hz : ∀ j, raw42720step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42720step1 = (fun i j => raw42720step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42720step1 raw42720step0; decide +kernel
      have hl : raw42720step1Labels = raw42720step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42720step0 raw42720step0Labels permutation80 hz
    mixedMoment B raw42720step1 raw42720step1Labels = mixedMoment B raw42720step2 raw42720step2Labels := by
      have ha : raw42720step2 = (fun i j => raw42720step1 (permutation28 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42720step2 raw42720step1; decide +kernel
      have hl : raw42720step2Labels = raw42720step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42720step1 raw42720step1Labels permutation28 permutation4
    mixedMoment B raw42720step2 raw42720step2Labels = mixedMoment B raw42720step3 raw42720step3Labels := by
      have ha : raw42720step3 = -raw42720step2 := by apply Matrix.ext; change ∀ i j, raw42720step3 i j = -(raw42720step2 i j); unfold raw42720step3 raw42720step2; decide +kernel
      have hl : raw42720step3Labels = raw42720step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42720step3 raw42720step3Labels = mixedMoment B raw42720step4 raw42720step4Labels := by
      have ha : raw42720step4 = raw42720step3 := by apply Matrix.ext; unfold raw42720step4 raw42720step3; decide +kernel
      have hl : raw42720step3Labels = labelEmbedding1 ∘ raw42720step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42720step3 raw42720step3Labels raw42720step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3302 node3302Labels := by rfl

def raw42721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw42721Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw42721step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42721step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 2, -4]]
def raw42721step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42721step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw42721step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42721 raw42721Labels = mixedMoment B node4609 node4609Labels := by
  calc
    mixedMoment B raw42721 raw42721Labels = mixedMoment B raw42721step0 raw42721step0Labels := by
      have hz : ∀ j, raw42721 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42721step0 = (fun i j => raw42721 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42721step0 raw42721; decide +kernel
      have hl : raw42721step0Labels = raw42721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42721 raw42721Labels permutation434 hz
    mixedMoment B raw42721step0 raw42721step0Labels = mixedMoment B raw42721step1 raw42721step1Labels := by
      have hz : ∀ j, raw42721step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42721step1 = (fun i j => raw42721step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42721step1 raw42721step0; decide +kernel
      have hl : raw42721step1Labels = raw42721step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42721step0 raw42721step0Labels permutation80 hz
    mixedMoment B raw42721step1 raw42721step1Labels = mixedMoment B raw42721step2 raw42721step2Labels := by
      have ha : raw42721step2 = (fun i j => raw42721step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42721step2 raw42721step1; decide +kernel
      have hl : raw42721step2Labels = raw42721step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42721step1 raw42721step1Labels permutation29 permutation6
    _ = mixedMoment B node4609 node4609Labels := by rfl

def raw42722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42722Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42722step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw42722step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42722step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42722step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42722step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42722step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42722 raw42722Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw42722 raw42722Labels = mixedMoment B raw42722step0 raw42722step0Labels := by
      have hz : ∀ j, raw42722 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42722step0 = (fun i j => raw42722 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42722step0 raw42722; decide +kernel
      have hl : raw42722step0Labels = raw42722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42722 raw42722Labels permutation346 hz
    mixedMoment B raw42722step0 raw42722step0Labels = mixedMoment B raw42722step1 raw42722step1Labels := by
      have ha : raw42722step1 = (fun i j => raw42722step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42722step1 raw42722step0; decide +kernel
      have hl : raw42722step1Labels = raw42722step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42722step0 raw42722step0Labels permutation151 permutation2
    mixedMoment B raw42722step1 raw42722step1Labels = mixedMoment B raw42722step2 raw42722step2Labels := by
      have ha : raw42722step2 = -raw42722step1 := by apply Matrix.ext; change ∀ i j, raw42722step2 i j = -(raw42722step1 i j); unfold raw42722step2 raw42722step1; decide +kernel
      have hl : raw42722step2Labels = raw42722step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42722step2 raw42722step2Labels = mixedMoment B raw42722step3 raw42722step3Labels := by
      have ha : raw42722step3 = raw42722step2 := by apply Matrix.ext; unfold raw42722step3 raw42722step2; decide +kernel
      have hl : raw42722step2Labels = labelEmbedding1 ∘ raw42722step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42722step2 raw42722step2Labels raw42722step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

def raw42723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42723Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42723step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw42723step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42723step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw42723step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42723 raw42723Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw42723 raw42723Labels = mixedMoment B raw42723step0 raw42723step0Labels := by
      have hz : ∀ j, raw42723 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42723step0 = (fun i j => raw42723 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42723step0 raw42723; decide +kernel
      have hl : raw42723step0Labels = raw42723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42723 raw42723Labels permutation346 hz
    mixedMoment B raw42723step0 raw42723step0Labels = mixedMoment B raw42723step1 raw42723step1Labels := by
      have ha : raw42723step1 = (fun i j => raw42723step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42723step1 raw42723step0; decide +kernel
      have hl : raw42723step1Labels = raw42723step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42723step0 raw42723step0Labels permutation149 permutation7
    mixedMoment B raw42723step1 raw42723step1Labels = mixedMoment B raw42723step2 raw42723step2Labels := by
      have ha : raw42723step2 = raw42723step1 := by apply Matrix.ext; unfold raw42723step2 raw42723step1; decide +kernel
      have hl : raw42723step1Labels = labelEmbedding6 ∘ raw42723step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42723step1 raw42723step1Labels raw42723step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4591 node4591Labels := by rfl

def raw42724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw42724Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw42724step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw42724step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw42724step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42724step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw42724step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42724 raw42724Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw42724 raw42724Labels = mixedMoment B raw42724step0 raw42724step0Labels := by
      have hz : ∀ j, raw42724 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42724step0 = (fun i j => raw42724 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42724step0 raw42724; decide +kernel
      have hl : raw42724step0Labels = raw42724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42724 raw42724Labels permutation346 hz
    mixedMoment B raw42724step0 raw42724step0Labels = mixedMoment B raw42724step1 raw42724step1Labels := by
      have ha : raw42724step1 = (fun i j => raw42724step0 (permutation88 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42724step1 raw42724step0; decide +kernel
      have hl : raw42724step1Labels = raw42724step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42724step0 raw42724step0Labels permutation88 permutation4
    mixedMoment B raw42724step1 raw42724step1Labels = mixedMoment B raw42724step2 raw42724step2Labels := by
      have ha : raw42724step2 = -raw42724step1 := by apply Matrix.ext; change ∀ i j, raw42724step2 i j = -(raw42724step1 i j); unfold raw42724step2 raw42724step1; decide +kernel
      have hl : raw42724step2Labels = raw42724step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42724step2 raw42724step2Labels = mixedMoment B raw42724step3 raw42724step3Labels := by
      have ha : raw42724step3 = raw42724step2 := by apply Matrix.ext; unfold raw42724step3 raw42724step2; decide +kernel
      have hl : raw42724step2Labels = labelEmbedding1 ∘ raw42724step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42724step2 raw42724step2Labels raw42724step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3523 node3523Labels := by rfl

def raw42725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw42725Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw42725step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw42725step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42725 raw42725Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw42725 raw42725Labels = mixedMoment B raw42725step0 raw42725step0Labels := by
      have hz : ∀ j, raw42725 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42725step0 = (fun i j => raw42725 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42725step0 raw42725; decide +kernel
      have hl : raw42725step0Labels = raw42725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42725 raw42725Labels permutation346 hz
    mixedMoment B raw42725step0 raw42725step0Labels = mixedMoment B raw42725step1 raw42725step1Labels := by
      have ha : raw42725step1 = (fun i j => raw42725step0 (permutation95 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42725step1 raw42725step0; decide +kernel
      have hl : raw42725step1Labels = raw42725step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42725step0 raw42725step0Labels permutation95 permutation6
    _ = mixedMoment B node5139 node5139Labels := by rfl

def raw42726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw42726Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw42726step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw42726step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42726step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw42726step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42726 raw42726Labels = mixedMoment B node3543 node3543Labels := by
  calc
    mixedMoment B raw42726 raw42726Labels = mixedMoment B raw42726step0 raw42726step0Labels := by
      have hz : ∀ j, raw42726 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42726step0 = (fun i j => raw42726 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42726step0 raw42726; decide +kernel
      have hl : raw42726step0Labels = raw42726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42726 raw42726Labels permutation346 hz
    mixedMoment B raw42726step0 raw42726step0Labels = mixedMoment B raw42726step1 raw42726step1Labels := by
      have ha : raw42726step1 = (fun i j => raw42726step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42726step1 raw42726step0; decide +kernel
      have hl : raw42726step1Labels = raw42726step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42726step0 raw42726step0Labels permutation35 permutation2
    mixedMoment B raw42726step1 raw42726step1Labels = mixedMoment B raw42726step2 raw42726step2Labels := by
      have ha : raw42726step2 = raw42726step1 := by apply Matrix.ext; unfold raw42726step2 raw42726step1; decide +kernel
      have hl : raw42726step1Labels = labelEmbedding1 ∘ raw42726step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42726step1 raw42726step1Labels raw42726step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3543 node3543Labels := by rfl

def raw42727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw42727Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw42727step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42727step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw42727step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42727 raw42727Labels = mixedMoment B node5252 node5252Labels := by
  calc
    mixedMoment B raw42727 raw42727Labels = mixedMoment B raw42727step0 raw42727step0Labels := by
      have hz : ∀ j, raw42727 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42727step0 = (fun i j => raw42727 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42727step0 raw42727; decide +kernel
      have hl : raw42727step0Labels = raw42727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42727 raw42727Labels permutation346 hz
    mixedMoment B raw42727step0 raw42727step0Labels = mixedMoment B raw42727step1 raw42727step1Labels := by
      have ha : raw42727step1 = (fun i j => raw42727step0 (permutation89 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42727step1 raw42727step0; decide +kernel
      have hl : raw42727step1Labels = raw42727step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42727step0 raw42727step0Labels permutation89 permutation6
    _ = mixedMoment B node5252 node5252Labels := by rfl

def raw42728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw42728Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw42728step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42728step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42728step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42728step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42728 raw42728Labels = mixedMoment B node3542 node3542Labels := by
  calc
    mixedMoment B raw42728 raw42728Labels = mixedMoment B raw42728step0 raw42728step0Labels := by
      have hz : ∀ j, raw42728 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42728step0 = (fun i j => raw42728 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42728step0 raw42728; decide +kernel
      have hl : raw42728step0Labels = raw42728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42728 raw42728Labels permutation346 hz
    mixedMoment B raw42728step0 raw42728step0Labels = mixedMoment B raw42728step1 raw42728step1Labels := by
      have ha : raw42728step1 = (fun i j => raw42728step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42728step1 raw42728step0; decide +kernel
      have hl : raw42728step1Labels = raw42728step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42728step0 raw42728step0Labels permutation36 permutation2
    mixedMoment B raw42728step1 raw42728step1Labels = mixedMoment B raw42728step2 raw42728step2Labels := by
      have ha : raw42728step2 = raw42728step1 := by apply Matrix.ext; unfold raw42728step2 raw42728step1; decide +kernel
      have hl : raw42728step1Labels = labelEmbedding1 ∘ raw42728step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42728step1 raw42728step1Labels raw42728step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3542 node3542Labels := by rfl

def raw42729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw42729Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw42729step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw42729step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw42729step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42729step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw42729step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42729 raw42729Labels = mixedMoment B node5189 node5189Labels := by
  calc
    mixedMoment B raw42729 raw42729Labels = mixedMoment B raw42729step0 raw42729step0Labels := by
      have hz : ∀ j, raw42729 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42729step0 = (fun i j => raw42729 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42729step0 raw42729; decide +kernel
      have hl : raw42729step0Labels = raw42729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42729 raw42729Labels permutation346 hz
    mixedMoment B raw42729step0 raw42729step0Labels = mixedMoment B raw42729step1 raw42729step1Labels := by
      have ha : raw42729step1 = (fun i j => raw42729step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42729step1 raw42729step0; decide +kernel
      have hl : raw42729step1Labels = raw42729step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42729step0 raw42729step0Labels permutation50 permutation7
    mixedMoment B raw42729step1 raw42729step1Labels = mixedMoment B raw42729step2 raw42729step2Labels := by
      have ha : raw42729step2 = -raw42729step1 := by apply Matrix.ext; change ∀ i j, raw42729step2 i j = -(raw42729step1 i j); unfold raw42729step2 raw42729step1; decide +kernel
      have hl : raw42729step2Labels = raw42729step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42729step2 raw42729step2Labels = mixedMoment B raw42729step3 raw42729step3Labels := by
      have ha : raw42729step3 = raw42729step2 := by apply Matrix.ext; unfold raw42729step3 raw42729step2; decide +kernel
      have hl : raw42729step2Labels = labelEmbedding6 ∘ raw42729step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42729step2 raw42729step2Labels raw42729step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5189 node5189Labels := by rfl

def raw42730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42730Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42730step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42730step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42730step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42730step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42730 raw42730Labels = mixedMoment B node3519 node3519Labels := by
  calc
    mixedMoment B raw42730 raw42730Labels = mixedMoment B raw42730step0 raw42730step0Labels := by
      have ha : raw42730step0 = (fun i j => raw42730 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42730step0 raw42730; decide +kernel
      have hl : raw42730step0Labels = raw42730Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42730 raw42730Labels permutation157 permutation2
    mixedMoment B raw42730step0 raw42730step0Labels = mixedMoment B raw42730step1 raw42730step1Labels := by
      have ha : raw42730step1 = raw42730step0 := by apply Matrix.ext; unfold raw42730step1 raw42730step0; decide +kernel
      have hl : raw42730step0Labels = labelEmbedding1 ∘ raw42730step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42730step0 raw42730step0Labels raw42730step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3519 node3519Labels := by rfl

def raw42731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42731Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw42731step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42731 raw42731Labels = mixedMoment B node5128 node5128Labels := by
  calc
    mixedMoment B raw42731 raw42731Labels = mixedMoment B raw42731step0 raw42731step0Labels := by
      have ha : raw42731step0 = (fun i j => raw42731 (permutation494 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42731step0 raw42731; decide +kernel
      have hl : raw42731step0Labels = raw42731Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42731 raw42731Labels permutation494 permutation6
    _ = mixedMoment B node5128 node5128Labels := by rfl

def raw42732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42732Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw42732step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw42732step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42732step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw42732step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42732step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw42732step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42732 raw42732Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw42732 raw42732Labels = mixedMoment B raw42732step0 raw42732step0Labels := by
      have hz : ∀ j, raw42732 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42732step0 = (fun i j => raw42732 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42732step0 raw42732; decide +kernel
      have hl : raw42732step0Labels = raw42732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42732 raw42732Labels permutation434 hz
    mixedMoment B raw42732step0 raw42732step0Labels = mixedMoment B raw42732step1 raw42732step1Labels := by
      have ha : raw42732step1 = (fun i j => raw42732step0 (permutation94 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42732step1 raw42732step0; decide +kernel
      have hl : raw42732step1Labels = raw42732step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42732step0 raw42732step0Labels permutation94 permutation4
    mixedMoment B raw42732step1 raw42732step1Labels = mixedMoment B raw42732step2 raw42732step2Labels := by
      have ha : raw42732step2 = -raw42732step1 := by apply Matrix.ext; change ∀ i j, raw42732step2 i j = -(raw42732step1 i j); unfold raw42732step2 raw42732step1; decide +kernel
      have hl : raw42732step2Labels = raw42732step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42732step2 raw42732step2Labels = mixedMoment B raw42732step3 raw42732step3Labels := by
      have ha : raw42732step3 = raw42732step2 := by apply Matrix.ext; unfold raw42732step3 raw42732step2; decide +kernel
      have hl : raw42732step2Labels = labelEmbedding1 ∘ raw42732step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42732step2 raw42732step2Labels raw42732step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2207 node2207Labels := by rfl

def raw42733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42733Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw42733step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw42733step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42733 raw42733Labels = mixedMoment B node4817 node4817Labels := by
  calc
    mixedMoment B raw42733 raw42733Labels = mixedMoment B raw42733step0 raw42733step0Labels := by
      have hz : ∀ j, raw42733 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42733step0 = (fun i j => raw42733 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42733step0 raw42733; decide +kernel
      have hl : raw42733step0Labels = raw42733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42733 raw42733Labels permutation434 hz
    mixedMoment B raw42733step0 raw42733step0Labels = mixedMoment B raw42733step1 raw42733step1Labels := by
      have ha : raw42733step1 = (fun i j => raw42733step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42733step1 raw42733step0; decide +kernel
      have hl : raw42733step1Labels = raw42733step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42733step0 raw42733step0Labels permutation97 permutation6
    _ = mixedMoment B node4817 node4817Labels := by rfl

def raw42734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42734Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw42734step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3]]
def raw42734step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42734step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw42734step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42734step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw42734step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42734 raw42734Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw42734 raw42734Labels = mixedMoment B raw42734step0 raw42734step0Labels := by
      have hz : ∀ j, raw42734 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42734step0 = (fun i j => raw42734 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42734step0 raw42734; decide +kernel
      have hl : raw42734step0Labels = raw42734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42734 raw42734Labels permutation434 hz
    mixedMoment B raw42734step0 raw42734step0Labels = mixedMoment B raw42734step1 raw42734step1Labels := by
      have ha : raw42734step1 = (fun i j => raw42734step0 (permutation91 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42734step1 raw42734step0; decide +kernel
      have hl : raw42734step1Labels = raw42734step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42734step0 raw42734step0Labels permutation91 permutation4
    mixedMoment B raw42734step1 raw42734step1Labels = mixedMoment B raw42734step2 raw42734step2Labels := by
      have ha : raw42734step2 = -raw42734step1 := by apply Matrix.ext; change ∀ i j, raw42734step2 i j = -(raw42734step1 i j); unfold raw42734step2 raw42734step1; decide +kernel
      have hl : raw42734step2Labels = raw42734step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42734step2 raw42734step2Labels = mixedMoment B raw42734step3 raw42734step3Labels := by
      have ha : raw42734step3 = raw42734step2 := by apply Matrix.ext; unfold raw42734step3 raw42734step2; decide +kernel
      have hl : raw42734step2Labels = labelEmbedding1 ∘ raw42734step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42734step2 raw42734step2Labels raw42734step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2259 node2259Labels := by rfl

def raw42735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42735Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw42735step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw42735step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42735 raw42735Labels = mixedMoment B node4853 node4853Labels := by
  calc
    mixedMoment B raw42735 raw42735Labels = mixedMoment B raw42735step0 raw42735step0Labels := by
      have hz : ∀ j, raw42735 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42735step0 = (fun i j => raw42735 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42735step0 raw42735; decide +kernel
      have hl : raw42735step0Labels = raw42735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42735 raw42735Labels permutation434 hz
    mixedMoment B raw42735step0 raw42735step0Labels = mixedMoment B raw42735step1 raw42735step1Labels := by
      have ha : raw42735step1 = (fun i j => raw42735step0 (permutation103 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42735step1 raw42735step0; decide +kernel
      have hl : raw42735step1Labels = raw42735step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42735step0 raw42735step0Labels permutation103 permutation6
    _ = mixedMoment B node4853 node4853Labels := by rfl

def raw42736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42736Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw42736step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42736step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw42736step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42736step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw42736step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42736step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw42736step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42736 raw42736Labels = mixedMoment B node2153 node2153Labels := by
  calc
    mixedMoment B raw42736 raw42736Labels = mixedMoment B raw42736step0 raw42736step0Labels := by
      have hz : ∀ j, raw42736 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42736step0 = (fun i j => raw42736 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42736step0 raw42736; decide +kernel
      have hl : raw42736step0Labels = raw42736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42736 raw42736Labels permutation434 hz
    mixedMoment B raw42736step0 raw42736step0Labels = mixedMoment B raw42736step1 raw42736step1Labels := by
      have ha : raw42736step1 = (fun i j => raw42736step0 (permutation100 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42736step1 raw42736step0; decide +kernel
      have hl : raw42736step1Labels = raw42736step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42736step0 raw42736step0Labels permutation100 permutation4
    mixedMoment B raw42736step1 raw42736step1Labels = mixedMoment B raw42736step2 raw42736step2Labels := by
      have ha : raw42736step2 = -raw42736step1 := by apply Matrix.ext; change ∀ i j, raw42736step2 i j = -(raw42736step1 i j); unfold raw42736step2 raw42736step1; decide +kernel
      have hl : raw42736step2Labels = raw42736step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42736step2 raw42736step2Labels = mixedMoment B raw42736step3 raw42736step3Labels := by
      have ha : raw42736step3 = raw42736step2 := by apply Matrix.ext; unfold raw42736step3 raw42736step2; decide +kernel
      have hl : raw42736step2Labels = labelEmbedding1 ∘ raw42736step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42736step2 raw42736step2Labels raw42736step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2153 node2153Labels := by rfl

def raw42737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42737Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw42737step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw42737step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42737 raw42737Labels = mixedMoment B node4682 node4682Labels := by
  calc
    mixedMoment B raw42737 raw42737Labels = mixedMoment B raw42737step0 raw42737step0Labels := by
      have hz : ∀ j, raw42737 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42737step0 = (fun i j => raw42737 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42737step0 raw42737; decide +kernel
      have hl : raw42737step0Labels = raw42737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42737 raw42737Labels permutation434 hz
    mixedMoment B raw42737step0 raw42737step0Labels = mixedMoment B raw42737step1 raw42737step1Labels := by
      have ha : raw42737step1 = (fun i j => raw42737step0 (permutation101 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42737step1 raw42737step0; decide +kernel
      have hl : raw42737step1Labels = raw42737step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42737step0 raw42737step0Labels permutation101 permutation6
    _ = mixedMoment B node4682 node4682Labels := by rfl

def raw42738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42738Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42738step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw42738step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42738step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42738step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42738step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42738step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42738 raw42738Labels = mixedMoment B node2147 node2147Labels := by
  calc
    mixedMoment B raw42738 raw42738Labels = mixedMoment B raw42738step0 raw42738step0Labels := by
      have ha : raw42738step0 = (fun i j => raw42738 (permutation423 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42738step0 raw42738; decide +kernel
      have hl : raw42738step0Labels = raw42738Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42738 raw42738Labels permutation423 permutation4
    mixedMoment B raw42738step0 raw42738step0Labels = mixedMoment B raw42738step1 raw42738step1Labels := by
      have ha : raw42738step1 = -raw42738step0 := by apply Matrix.ext; change ∀ i j, raw42738step1 i j = -(raw42738step0 i j); unfold raw42738step1 raw42738step0; decide +kernel
      have hl : raw42738step1Labels = raw42738step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42738step1 raw42738step1Labels = mixedMoment B raw42738step2 raw42738step2Labels := by
      have ha : raw42738step2 = raw42738step1 := by apply Matrix.ext; unfold raw42738step2 raw42738step1; decide +kernel
      have hl : raw42738step1Labels = labelEmbedding1 ∘ raw42738step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42738step1 raw42738step1Labels raw42738step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2147 node2147Labels := by rfl

def raw42739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42739Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42739step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw42739step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42739 raw42739Labels = mixedMoment B node4664 node4664Labels := by
  calc
    mixedMoment B raw42739 raw42739Labels = mixedMoment B raw42739step0 raw42739step0Labels := by
      have ha : raw42739step0 = (fun i j => raw42739 (permutation431 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42739step0 raw42739; decide +kernel
      have hl : raw42739step0Labels = raw42739Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42739 raw42739Labels permutation431 permutation6
    _ = mixedMoment B node4664 node4664Labels := by rfl

def raw42740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42740Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw42740step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42740step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw42740step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42740step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw42740step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42740 raw42740Labels = mixedMoment B node2175 node2175Labels := by
  calc
    mixedMoment B raw42740 raw42740Labels = mixedMoment B raw42740step0 raw42740step0Labels := by
      have ha : raw42740step0 = (fun i j => raw42740 (permutation391 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42740step0 raw42740; decide +kernel
      have hl : raw42740step0Labels = raw42740Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42740 raw42740Labels permutation391 permutation4
    mixedMoment B raw42740step0 raw42740step0Labels = mixedMoment B raw42740step1 raw42740step1Labels := by
      have ha : raw42740step1 = -raw42740step0 := by apply Matrix.ext; change ∀ i j, raw42740step1 i j = -(raw42740step0 i j); unfold raw42740step1 raw42740step0; decide +kernel
      have hl : raw42740step1Labels = raw42740step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42740step1 raw42740step1Labels = mixedMoment B raw42740step2 raw42740step2Labels := by
      have ha : raw42740step2 = raw42740step1 := by apply Matrix.ext; unfold raw42740step2 raw42740step1; decide +kernel
      have hl : raw42740step1Labels = labelEmbedding1 ∘ raw42740step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42740step1 raw42740step1Labels raw42740step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2175 node2175Labels := by rfl

def raw42741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42741Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw42741step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42741 raw42741Labels = mixedMoment B node4761 node4761Labels := by
  calc
    mixedMoment B raw42741 raw42741Labels = mixedMoment B raw42741step0 raw42741step0Labels := by
      have ha : raw42741step0 = (fun i j => raw42741 (permutation392 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42741step0 raw42741; decide +kernel
      have hl : raw42741step0Labels = raw42741Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42741 raw42741Labels permutation392 permutation6
    _ = mixedMoment B node4761 node4761Labels := by rfl

def raw42742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42742Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw42742step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42742step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw42742step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42742step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw42742step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42742 raw42742Labels = mixedMoment B node2201 node2201Labels := by
  calc
    mixedMoment B raw42742 raw42742Labels = mixedMoment B raw42742step0 raw42742step0Labels := by
      have ha : raw42742step0 = (fun i j => raw42742 (permutation387 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42742step0 raw42742; decide +kernel
      have hl : raw42742step0Labels = raw42742Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42742 raw42742Labels permutation387 permutation4
    mixedMoment B raw42742step0 raw42742step0Labels = mixedMoment B raw42742step1 raw42742step1Labels := by
      have ha : raw42742step1 = -raw42742step0 := by apply Matrix.ext; change ∀ i j, raw42742step1 i j = -(raw42742step0 i j); unfold raw42742step1 raw42742step0; decide +kernel
      have hl : raw42742step1Labels = raw42742step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42742step1 raw42742step1Labels = mixedMoment B raw42742step2 raw42742step2Labels := by
      have ha : raw42742step2 = raw42742step1 := by apply Matrix.ext; unfold raw42742step2 raw42742step1; decide +kernel
      have hl : raw42742step1Labels = labelEmbedding1 ∘ raw42742step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42742step1 raw42742step1Labels raw42742step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2201 node2201Labels := by rfl

def raw42743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42743Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw42743step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42743 raw42743Labels = mixedMoment B node4792 node4792Labels := by
  calc
    mixedMoment B raw42743 raw42743Labels = mixedMoment B raw42743step0 raw42743step0Labels := by
      have ha : raw42743step0 = (fun i j => raw42743 (permutation394 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42743step0 raw42743; decide +kernel
      have hl : raw42743step0Labels = raw42743Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42743 raw42743Labels permutation394 permutation6
    _ = mixedMoment B node4792 node4792Labels := by rfl

def raw42744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42744Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42744step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42744step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42744step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42744step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42744 raw42744Labels = mixedMoment B node3464 node3464Labels := by
  calc
    mixedMoment B raw42744 raw42744Labels = mixedMoment B raw42744step0 raw42744step0Labels := by
      have ha : raw42744step0 = (fun i j => raw42744 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42744step0 raw42744; decide +kernel
      have hl : raw42744step0Labels = raw42744Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42744 raw42744Labels permutation158 permutation2
    mixedMoment B raw42744step0 raw42744step0Labels = mixedMoment B raw42744step1 raw42744step1Labels := by
      have ha : raw42744step1 = raw42744step0 := by apply Matrix.ext; unfold raw42744step1 raw42744step0; decide +kernel
      have hl : raw42744step0Labels = labelEmbedding1 ∘ raw42744step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42744step0 raw42744step0Labels raw42744step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3464 node3464Labels := by rfl

def raw42745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42745Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42745step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw42745step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42745step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42745step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42745step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42745step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42745 raw42745Labels = mixedMoment B node5086 node5086Labels := by
  calc
    mixedMoment B raw42745 raw42745Labels = mixedMoment B raw42745step0 raw42745step0Labels := by
      have ha : raw42745step0 = (fun i j => raw42745 (permutation173 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42745step0 raw42745; decide +kernel
      have hl : raw42745step0Labels = raw42745Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42745 raw42745Labels permutation173 permutation7
    mixedMoment B raw42745step0 raw42745step0Labels = mixedMoment B raw42745step1 raw42745step1Labels := by
      have ha : raw42745step1 = -raw42745step0 := by apply Matrix.ext; change ∀ i j, raw42745step1 i j = -(raw42745step0 i j); unfold raw42745step1 raw42745step0; decide +kernel
      have hl : raw42745step1Labels = raw42745step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42745step1 raw42745step1Labels = mixedMoment B raw42745step2 raw42745step2Labels := by
      have ha : raw42745step2 = raw42745step1 := by apply Matrix.ext; unfold raw42745step2 raw42745step1; decide +kernel
      have hl : raw42745step1Labels = labelEmbedding6 ∘ raw42745step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42745step1 raw42745step1Labels raw42745step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5086 node5086Labels := by rfl

def raw42746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42746Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42746step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42746step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42746step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42746 raw42746Labels = mixedMoment B node3463 node3463Labels := by
  calc
    mixedMoment B raw42746 raw42746Labels = mixedMoment B raw42746step0 raw42746step0Labels := by
      have ha : raw42746step0 = (fun i j => raw42746 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42746step0 raw42746; decide +kernel
      have hl : raw42746step0Labels = raw42746Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42746 raw42746Labels permutation158 permutation2
    mixedMoment B raw42746step0 raw42746step0Labels = mixedMoment B raw42746step1 raw42746step1Labels := by
      have ha : raw42746step1 = raw42746step0 := by apply Matrix.ext; unfold raw42746step1 raw42746step0; decide +kernel
      have hl : raw42746step0Labels = labelEmbedding1 ∘ raw42746step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42746step0 raw42746step0Labels raw42746step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3463 node3463Labels := by rfl

def raw42747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42747Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw42747step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42747step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42747step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42747step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42747step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42747 raw42747Labels = mixedMoment B node5074 node5074Labels := by
  calc
    mixedMoment B raw42747 raw42747Labels = mixedMoment B raw42747step0 raw42747step0Labels := by
      have ha : raw42747step0 = (fun i j => raw42747 (permutation167 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42747step0 raw42747; decide +kernel
      have hl : raw42747step0Labels = raw42747Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42747 raw42747Labels permutation167 permutation7
    mixedMoment B raw42747step0 raw42747step0Labels = mixedMoment B raw42747step1 raw42747step1Labels := by
      have ha : raw42747step1 = -raw42747step0 := by apply Matrix.ext; change ∀ i j, raw42747step1 i j = -(raw42747step0 i j); unfold raw42747step1 raw42747step0; decide +kernel
      have hl : raw42747step1Labels = raw42747step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42747step1 raw42747step1Labels = mixedMoment B raw42747step2 raw42747step2Labels := by
      have ha : raw42747step2 = raw42747step1 := by apply Matrix.ext; unfold raw42747step2 raw42747step1; decide +kernel
      have hl : raw42747step1Labels = labelEmbedding6 ∘ raw42747step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42747step1 raw42747step1Labels raw42747step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5074 node5074Labels := by rfl

def raw42748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42748Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42748step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw42748step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42748step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw42748step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42748 raw42748Labels = mixedMoment B node3462 node3462Labels := by
  calc
    mixedMoment B raw42748 raw42748Labels = mixedMoment B raw42748step0 raw42748step0Labels := by
      have ha : raw42748step0 = (fun i j => raw42748 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42748step0 raw42748; decide +kernel
      have hl : raw42748step0Labels = raw42748Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42748 raw42748Labels permutation158 permutation2
    mixedMoment B raw42748step0 raw42748step0Labels = mixedMoment B raw42748step1 raw42748step1Labels := by
      have ha : raw42748step1 = raw42748step0 := by apply Matrix.ext; unfold raw42748step1 raw42748step0; decide +kernel
      have hl : raw42748step0Labels = labelEmbedding1 ∘ raw42748step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42748step0 raw42748step0Labels raw42748step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3462 node3462Labels := by rfl

def raw42749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42749Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42749step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw42749step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42749step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw42749step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42749step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw42749step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42749 raw42749Labels = mixedMoment B node5042 node5042Labels := by
  calc
    mixedMoment B raw42749 raw42749Labels = mixedMoment B raw42749step0 raw42749step0Labels := by
      have ha : raw42749step0 = (fun i j => raw42749 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42749step0 raw42749; decide +kernel
      have hl : raw42749step0Labels = raw42749Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42749 raw42749Labels permutation166 permutation7
    mixedMoment B raw42749step0 raw42749step0Labels = mixedMoment B raw42749step1 raw42749step1Labels := by
      have ha : raw42749step1 = -raw42749step0 := by apply Matrix.ext; change ∀ i j, raw42749step1 i j = -(raw42749step0 i j); unfold raw42749step1 raw42749step0; decide +kernel
      have hl : raw42749step1Labels = raw42749step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42749step1 raw42749step1Labels = mixedMoment B raw42749step2 raw42749step2Labels := by
      have ha : raw42749step2 = raw42749step1 := by apply Matrix.ext; unfold raw42749step2 raw42749step1; decide +kernel
      have hl : raw42749step1Labels = labelEmbedding6 ∘ raw42749step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42749step1 raw42749step1Labels raw42749step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5042 node5042Labels := by rfl

def raw42750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42750Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw42750step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42750step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw42750step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42750 raw42750Labels = mixedMoment B node3480 node3480Labels := by
  calc
    mixedMoment B raw42750 raw42750Labels = mixedMoment B raw42750step0 raw42750step0Labels := by
      have hz : ∀ j, raw42750 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42750step0 = (fun i j => raw42750 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42750step0 raw42750; decide +kernel
      have hl : raw42750step0Labels = raw42750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42750 raw42750Labels permutation434 hz
    mixedMoment B raw42750step0 raw42750step0Labels = mixedMoment B raw42750step1 raw42750step1Labels := by
      have ha : raw42750step1 = raw42750step0 := by apply Matrix.ext; unfold raw42750step1 raw42750step0; decide +kernel
      have hl : raw42750step0Labels = labelEmbedding1 ∘ raw42750step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42750step0 raw42750step0Labels raw42750step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3480 node3480Labels := by rfl

def raw42751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42751Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw42751step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw42751step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw42751step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42751step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw42751step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42751 raw42751Labels = mixedMoment B node5090 node5090Labels := by
  calc
    mixedMoment B raw42751 raw42751Labels = mixedMoment B raw42751step0 raw42751step0Labels := by
      have hz : ∀ j, raw42751 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42751step0 = (fun i j => raw42751 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42751step0 raw42751; decide +kernel
      have hl : raw42751step0Labels = raw42751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42751 raw42751Labels permutation434 hz
    mixedMoment B raw42751step0 raw42751step0Labels = mixedMoment B raw42751step1 raw42751step1Labels := by
      have ha : raw42751step1 = (fun i j => raw42751step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42751step1 raw42751step0; decide +kernel
      have hl : raw42751step1Labels = raw42751step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42751step0 raw42751step0Labels permutation36 permutation7
    mixedMoment B raw42751step1 raw42751step1Labels = mixedMoment B raw42751step2 raw42751step2Labels := by
      have ha : raw42751step2 = -raw42751step1 := by apply Matrix.ext; change ∀ i j, raw42751step2 i j = -(raw42751step1 i j); unfold raw42751step2 raw42751step1; decide +kernel
      have hl : raw42751step2Labels = raw42751step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42751step2 raw42751step2Labels = mixedMoment B raw42751step3 raw42751step3Labels := by
      have ha : raw42751step3 = raw42751step2 := by apply Matrix.ext; unfold raw42751step3 raw42751step2; decide +kernel
      have hl : raw42751step2Labels = labelEmbedding6 ∘ raw42751step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42751step2 raw42751step2Labels raw42751step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5090 node5090Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
