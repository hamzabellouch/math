import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw25984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25984Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25984step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw25984step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25984step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw25984step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25984step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw25984step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25984 raw25984Labels = mixedMoment B node1700 node1700Labels := by
  calc
    mixedMoment B raw25984 raw25984Labels = mixedMoment B raw25984step0 raw25984step0Labels := by
      have hz : ∀ j, raw25984 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25984step0 = (fun i j => raw25984 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25984step0 raw25984; decide +kernel
      have hl : raw25984step0Labels = raw25984Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25984 raw25984Labels permutation265 hz
    mixedMoment B raw25984step0 raw25984step0Labels = mixedMoment B raw25984step1 raw25984step1Labels := by
      have ha : raw25984step1 = (fun i j => raw25984step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25984step1 raw25984step0; decide +kernel
      have hl : raw25984step1Labels = raw25984step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25984step0 raw25984step0Labels permutation32 permutation7
    mixedMoment B raw25984step1 raw25984step1Labels = mixedMoment B raw25984step2 raw25984step2Labels := by
      have ha : raw25984step2 = -raw25984step1 := by apply Matrix.ext; change ∀ i j, raw25984step2 i j = -(raw25984step1 i j); unfold raw25984step2 raw25984step1; decide +kernel
      have hl : raw25984step2Labels = raw25984step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25984step2 raw25984step2Labels = mixedMoment B raw25984step3 raw25984step3Labels := by
      have ha : raw25984step3 = raw25984step2 := by apply Matrix.ext; unfold raw25984step3 raw25984step2; decide +kernel
      have hl : raw25984step2Labels = labelEmbedding1 ∘ raw25984step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25984step2 raw25984step2Labels raw25984step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1700 node1700Labels := by rfl

def raw25985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25985Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25985step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25985step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25985step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25985step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw25985step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25985step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25985step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25985step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25985step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25985 raw25985Labels = mixedMoment B node1513 node1513Labels := by
  calc
    mixedMoment B raw25985 raw25985Labels = mixedMoment B raw25985step0 raw25985step0Labels := by
      have hz : ∀ j, raw25985 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25985step0 = (fun i j => raw25985 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25985step0 raw25985; decide +kernel
      have hl : raw25985step0Labels = raw25985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25985 raw25985Labels permutation346 hz
    mixedMoment B raw25985step0 raw25985step0Labels = mixedMoment B raw25985step1 raw25985step1Labels := by
      have hz : ∀ j, raw25985step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25985step1 = (fun i j => raw25985step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25985step1 raw25985step0; decide +kernel
      have hl : raw25985step1Labels = raw25985step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25985step0 raw25985step0Labels permutation56 hz
    mixedMoment B raw25985step1 raw25985step1Labels = mixedMoment B raw25985step2 raw25985step2Labels := by
      have ha : raw25985step2 = (fun i j => raw25985step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25985step2 raw25985step1; decide +kernel
      have hl : raw25985step2Labels = raw25985step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25985step1 raw25985step1Labels permutation10 permutation7
    mixedMoment B raw25985step2 raw25985step2Labels = mixedMoment B raw25985step3 raw25985step3Labels := by
      have ha : raw25985step3 = -raw25985step2 := by apply Matrix.ext; change ∀ i j, raw25985step3 i j = -(raw25985step2 i j); unfold raw25985step3 raw25985step2; decide +kernel
      have hl : raw25985step3Labels = raw25985step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25985step3 raw25985step3Labels = mixedMoment B raw25985step4 raw25985step4Labels := by
      have ha : raw25985step4 = raw25985step3 := by apply Matrix.ext; unfold raw25985step4 raw25985step3; decide +kernel
      have hl : raw25985step3Labels = labelEmbedding1 ∘ raw25985step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25985step3 raw25985step3Labels raw25985step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1513 node1513Labels := by rfl

def raw25986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25986Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25986step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25986step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw25986step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25986step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25986step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25986step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25986step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25986 raw25986Labels = mixedMoment B node1669 node1669Labels := by
  calc
    mixedMoment B raw25986 raw25986Labels = mixedMoment B raw25986step0 raw25986step0Labels := by
      have hz : ∀ j, raw25986 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25986step0 = (fun i j => raw25986 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25986step0 raw25986; decide +kernel
      have hl : raw25986step0Labels = raw25986Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25986 raw25986Labels permutation346 hz
    mixedMoment B raw25986step0 raw25986step0Labels = mixedMoment B raw25986step1 raw25986step1Labels := by
      have ha : raw25986step1 = (fun i j => raw25986step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25986step1 raw25986step0; decide +kernel
      have hl : raw25986step1Labels = raw25986step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25986step0 raw25986step0Labels permutation34 permutation7
    mixedMoment B raw25986step1 raw25986step1Labels = mixedMoment B raw25986step2 raw25986step2Labels := by
      have ha : raw25986step2 = -raw25986step1 := by apply Matrix.ext; change ∀ i j, raw25986step2 i j = -(raw25986step1 i j); unfold raw25986step2 raw25986step1; decide +kernel
      have hl : raw25986step2Labels = raw25986step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25986step2 raw25986step2Labels = mixedMoment B raw25986step3 raw25986step3Labels := by
      have ha : raw25986step3 = raw25986step2 := by apply Matrix.ext; unfold raw25986step3 raw25986step2; decide +kernel
      have hl : raw25986step2Labels = labelEmbedding1 ∘ raw25986step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25986step2 raw25986step2Labels raw25986step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1669 node1669Labels := by rfl

def raw25987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25987Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25987step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw25987step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25987step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25987step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25987step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25987step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25987 raw25987Labels = mixedMoment B node1669 node1669Labels := by
  calc
    mixedMoment B raw25987 raw25987Labels = mixedMoment B raw25987step0 raw25987step0Labels := by
      have hz : ∀ j, raw25987 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25987step0 = (fun i j => raw25987 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25987step0 raw25987; decide +kernel
      have hl : raw25987step0Labels = raw25987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25987 raw25987Labels permutation265 hz
    mixedMoment B raw25987step0 raw25987step0Labels = mixedMoment B raw25987step1 raw25987step1Labels := by
      have ha : raw25987step1 = (fun i j => raw25987step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25987step1 raw25987step0; decide +kernel
      have hl : raw25987step1Labels = raw25987step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25987step0 raw25987step0Labels permutation34 permutation7
    mixedMoment B raw25987step1 raw25987step1Labels = mixedMoment B raw25987step2 raw25987step2Labels := by
      have ha : raw25987step2 = -raw25987step1 := by apply Matrix.ext; change ∀ i j, raw25987step2 i j = -(raw25987step1 i j); unfold raw25987step2 raw25987step1; decide +kernel
      have hl : raw25987step2Labels = raw25987step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25987step2 raw25987step2Labels = mixedMoment B raw25987step3 raw25987step3Labels := by
      have ha : raw25987step3 = raw25987step2 := by apply Matrix.ext; unfold raw25987step3 raw25987step2; decide +kernel
      have hl : raw25987step2Labels = labelEmbedding1 ∘ raw25987step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25987step2 raw25987step2Labels raw25987step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1669 node1669Labels := by rfl

def raw25988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 1, -3]]
def raw25988Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25988step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25988step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25988step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25988step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw25988step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25988step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-3, 1, 2]]
def raw25988step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25988step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw25988step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25988step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw25988step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25988 raw25988Labels = mixedMoment B node1741 node1741Labels := by
  calc
    mixedMoment B raw25988 raw25988Labels = mixedMoment B raw25988step0 raw25988step0Labels := by
      have hz : ∀ j, raw25988 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25988step0 = (fun i j => raw25988 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25988step0 raw25988; decide +kernel
      have hl : raw25988step0Labels = raw25988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25988 raw25988Labels permutation520 hz
    mixedMoment B raw25988step0 raw25988step0Labels = mixedMoment B raw25988step1 raw25988step1Labels := by
      have hz : ∀ j, raw25988step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25988step1 = (fun i j => raw25988step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25988step1 raw25988step0; decide +kernel
      have hl : raw25988step1Labels = raw25988step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25988step0 raw25988step0Labels permutation80 hz
    mixedMoment B raw25988step1 raw25988step1Labels = mixedMoment B raw25988step2 raw25988step2Labels := by
      have hz : ∀ j, raw25988step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw25988step2 = (fun i j => raw25988step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw25988step2 raw25988step1; decide +kernel
      have hl : raw25988step2Labels = raw25988step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25988step1 raw25988step1Labels permutation14 hz
    mixedMoment B raw25988step2 raw25988step2Labels = mixedMoment B raw25988step3 raw25988step3Labels := by
      have ha : raw25988step3 = (fun i j => raw25988step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25988step3 raw25988step2; decide +kernel
      have hl : raw25988step3Labels = raw25988step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25988step2 raw25988step2Labels permutation2 permutation7
    mixedMoment B raw25988step3 raw25988step3Labels = mixedMoment B raw25988step4 raw25988step4Labels := by
      have ha : raw25988step4 = -raw25988step3 := by apply Matrix.ext; change ∀ i j, raw25988step4 i j = -(raw25988step3 i j); unfold raw25988step4 raw25988step3; decide +kernel
      have hl : raw25988step4Labels = raw25988step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25988step4 raw25988step4Labels = mixedMoment B raw25988step5 raw25988step5Labels := by
      have ha : raw25988step5 = raw25988step4 := by apply Matrix.ext; unfold raw25988step5 raw25988step4; decide +kernel
      have hl : raw25988step4Labels = labelEmbedding1 ∘ raw25988step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25988step4 raw25988step4Labels raw25988step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1741 node1741Labels := by rfl

def raw25989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25989Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25989step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25989step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw25989step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25989step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw25989step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25989step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw25989step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25989step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw25989step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25989 raw25989Labels = mixedMoment B node1716 node1716Labels := by
  calc
    mixedMoment B raw25989 raw25989Labels = mixedMoment B raw25989step0 raw25989step0Labels := by
      have hz : ∀ j, raw25989 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25989step0 = (fun i j => raw25989 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25989step0 raw25989; decide +kernel
      have hl : raw25989step0Labels = raw25989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25989 raw25989Labels permutation346 hz
    mixedMoment B raw25989step0 raw25989step0Labels = mixedMoment B raw25989step1 raw25989step1Labels := by
      have hz : ∀ j, raw25989step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25989step1 = (fun i j => raw25989step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25989step1 raw25989step0; decide +kernel
      have hl : raw25989step1Labels = raw25989step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25989step0 raw25989step0Labels permutation56 hz
    mixedMoment B raw25989step1 raw25989step1Labels = mixedMoment B raw25989step2 raw25989step2Labels := by
      have ha : raw25989step2 = (fun i j => raw25989step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25989step2 raw25989step1; decide +kernel
      have hl : raw25989step2Labels = raw25989step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25989step1 raw25989step1Labels permutation10 permutation7
    mixedMoment B raw25989step2 raw25989step2Labels = mixedMoment B raw25989step3 raw25989step3Labels := by
      have ha : raw25989step3 = -raw25989step2 := by apply Matrix.ext; change ∀ i j, raw25989step3 i j = -(raw25989step2 i j); unfold raw25989step3 raw25989step2; decide +kernel
      have hl : raw25989step3Labels = raw25989step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25989step3 raw25989step3Labels = mixedMoment B raw25989step4 raw25989step4Labels := by
      have ha : raw25989step4 = raw25989step3 := by apply Matrix.ext; unfold raw25989step4 raw25989step3; decide +kernel
      have hl : raw25989step3Labels = labelEmbedding1 ∘ raw25989step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25989step3 raw25989step3Labels raw25989step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1716 node1716Labels := by rfl

def raw25990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25990Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25990step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25990step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25990step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25990step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw25990step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25990step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25990step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25990step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25990step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25990 raw25990Labels = mixedMoment B node1513 node1513Labels := by
  calc
    mixedMoment B raw25990 raw25990Labels = mixedMoment B raw25990step0 raw25990step0Labels := by
      have hz : ∀ j, raw25990 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25990step0 = (fun i j => raw25990 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25990step0 raw25990; decide +kernel
      have hl : raw25990step0Labels = raw25990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25990 raw25990Labels permutation346 hz
    mixedMoment B raw25990step0 raw25990step0Labels = mixedMoment B raw25990step1 raw25990step1Labels := by
      have hz : ∀ j, raw25990step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25990step1 = (fun i j => raw25990step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25990step1 raw25990step0; decide +kernel
      have hl : raw25990step1Labels = raw25990step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25990step0 raw25990step0Labels permutation56 hz
    mixedMoment B raw25990step1 raw25990step1Labels = mixedMoment B raw25990step2 raw25990step2Labels := by
      have ha : raw25990step2 = (fun i j => raw25990step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25990step2 raw25990step1; decide +kernel
      have hl : raw25990step2Labels = raw25990step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25990step1 raw25990step1Labels permutation8 permutation7
    mixedMoment B raw25990step2 raw25990step2Labels = mixedMoment B raw25990step3 raw25990step3Labels := by
      have ha : raw25990step3 = -raw25990step2 := by apply Matrix.ext; change ∀ i j, raw25990step3 i j = -(raw25990step2 i j); unfold raw25990step3 raw25990step2; decide +kernel
      have hl : raw25990step3Labels = raw25990step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25990step3 raw25990step3Labels = mixedMoment B raw25990step4 raw25990step4Labels := by
      have ha : raw25990step4 = raw25990step3 := by apply Matrix.ext; unfold raw25990step4 raw25990step3; decide +kernel
      have hl : raw25990step3Labels = labelEmbedding1 ∘ raw25990step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25990step3 raw25990step3Labels raw25990step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1513 node1513Labels := by rfl

def raw25991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25991Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25991step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw25991step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25991step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25991step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25991step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25991step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25991 raw25991Labels = mixedMoment B node1669 node1669Labels := by
  calc
    mixedMoment B raw25991 raw25991Labels = mixedMoment B raw25991step0 raw25991step0Labels := by
      have hz : ∀ j, raw25991 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25991step0 = (fun i j => raw25991 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25991step0 raw25991; decide +kernel
      have hl : raw25991step0Labels = raw25991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25991 raw25991Labels permutation346 hz
    mixedMoment B raw25991step0 raw25991step0Labels = mixedMoment B raw25991step1 raw25991step1Labels := by
      have ha : raw25991step1 = (fun i j => raw25991step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25991step1 raw25991step0; decide +kernel
      have hl : raw25991step1Labels = raw25991step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25991step0 raw25991step0Labels permutation32 permutation7
    mixedMoment B raw25991step1 raw25991step1Labels = mixedMoment B raw25991step2 raw25991step2Labels := by
      have ha : raw25991step2 = -raw25991step1 := by apply Matrix.ext; change ∀ i j, raw25991step2 i j = -(raw25991step1 i j); unfold raw25991step2 raw25991step1; decide +kernel
      have hl : raw25991step2Labels = raw25991step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25991step2 raw25991step2Labels = mixedMoment B raw25991step3 raw25991step3Labels := by
      have ha : raw25991step3 = raw25991step2 := by apply Matrix.ext; unfold raw25991step3 raw25991step2; decide +kernel
      have hl : raw25991step2Labels = labelEmbedding1 ∘ raw25991step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25991step2 raw25991step2Labels raw25991step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1669 node1669Labels := by rfl

def raw25992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25992Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25992step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw25992step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25992step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25992step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25992step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw25992step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25992 raw25992Labels = mixedMoment B node1669 node1669Labels := by
  calc
    mixedMoment B raw25992 raw25992Labels = mixedMoment B raw25992step0 raw25992step0Labels := by
      have hz : ∀ j, raw25992 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25992step0 = (fun i j => raw25992 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25992step0 raw25992; decide +kernel
      have hl : raw25992step0Labels = raw25992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25992 raw25992Labels permutation265 hz
    mixedMoment B raw25992step0 raw25992step0Labels = mixedMoment B raw25992step1 raw25992step1Labels := by
      have ha : raw25992step1 = (fun i j => raw25992step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25992step1 raw25992step0; decide +kernel
      have hl : raw25992step1Labels = raw25992step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25992step0 raw25992step0Labels permutation32 permutation7
    mixedMoment B raw25992step1 raw25992step1Labels = mixedMoment B raw25992step2 raw25992step2Labels := by
      have ha : raw25992step2 = -raw25992step1 := by apply Matrix.ext; change ∀ i j, raw25992step2 i j = -(raw25992step1 i j); unfold raw25992step2 raw25992step1; decide +kernel
      have hl : raw25992step2Labels = raw25992step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25992step2 raw25992step2Labels = mixedMoment B raw25992step3 raw25992step3Labels := by
      have ha : raw25992step3 = raw25992step2 := by apply Matrix.ext; unfold raw25992step3 raw25992step2; decide +kernel
      have hl : raw25992step2Labels = labelEmbedding1 ∘ raw25992step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25992step2 raw25992step2Labels raw25992step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1669 node1669Labels := by rfl

def raw25993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw25993Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw25993step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25993step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw25993step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25993step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw25993step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25993step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw25993step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25993step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw25993step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25993 raw25993Labels = mixedMoment B node1716 node1716Labels := by
  calc
    mixedMoment B raw25993 raw25993Labels = mixedMoment B raw25993step0 raw25993step0Labels := by
      have hz : ∀ j, raw25993 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25993step0 = (fun i j => raw25993 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25993step0 raw25993; decide +kernel
      have hl : raw25993step0Labels = raw25993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25993 raw25993Labels permutation346 hz
    mixedMoment B raw25993step0 raw25993step0Labels = mixedMoment B raw25993step1 raw25993step1Labels := by
      have hz : ∀ j, raw25993step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25993step1 = (fun i j => raw25993step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25993step1 raw25993step0; decide +kernel
      have hl : raw25993step1Labels = raw25993step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25993step0 raw25993step0Labels permutation56 hz
    mixedMoment B raw25993step1 raw25993step1Labels = mixedMoment B raw25993step2 raw25993step2Labels := by
      have ha : raw25993step2 = (fun i j => raw25993step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25993step2 raw25993step1; decide +kernel
      have hl : raw25993step2Labels = raw25993step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25993step1 raw25993step1Labels permutation8 permutation7
    mixedMoment B raw25993step2 raw25993step2Labels = mixedMoment B raw25993step3 raw25993step3Labels := by
      have ha : raw25993step3 = -raw25993step2 := by apply Matrix.ext; change ∀ i j, raw25993step3 i j = -(raw25993step2 i j); unfold raw25993step3 raw25993step2; decide +kernel
      have hl : raw25993step3Labels = raw25993step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25993step3 raw25993step3Labels = mixedMoment B raw25993step4 raw25993step4Labels := by
      have ha : raw25993step4 = raw25993step3 := by apply Matrix.ext; unfold raw25993step4 raw25993step3; decide +kernel
      have hl : raw25993step3Labels = labelEmbedding1 ∘ raw25993step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25993step3 raw25993step3Labels raw25993step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1716 node1716Labels := by rfl

def raw25994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25994Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25994step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25994step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25994step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25994 raw25994Labels = mixedMoment B node1080 node1080Labels := by
  calc
    mixedMoment B raw25994 raw25994Labels = mixedMoment B raw25994step0 raw25994step0Labels := by
      have hz : ∀ j, raw25994 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25994step0 = (fun i j => raw25994 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25994step0 raw25994; decide +kernel
      have hl : raw25994step0Labels = raw25994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25994 raw25994Labels permutation346 hz
    mixedMoment B raw25994step0 raw25994step0Labels = mixedMoment B raw25994step1 raw25994step1Labels := by
      have hz : ∀ j, raw25994step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25994step1 = (fun i j => raw25994step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25994step1 raw25994step0; decide +kernel
      have hl : raw25994step1Labels = raw25994step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25994step0 raw25994step0Labels permutation56 hz
    _ = mixedMoment B node1080 node1080Labels := by rfl

def raw25995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25995Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25995step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25995 raw25995Labels = mixedMoment B node598 node598Labels := by
  calc
    mixedMoment B raw25995 raw25995Labels = mixedMoment B raw25995step0 raw25995step0Labels := by
      have hz : ∀ j, raw25995 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25995step0 = (fun i j => raw25995 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25995step0 raw25995; decide +kernel
      have hl : raw25995step0Labels = raw25995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25995 raw25995Labels permutation346 hz
    _ = mixedMoment B node598 node598Labels := by rfl

def raw25996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25996Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25996step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25996 raw25996Labels = mixedMoment B node598 node598Labels := by
  calc
    mixedMoment B raw25996 raw25996Labels = mixedMoment B raw25996step0 raw25996step0Labels := by
      have hz : ∀ j, raw25996 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25996step0 = (fun i j => raw25996 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25996step0 raw25996; decide +kernel
      have hl : raw25996step0Labels = raw25996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25996 raw25996Labels permutation265 hz
    _ = mixedMoment B node598 node598Labels := by rfl

def raw25997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25997Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25997step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25997step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25997step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25997step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25997 raw25997Labels = mixedMoment B node607 node607Labels := by
  calc
    mixedMoment B raw25997 raw25997Labels = mixedMoment B raw25997step0 raw25997step0Labels := by
      have hz : ∀ j, raw25997 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25997step0 = (fun i j => raw25997 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25997step0 raw25997; decide +kernel
      have hl : raw25997step0Labels = raw25997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25997 raw25997Labels permutation346 hz
    mixedMoment B raw25997step0 raw25997step0Labels = mixedMoment B raw25997step1 raw25997step1Labels := by
      have hz : ∀ j, raw25997step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25997step1 = (fun i j => raw25997step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25997step1 raw25997step0; decide +kernel
      have hl : raw25997step1Labels = raw25997step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25997step0 raw25997step0Labels permutation56 hz
    mixedMoment B raw25997step1 raw25997step1Labels = mixedMoment B raw25997step2 raw25997step2Labels := by
      have ha : raw25997step2 = (fun i j => raw25997step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25997step2 raw25997step1; decide +kernel
      have hl : raw25997step2Labels = raw25997step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25997step1 raw25997step1Labels permutation10 permutation2
    _ = mixedMoment B node607 node607Labels := by rfl

def raw25998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25998Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25998step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw25998step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25998 raw25998Labels = mixedMoment B node607 node607Labels := by
  calc
    mixedMoment B raw25998 raw25998Labels = mixedMoment B raw25998step0 raw25998step0Labels := by
      have hz : ∀ j, raw25998 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25998step0 = (fun i j => raw25998 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25998step0 raw25998; decide +kernel
      have hl : raw25998step0Labels = raw25998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25998 raw25998Labels permutation346 hz
    mixedMoment B raw25998step0 raw25998step0Labels = mixedMoment B raw25998step1 raw25998step1Labels := by
      have hz : ∀ j, raw25998step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25998step1 = (fun i j => raw25998step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25998step1 raw25998step0; decide +kernel
      have hl : raw25998step1Labels = raw25998step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25998step0 raw25998step0Labels permutation56 hz
    _ = mixedMoment B node607 node607Labels := by rfl

def raw25999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25999Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25999step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25999step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25999 raw25999Labels = mixedMoment B node918 node918Labels := by
  calc
    mixedMoment B raw25999 raw25999Labels = mixedMoment B raw25999step0 raw25999step0Labels := by
      have ha : raw25999step0 = (fun i j => raw25999 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25999step0 raw25999; decide +kernel
      have hl : raw25999step0Labels = raw25999Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25999 raw25999Labels permutation176 permutation2
    _ = mixedMoment B node918 node918Labels := by rfl

def raw26000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw26000Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw26000step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26000step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw26000step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26000 raw26000Labels = mixedMoment B node1080 node1080Labels := by
  calc
    mixedMoment B raw26000 raw26000Labels = mixedMoment B raw26000step0 raw26000step0Labels := by
      have hz : ∀ j, raw26000 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26000step0 = (fun i j => raw26000 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26000step0 raw26000; decide +kernel
      have hl : raw26000step0Labels = raw26000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26000 raw26000Labels permutation520 hz
    mixedMoment B raw26000step0 raw26000step0Labels = mixedMoment B raw26000step1 raw26000step1Labels := by
      have hz : ∀ j, raw26000step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw26000step1 = (fun i j => raw26000step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw26000step1 raw26000step0; decide +kernel
      have hl : raw26000step1Labels = raw26000step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26000step0 raw26000step0Labels permutation80 hz
    _ = mixedMoment B node1080 node1080Labels := by rfl

def raw26001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw26001Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw26001step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26001 raw26001Labels = mixedMoment B node1078 node1078Labels := by
  calc
    mixedMoment B raw26001 raw26001Labels = mixedMoment B raw26001step0 raw26001step0Labels := by
      have hz : ∀ j, raw26001 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26001step0 = (fun i j => raw26001 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26001step0 raw26001; decide +kernel
      have hl : raw26001step0Labels = raw26001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26001 raw26001Labels permutation346 hz
    _ = mixedMoment B node1078 node1078Labels := by rfl

def raw26002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26002Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26002step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26002step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26002step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26002step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26002 raw26002Labels = mixedMoment B node4114 node4114Labels := by
  calc
    mixedMoment B raw26002 raw26002Labels = mixedMoment B raw26002step0 raw26002step0Labels := by
      have hz : ∀ j, raw26002 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26002step0 = (fun i j => raw26002 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26002step0 raw26002; decide +kernel
      have hl : raw26002step0Labels = raw26002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26002 raw26002Labels permutation346 hz
    mixedMoment B raw26002step0 raw26002step0Labels = mixedMoment B raw26002step1 raw26002step1Labels := by
      have ha : raw26002step1 = (fun i j => raw26002step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26002step1 raw26002step0; decide +kernel
      have hl : raw26002step1Labels = raw26002step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26002step0 raw26002step0Labels permutation40 permutation3
    mixedMoment B raw26002step1 raw26002step1Labels = mixedMoment B raw26002step2 raw26002step2Labels := by
      have ha : raw26002step2 = raw26002step1 := by apply Matrix.ext; unfold raw26002step2 raw26002step1; decide +kernel
      have hl : raw26002step1Labels = labelEmbedding6 ∘ raw26002step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26002step1 raw26002step1Labels raw26002step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4114 node4114Labels := by rfl

def raw26003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26003Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26003step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26003step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26003step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26003step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26003 raw26003Labels = mixedMoment B node4297 node4297Labels := by
  calc
    mixedMoment B raw26003 raw26003Labels = mixedMoment B raw26003step0 raw26003step0Labels := by
      have ha : raw26003step0 = (fun i j => raw26003 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26003step0 raw26003; decide +kernel
      have hl : raw26003step0Labels = raw26003Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26003 raw26003Labels permutation184 permutation3
    mixedMoment B raw26003step0 raw26003step0Labels = mixedMoment B raw26003step1 raw26003step1Labels := by
      have ha : raw26003step1 = raw26003step0 := by apply Matrix.ext; unfold raw26003step1 raw26003step0; decide +kernel
      have hl : raw26003step0Labels = labelEmbedding6 ∘ raw26003step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26003step0 raw26003step0Labels raw26003step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4297 node4297Labels := by rfl

def raw26004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw26004Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw26004step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26004step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26004step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26004step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26004 raw26004Labels = mixedMoment B node4418 node4418Labels := by
  calc
    mixedMoment B raw26004 raw26004Labels = mixedMoment B raw26004step0 raw26004step0Labels := by
      have hz : ∀ j, raw26004 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26004step0 = (fun i j => raw26004 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26004step0 raw26004; decide +kernel
      have hl : raw26004step0Labels = raw26004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26004 raw26004Labels permutation346 hz
    mixedMoment B raw26004step0 raw26004step0Labels = mixedMoment B raw26004step1 raw26004step1Labels := by
      have ha : raw26004step1 = (fun i j => raw26004step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26004step1 raw26004step0; decide +kernel
      have hl : raw26004step1Labels = raw26004step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26004step0 raw26004step0Labels permutation46 permutation3
    mixedMoment B raw26004step1 raw26004step1Labels = mixedMoment B raw26004step2 raw26004step2Labels := by
      have ha : raw26004step2 = raw26004step1 := by apply Matrix.ext; unfold raw26004step2 raw26004step1; decide +kernel
      have hl : raw26004step1Labels = labelEmbedding6 ∘ raw26004step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26004step1 raw26004step1Labels raw26004step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4418 node4418Labels := by rfl

def raw26005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26005Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26005step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26005step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26005step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26005step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26005step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26005 raw26005Labels = mixedMoment B node4114 node4114Labels := by
  calc
    mixedMoment B raw26005 raw26005Labels = mixedMoment B raw26005step0 raw26005step0Labels := by
      have hz : ∀ j, raw26005 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26005step0 = (fun i j => raw26005 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26005step0 raw26005; decide +kernel
      have hl : raw26005step0Labels = raw26005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26005 raw26005Labels permutation265 hz
    mixedMoment B raw26005step0 raw26005step0Labels = mixedMoment B raw26005step1 raw26005step1Labels := by
      have ha : raw26005step1 = (fun i j => raw26005step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26005step1 raw26005step0; decide +kernel
      have hl : raw26005step1Labels = raw26005step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26005step0 raw26005step0Labels permutation40 permutation3
    mixedMoment B raw26005step1 raw26005step1Labels = mixedMoment B raw26005step2 raw26005step2Labels := by
      have ha : raw26005step2 = raw26005step1 := by apply Matrix.ext; unfold raw26005step2 raw26005step1; decide +kernel
      have hl : raw26005step1Labels = labelEmbedding6 ∘ raw26005step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26005step1 raw26005step1Labels raw26005step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4114 node4114Labels := by rfl

def raw26006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26006Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26006step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26006step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26006step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26006step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26006 raw26006Labels = mixedMoment B node4297 node4297Labels := by
  calc
    mixedMoment B raw26006 raw26006Labels = mixedMoment B raw26006step0 raw26006step0Labels := by
      have ha : raw26006step0 = (fun i j => raw26006 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26006step0 raw26006; decide +kernel
      have hl : raw26006step0Labels = raw26006Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26006 raw26006Labels permutation160 permutation3
    mixedMoment B raw26006step0 raw26006step0Labels = mixedMoment B raw26006step1 raw26006step1Labels := by
      have ha : raw26006step1 = raw26006step0 := by apply Matrix.ext; unfold raw26006step1 raw26006step0; decide +kernel
      have hl : raw26006step0Labels = labelEmbedding6 ∘ raw26006step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26006step0 raw26006step0Labels raw26006step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4297 node4297Labels := by rfl

def raw26007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw26007Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw26007step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26007step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26007step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26007step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26007 raw26007Labels = mixedMoment B node4418 node4418Labels := by
  calc
    mixedMoment B raw26007 raw26007Labels = mixedMoment B raw26007step0 raw26007step0Labels := by
      have hz : ∀ j, raw26007 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26007step0 = (fun i j => raw26007 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26007step0 raw26007; decide +kernel
      have hl : raw26007step0Labels = raw26007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26007 raw26007Labels permutation265 hz
    mixedMoment B raw26007step0 raw26007step0Labels = mixedMoment B raw26007step1 raw26007step1Labels := by
      have ha : raw26007step1 = (fun i j => raw26007step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26007step1 raw26007step0; decide +kernel
      have hl : raw26007step1Labels = raw26007step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26007step0 raw26007step0Labels permutation46 permutation3
    mixedMoment B raw26007step1 raw26007step1Labels = mixedMoment B raw26007step2 raw26007step2Labels := by
      have ha : raw26007step2 = raw26007step1 := by apply Matrix.ext; unfold raw26007step2 raw26007step1; decide +kernel
      have hl : raw26007step1Labels = labelEmbedding6 ∘ raw26007step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26007step1 raw26007step1Labels raw26007step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4418 node4418Labels := by rfl

def raw26008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26008Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26008step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26008step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![2, -1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26008step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26008step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw26008step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26008step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw26008step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26008 raw26008Labels = mixedMoment B node4122 node4122Labels := by
  calc
    mixedMoment B raw26008 raw26008Labels = mixedMoment B raw26008step0 raw26008step0Labels := by
      have hz : ∀ j, raw26008 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26008step0 = (fun i j => raw26008 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26008step0 raw26008; decide +kernel
      have hl : raw26008step0Labels = raw26008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26008 raw26008Labels permutation346 hz
    mixedMoment B raw26008step0 raw26008step0Labels = mixedMoment B raw26008step1 raw26008step1Labels := by
      have hz : ∀ j, raw26008step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26008step1 = (fun i j => raw26008step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26008step1 raw26008step0; decide +kernel
      have hl : raw26008step1Labels = raw26008step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26008step0 raw26008step0Labels permutation56 hz
    mixedMoment B raw26008step1 raw26008step1Labels = mixedMoment B raw26008step2 raw26008step2Labels := by
      have ha : raw26008step2 = (fun i j => raw26008step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26008step2 raw26008step1; decide +kernel
      have hl : raw26008step2Labels = raw26008step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26008step1 raw26008step1Labels permutation10 permutation3
    mixedMoment B raw26008step2 raw26008step2Labels = mixedMoment B raw26008step3 raw26008step3Labels := by
      have ha : raw26008step3 = raw26008step2 := by apply Matrix.ext; unfold raw26008step3 raw26008step2; decide +kernel
      have hl : raw26008step2Labels = labelEmbedding6 ∘ raw26008step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26008step2 raw26008step2Labels raw26008step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4122 node4122Labels := by rfl

def raw26009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26009Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26009step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw26009step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26009step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw26009step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26009 raw26009Labels = mixedMoment B node4304 node4304Labels := by
  calc
    mixedMoment B raw26009 raw26009Labels = mixedMoment B raw26009step0 raw26009step0Labels := by
      have hz : ∀ j, raw26009 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26009step0 = (fun i j => raw26009 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26009step0 raw26009; decide +kernel
      have hl : raw26009step0Labels = raw26009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26009 raw26009Labels permutation346 hz
    mixedMoment B raw26009step0 raw26009step0Labels = mixedMoment B raw26009step1 raw26009step1Labels := by
      have ha : raw26009step1 = (fun i j => raw26009step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26009step1 raw26009step0; decide +kernel
      have hl : raw26009step1Labels = raw26009step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26009step0 raw26009step0Labels permutation34 permutation3
    mixedMoment B raw26009step1 raw26009step1Labels = mixedMoment B raw26009step2 raw26009step2Labels := by
      have ha : raw26009step2 = raw26009step1 := by apply Matrix.ext; unfold raw26009step2 raw26009step1; decide +kernel
      have hl : raw26009step1Labels = labelEmbedding6 ∘ raw26009step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26009step1 raw26009step1Labels raw26009step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4304 node4304Labels := by rfl

def raw26010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26010Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26010step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw26010step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26010step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw26010step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26010 raw26010Labels = mixedMoment B node4304 node4304Labels := by
  calc
    mixedMoment B raw26010 raw26010Labels = mixedMoment B raw26010step0 raw26010step0Labels := by
      have hz : ∀ j, raw26010 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26010step0 = (fun i j => raw26010 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26010step0 raw26010; decide +kernel
      have hl : raw26010step0Labels = raw26010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26010 raw26010Labels permutation265 hz
    mixedMoment B raw26010step0 raw26010step0Labels = mixedMoment B raw26010step1 raw26010step1Labels := by
      have ha : raw26010step1 = (fun i j => raw26010step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26010step1 raw26010step0; decide +kernel
      have hl : raw26010step1Labels = raw26010step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26010step0 raw26010step0Labels permutation34 permutation3
    mixedMoment B raw26010step1 raw26010step1Labels = mixedMoment B raw26010step2 raw26010step2Labels := by
      have ha : raw26010step2 = raw26010step1 := by apply Matrix.ext; unfold raw26010step2 raw26010step1; decide +kernel
      have hl : raw26010step1Labels = labelEmbedding6 ∘ raw26010step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26010step1 raw26010step1Labels raw26010step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4304 node4304Labels := by rfl

def raw26011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw26011Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw26011step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26011step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw26011step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26011step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw26011step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26011step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw26011step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26011 raw26011Labels = mixedMoment B node4431 node4431Labels := by
  calc
    mixedMoment B raw26011 raw26011Labels = mixedMoment B raw26011step0 raw26011step0Labels := by
      have hz : ∀ j, raw26011 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26011step0 = (fun i j => raw26011 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26011step0 raw26011; decide +kernel
      have hl : raw26011step0Labels = raw26011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26011 raw26011Labels permutation346 hz
    mixedMoment B raw26011step0 raw26011step0Labels = mixedMoment B raw26011step1 raw26011step1Labels := by
      have hz : ∀ j, raw26011step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26011step1 = (fun i j => raw26011step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26011step1 raw26011step0; decide +kernel
      have hl : raw26011step1Labels = raw26011step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26011step0 raw26011step0Labels permutation56 hz
    mixedMoment B raw26011step1 raw26011step1Labels = mixedMoment B raw26011step2 raw26011step2Labels := by
      have ha : raw26011step2 = (fun i j => raw26011step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26011step2 raw26011step1; decide +kernel
      have hl : raw26011step2Labels = raw26011step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26011step1 raw26011step1Labels permutation10 permutation3
    mixedMoment B raw26011step2 raw26011step2Labels = mixedMoment B raw26011step3 raw26011step3Labels := by
      have ha : raw26011step3 = raw26011step2 := by apply Matrix.ext; unfold raw26011step3 raw26011step2; decide +kernel
      have hl : raw26011step2Labels = labelEmbedding6 ∘ raw26011step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26011step2 raw26011step2Labels raw26011step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4431 node4431Labels := by rfl

def raw26012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -3, 1]]
def raw26012Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -3, 1]]
def raw26012step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26012step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, 0, -1], ![2, -1, -1], ![2, -3, 1]]
def raw26012step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26012step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw26012step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26012step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw26012step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26012 raw26012Labels = mixedMoment B node4122 node4122Labels := by
  calc
    mixedMoment B raw26012 raw26012Labels = mixedMoment B raw26012step0 raw26012step0Labels := by
      have hz : ∀ j, raw26012 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26012step0 = (fun i j => raw26012 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26012step0 raw26012; decide +kernel
      have hl : raw26012step0Labels = raw26012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26012 raw26012Labels permutation346 hz
    mixedMoment B raw26012step0 raw26012step0Labels = mixedMoment B raw26012step1 raw26012step1Labels := by
      have hz : ∀ j, raw26012step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26012step1 = (fun i j => raw26012step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26012step1 raw26012step0; decide +kernel
      have hl : raw26012step1Labels = raw26012step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26012step0 raw26012step0Labels permutation56 hz
    mixedMoment B raw26012step1 raw26012step1Labels = mixedMoment B raw26012step2 raw26012step2Labels := by
      have ha : raw26012step2 = (fun i j => raw26012step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26012step2 raw26012step1; decide +kernel
      have hl : raw26012step2Labels = raw26012step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26012step1 raw26012step1Labels permutation8 permutation3
    mixedMoment B raw26012step2 raw26012step2Labels = mixedMoment B raw26012step3 raw26012step3Labels := by
      have ha : raw26012step3 = raw26012step2 := by apply Matrix.ext; unfold raw26012step3 raw26012step2; decide +kernel
      have hl : raw26012step2Labels = labelEmbedding6 ∘ raw26012step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26012step2 raw26012step2Labels raw26012step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4122 node4122Labels := by rfl

def raw26013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -3, 1]]
def raw26013Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -3, 1]]
def raw26013step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw26013step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26013step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw26013step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26013 raw26013Labels = mixedMoment B node4304 node4304Labels := by
  calc
    mixedMoment B raw26013 raw26013Labels = mixedMoment B raw26013step0 raw26013step0Labels := by
      have hz : ∀ j, raw26013 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26013step0 = (fun i j => raw26013 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26013step0 raw26013; decide +kernel
      have hl : raw26013step0Labels = raw26013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26013 raw26013Labels permutation346 hz
    mixedMoment B raw26013step0 raw26013step0Labels = mixedMoment B raw26013step1 raw26013step1Labels := by
      have ha : raw26013step1 = (fun i j => raw26013step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26013step1 raw26013step0; decide +kernel
      have hl : raw26013step1Labels = raw26013step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26013step0 raw26013step0Labels permutation32 permutation3
    mixedMoment B raw26013step1 raw26013step1Labels = mixedMoment B raw26013step2 raw26013step2Labels := by
      have ha : raw26013step2 = raw26013step1 := by apply Matrix.ext; unfold raw26013step2 raw26013step1; decide +kernel
      have hl : raw26013step1Labels = labelEmbedding6 ∘ raw26013step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26013step1 raw26013step1Labels raw26013step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4304 node4304Labels := by rfl

def raw26014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -3, 1]]
def raw26014Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -3, 1]]
def raw26014step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw26014step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26014step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw26014step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26014 raw26014Labels = mixedMoment B node4304 node4304Labels := by
  calc
    mixedMoment B raw26014 raw26014Labels = mixedMoment B raw26014step0 raw26014step0Labels := by
      have hz : ∀ j, raw26014 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26014step0 = (fun i j => raw26014 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26014step0 raw26014; decide +kernel
      have hl : raw26014step0Labels = raw26014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26014 raw26014Labels permutation265 hz
    mixedMoment B raw26014step0 raw26014step0Labels = mixedMoment B raw26014step1 raw26014step1Labels := by
      have ha : raw26014step1 = (fun i j => raw26014step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26014step1 raw26014step0; decide +kernel
      have hl : raw26014step1Labels = raw26014step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26014step0 raw26014step0Labels permutation32 permutation3
    mixedMoment B raw26014step1 raw26014step1Labels = mixedMoment B raw26014step2 raw26014step2Labels := by
      have ha : raw26014step2 = raw26014step1 := by apply Matrix.ext; unfold raw26014step2 raw26014step1; decide +kernel
      have hl : raw26014step1Labels = labelEmbedding6 ∘ raw26014step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26014step1 raw26014step1Labels raw26014step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4304 node4304Labels := by rfl

def raw26015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -4, 1]]
def raw26015Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -4, 1]]
def raw26015step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26015step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, 0, -1], ![1, 0, -1], ![3, -4, 1]]
def raw26015step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26015step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw26015step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26015step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw26015step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26015 raw26015Labels = mixedMoment B node4116 node4116Labels := by
  calc
    mixedMoment B raw26015 raw26015Labels = mixedMoment B raw26015step0 raw26015step0Labels := by
      have hz : ∀ j, raw26015 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26015step0 = (fun i j => raw26015 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26015step0 raw26015; decide +kernel
      have hl : raw26015step0Labels = raw26015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26015 raw26015Labels permutation346 hz
    mixedMoment B raw26015step0 raw26015step0Labels = mixedMoment B raw26015step1 raw26015step1Labels := by
      have hz : ∀ j, raw26015step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26015step1 = (fun i j => raw26015step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26015step1 raw26015step0; decide +kernel
      have hl : raw26015step1Labels = raw26015step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26015step0 raw26015step0Labels permutation56 hz
    mixedMoment B raw26015step1 raw26015step1Labels = mixedMoment B raw26015step2 raw26015step2Labels := by
      have ha : raw26015step2 = (fun i j => raw26015step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26015step2 raw26015step1; decide +kernel
      have hl : raw26015step2Labels = raw26015step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26015step1 raw26015step1Labels permutation8 permutation3
    mixedMoment B raw26015step2 raw26015step2Labels = mixedMoment B raw26015step3 raw26015step3Labels := by
      have ha : raw26015step3 = raw26015step2 := by apply Matrix.ext; unfold raw26015step3 raw26015step2; decide +kernel
      have hl : raw26015step2Labels = labelEmbedding6 ∘ raw26015step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26015step2 raw26015step2Labels raw26015step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4116 node4116Labels := by rfl

def raw26016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -4, 1]]
def raw26016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -4, 1]]
def raw26016step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw26016step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26016step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw26016step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26016 raw26016Labels = mixedMoment B node4299 node4299Labels := by
  calc
    mixedMoment B raw26016 raw26016Labels = mixedMoment B raw26016step0 raw26016step0Labels := by
      have hz : ∀ j, raw26016 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26016step0 = (fun i j => raw26016 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26016step0 raw26016; decide +kernel
      have hl : raw26016step0Labels = raw26016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26016 raw26016Labels permutation346 hz
    mixedMoment B raw26016step0 raw26016step0Labels = mixedMoment B raw26016step1 raw26016step1Labels := by
      have ha : raw26016step1 = (fun i j => raw26016step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26016step1 raw26016step0; decide +kernel
      have hl : raw26016step1Labels = raw26016step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26016step0 raw26016step0Labels permutation32 permutation3
    mixedMoment B raw26016step1 raw26016step1Labels = mixedMoment B raw26016step2 raw26016step2Labels := by
      have ha : raw26016step2 = raw26016step1 := by apply Matrix.ext; unfold raw26016step2 raw26016step1; decide +kernel
      have hl : raw26016step1Labels = labelEmbedding6 ∘ raw26016step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26016step1 raw26016step1Labels raw26016step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4299 node4299Labels := by rfl

def raw26017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -4, 1]]
def raw26017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -4, 1]]
def raw26017step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw26017step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26017step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw26017step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26017 raw26017Labels = mixedMoment B node4299 node4299Labels := by
  calc
    mixedMoment B raw26017 raw26017Labels = mixedMoment B raw26017step0 raw26017step0Labels := by
      have hz : ∀ j, raw26017 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26017step0 = (fun i j => raw26017 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26017step0 raw26017; decide +kernel
      have hl : raw26017step0Labels = raw26017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26017 raw26017Labels permutation265 hz
    mixedMoment B raw26017step0 raw26017step0Labels = mixedMoment B raw26017step1 raw26017step1Labels := by
      have ha : raw26017step1 = (fun i j => raw26017step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26017step1 raw26017step0; decide +kernel
      have hl : raw26017step1Labels = raw26017step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26017step0 raw26017step0Labels permutation32 permutation3
    mixedMoment B raw26017step1 raw26017step1Labels = mixedMoment B raw26017step2 raw26017step2Labels := by
      have ha : raw26017step2 = raw26017step1 := by apply Matrix.ext; unfold raw26017step2 raw26017step1; decide +kernel
      have hl : raw26017step1Labels = labelEmbedding6 ∘ raw26017step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26017step1 raw26017step1Labels raw26017step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4299 node4299Labels := by rfl

def raw26018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -4, 1]]
def raw26018Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -4, 1]]
def raw26018step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26018step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 1, -1], ![3, -4, 1]]
def raw26018step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26018step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw26018step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw26018step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw26018step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26018 raw26018Labels = mixedMoment B node4421 node4421Labels := by
  calc
    mixedMoment B raw26018 raw26018Labels = mixedMoment B raw26018step0 raw26018step0Labels := by
      have hz : ∀ j, raw26018 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26018step0 = (fun i j => raw26018 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26018step0 raw26018; decide +kernel
      have hl : raw26018step0Labels = raw26018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26018 raw26018Labels permutation346 hz
    mixedMoment B raw26018step0 raw26018step0Labels = mixedMoment B raw26018step1 raw26018step1Labels := by
      have hz : ∀ j, raw26018step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26018step1 = (fun i j => raw26018step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26018step1 raw26018step0; decide +kernel
      have hl : raw26018step1Labels = raw26018step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26018step0 raw26018step0Labels permutation56 hz
    mixedMoment B raw26018step1 raw26018step1Labels = mixedMoment B raw26018step2 raw26018step2Labels := by
      have ha : raw26018step2 = (fun i j => raw26018step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26018step2 raw26018step1; decide +kernel
      have hl : raw26018step2Labels = raw26018step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26018step1 raw26018step1Labels permutation10 permutation3
    mixedMoment B raw26018step2 raw26018step2Labels = mixedMoment B raw26018step3 raw26018step3Labels := by
      have ha : raw26018step3 = raw26018step2 := by apply Matrix.ext; unfold raw26018step3 raw26018step2; decide +kernel
      have hl : raw26018step2Labels = labelEmbedding6 ∘ raw26018step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26018step2 raw26018step2Labels raw26018step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4421 node4421Labels := by rfl

def raw26019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26019Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26019step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26019step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw26019step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26019step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw26019step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26019 raw26019Labels = mixedMoment B node2784 node2784Labels := by
  calc
    mixedMoment B raw26019 raw26019Labels = mixedMoment B raw26019step0 raw26019step0Labels := by
      have hz : ∀ j, raw26019 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26019step0 = (fun i j => raw26019 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26019step0 raw26019; decide +kernel
      have hl : raw26019step0Labels = raw26019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26019 raw26019Labels permutation346 hz
    mixedMoment B raw26019step0 raw26019step0Labels = mixedMoment B raw26019step1 raw26019step1Labels := by
      have hz : ∀ j, raw26019step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26019step1 = (fun i j => raw26019step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26019step1 raw26019step0; decide +kernel
      have hl : raw26019step1Labels = raw26019step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26019step0 raw26019step0Labels permutation56 hz
    mixedMoment B raw26019step1 raw26019step1Labels = mixedMoment B raw26019step2 raw26019step2Labels := by
      have ha : raw26019step2 = (fun i j => raw26019step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26019step2 raw26019step1; decide +kernel
      have hl : raw26019step2Labels = raw26019step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26019step1 raw26019step1Labels permutation8 permutation3
    _ = mixedMoment B node2784 node2784Labels := by rfl

def raw26020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26020Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26020step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26020step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26020step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26020 raw26020Labels = mixedMoment B node551 node551Labels := by
  calc
    mixedMoment B raw26020 raw26020Labels = mixedMoment B raw26020step0 raw26020step0Labels := by
      have hz : ∀ j, raw26020 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26020step0 = (fun i j => raw26020 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26020step0 raw26020; decide +kernel
      have hl : raw26020step0Labels = raw26020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26020 raw26020Labels permutation346 hz
    mixedMoment B raw26020step0 raw26020step0Labels = mixedMoment B raw26020step1 raw26020step1Labels := by
      have ha : raw26020step1 = (fun i j => raw26020step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26020step1 raw26020step0; decide +kernel
      have hl : raw26020step1Labels = raw26020step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26020step0 raw26020step0Labels permutation40 permutation3
    _ = mixedMoment B node551 node551Labels := by rfl

def raw26021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26021Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26021step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26021 raw26021Labels = mixedMoment B node875 node875Labels := by
  calc
    mixedMoment B raw26021 raw26021Labels = mixedMoment B raw26021step0 raw26021step0Labels := by
      have ha : raw26021step0 = (fun i j => raw26021 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26021step0 raw26021; decide +kernel
      have hl : raw26021step0Labels = raw26021Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26021 raw26021Labels permutation184 permutation3
    _ = mixedMoment B node875 node875Labels := by rfl

def raw26022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26022Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26022step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26022step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26022 raw26022Labels = mixedMoment B node999 node999Labels := by
  calc
    mixedMoment B raw26022 raw26022Labels = mixedMoment B raw26022step0 raw26022step0Labels := by
      have hz : ∀ j, raw26022 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26022step0 = (fun i j => raw26022 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26022step0 raw26022; decide +kernel
      have hl : raw26022step0Labels = raw26022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26022 raw26022Labels permutation346 hz
    mixedMoment B raw26022step0 raw26022step0Labels = mixedMoment B raw26022step1 raw26022step1Labels := by
      have ha : raw26022step1 = (fun i j => raw26022step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26022step1 raw26022step0; decide +kernel
      have hl : raw26022step1Labels = raw26022step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26022step0 raw26022step0Labels permutation40 permutation3
    _ = mixedMoment B node999 node999Labels := by rfl

def raw26023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw26023Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw26023step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26023step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26023step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26023 raw26023Labels = mixedMoment B node999 node999Labels := by
  calc
    mixedMoment B raw26023 raw26023Labels = mixedMoment B raw26023step0 raw26023step0Labels := by
      have hz : ∀ j, raw26023 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26023step0 = (fun i j => raw26023 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26023step0 raw26023; decide +kernel
      have hl : raw26023step0Labels = raw26023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26023 raw26023Labels permutation346 hz
    mixedMoment B raw26023step0 raw26023step0Labels = mixedMoment B raw26023step1 raw26023step1Labels := by
      have ha : raw26023step1 = (fun i j => raw26023step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26023step1 raw26023step0; decide +kernel
      have hl : raw26023step1Labels = raw26023step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26023step0 raw26023step0Labels permutation46 permutation3
    _ = mixedMoment B node999 node999Labels := by rfl

def raw26024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26024Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26024step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26024 raw26024Labels = mixedMoment B node551 node551Labels := by
  calc
    mixedMoment B raw26024 raw26024Labels = mixedMoment B raw26024step0 raw26024step0Labels := by
      have hz : ∀ j, raw26024 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26024step0 = (fun i j => raw26024 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26024step0 raw26024; decide +kernel
      have hl : raw26024step0Labels = raw26024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26024 raw26024Labels permutation265 hz
    mixedMoment B raw26024step0 raw26024step0Labels = mixedMoment B raw26024step1 raw26024step1Labels := by
      have ha : raw26024step1 = (fun i j => raw26024step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26024step1 raw26024step0; decide +kernel
      have hl : raw26024step1Labels = raw26024step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26024step0 raw26024step0Labels permutation40 permutation3
    _ = mixedMoment B node551 node551Labels := by rfl

def raw26025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26025Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26025step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26025step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26025 raw26025Labels = mixedMoment B node875 node875Labels := by
  calc
    mixedMoment B raw26025 raw26025Labels = mixedMoment B raw26025step0 raw26025step0Labels := by
      have ha : raw26025step0 = (fun i j => raw26025 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26025step0 raw26025; decide +kernel
      have hl : raw26025step0Labels = raw26025Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26025 raw26025Labels permutation160 permutation3
    _ = mixedMoment B node875 node875Labels := by rfl

def raw26026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26026Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26026step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26026step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26026step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26026 raw26026Labels = mixedMoment B node999 node999Labels := by
  calc
    mixedMoment B raw26026 raw26026Labels = mixedMoment B raw26026step0 raw26026step0Labels := by
      have hz : ∀ j, raw26026 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26026step0 = (fun i j => raw26026 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26026step0 raw26026; decide +kernel
      have hl : raw26026step0Labels = raw26026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26026 raw26026Labels permutation265 hz
    mixedMoment B raw26026step0 raw26026step0Labels = mixedMoment B raw26026step1 raw26026step1Labels := by
      have ha : raw26026step1 = (fun i j => raw26026step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26026step1 raw26026step0; decide +kernel
      have hl : raw26026step1Labels = raw26026step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26026step0 raw26026step0Labels permutation40 permutation3
    _ = mixedMoment B node999 node999Labels := by rfl

def raw26027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw26027Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw26027step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26027step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26027 raw26027Labels = mixedMoment B node999 node999Labels := by
  calc
    mixedMoment B raw26027 raw26027Labels = mixedMoment B raw26027step0 raw26027step0Labels := by
      have hz : ∀ j, raw26027 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26027step0 = (fun i j => raw26027 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26027step0 raw26027; decide +kernel
      have hl : raw26027step0Labels = raw26027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26027 raw26027Labels permutation265 hz
    mixedMoment B raw26027step0 raw26027step0Labels = mixedMoment B raw26027step1 raw26027step1Labels := by
      have ha : raw26027step1 = (fun i j => raw26027step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26027step1 raw26027step0; decide +kernel
      have hl : raw26027step1Labels = raw26027step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26027step0 raw26027step0Labels permutation46 permutation3
    _ = mixedMoment B node999 node999Labels := by rfl

def raw26028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26028Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26028step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26028step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![2, -1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26028step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26028step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw26028step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26028 raw26028Labels = mixedMoment B node556 node556Labels := by
  calc
    mixedMoment B raw26028 raw26028Labels = mixedMoment B raw26028step0 raw26028step0Labels := by
      have hz : ∀ j, raw26028 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26028step0 = (fun i j => raw26028 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26028step0 raw26028; decide +kernel
      have hl : raw26028step0Labels = raw26028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26028 raw26028Labels permutation346 hz
    mixedMoment B raw26028step0 raw26028step0Labels = mixedMoment B raw26028step1 raw26028step1Labels := by
      have hz : ∀ j, raw26028step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26028step1 = (fun i j => raw26028step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26028step1 raw26028step0; decide +kernel
      have hl : raw26028step1Labels = raw26028step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26028step0 raw26028step0Labels permutation56 hz
    mixedMoment B raw26028step1 raw26028step1Labels = mixedMoment B raw26028step2 raw26028step2Labels := by
      have ha : raw26028step2 = (fun i j => raw26028step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26028step2 raw26028step1; decide +kernel
      have hl : raw26028step2Labels = raw26028step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26028step1 raw26028step1Labels permutation10 permutation3
    _ = mixedMoment B node556 node556Labels := by rfl

def raw26029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26029Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26029step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw26029step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26029 raw26029Labels = mixedMoment B node882 node882Labels := by
  calc
    mixedMoment B raw26029 raw26029Labels = mixedMoment B raw26029step0 raw26029step0Labels := by
      have hz : ∀ j, raw26029 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26029step0 = (fun i j => raw26029 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26029step0 raw26029; decide +kernel
      have hl : raw26029step0Labels = raw26029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26029 raw26029Labels permutation346 hz
    mixedMoment B raw26029step0 raw26029step0Labels = mixedMoment B raw26029step1 raw26029step1Labels := by
      have ha : raw26029step1 = (fun i j => raw26029step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26029step1 raw26029step0; decide +kernel
      have hl : raw26029step1Labels = raw26029step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26029step0 raw26029step0Labels permutation34 permutation3
    _ = mixedMoment B node882 node882Labels := by rfl

def raw26030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26030Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26030step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26030step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw26030step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26030 raw26030Labels = mixedMoment B node882 node882Labels := by
  calc
    mixedMoment B raw26030 raw26030Labels = mixedMoment B raw26030step0 raw26030step0Labels := by
      have hz : ∀ j, raw26030 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26030step0 = (fun i j => raw26030 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26030step0 raw26030; decide +kernel
      have hl : raw26030step0Labels = raw26030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26030 raw26030Labels permutation265 hz
    mixedMoment B raw26030step0 raw26030step0Labels = mixedMoment B raw26030step1 raw26030step1Labels := by
      have ha : raw26030step1 = (fun i j => raw26030step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26030step1 raw26030step0; decide +kernel
      have hl : raw26030step1Labels = raw26030step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26030step0 raw26030step0Labels permutation34 permutation3
    _ = mixedMoment B node882 node882Labels := by rfl

def raw26031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw26031Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw26031step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26031step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw26031step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26031step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw26031step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26031 raw26031Labels = mixedMoment B node1012 node1012Labels := by
  calc
    mixedMoment B raw26031 raw26031Labels = mixedMoment B raw26031step0 raw26031step0Labels := by
      have hz : ∀ j, raw26031 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26031step0 = (fun i j => raw26031 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26031step0 raw26031; decide +kernel
      have hl : raw26031step0Labels = raw26031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26031 raw26031Labels permutation346 hz
    mixedMoment B raw26031step0 raw26031step0Labels = mixedMoment B raw26031step1 raw26031step1Labels := by
      have hz : ∀ j, raw26031step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26031step1 = (fun i j => raw26031step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26031step1 raw26031step0; decide +kernel
      have hl : raw26031step1Labels = raw26031step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26031step0 raw26031step0Labels permutation56 hz
    mixedMoment B raw26031step1 raw26031step1Labels = mixedMoment B raw26031step2 raw26031step2Labels := by
      have ha : raw26031step2 = (fun i j => raw26031step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26031step2 raw26031step1; decide +kernel
      have hl : raw26031step2Labels = raw26031step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26031step1 raw26031step1Labels permutation10 permutation3
    _ = mixedMoment B node1012 node1012Labels := by rfl

def raw26032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -3, 1]]
def raw26032Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -3, 1]]
def raw26032step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26032step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, 0, -1], ![2, -1, -1], ![2, -3, 1]]
def raw26032step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26032step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw26032step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26032 raw26032Labels = mixedMoment B node556 node556Labels := by
  calc
    mixedMoment B raw26032 raw26032Labels = mixedMoment B raw26032step0 raw26032step0Labels := by
      have hz : ∀ j, raw26032 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26032step0 = (fun i j => raw26032 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26032step0 raw26032; decide +kernel
      have hl : raw26032step0Labels = raw26032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26032 raw26032Labels permutation346 hz
    mixedMoment B raw26032step0 raw26032step0Labels = mixedMoment B raw26032step1 raw26032step1Labels := by
      have hz : ∀ j, raw26032step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26032step1 = (fun i j => raw26032step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26032step1 raw26032step0; decide +kernel
      have hl : raw26032step1Labels = raw26032step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26032step0 raw26032step0Labels permutation56 hz
    mixedMoment B raw26032step1 raw26032step1Labels = mixedMoment B raw26032step2 raw26032step2Labels := by
      have ha : raw26032step2 = (fun i j => raw26032step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26032step2 raw26032step1; decide +kernel
      have hl : raw26032step2Labels = raw26032step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26032step1 raw26032step1Labels permutation8 permutation3
    _ = mixedMoment B node556 node556Labels := by rfl

def raw26033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -3, 1]]
def raw26033Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -3, 1]]
def raw26033step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26033step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw26033step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26033 raw26033Labels = mixedMoment B node882 node882Labels := by
  calc
    mixedMoment B raw26033 raw26033Labels = mixedMoment B raw26033step0 raw26033step0Labels := by
      have hz : ∀ j, raw26033 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26033step0 = (fun i j => raw26033 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26033step0 raw26033; decide +kernel
      have hl : raw26033step0Labels = raw26033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26033 raw26033Labels permutation346 hz
    mixedMoment B raw26033step0 raw26033step0Labels = mixedMoment B raw26033step1 raw26033step1Labels := by
      have ha : raw26033step1 = (fun i j => raw26033step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26033step1 raw26033step0; decide +kernel
      have hl : raw26033step1Labels = raw26033step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26033step0 raw26033step0Labels permutation32 permutation3
    _ = mixedMoment B node882 node882Labels := by rfl

def raw26034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -3, 1]]
def raw26034Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -3, 1]]
def raw26034step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26034step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw26034step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26034 raw26034Labels = mixedMoment B node882 node882Labels := by
  calc
    mixedMoment B raw26034 raw26034Labels = mixedMoment B raw26034step0 raw26034step0Labels := by
      have hz : ∀ j, raw26034 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26034step0 = (fun i j => raw26034 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26034step0 raw26034; decide +kernel
      have hl : raw26034step0Labels = raw26034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26034 raw26034Labels permutation265 hz
    mixedMoment B raw26034step0 raw26034step0Labels = mixedMoment B raw26034step1 raw26034step1Labels := by
      have ha : raw26034step1 = (fun i j => raw26034step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26034step1 raw26034step0; decide +kernel
      have hl : raw26034step1Labels = raw26034step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26034step0 raw26034step0Labels permutation32 permutation3
    _ = mixedMoment B node882 node882Labels := by rfl

def raw26035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw26035Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw26035step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26035step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw26035step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26035step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw26035step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26035 raw26035Labels = mixedMoment B node1012 node1012Labels := by
  calc
    mixedMoment B raw26035 raw26035Labels = mixedMoment B raw26035step0 raw26035step0Labels := by
      have hz : ∀ j, raw26035 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26035step0 = (fun i j => raw26035 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26035step0 raw26035; decide +kernel
      have hl : raw26035step0Labels = raw26035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26035 raw26035Labels permutation346 hz
    mixedMoment B raw26035step0 raw26035step0Labels = mixedMoment B raw26035step1 raw26035step1Labels := by
      have hz : ∀ j, raw26035step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26035step1 = (fun i j => raw26035step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26035step1 raw26035step0; decide +kernel
      have hl : raw26035step1Labels = raw26035step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26035step0 raw26035step0Labels permutation56 hz
    mixedMoment B raw26035step1 raw26035step1Labels = mixedMoment B raw26035step2 raw26035step2Labels := by
      have ha : raw26035step2 = (fun i j => raw26035step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26035step2 raw26035step1; decide +kernel
      have hl : raw26035step2Labels = raw26035step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26035step1 raw26035step1Labels permutation8 permutation3
    _ = mixedMoment B node1012 node1012Labels := by rfl

def raw26036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -4, 1]]
def raw26036Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -4, 1]]
def raw26036step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26036step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, 0, -1], ![1, 0, -1], ![3, -4, 1]]
def raw26036step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26036step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw26036step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26036 raw26036Labels = mixedMoment B node553 node553Labels := by
  calc
    mixedMoment B raw26036 raw26036Labels = mixedMoment B raw26036step0 raw26036step0Labels := by
      have hz : ∀ j, raw26036 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26036step0 = (fun i j => raw26036 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26036step0 raw26036; decide +kernel
      have hl : raw26036step0Labels = raw26036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26036 raw26036Labels permutation346 hz
    mixedMoment B raw26036step0 raw26036step0Labels = mixedMoment B raw26036step1 raw26036step1Labels := by
      have hz : ∀ j, raw26036step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26036step1 = (fun i j => raw26036step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26036step1 raw26036step0; decide +kernel
      have hl : raw26036step1Labels = raw26036step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26036step0 raw26036step0Labels permutation56 hz
    mixedMoment B raw26036step1 raw26036step1Labels = mixedMoment B raw26036step2 raw26036step2Labels := by
      have ha : raw26036step2 = (fun i j => raw26036step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26036step2 raw26036step1; decide +kernel
      have hl : raw26036step2Labels = raw26036step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26036step1 raw26036step1Labels permutation8 permutation3
    _ = mixedMoment B node553 node553Labels := by rfl

def raw26037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -4, 1]]
def raw26037Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -4, 1]]
def raw26037step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26037step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw26037step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26037 raw26037Labels = mixedMoment B node877 node877Labels := by
  calc
    mixedMoment B raw26037 raw26037Labels = mixedMoment B raw26037step0 raw26037step0Labels := by
      have hz : ∀ j, raw26037 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26037step0 = (fun i j => raw26037 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26037step0 raw26037; decide +kernel
      have hl : raw26037step0Labels = raw26037Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26037 raw26037Labels permutation346 hz
    mixedMoment B raw26037step0 raw26037step0Labels = mixedMoment B raw26037step1 raw26037step1Labels := by
      have ha : raw26037step1 = (fun i j => raw26037step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26037step1 raw26037step0; decide +kernel
      have hl : raw26037step1Labels = raw26037step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26037step0 raw26037step0Labels permutation32 permutation3
    _ = mixedMoment B node877 node877Labels := by rfl

def raw26038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -4, 1]]
def raw26038Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -4, 1]]
def raw26038step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26038step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw26038step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26038 raw26038Labels = mixedMoment B node877 node877Labels := by
  calc
    mixedMoment B raw26038 raw26038Labels = mixedMoment B raw26038step0 raw26038step0Labels := by
      have hz : ∀ j, raw26038 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26038step0 = (fun i j => raw26038 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26038step0 raw26038; decide +kernel
      have hl : raw26038step0Labels = raw26038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26038 raw26038Labels permutation265 hz
    mixedMoment B raw26038step0 raw26038step0Labels = mixedMoment B raw26038step1 raw26038step1Labels := by
      have ha : raw26038step1 = (fun i j => raw26038step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26038step1 raw26038step0; decide +kernel
      have hl : raw26038step1Labels = raw26038step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26038step0 raw26038step0Labels permutation32 permutation3
    _ = mixedMoment B node877 node877Labels := by rfl

def raw26039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw26039Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw26039step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26039step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw26039step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26039step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw26039step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26039 raw26039Labels = mixedMoment B node1002 node1002Labels := by
  calc
    mixedMoment B raw26039 raw26039Labels = mixedMoment B raw26039step0 raw26039step0Labels := by
      have hz : ∀ j, raw26039 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26039step0 = (fun i j => raw26039 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26039step0 raw26039; decide +kernel
      have hl : raw26039step0Labels = raw26039Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26039 raw26039Labels permutation346 hz
    mixedMoment B raw26039step0 raw26039step0Labels = mixedMoment B raw26039step1 raw26039step1Labels := by
      have hz : ∀ j, raw26039step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26039step1 = (fun i j => raw26039step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26039step1 raw26039step0; decide +kernel
      have hl : raw26039step1Labels = raw26039step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26039step0 raw26039step0Labels permutation56 hz
    mixedMoment B raw26039step1 raw26039step1Labels = mixedMoment B raw26039step2 raw26039step2Labels := by
      have ha : raw26039step2 = (fun i j => raw26039step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26039step2 raw26039step1; decide +kernel
      have hl : raw26039step2Labels = raw26039step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26039step1 raw26039step1Labels permutation8 permutation3
    _ = mixedMoment B node1002 node1002Labels := by rfl

def raw26040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -4, 1]]
def raw26040Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -4, 1]]
def raw26040step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26040step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 1, -1], ![3, -4, 1]]
def raw26040step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26040step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw26040step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26040 raw26040Labels = mixedMoment B node1002 node1002Labels := by
  calc
    mixedMoment B raw26040 raw26040Labels = mixedMoment B raw26040step0 raw26040step0Labels := by
      have hz : ∀ j, raw26040 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26040step0 = (fun i j => raw26040 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26040step0 raw26040; decide +kernel
      have hl : raw26040step0Labels = raw26040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26040 raw26040Labels permutation346 hz
    mixedMoment B raw26040step0 raw26040step0Labels = mixedMoment B raw26040step1 raw26040step1Labels := by
      have hz : ∀ j, raw26040step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26040step1 = (fun i j => raw26040step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26040step1 raw26040step0; decide +kernel
      have hl : raw26040step1Labels = raw26040step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26040step0 raw26040step0Labels permutation56 hz
    mixedMoment B raw26040step1 raw26040step1Labels = mixedMoment B raw26040step2 raw26040step2Labels := by
      have ha : raw26040step2 = (fun i j => raw26040step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw26040step2 raw26040step1; decide +kernel
      have hl : raw26040step2Labels = raw26040step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26040step1 raw26040step1Labels permutation10 permutation3
    _ = mixedMoment B node1002 node1002Labels := by rfl

def raw26041 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26041Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26041step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26041step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw26041step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26041step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw26041step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26041step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw26041step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26041 raw26041Labels = mixedMoment B node4251 node4251Labels := by
  calc
    mixedMoment B raw26041 raw26041Labels = mixedMoment B raw26041step0 raw26041step0Labels := by
      have hz : ∀ j, raw26041 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26041step0 = (fun i j => raw26041 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26041step0 raw26041; decide +kernel
      have hl : raw26041step0Labels = raw26041Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26041 raw26041Labels permutation265 hz
    mixedMoment B raw26041step0 raw26041step0Labels = mixedMoment B raw26041step1 raw26041step1Labels := by
      have ha : raw26041step1 = (fun i j => raw26041step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26041step1 raw26041step0; decide +kernel
      have hl : raw26041step1Labels = raw26041step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26041step0 raw26041step0Labels permutation40 permutation4
    mixedMoment B raw26041step1 raw26041step1Labels = mixedMoment B raw26041step2 raw26041step2Labels := by
      have ha : raw26041step2 = -raw26041step1 := by apply Matrix.ext; change ∀ i j, raw26041step2 i j = -(raw26041step1 i j); unfold raw26041step2 raw26041step1; decide +kernel
      have hl : raw26041step2Labels = raw26041step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26041step2 raw26041step2Labels = mixedMoment B raw26041step3 raw26041step3Labels := by
      have ha : raw26041step3 = raw26041step2 := by apply Matrix.ext; unfold raw26041step3 raw26041step2; decide +kernel
      have hl : raw26041step2Labels = labelEmbedding7 ∘ raw26041step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26041step2 raw26041step2Labels raw26041step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4251 node4251Labels := by rfl

def raw26042 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26042Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26042step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw26042step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26042step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw26042step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26042 raw26042Labels = mixedMoment B node4395 node4395Labels := by
  calc
    mixedMoment B raw26042 raw26042Labels = mixedMoment B raw26042step0 raw26042step0Labels := by
      have ha : raw26042step0 = (fun i j => raw26042 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26042step0 raw26042; decide +kernel
      have hl : raw26042step0Labels = raw26042Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26042 raw26042Labels permutation152 permutation6
    mixedMoment B raw26042step0 raw26042step0Labels = mixedMoment B raw26042step1 raw26042step1Labels := by
      have ha : raw26042step1 = raw26042step0 := by apply Matrix.ext; unfold raw26042step1 raw26042step0; decide +kernel
      have hl : raw26042step0Labels = labelEmbedding9 ∘ raw26042step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26042step0 raw26042step0Labels raw26042step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4395 node4395Labels := by rfl

def raw26043 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26043Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26043step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw26043step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26043step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw26043step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26043 raw26043Labels = mixedMoment B node4450 node4450Labels := by
  calc
    mixedMoment B raw26043 raw26043Labels = mixedMoment B raw26043step0 raw26043step0Labels := by
      have hz : ∀ j, raw26043 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26043step0 = (fun i j => raw26043 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26043step0 raw26043; decide +kernel
      have hl : raw26043step0Labels = raw26043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26043 raw26043Labels permutation265 hz
    mixedMoment B raw26043step0 raw26043step0Labels = mixedMoment B raw26043step1 raw26043step1Labels := by
      have ha : raw26043step1 = (fun i j => raw26043step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26043step1 raw26043step0; decide +kernel
      have hl : raw26043step1Labels = raw26043step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26043step0 raw26043step0Labels permutation32 permutation6
    mixedMoment B raw26043step1 raw26043step1Labels = mixedMoment B raw26043step2 raw26043step2Labels := by
      have ha : raw26043step2 = raw26043step1 := by apply Matrix.ext; unfold raw26043step2 raw26043step1; decide +kernel
      have hl : raw26043step1Labels = labelEmbedding9 ∘ raw26043step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26043step1 raw26043step1Labels raw26043step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4450 node4450Labels := by rfl

def raw26044 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw26044Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw26044step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw26044step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26044step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw26044step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26044 raw26044Labels = mixedMoment B node4450 node4450Labels := by
  calc
    mixedMoment B raw26044 raw26044Labels = mixedMoment B raw26044step0 raw26044step0Labels := by
      have hz : ∀ j, raw26044 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26044step0 = (fun i j => raw26044 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26044step0 raw26044; decide +kernel
      have hl : raw26044step0Labels = raw26044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26044 raw26044Labels permutation265 hz
    mixedMoment B raw26044step0 raw26044step0Labels = mixedMoment B raw26044step1 raw26044step1Labels := by
      have ha : raw26044step1 = (fun i j => raw26044step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26044step1 raw26044step0; decide +kernel
      have hl : raw26044step1Labels = raw26044step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26044step0 raw26044step0Labels permutation34 permutation6
    mixedMoment B raw26044step1 raw26044step1Labels = mixedMoment B raw26044step2 raw26044step2Labels := by
      have ha : raw26044step2 = raw26044step1 := by apply Matrix.ext; unfold raw26044step2 raw26044step1; decide +kernel
      have hl : raw26044step1Labels = labelEmbedding9 ∘ raw26044step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26044step1 raw26044step1Labels raw26044step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4450 node4450Labels := by rfl

def raw26045 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26045Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26045step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26045step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26045step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26045step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw26045step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26045step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw26045step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26045step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw26045step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26045 raw26045Labels = mixedMoment B node4269 node4269Labels := by
  calc
    mixedMoment B raw26045 raw26045Labels = mixedMoment B raw26045step0 raw26045step0Labels := by
      have hz : ∀ j, raw26045 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26045step0 = (fun i j => raw26045 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26045step0 raw26045; decide +kernel
      have hl : raw26045step0Labels = raw26045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26045 raw26045Labels permutation346 hz
    mixedMoment B raw26045step0 raw26045step0Labels = mixedMoment B raw26045step1 raw26045step1Labels := by
      have hz : ∀ j, raw26045step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26045step1 = (fun i j => raw26045step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26045step1 raw26045step0; decide +kernel
      have hl : raw26045step1Labels = raw26045step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26045step0 raw26045step0Labels permutation56 hz
    mixedMoment B raw26045step1 raw26045step1Labels = mixedMoment B raw26045step2 raw26045step2Labels := by
      have ha : raw26045step2 = (fun i j => raw26045step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26045step2 raw26045step1; decide +kernel
      have hl : raw26045step2Labels = raw26045step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26045step1 raw26045step1Labels permutation10 permutation4
    mixedMoment B raw26045step2 raw26045step2Labels = mixedMoment B raw26045step3 raw26045step3Labels := by
      have ha : raw26045step3 = -raw26045step2 := by apply Matrix.ext; change ∀ i j, raw26045step3 i j = -(raw26045step2 i j); unfold raw26045step3 raw26045step2; decide +kernel
      have hl : raw26045step3Labels = raw26045step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26045step3 raw26045step3Labels = mixedMoment B raw26045step4 raw26045step4Labels := by
      have ha : raw26045step4 = raw26045step3 := by apply Matrix.ext; unfold raw26045step4 raw26045step3; decide +kernel
      have hl : raw26045step3Labels = labelEmbedding7 ∘ raw26045step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26045step3 raw26045step3Labels raw26045step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4269 node4269Labels := by rfl

def raw26046 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26046Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26046step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26046step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26046step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26046step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26046step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26046 raw26046Labels = mixedMoment B node4418 node4418Labels := by
  calc
    mixedMoment B raw26046 raw26046Labels = mixedMoment B raw26046step0 raw26046step0Labels := by
      have hz : ∀ j, raw26046 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26046step0 = (fun i j => raw26046 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26046step0 raw26046; decide +kernel
      have hl : raw26046step0Labels = raw26046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26046 raw26046Labels permutation346 hz
    mixedMoment B raw26046step0 raw26046step0Labels = mixedMoment B raw26046step1 raw26046step1Labels := by
      have ha : raw26046step1 = (fun i j => raw26046step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26046step1 raw26046step0; decide +kernel
      have hl : raw26046step1Labels = raw26046step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26046step0 raw26046step0Labels permutation34 permutation6
    mixedMoment B raw26046step1 raw26046step1Labels = mixedMoment B raw26046step2 raw26046step2Labels := by
      have ha : raw26046step2 = raw26046step1 := by apply Matrix.ext; unfold raw26046step2 raw26046step1; decide +kernel
      have hl : raw26046step1Labels = labelEmbedding9 ∘ raw26046step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26046step1 raw26046step1Labels raw26046step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4418 node4418Labels := by rfl

def raw26047 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw26047Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw26047step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26047step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw26047step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26047step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw26047step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26047step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw26047step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26047 raw26047Labels = mixedMoment B node4490 node4490Labels := by
  calc
    mixedMoment B raw26047 raw26047Labels = mixedMoment B raw26047step0 raw26047step0Labels := by
      have hz : ∀ j, raw26047 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26047step0 = (fun i j => raw26047 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26047step0 raw26047; decide +kernel
      have hl : raw26047step0Labels = raw26047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26047 raw26047Labels permutation346 hz
    mixedMoment B raw26047step0 raw26047step0Labels = mixedMoment B raw26047step1 raw26047step1Labels := by
      have hz : ∀ j, raw26047step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26047step1 = (fun i j => raw26047step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26047step1 raw26047step0; decide +kernel
      have hl : raw26047step1Labels = raw26047step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26047step0 raw26047step0Labels permutation56 hz
    mixedMoment B raw26047step1 raw26047step1Labels = mixedMoment B raw26047step2 raw26047step2Labels := by
      have ha : raw26047step2 = (fun i j => raw26047step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26047step2 raw26047step1; decide +kernel
      have hl : raw26047step2Labels = raw26047step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26047step1 raw26047step1Labels permutation10 permutation6
    mixedMoment B raw26047step2 raw26047step2Labels = mixedMoment B raw26047step3 raw26047step3Labels := by
      have ha : raw26047step3 = raw26047step2 := by apply Matrix.ext; unfold raw26047step3 raw26047step2; decide +kernel
      have hl : raw26047step2Labels = labelEmbedding9 ∘ raw26047step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26047step2 raw26047step2Labels raw26047step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4490 node4490Labels := by rfl

def raw26048 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26048Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26048step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26048step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 0, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26048step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26048step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw26048step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26048step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw26048step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26048step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw26048step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26048 raw26048Labels = mixedMoment B node4269 node4269Labels := by
  calc
    mixedMoment B raw26048 raw26048Labels = mixedMoment B raw26048step0 raw26048step0Labels := by
      have hz : ∀ j, raw26048 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26048step0 = (fun i j => raw26048 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26048step0 raw26048; decide +kernel
      have hl : raw26048step0Labels = raw26048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26048 raw26048Labels permutation346 hz
    mixedMoment B raw26048step0 raw26048step0Labels = mixedMoment B raw26048step1 raw26048step1Labels := by
      have hz : ∀ j, raw26048step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26048step1 = (fun i j => raw26048step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26048step1 raw26048step0; decide +kernel
      have hl : raw26048step1Labels = raw26048step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26048step0 raw26048step0Labels permutation56 hz
    mixedMoment B raw26048step1 raw26048step1Labels = mixedMoment B raw26048step2 raw26048step2Labels := by
      have ha : raw26048step2 = (fun i j => raw26048step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26048step2 raw26048step1; decide +kernel
      have hl : raw26048step2Labels = raw26048step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26048step1 raw26048step1Labels permutation8 permutation4
    mixedMoment B raw26048step2 raw26048step2Labels = mixedMoment B raw26048step3 raw26048step3Labels := by
      have ha : raw26048step3 = -raw26048step2 := by apply Matrix.ext; change ∀ i j, raw26048step3 i j = -(raw26048step2 i j); unfold raw26048step3 raw26048step2; decide +kernel
      have hl : raw26048step3Labels = raw26048step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26048step3 raw26048step3Labels = mixedMoment B raw26048step4 raw26048step4Labels := by
      have ha : raw26048step4 = raw26048step3 := by apply Matrix.ext; unfold raw26048step4 raw26048step3; decide +kernel
      have hl : raw26048step3Labels = labelEmbedding7 ∘ raw26048step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26048step3 raw26048step3Labels raw26048step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4269 node4269Labels := by rfl

def raw26049 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26049step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26049step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26049step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26049step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26049step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26049 raw26049Labels = mixedMoment B node4418 node4418Labels := by
  calc
    mixedMoment B raw26049 raw26049Labels = mixedMoment B raw26049step0 raw26049step0Labels := by
      have hz : ∀ j, raw26049 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26049step0 = (fun i j => raw26049 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26049step0 raw26049; decide +kernel
      have hl : raw26049step0Labels = raw26049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26049 raw26049Labels permutation346 hz
    mixedMoment B raw26049step0 raw26049step0Labels = mixedMoment B raw26049step1 raw26049step1Labels := by
      have ha : raw26049step1 = (fun i j => raw26049step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26049step1 raw26049step0; decide +kernel
      have hl : raw26049step1Labels = raw26049step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26049step0 raw26049step0Labels permutation32 permutation6
    mixedMoment B raw26049step1 raw26049step1Labels = mixedMoment B raw26049step2 raw26049step2Labels := by
      have ha : raw26049step2 = raw26049step1 := by apply Matrix.ext; unfold raw26049step2 raw26049step1; decide +kernel
      have hl : raw26049step1Labels = labelEmbedding9 ∘ raw26049step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26049step1 raw26049step1Labels raw26049step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4418 node4418Labels := by rfl

def raw26050 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26050Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26050step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26050step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26050step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26050step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26050 raw26050Labels = mixedMoment B node4418 node4418Labels := by
  calc
    mixedMoment B raw26050 raw26050Labels = mixedMoment B raw26050step0 raw26050step0Labels := by
      have hz : ∀ j, raw26050 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26050step0 = (fun i j => raw26050 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26050step0 raw26050; decide +kernel
      have hl : raw26050step0Labels = raw26050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26050 raw26050Labels permutation265 hz
    mixedMoment B raw26050step0 raw26050step0Labels = mixedMoment B raw26050step1 raw26050step1Labels := by
      have ha : raw26050step1 = (fun i j => raw26050step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26050step1 raw26050step0; decide +kernel
      have hl : raw26050step1Labels = raw26050step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26050step0 raw26050step0Labels permutation32 permutation6
    mixedMoment B raw26050step1 raw26050step1Labels = mixedMoment B raw26050step2 raw26050step2Labels := by
      have ha : raw26050step2 = raw26050step1 := by apply Matrix.ext; unfold raw26050step2 raw26050step1; decide +kernel
      have hl : raw26050step1Labels = labelEmbedding9 ∘ raw26050step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26050step1 raw26050step1Labels raw26050step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4418 node4418Labels := by rfl

def raw26051 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26051Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26051step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26051step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26051step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26051step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw26051step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26051step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw26051step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26051 raw26051Labels = mixedMoment B node4490 node4490Labels := by
  calc
    mixedMoment B raw26051 raw26051Labels = mixedMoment B raw26051step0 raw26051step0Labels := by
      have hz : ∀ j, raw26051 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26051step0 = (fun i j => raw26051 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26051step0 raw26051; decide +kernel
      have hl : raw26051step0Labels = raw26051Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26051 raw26051Labels permutation346 hz
    mixedMoment B raw26051step0 raw26051step0Labels = mixedMoment B raw26051step1 raw26051step1Labels := by
      have hz : ∀ j, raw26051step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26051step1 = (fun i j => raw26051step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26051step1 raw26051step0; decide +kernel
      have hl : raw26051step1Labels = raw26051step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26051step0 raw26051step0Labels permutation56 hz
    mixedMoment B raw26051step1 raw26051step1Labels = mixedMoment B raw26051step2 raw26051step2Labels := by
      have ha : raw26051step2 = (fun i j => raw26051step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26051step2 raw26051step1; decide +kernel
      have hl : raw26051step2Labels = raw26051step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26051step1 raw26051step1Labels permutation8 permutation6
    mixedMoment B raw26051step2 raw26051step2Labels = mixedMoment B raw26051step3 raw26051step3Labels := by
      have ha : raw26051step3 = raw26051step2 := by apply Matrix.ext; unfold raw26051step3 raw26051step2; decide +kernel
      have hl : raw26051step2Labels = labelEmbedding9 ∘ raw26051step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26051step2 raw26051step2Labels raw26051step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4490 node4490Labels := by rfl

def raw26052 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26052Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26052step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26052step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 0, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26052step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26052step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-4, 2, 2]]
def raw26052step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26052step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw26052step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26052step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw26052step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26052 raw26052Labels = mixedMoment B node4257 node4257Labels := by
  calc
    mixedMoment B raw26052 raw26052Labels = mixedMoment B raw26052step0 raw26052step0Labels := by
      have hz : ∀ j, raw26052 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26052step0 = (fun i j => raw26052 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26052step0 raw26052; decide +kernel
      have hl : raw26052step0Labels = raw26052Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26052 raw26052Labels permutation346 hz
    mixedMoment B raw26052step0 raw26052step0Labels = mixedMoment B raw26052step1 raw26052step1Labels := by
      have hz : ∀ j, raw26052step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26052step1 = (fun i j => raw26052step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26052step1 raw26052step0; decide +kernel
      have hl : raw26052step1Labels = raw26052step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26052step0 raw26052step0Labels permutation56 hz
    mixedMoment B raw26052step1 raw26052step1Labels = mixedMoment B raw26052step2 raw26052step2Labels := by
      have ha : raw26052step2 = (fun i j => raw26052step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26052step2 raw26052step1; decide +kernel
      have hl : raw26052step2Labels = raw26052step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26052step1 raw26052step1Labels permutation8 permutation4
    mixedMoment B raw26052step2 raw26052step2Labels = mixedMoment B raw26052step3 raw26052step3Labels := by
      have ha : raw26052step3 = -raw26052step2 := by apply Matrix.ext; change ∀ i j, raw26052step3 i j = -(raw26052step2 i j); unfold raw26052step3 raw26052step2; decide +kernel
      have hl : raw26052step3Labels = raw26052step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26052step3 raw26052step3Labels = mixedMoment B raw26052step4 raw26052step4Labels := by
      have ha : raw26052step4 = raw26052step3 := by apply Matrix.ext; unfold raw26052step4 raw26052step3; decide +kernel
      have hl : raw26052step3Labels = labelEmbedding7 ∘ raw26052step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26052step3 raw26052step3Labels raw26052step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4257 node4257Labels := by rfl

def raw26053 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26053Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26053step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26053step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw26053step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26053step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw26053step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26053 raw26053Labels = mixedMoment B node4416 node4416Labels := by
  calc
    mixedMoment B raw26053 raw26053Labels = mixedMoment B raw26053step0 raw26053step0Labels := by
      have hz : ∀ j, raw26053 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26053step0 = (fun i j => raw26053 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26053step0 raw26053; decide +kernel
      have hl : raw26053step0Labels = raw26053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26053 raw26053Labels permutation346 hz
    mixedMoment B raw26053step0 raw26053step0Labels = mixedMoment B raw26053step1 raw26053step1Labels := by
      have ha : raw26053step1 = (fun i j => raw26053step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26053step1 raw26053step0; decide +kernel
      have hl : raw26053step1Labels = raw26053step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26053step0 raw26053step0Labels permutation32 permutation6
    mixedMoment B raw26053step1 raw26053step1Labels = mixedMoment B raw26053step2 raw26053step2Labels := by
      have ha : raw26053step2 = raw26053step1 := by apply Matrix.ext; unfold raw26053step2 raw26053step1; decide +kernel
      have hl : raw26053step1Labels = labelEmbedding9 ∘ raw26053step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26053step1 raw26053step1Labels raw26053step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4416 node4416Labels := by rfl

def raw26054 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26054Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26054step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw26054step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26054step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw26054step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26054 raw26054Labels = mixedMoment B node4416 node4416Labels := by
  calc
    mixedMoment B raw26054 raw26054Labels = mixedMoment B raw26054step0 raw26054step0Labels := by
      have hz : ∀ j, raw26054 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26054step0 = (fun i j => raw26054 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26054step0 raw26054; decide +kernel
      have hl : raw26054step0Labels = raw26054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26054 raw26054Labels permutation265 hz
    mixedMoment B raw26054step0 raw26054step0Labels = mixedMoment B raw26054step1 raw26054step1Labels := by
      have ha : raw26054step1 = (fun i j => raw26054step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26054step1 raw26054step0; decide +kernel
      have hl : raw26054step1Labels = raw26054step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26054step0 raw26054step0Labels permutation32 permutation6
    mixedMoment B raw26054step1 raw26054step1Labels = mixedMoment B raw26054step2 raw26054step2Labels := by
      have ha : raw26054step2 = raw26054step1 := by apply Matrix.ext; unfold raw26054step2 raw26054step1; decide +kernel
      have hl : raw26054step1Labels = labelEmbedding9 ∘ raw26054step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26054step1 raw26054step1Labels raw26054step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4416 node4416Labels := by rfl

def raw26055 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26055Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26055step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26055step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 1, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26055step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26055step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw26055step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26055step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw26055step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26055 raw26055Labels = mixedMoment B node4488 node4488Labels := by
  calc
    mixedMoment B raw26055 raw26055Labels = mixedMoment B raw26055step0 raw26055step0Labels := by
      have hz : ∀ j, raw26055 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26055step0 = (fun i j => raw26055 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26055step0 raw26055; decide +kernel
      have hl : raw26055step0Labels = raw26055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26055 raw26055Labels permutation346 hz
    mixedMoment B raw26055step0 raw26055step0Labels = mixedMoment B raw26055step1 raw26055step1Labels := by
      have hz : ∀ j, raw26055step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26055step1 = (fun i j => raw26055step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26055step1 raw26055step0; decide +kernel
      have hl : raw26055step1Labels = raw26055step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26055step0 raw26055step0Labels permutation56 hz
    mixedMoment B raw26055step1 raw26055step1Labels = mixedMoment B raw26055step2 raw26055step2Labels := by
      have ha : raw26055step2 = (fun i j => raw26055step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26055step2 raw26055step1; decide +kernel
      have hl : raw26055step2Labels = raw26055step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26055step1 raw26055step1Labels permutation8 permutation6
    mixedMoment B raw26055step2 raw26055step2Labels = mixedMoment B raw26055step3 raw26055step3Labels := by
      have ha : raw26055step3 = raw26055step2 := by apply Matrix.ext; unfold raw26055step3 raw26055step2; decide +kernel
      have hl : raw26055step2Labels = labelEmbedding9 ∘ raw26055step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26055step2 raw26055step2Labels raw26055step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4488 node4488Labels := by rfl

def raw26056 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![2, -4, 2]]
def raw26056Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![2, -4, 2]]
def raw26056step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26056step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![-2, 1, 1], ![2, -4, 2]]
def raw26056step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26056step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw26056step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26056step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw26056step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26056 raw26056Labels = mixedMoment B node4488 node4488Labels := by
  calc
    mixedMoment B raw26056 raw26056Labels = mixedMoment B raw26056step0 raw26056step0Labels := by
      have hz : ∀ j, raw26056 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26056step0 = (fun i j => raw26056 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26056step0 raw26056; decide +kernel
      have hl : raw26056step0Labels = raw26056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26056 raw26056Labels permutation346 hz
    mixedMoment B raw26056step0 raw26056step0Labels = mixedMoment B raw26056step1 raw26056step1Labels := by
      have hz : ∀ j, raw26056step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26056step1 = (fun i j => raw26056step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26056step1 raw26056step0; decide +kernel
      have hl : raw26056step1Labels = raw26056step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26056step0 raw26056step0Labels permutation56 hz
    mixedMoment B raw26056step1 raw26056step1Labels = mixedMoment B raw26056step2 raw26056step2Labels := by
      have ha : raw26056step2 = (fun i j => raw26056step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26056step2 raw26056step1; decide +kernel
      have hl : raw26056step2Labels = raw26056step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26056step1 raw26056step1Labels permutation10 permutation6
    mixedMoment B raw26056step2 raw26056step2Labels = mixedMoment B raw26056step3 raw26056step3Labels := by
      have ha : raw26056step3 = raw26056step2 := by apply Matrix.ext; unfold raw26056step3 raw26056step2; decide +kernel
      have hl : raw26056step2Labels = labelEmbedding9 ∘ raw26056step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26056step2 raw26056step2Labels raw26056step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4488 node4488Labels := by rfl

def raw26057 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26057Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26057step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -4, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw26057step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26057step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw26057step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26057step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw26057step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26057 raw26057Labels = mixedMoment B node1478 node1478Labels := by
  calc
    mixedMoment B raw26057 raw26057Labels = mixedMoment B raw26057step0 raw26057step0Labels := by
      have hz : ∀ j, raw26057 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26057step0 = (fun i j => raw26057 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26057step0 raw26057; decide +kernel
      have hl : raw26057step0Labels = raw26057Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26057 raw26057Labels permutation265 hz
    mixedMoment B raw26057step0 raw26057step0Labels = mixedMoment B raw26057step1 raw26057step1Labels := by
      have ha : raw26057step1 = (fun i j => raw26057step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26057step1 raw26057step0; decide +kernel
      have hl : raw26057step1Labels = raw26057step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26057step0 raw26057step0Labels permutation40 permutation5
    mixedMoment B raw26057step1 raw26057step1Labels = mixedMoment B raw26057step2 raw26057step2Labels := by
      have ha : raw26057step2 = -raw26057step1 := by apply Matrix.ext; change ∀ i j, raw26057step2 i j = -(raw26057step1 i j); unfold raw26057step2 raw26057step1; decide +kernel
      have hl : raw26057step2Labels = raw26057step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26057step2 raw26057step2Labels = mixedMoment B raw26057step3 raw26057step3Labels := by
      have ha : raw26057step3 = raw26057step2 := by apply Matrix.ext; unfold raw26057step3 raw26057step2; decide +kernel
      have hl : raw26057step2Labels = labelEmbedding1 ∘ raw26057step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26057step2 raw26057step2Labels raw26057step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1478 node1478Labels := by rfl

def raw26058 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26058Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26058step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26058step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw26058step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26058 raw26058Labels = mixedMoment B node1398 node1398Labels := by
  calc
    mixedMoment B raw26058 raw26058Labels = mixedMoment B raw26058step0 raw26058step0Labels := by
      have ha : raw26058step0 = (fun i j => raw26058 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26058step0 raw26058; decide +kernel
      have hl : raw26058step0Labels = raw26058Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26058 raw26058Labels permutation176 permutation7
    mixedMoment B raw26058step0 raw26058step0Labels = mixedMoment B raw26058step1 raw26058step1Labels := by
      have ha : raw26058step1 = raw26058step0 := by apply Matrix.ext; unfold raw26058step1 raw26058step0; decide +kernel
      have hl : raw26058step0Labels = labelEmbedding1 ∘ raw26058step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26058step0 raw26058step0Labels raw26058step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1398 node1398Labels := by rfl

def raw26059 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26059Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26059step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw26059step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26059step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw26059step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26059 raw26059Labels = mixedMoment B node1415 node1415Labels := by
  calc
    mixedMoment B raw26059 raw26059Labels = mixedMoment B raw26059step0 raw26059step0Labels := by
      have hz : ∀ j, raw26059 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26059step0 = (fun i j => raw26059 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26059step0 raw26059; decide +kernel
      have hl : raw26059step0Labels = raw26059Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26059 raw26059Labels permutation265 hz
    mixedMoment B raw26059step0 raw26059step0Labels = mixedMoment B raw26059step1 raw26059step1Labels := by
      have ha : raw26059step1 = (fun i j => raw26059step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26059step1 raw26059step0; decide +kernel
      have hl : raw26059step1Labels = raw26059step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26059step0 raw26059step0Labels permutation34 permutation7
    mixedMoment B raw26059step1 raw26059step1Labels = mixedMoment B raw26059step2 raw26059step2Labels := by
      have ha : raw26059step2 = raw26059step1 := by apply Matrix.ext; unfold raw26059step2 raw26059step1; decide +kernel
      have hl : raw26059step1Labels = labelEmbedding1 ∘ raw26059step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26059step1 raw26059step1Labels raw26059step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1415 node1415Labels := by rfl

def raw26060 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw26060Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw26060step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26060step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw26060step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26060step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw26060step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26060 raw26060Labels = mixedMoment B node1415 node1415Labels := by
  calc
    mixedMoment B raw26060 raw26060Labels = mixedMoment B raw26060step0 raw26060step0Labels := by
      have hz : ∀ j, raw26060 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26060step0 = (fun i j => raw26060 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26060step0 raw26060; decide +kernel
      have hl : raw26060step0Labels = raw26060Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26060 raw26060Labels permutation265 hz
    mixedMoment B raw26060step0 raw26060step0Labels = mixedMoment B raw26060step1 raw26060step1Labels := by
      have ha : raw26060step1 = (fun i j => raw26060step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26060step1 raw26060step0; decide +kernel
      have hl : raw26060step1Labels = raw26060step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26060step0 raw26060step0Labels permutation32 permutation7
    mixedMoment B raw26060step1 raw26060step1Labels = mixedMoment B raw26060step2 raw26060step2Labels := by
      have ha : raw26060step2 = raw26060step1 := by apply Matrix.ext; unfold raw26060step2 raw26060step1; decide +kernel
      have hl : raw26060step1Labels = labelEmbedding1 ∘ raw26060step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26060step1 raw26060step1Labels raw26060step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1415 node1415Labels := by rfl

def raw26061 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26061Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26061step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26061step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26061step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26061step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -4, 0], ![0, 1, -1], ![-1, 1, 0], ![-3, 2, 1]]
def raw26061step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26061step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![3, -2, -1]]
def raw26061step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26061step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![3, -2, -1]]
def raw26061step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26061 raw26061Labels = mixedMoment B node1484 node1484Labels := by
  calc
    mixedMoment B raw26061 raw26061Labels = mixedMoment B raw26061step0 raw26061step0Labels := by
      have hz : ∀ j, raw26061 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26061step0 = (fun i j => raw26061 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26061step0 raw26061; decide +kernel
      have hl : raw26061step0Labels = raw26061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26061 raw26061Labels permutation346 hz
    mixedMoment B raw26061step0 raw26061step0Labels = mixedMoment B raw26061step1 raw26061step1Labels := by
      have hz : ∀ j, raw26061step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26061step1 = (fun i j => raw26061step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26061step1 raw26061step0; decide +kernel
      have hl : raw26061step1Labels = raw26061step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26061step0 raw26061step0Labels permutation56 hz
    mixedMoment B raw26061step1 raw26061step1Labels = mixedMoment B raw26061step2 raw26061step2Labels := by
      have ha : raw26061step2 = (fun i j => raw26061step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26061step2 raw26061step1; decide +kernel
      have hl : raw26061step2Labels = raw26061step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26061step1 raw26061step1Labels permutation10 permutation5
    mixedMoment B raw26061step2 raw26061step2Labels = mixedMoment B raw26061step3 raw26061step3Labels := by
      have ha : raw26061step3 = -raw26061step2 := by apply Matrix.ext; change ∀ i j, raw26061step3 i j = -(raw26061step2 i j); unfold raw26061step3 raw26061step2; decide +kernel
      have hl : raw26061step3Labels = raw26061step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26061step3 raw26061step3Labels = mixedMoment B raw26061step4 raw26061step4Labels := by
      have ha : raw26061step4 = raw26061step3 := by apply Matrix.ext; unfold raw26061step4 raw26061step3; decide +kernel
      have hl : raw26061step3Labels = labelEmbedding1 ∘ raw26061step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26061step3 raw26061step3Labels raw26061step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1484 node1484Labels := by rfl

def raw26062 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26062Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26062step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw26062step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26062step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw26062step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26062 raw26062Labels = mixedMoment B node1427 node1427Labels := by
  calc
    mixedMoment B raw26062 raw26062Labels = mixedMoment B raw26062step0 raw26062step0Labels := by
      have hz : ∀ j, raw26062 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26062step0 = (fun i j => raw26062 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26062step0 raw26062; decide +kernel
      have hl : raw26062step0Labels = raw26062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26062 raw26062Labels permutation346 hz
    mixedMoment B raw26062step0 raw26062step0Labels = mixedMoment B raw26062step1 raw26062step1Labels := by
      have ha : raw26062step1 = (fun i j => raw26062step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26062step1 raw26062step0; decide +kernel
      have hl : raw26062step1Labels = raw26062step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26062step0 raw26062step0Labels permutation32 permutation7
    mixedMoment B raw26062step1 raw26062step1Labels = mixedMoment B raw26062step2 raw26062step2Labels := by
      have ha : raw26062step2 = raw26062step1 := by apply Matrix.ext; unfold raw26062step2 raw26062step1; decide +kernel
      have hl : raw26062step1Labels = labelEmbedding1 ∘ raw26062step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26062step1 raw26062step1Labels raw26062step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1427 node1427Labels := by rfl

def raw26063 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26063Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw26063step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw26063step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26063step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw26063step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26063 raw26063Labels = mixedMoment B node1427 node1427Labels := by
  calc
    mixedMoment B raw26063 raw26063Labels = mixedMoment B raw26063step0 raw26063step0Labels := by
      have hz : ∀ j, raw26063 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26063step0 = (fun i j => raw26063 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26063step0 raw26063; decide +kernel
      have hl : raw26063step0Labels = raw26063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26063 raw26063Labels permutation265 hz
    mixedMoment B raw26063step0 raw26063step0Labels = mixedMoment B raw26063step1 raw26063step1Labels := by
      have ha : raw26063step1 = (fun i j => raw26063step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26063step1 raw26063step0; decide +kernel
      have hl : raw26063step1Labels = raw26063step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26063step0 raw26063step0Labels permutation32 permutation7
    mixedMoment B raw26063step1 raw26063step1Labels = mixedMoment B raw26063step2 raw26063step2Labels := by
      have ha : raw26063step2 = raw26063step1 := by apply Matrix.ext; unfold raw26063step2 raw26063step1; decide +kernel
      have hl : raw26063step1Labels = labelEmbedding1 ∘ raw26063step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26063step1 raw26063step1Labels raw26063step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1427 node1427Labels := by rfl

def raw26064 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw26064Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw26064step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26064step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw26064step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26064step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw26064step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26064step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw26064step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26064 raw26064Labels = mixedMoment B node1449 node1449Labels := by
  calc
    mixedMoment B raw26064 raw26064Labels = mixedMoment B raw26064step0 raw26064step0Labels := by
      have hz : ∀ j, raw26064 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26064step0 = (fun i j => raw26064 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26064step0 raw26064; decide +kernel
      have hl : raw26064step0Labels = raw26064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26064 raw26064Labels permutation346 hz
    mixedMoment B raw26064step0 raw26064step0Labels = mixedMoment B raw26064step1 raw26064step1Labels := by
      have hz : ∀ j, raw26064step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26064step1 = (fun i j => raw26064step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26064step1 raw26064step0; decide +kernel
      have hl : raw26064step1Labels = raw26064step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26064step0 raw26064step0Labels permutation56 hz
    mixedMoment B raw26064step1 raw26064step1Labels = mixedMoment B raw26064step2 raw26064step2Labels := by
      have ha : raw26064step2 = (fun i j => raw26064step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26064step2 raw26064step1; decide +kernel
      have hl : raw26064step2Labels = raw26064step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26064step1 raw26064step1Labels permutation8 permutation7
    mixedMoment B raw26064step2 raw26064step2Labels = mixedMoment B raw26064step3 raw26064step3Labels := by
      have ha : raw26064step3 = raw26064step2 := by apply Matrix.ext; unfold raw26064step3 raw26064step2; decide +kernel
      have hl : raw26064step2Labels = labelEmbedding1 ∘ raw26064step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26064step2 raw26064step2Labels raw26064step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1449 node1449Labels := by rfl

def raw26065 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26065Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26065step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26065step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 0, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26065step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26065step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -4, 0], ![0, 1, -1], ![-1, 1, 0], ![-3, 2, 1]]
def raw26065step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26065step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![3, -2, -1]]
def raw26065step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26065step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![3, -2, -1]]
def raw26065step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26065 raw26065Labels = mixedMoment B node1484 node1484Labels := by
  calc
    mixedMoment B raw26065 raw26065Labels = mixedMoment B raw26065step0 raw26065step0Labels := by
      have hz : ∀ j, raw26065 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26065step0 = (fun i j => raw26065 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26065step0 raw26065; decide +kernel
      have hl : raw26065step0Labels = raw26065Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26065 raw26065Labels permutation346 hz
    mixedMoment B raw26065step0 raw26065step0Labels = mixedMoment B raw26065step1 raw26065step1Labels := by
      have hz : ∀ j, raw26065step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26065step1 = (fun i j => raw26065step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26065step1 raw26065step0; decide +kernel
      have hl : raw26065step1Labels = raw26065step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26065step0 raw26065step0Labels permutation56 hz
    mixedMoment B raw26065step1 raw26065step1Labels = mixedMoment B raw26065step2 raw26065step2Labels := by
      have ha : raw26065step2 = (fun i j => raw26065step1 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26065step2 raw26065step1; decide +kernel
      have hl : raw26065step2Labels = raw26065step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26065step1 raw26065step1Labels permutation8 permutation5
    mixedMoment B raw26065step2 raw26065step2Labels = mixedMoment B raw26065step3 raw26065step3Labels := by
      have ha : raw26065step3 = -raw26065step2 := by apply Matrix.ext; change ∀ i j, raw26065step3 i j = -(raw26065step2 i j); unfold raw26065step3 raw26065step2; decide +kernel
      have hl : raw26065step3Labels = raw26065step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26065step3 raw26065step3Labels = mixedMoment B raw26065step4 raw26065step4Labels := by
      have ha : raw26065step4 = raw26065step3 := by apply Matrix.ext; unfold raw26065step4 raw26065step3; decide +kernel
      have hl : raw26065step3Labels = labelEmbedding1 ∘ raw26065step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26065step3 raw26065step3Labels raw26065step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1484 node1484Labels := by rfl

def raw26066 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26066Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26066step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26066step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw26066step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26066step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw26066step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26066 raw26066Labels = mixedMoment B node1427 node1427Labels := by
  calc
    mixedMoment B raw26066 raw26066Labels = mixedMoment B raw26066step0 raw26066step0Labels := by
      have hz : ∀ j, raw26066 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26066step0 = (fun i j => raw26066 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26066step0 raw26066; decide +kernel
      have hl : raw26066step0Labels = raw26066Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26066 raw26066Labels permutation346 hz
    mixedMoment B raw26066step0 raw26066step0Labels = mixedMoment B raw26066step1 raw26066step1Labels := by
      have ha : raw26066step1 = (fun i j => raw26066step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26066step1 raw26066step0; decide +kernel
      have hl : raw26066step1Labels = raw26066step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26066step0 raw26066step0Labels permutation34 permutation7
    mixedMoment B raw26066step1 raw26066step1Labels = mixedMoment B raw26066step2 raw26066step2Labels := by
      have ha : raw26066step2 = raw26066step1 := by apply Matrix.ext; unfold raw26066step2 raw26066step1; decide +kernel
      have hl : raw26066step1Labels = labelEmbedding1 ∘ raw26066step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26066step1 raw26066step1Labels raw26066step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1427 node1427Labels := by rfl

def raw26067 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26067Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26067step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26067step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw26067step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26067step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw26067step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26067 raw26067Labels = mixedMoment B node1427 node1427Labels := by
  calc
    mixedMoment B raw26067 raw26067Labels = mixedMoment B raw26067step0 raw26067step0Labels := by
      have hz : ∀ j, raw26067 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26067step0 = (fun i j => raw26067 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26067step0 raw26067; decide +kernel
      have hl : raw26067step0Labels = raw26067Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26067 raw26067Labels permutation265 hz
    mixedMoment B raw26067step0 raw26067step0Labels = mixedMoment B raw26067step1 raw26067step1Labels := by
      have ha : raw26067step1 = (fun i j => raw26067step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26067step1 raw26067step0; decide +kernel
      have hl : raw26067step1Labels = raw26067step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26067step0 raw26067step0Labels permutation34 permutation7
    mixedMoment B raw26067step1 raw26067step1Labels = mixedMoment B raw26067step2 raw26067step2Labels := by
      have ha : raw26067step2 = raw26067step1 := by apply Matrix.ext; unfold raw26067step2 raw26067step1; decide +kernel
      have hl : raw26067step1Labels = labelEmbedding1 ∘ raw26067step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26067step1 raw26067step1Labels raw26067step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1427 node1427Labels := by rfl

def raw26068 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26068Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26068step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26068step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26068step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26068step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw26068step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26068step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw26068step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26068 raw26068Labels = mixedMoment B node1449 node1449Labels := by
  calc
    mixedMoment B raw26068 raw26068Labels = mixedMoment B raw26068step0 raw26068step0Labels := by
      have hz : ∀ j, raw26068 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26068step0 = (fun i j => raw26068 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26068step0 raw26068; decide +kernel
      have hl : raw26068step0Labels = raw26068Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26068 raw26068Labels permutation346 hz
    mixedMoment B raw26068step0 raw26068step0Labels = mixedMoment B raw26068step1 raw26068step1Labels := by
      have hz : ∀ j, raw26068step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26068step1 = (fun i j => raw26068step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26068step1 raw26068step0; decide +kernel
      have hl : raw26068step1Labels = raw26068step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26068step0 raw26068step0Labels permutation56 hz
    mixedMoment B raw26068step1 raw26068step1Labels = mixedMoment B raw26068step2 raw26068step2Labels := by
      have ha : raw26068step2 = (fun i j => raw26068step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26068step2 raw26068step1; decide +kernel
      have hl : raw26068step2Labels = raw26068step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26068step1 raw26068step1Labels permutation10 permutation7
    mixedMoment B raw26068step2 raw26068step2Labels = mixedMoment B raw26068step3 raw26068step3Labels := by
      have ha : raw26068step3 = raw26068step2 := by apply Matrix.ext; unfold raw26068step3 raw26068step2; decide +kernel
      have hl : raw26068step2Labels = labelEmbedding1 ∘ raw26068step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26068step2 raw26068step2Labels raw26068step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1449 node1449Labels := by rfl

def raw26069 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26069Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26069step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26069step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 0, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26069step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26069step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw26069step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26069step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![4, -4, 0]]
def raw26069step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26069 raw26069Labels = mixedMoment B node1255 node1255Labels := by
  calc
    mixedMoment B raw26069 raw26069Labels = mixedMoment B raw26069step0 raw26069step0Labels := by
      have hz : ∀ j, raw26069 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26069step0 = (fun i j => raw26069 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26069step0 raw26069; decide +kernel
      have hl : raw26069step0Labels = raw26069Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26069 raw26069Labels permutation346 hz
    mixedMoment B raw26069step0 raw26069step0Labels = mixedMoment B raw26069step1 raw26069step1Labels := by
      have hz : ∀ j, raw26069step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26069step1 = (fun i j => raw26069step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26069step1 raw26069step0; decide +kernel
      have hl : raw26069step1Labels = raw26069step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26069step0 raw26069step0Labels permutation56 hz
    mixedMoment B raw26069step1 raw26069step1Labels = mixedMoment B raw26069step2 raw26069step2Labels := by
      have ha : raw26069step2 = (fun i j => raw26069step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26069step2 raw26069step1; decide +kernel
      have hl : raw26069step2Labels = raw26069step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26069step1 raw26069step1Labels permutation29 permutation5
    mixedMoment B raw26069step2 raw26069step2Labels = mixedMoment B raw26069step3 raw26069step3Labels := by
      have ha : raw26069step3 = raw26069step2 := by apply Matrix.ext; unfold raw26069step3 raw26069step2; decide +kernel
      have hl : raw26069step2Labels = labelEmbedding1 ∘ raw26069step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26069step2 raw26069step2Labels raw26069step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1255 node1255Labels := by rfl

def raw26070 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26070Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26070step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw26070step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26070step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw26070step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26070 raw26070Labels = mixedMoment B node1252 node1252Labels := by
  calc
    mixedMoment B raw26070 raw26070Labels = mixedMoment B raw26070step0 raw26070step0Labels := by
      have hz : ∀ j, raw26070 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26070step0 = (fun i j => raw26070 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26070step0 raw26070; decide +kernel
      have hl : raw26070step0Labels = raw26070Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26070 raw26070Labels permutation346 hz
    mixedMoment B raw26070step0 raw26070step0Labels = mixedMoment B raw26070step1 raw26070step1Labels := by
      have ha : raw26070step1 = (fun i j => raw26070step0 (permutation145 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26070step1 raw26070step0; decide +kernel
      have hl : raw26070step1Labels = raw26070step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26070step0 raw26070step0Labels permutation145 permutation5
    mixedMoment B raw26070step1 raw26070step1Labels = mixedMoment B raw26070step2 raw26070step2Labels := by
      have ha : raw26070step2 = raw26070step1 := by apply Matrix.ext; unfold raw26070step2 raw26070step1; decide +kernel
      have hl : raw26070step1Labels = labelEmbedding1 ∘ raw26070step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26070step1 raw26070step1Labels raw26070step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1252 node1252Labels := by rfl

def raw26071 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26071Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26071step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26071step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw26071step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26071step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw26071step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26071 raw26071Labels = mixedMoment B node1252 node1252Labels := by
  calc
    mixedMoment B raw26071 raw26071Labels = mixedMoment B raw26071step0 raw26071step0Labels := by
      have hz : ∀ j, raw26071 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26071step0 = (fun i j => raw26071 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26071step0 raw26071; decide +kernel
      have hl : raw26071step0Labels = raw26071Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26071 raw26071Labels permutation265 hz
    mixedMoment B raw26071step0 raw26071step0Labels = mixedMoment B raw26071step1 raw26071step1Labels := by
      have ha : raw26071step1 = (fun i j => raw26071step0 (permutation145 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26071step1 raw26071step0; decide +kernel
      have hl : raw26071step1Labels = raw26071step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26071step0 raw26071step0Labels permutation145 permutation5
    mixedMoment B raw26071step1 raw26071step1Labels = mixedMoment B raw26071step2 raw26071step2Labels := by
      have ha : raw26071step2 = raw26071step1 := by apply Matrix.ext; unfold raw26071step2 raw26071step1; decide +kernel
      have hl : raw26071step1Labels = labelEmbedding1 ∘ raw26071step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26071step1 raw26071step1Labels raw26071step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1252 node1252Labels := by rfl

def raw26072 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26072Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26072step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26072step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 1, 1], ![-1, 0, 1], ![2, -4, 2]]
def raw26072step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26072step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw26072step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26072step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw26072step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26072 raw26072Labels = mixedMoment B node1272 node1272Labels := by
  calc
    mixedMoment B raw26072 raw26072Labels = mixedMoment B raw26072step0 raw26072step0Labels := by
      have hz : ∀ j, raw26072 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26072step0 = (fun i j => raw26072 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26072step0 raw26072; decide +kernel
      have hl : raw26072step0Labels = raw26072Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26072 raw26072Labels permutation346 hz
    mixedMoment B raw26072step0 raw26072step0Labels = mixedMoment B raw26072step1 raw26072step1Labels := by
      have hz : ∀ j, raw26072step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26072step1 = (fun i j => raw26072step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26072step1 raw26072step0; decide +kernel
      have hl : raw26072step1Labels = raw26072step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26072step0 raw26072step0Labels permutation56 hz
    mixedMoment B raw26072step1 raw26072step1Labels = mixedMoment B raw26072step2 raw26072step2Labels := by
      have ha : raw26072step2 = (fun i j => raw26072step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26072step2 raw26072step1; decide +kernel
      have hl : raw26072step2Labels = raw26072step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26072step1 raw26072step1Labels permutation31 permutation5
    mixedMoment B raw26072step2 raw26072step2Labels = mixedMoment B raw26072step3 raw26072step3Labels := by
      have ha : raw26072step3 = raw26072step2 := by apply Matrix.ext; unfold raw26072step3 raw26072step2; decide +kernel
      have hl : raw26072step2Labels = labelEmbedding1 ∘ raw26072step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26072step2 raw26072step2Labels raw26072step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1272 node1272Labels := by rfl

def raw26073 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![2, -4, 2]]
def raw26073Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![2, -4, 2]]
def raw26073step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26073step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![-2, 1, 1], ![2, -4, 2]]
def raw26073step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26073step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw26073step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26073step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw26073step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26073 raw26073Labels = mixedMoment B node1272 node1272Labels := by
  calc
    mixedMoment B raw26073 raw26073Labels = mixedMoment B raw26073step0 raw26073step0Labels := by
      have hz : ∀ j, raw26073 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26073step0 = (fun i j => raw26073 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26073step0 raw26073; decide +kernel
      have hl : raw26073step0Labels = raw26073Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26073 raw26073Labels permutation346 hz
    mixedMoment B raw26073step0 raw26073step0Labels = mixedMoment B raw26073step1 raw26073step1Labels := by
      have hz : ∀ j, raw26073step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26073step1 = (fun i j => raw26073step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26073step1 raw26073step0; decide +kernel
      have hl : raw26073step1Labels = raw26073step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26073step0 raw26073step0Labels permutation56 hz
    mixedMoment B raw26073step1 raw26073step1Labels = mixedMoment B raw26073step2 raw26073step2Labels := by
      have ha : raw26073step2 = (fun i j => raw26073step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw26073step2 raw26073step1; decide +kernel
      have hl : raw26073step2Labels = raw26073step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26073step1 raw26073step1Labels permutation29 permutation5
    mixedMoment B raw26073step2 raw26073step2Labels = mixedMoment B raw26073step3 raw26073step3Labels := by
      have ha : raw26073step3 = raw26073step2 := by apply Matrix.ext; unfold raw26073step3 raw26073step2; decide +kernel
      have hl : raw26073step2Labels = labelEmbedding1 ∘ raw26073step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26073step2 raw26073step2Labels raw26073step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1272 node1272Labels := by rfl

def raw26074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![2, -2, 0]]
def raw26074Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![2, -2, 0]]
def raw26074step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw26074step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26074 raw26074Labels = mixedMoment B node1006 node1006Labels := by
  calc
    mixedMoment B raw26074 raw26074Labels = mixedMoment B raw26074step0 raw26074step0Labels := by
      have hz : ∀ j, raw26074 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26074step0 = (fun i j => raw26074 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26074step0 raw26074; decide +kernel
      have hl : raw26074step0Labels = raw26074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26074 raw26074Labels permutation265 hz
    mixedMoment B raw26074step0 raw26074step0Labels = mixedMoment B raw26074step1 raw26074step1Labels := by
      have ha : raw26074step1 = (fun i j => raw26074step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26074step1 raw26074step0; decide +kernel
      have hl : raw26074step1Labels = raw26074step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26074step0 raw26074step0Labels permutation34 permutation2
    _ = mixedMoment B node1006 node1006Labels := by rfl

def raw26075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![2, -2, 0]]
def raw26075Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw26075step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26075 raw26075Labels = mixedMoment B node2001 node2001Labels := by
  calc
    mixedMoment B raw26075 raw26075Labels = mixedMoment B raw26075step0 raw26075step0Labels := by
      have ha : raw26075step0 = (fun i j => raw26075 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26075step0 raw26075; decide +kernel
      have hl : raw26075step0Labels = raw26075Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26075 raw26075Labels permutation154 permutation2
    _ = mixedMoment B node2001 node2001Labels := by rfl

def raw26076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 2, -3], ![1, 0, -1], ![2, -2, 0]]
def raw26076Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![1, 0, -1], ![2, -2, 0]]
def raw26076step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26076step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw26076step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26076 raw26076Labels = mixedMoment B node1948 node1948Labels := by
  calc
    mixedMoment B raw26076 raw26076Labels = mixedMoment B raw26076step0 raw26076step0Labels := by
      have hz : ∀ j, raw26076 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26076step0 = (fun i j => raw26076 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26076step0 raw26076; decide +kernel
      have hl : raw26076step0Labels = raw26076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26076 raw26076Labels permutation265 hz
    mixedMoment B raw26076step0 raw26076step0Labels = mixedMoment B raw26076step1 raw26076step1Labels := by
      have ha : raw26076step1 = (fun i j => raw26076step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26076step1 raw26076step0; decide +kernel
      have hl : raw26076step1Labels = raw26076step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26076step0 raw26076step0Labels permutation34 permutation2
    _ = mixedMoment B node1948 node1948Labels := by rfl

def raw26077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw26077Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw26077step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26077 raw26077Labels = mixedMoment B node2221 node2221Labels := by
  calc
    mixedMoment B raw26077 raw26077Labels = mixedMoment B raw26077step0 raw26077step0Labels := by
      have hz : ∀ j, raw26077 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26077step0 = (fun i j => raw26077 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26077step0 raw26077; decide +kernel
      have hl : raw26077step0Labels = raw26077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26077 raw26077Labels permutation265 hz
    _ = mixedMoment B node2221 node2221Labels := by rfl

def raw26078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![0, 1, -1], ![2, -2, 0]]
def raw26078Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![0, 1, -1], ![2, -2, 0]]
def raw26078step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw26078step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26078 raw26078Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw26078 raw26078Labels = mixedMoment B raw26078step0 raw26078step0Labels := by
      have hz : ∀ j, raw26078 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26078step0 = (fun i j => raw26078 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26078step0 raw26078; decide +kernel
      have hl : raw26078step0Labels = raw26078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26078 raw26078Labels permutation265 hz
    mixedMoment B raw26078step0 raw26078step0Labels = mixedMoment B raw26078step1 raw26078step1Labels := by
      have ha : raw26078step1 = (fun i j => raw26078step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26078step1 raw26078step0; decide +kernel
      have hl : raw26078step1Labels = raw26078step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26078step0 raw26078step0Labels permutation34 permutation2
    _ = mixedMoment B node2207 node2207Labels := by rfl

def raw26079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw26079Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw26079step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26079step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw26079step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26079 raw26079Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw26079 raw26079Labels = mixedMoment B raw26079step0 raw26079step0Labels := by
      have hz : ∀ j, raw26079 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26079step0 = (fun i j => raw26079 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26079step0 raw26079; decide +kernel
      have hl : raw26079step0Labels = raw26079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26079 raw26079Labels permutation265 hz
    mixedMoment B raw26079step0 raw26079step0Labels = mixedMoment B raw26079step1 raw26079step1Labels := by
      have ha : raw26079step1 = (fun i j => raw26079step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26079step1 raw26079step0; decide +kernel
      have hl : raw26079step1Labels = raw26079step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26079step0 raw26079step0Labels permutation37 permutation2
    _ = mixedMoment B node2224 node2224Labels := by rfl

def raw26080 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![3, -3], ![1, -1], ![0, 0]]
def raw26080Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26080step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![3, -3], ![1, -1]]
def raw26080step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26080step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![3, -3], ![1, -1]]
def raw26080step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26080step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw26080step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26080 raw26080Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw26080 raw26080Labels = mixedMoment B raw26080step0 raw26080step0Labels := by
      have hz : ∀ j, raw26080 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26080step0 = (fun i j => raw26080 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26080step0 raw26080; decide +kernel
      have hl : raw26080step0Labels = raw26080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26080 raw26080Labels permutation590 hz
    mixedMoment B raw26080step0 raw26080step0Labels = mixedMoment B raw26080step1 raw26080step1Labels := by
      have hz : ∀ j, raw26080step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26080step1 = (fun i j => raw26080step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26080step1 raw26080step0; decide +kernel
      have hl : raw26080step1Labels = raw26080step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26080step0 raw26080step0Labels permutation56 hz
    mixedMoment B raw26080step1 raw26080step1Labels = mixedMoment B raw26080step2 raw26080step2Labels := by
      have ha : raw26080step2 = (fun i j => raw26080step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw26080step2 raw26080step1; decide +kernel
      have hl : raw26080step2Labels = raw26080step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26080step1 raw26080step1Labels permutation9 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

def raw26081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw26081Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw26081step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26081 raw26081Labels = mixedMoment B node995 node995Labels := by
  calc
    mixedMoment B raw26081 raw26081Labels = mixedMoment B raw26081step0 raw26081step0Labels := by
      have ha : raw26081step0 = (fun i j => raw26081 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26081step0 raw26081; decide +kernel
      have hl : raw26081step0Labels = raw26081Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26081 raw26081Labels permutation181 permutation2
    _ = mixedMoment B node995 node995Labels := by rfl

def raw26082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw26082Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw26082step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw26082step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26082 raw26082Labels = mixedMoment B node1070 node1070Labels := by
  calc
    mixedMoment B raw26082 raw26082Labels = mixedMoment B raw26082step0 raw26082step0Labels := by
      have hz : ∀ j, raw26082 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26082step0 = (fun i j => raw26082 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26082step0 raw26082; decide +kernel
      have hl : raw26082step0Labels = raw26082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26082 raw26082Labels permutation265 hz
    mixedMoment B raw26082step0 raw26082step0Labels = mixedMoment B raw26082step1 raw26082step1Labels := by
      have ha : raw26082step1 = (fun i j => raw26082step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26082step1 raw26082step0; decide +kernel
      have hl : raw26082step1Labels = raw26082step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26082step0 raw26082step0Labels permutation37 permutation2
    _ = mixedMoment B node1070 node1070Labels := by rfl

def raw26083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3], ![1, 0, -1], ![1, -1, 0]]
def raw26083Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 1, -3], ![1, 0, -1], ![1, -1, 0]]
def raw26083step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26083step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26083step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26083 raw26083Labels = mixedMoment B node999 node999Labels := by
  calc
    mixedMoment B raw26083 raw26083Labels = mixedMoment B raw26083step0 raw26083step0Labels := by
      have hz : ∀ j, raw26083 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26083step0 = (fun i j => raw26083 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26083step0 raw26083; decide +kernel
      have hl : raw26083step0Labels = raw26083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26083 raw26083Labels permutation265 hz
    mixedMoment B raw26083step0 raw26083step0Labels = mixedMoment B raw26083step1 raw26083step1Labels := by
      have ha : raw26083step1 = (fun i j => raw26083step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26083step1 raw26083step0; decide +kernel
      have hl : raw26083step1Labels = raw26083step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26083step0 raw26083step0Labels permutation37 permutation2
    _ = mixedMoment B node999 node999Labels := by rfl

def raw26084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1], ![1, -1, 0]]
def raw26084Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1], ![1, -1, 0]]
def raw26084step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26084step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw26084step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26084 raw26084Labels = mixedMoment B node1001 node1001Labels := by
  calc
    mixedMoment B raw26084 raw26084Labels = mixedMoment B raw26084step0 raw26084step0Labels := by
      have hz : ∀ j, raw26084 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26084step0 = (fun i j => raw26084 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26084step0 raw26084; decide +kernel
      have hl : raw26084step0Labels = raw26084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26084 raw26084Labels permutation265 hz
    mixedMoment B raw26084step0 raw26084step0Labels = mixedMoment B raw26084step1 raw26084step1Labels := by
      have ha : raw26084step1 = (fun i j => raw26084step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26084step1 raw26084step0; decide +kernel
      have hl : raw26084step1Labels = raw26084step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26084step0 raw26084step0Labels permutation36 permutation2
    _ = mixedMoment B node1001 node1001Labels := by rfl

def raw26085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![2, -1, -1]]
def raw26085Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![2, -1, -1]]
def raw26085step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26085step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw26085step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26085 raw26085Labels = mixedMoment B node1001 node1001Labels := by
  calc
    mixedMoment B raw26085 raw26085Labels = mixedMoment B raw26085step0 raw26085step0Labels := by
      have hz : ∀ j, raw26085 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26085step0 = (fun i j => raw26085 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26085step0 raw26085; decide +kernel
      have hl : raw26085step0Labels = raw26085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26085 raw26085Labels permutation265 hz
    mixedMoment B raw26085step0 raw26085step0Labels = mixedMoment B raw26085step1 raw26085step1Labels := by
      have ha : raw26085step1 = (fun i j => raw26085step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26085step1 raw26085step0; decide +kernel
      have hl : raw26085step1Labels = raw26085step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26085step0 raw26085step0Labels permutation34 permutation2
    _ = mixedMoment B node1001 node1001Labels := by rfl

def raw26086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![2, -1, -1]]
def raw26086Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw26086step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26086 raw26086Labels = mixedMoment B node1998 node1998Labels := by
  calc
    mixedMoment B raw26086 raw26086Labels = mixedMoment B raw26086step0 raw26086step0Labels := by
      have ha : raw26086step0 = (fun i j => raw26086 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26086step0 raw26086; decide +kernel
      have hl : raw26086step0Labels = raw26086Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26086 raw26086Labels permutation154 permutation2
    _ = mixedMoment B node1998 node1998Labels := by rfl

def raw26087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 2, -3], ![1, -1, 0], ![2, -1, -1]]
def raw26087Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![1, -1, 0], ![2, -1, -1]]
def raw26087step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw26087step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26087 raw26087Labels = mixedMoment B node1946 node1946Labels := by
  calc
    mixedMoment B raw26087 raw26087Labels = mixedMoment B raw26087step0 raw26087step0Labels := by
      have hz : ∀ j, raw26087 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26087step0 = (fun i j => raw26087 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26087step0 raw26087; decide +kernel
      have hl : raw26087step0Labels = raw26087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26087 raw26087Labels permutation265 hz
    mixedMoment B raw26087step0 raw26087step0Labels = mixedMoment B raw26087step1 raw26087step1Labels := by
      have ha : raw26087step1 = (fun i j => raw26087step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26087step1 raw26087step0; decide +kernel
      have hl : raw26087step1Labels = raw26087step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26087step0 raw26087step0Labels permutation34 permutation2
    _ = mixedMoment B node1946 node1946Labels := by rfl

def raw26088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw26088Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw26088step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26088 raw26088Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw26088 raw26088Labels = mixedMoment B raw26088step0 raw26088step0Labels := by
      have hz : ∀ j, raw26088 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26088step0 = (fun i j => raw26088 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26088step0 raw26088; decide +kernel
      have hl : raw26088step0Labels = raw26088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26088 raw26088Labels permutation265 hz
    _ = mixedMoment B node2220 node2220Labels := by rfl

def raw26089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![0, 0, 0], ![2, -1, -1]]
def raw26089Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw26089step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw26089step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26089 raw26089Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw26089 raw26089Labels = mixedMoment B raw26089step0 raw26089step0Labels := by
      have hz : ∀ j, raw26089 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26089step0 = (fun i j => raw26089 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26089step0 raw26089; decide +kernel
      have hl : raw26089step0Labels = raw26089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26089 raw26089Labels permutation520 hz
    mixedMoment B raw26089step0 raw26089step0Labels = mixedMoment B raw26089step1 raw26089step1Labels := by
      have hz : ∀ j, raw26089step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26089step1 = (fun i j => raw26089step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26089step1 raw26089step0; decide +kernel
      have hl : raw26089step1Labels = raw26089step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26089step0 raw26089step0Labels permutation56 hz
    _ = mixedMoment B node2230 node2230Labels := by rfl

def raw26090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, 0, -1]]
def raw26090Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, 0, -1]]
def raw26090step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw26090step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26090 raw26090Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw26090 raw26090Labels = mixedMoment B raw26090step0 raw26090step0Labels := by
      have hz : ∀ j, raw26090 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26090step0 = (fun i j => raw26090 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26090step0 raw26090; decide +kernel
      have hl : raw26090step0Labels = raw26090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26090 raw26090Labels permutation265 hz
    mixedMoment B raw26090step0 raw26090step0Labels = mixedMoment B raw26090step1 raw26090step1Labels := by
      have ha : raw26090step1 = (fun i j => raw26090step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26090step1 raw26090step0; decide +kernel
      have hl : raw26090step1Labels = raw26090step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26090step0 raw26090step0Labels permutation35 permutation2
    _ = mixedMoment B node2224 node2224Labels := by rfl

def raw26091 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![3, -3], ![0, 0], ![1, -1]]
def raw26091Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26091step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![3, -3], ![1, -1]]
def raw26091step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26091step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![3, -3], ![1, -1]]
def raw26091step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26091step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw26091step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26091 raw26091Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw26091 raw26091Labels = mixedMoment B raw26091step0 raw26091step0Labels := by
      have hz : ∀ j, raw26091 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26091step0 = (fun i j => raw26091 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26091step0 raw26091; decide +kernel
      have hl : raw26091step0Labels = raw26091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26091 raw26091Labels permutation520 hz
    mixedMoment B raw26091step0 raw26091step0Labels = mixedMoment B raw26091step1 raw26091step1Labels := by
      have hz : ∀ j, raw26091step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26091step1 = (fun i j => raw26091step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26091step1 raw26091step0; decide +kernel
      have hl : raw26091step1Labels = raw26091step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26091step0 raw26091step0Labels permutation56 hz
    mixedMoment B raw26091step1 raw26091step1Labels = mixedMoment B raw26091step2 raw26091step2Labels := by
      have ha : raw26091step2 = (fun i j => raw26091step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw26091step2 raw26091step1; decide +kernel
      have hl : raw26091step2Labels = raw26091step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26091step1 raw26091step1Labels permutation9 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

def raw26092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw26092Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw26092step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26092 raw26092Labels = mixedMoment B node1008 node1008Labels := by
  calc
    mixedMoment B raw26092 raw26092Labels = mixedMoment B raw26092step0 raw26092step0Labels := by
      have hz : ∀ j, raw26092 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26092step0 = (fun i j => raw26092 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26092step0 raw26092; decide +kernel
      have hl : raw26092step0Labels = raw26092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26092 raw26092Labels permutation265 hz
    _ = mixedMoment B node1008 node1008Labels := by rfl

def raw26093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw26093Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26093 raw26093Labels = mixedMoment B node2002 node2002Labels := by
  calc
    _ = mixedMoment B node2002 node2002Labels := by rfl

def raw26094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw26094Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw26094step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26094 raw26094Labels = mixedMoment B node1949 node1949Labels := by
  calc
    mixedMoment B raw26094 raw26094Labels = mixedMoment B raw26094step0 raw26094step0Labels := by
      have hz : ∀ j, raw26094 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26094step0 = (fun i j => raw26094 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26094step0 raw26094; decide +kernel
      have hl : raw26094step0Labels = raw26094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26094 raw26094Labels permutation265 hz
    _ = mixedMoment B node1949 node1949Labels := by rfl

def raw26095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw26095Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw26095step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26095 raw26095Labels = mixedMoment B node2217 node2217Labels := by
  calc
    mixedMoment B raw26095 raw26095Labels = mixedMoment B raw26095step0 raw26095step0Labels := by
      have hz : ∀ j, raw26095 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26095step0 = (fun i j => raw26095 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26095step0 raw26095; decide +kernel
      have hl : raw26095step0Labels = raw26095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26095 raw26095Labels permutation265 hz
    _ = mixedMoment B node2217 node2217Labels := by rfl

def raw26096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![0, 2, -2], ![2, -2, 0]]
def raw26096Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![0, 2, -2], ![2, -2, 0]]
def raw26096step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw26096step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26096 raw26096Labels = mixedMoment B node2217 node2217Labels := by
  calc
    mixedMoment B raw26096 raw26096Labels = mixedMoment B raw26096step0 raw26096step0Labels := by
      have hz : ∀ j, raw26096 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26096step0 = (fun i j => raw26096 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26096step0 raw26096; decide +kernel
      have hl : raw26096step0Labels = raw26096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26096 raw26096Labels permutation265 hz
    mixedMoment B raw26096step0 raw26096step0Labels = mixedMoment B raw26096step1 raw26096step1Labels := by
      have ha : raw26096step1 = (fun i j => raw26096step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26096step1 raw26096step0; decide +kernel
      have hl : raw26096step1Labels = raw26096step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26096step0 raw26096step0Labels permutation34 permutation2
    _ = mixedMoment B node2217 node2217Labels := by rfl

def raw26097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw26097Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw26097step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26097step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw26097step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26097 raw26097Labels = mixedMoment B node2225 node2225Labels := by
  calc
    mixedMoment B raw26097 raw26097Labels = mixedMoment B raw26097step0 raw26097step0Labels := by
      have hz : ∀ j, raw26097 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26097step0 = (fun i j => raw26097 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26097step0 raw26097; decide +kernel
      have hl : raw26097step0Labels = raw26097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26097 raw26097Labels permutation265 hz
    mixedMoment B raw26097step0 raw26097step0Labels = mixedMoment B raw26097step1 raw26097step1Labels := by
      have ha : raw26097step1 = (fun i j => raw26097step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26097step1 raw26097step0; decide +kernel
      have hl : raw26097step1Labels = raw26097step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26097step0 raw26097step0Labels permutation36 permutation2
    _ = mixedMoment B node2225 node2225Labels := by rfl

def raw26098 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![2, -2], ![2, -2], ![0, 0]]
def raw26098Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26098step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![2, -2], ![2, -2]]
def raw26098step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26098step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw26098step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26098 raw26098Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw26098 raw26098Labels = mixedMoment B raw26098step0 raw26098step0Labels := by
      have hz : ∀ j, raw26098 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26098step0 = (fun i j => raw26098 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26098step0 raw26098; decide +kernel
      have hl : raw26098step0Labels = raw26098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26098 raw26098Labels permutation590 hz
    mixedMoment B raw26098step0 raw26098step0Labels = mixedMoment B raw26098step1 raw26098step1Labels := by
      have hz : ∀ j, raw26098step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26098step1 = (fun i j => raw26098step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26098step1 raw26098step0; decide +kernel
      have hl : raw26098step1Labels = raw26098step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26098step0 raw26098step0Labels permutation56 hz
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw26099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw26099Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26099step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw26099step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26099 raw26099Labels = mixedMoment B node996 node996Labels := by
  calc
    mixedMoment B raw26099 raw26099Labels = mixedMoment B raw26099step0 raw26099step0Labels := by
      have ha : raw26099step0 = (fun i j => raw26099 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26099step0 raw26099; decide +kernel
      have hl : raw26099step0Labels = raw26099Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26099 raw26099Labels permutation180 permutation2
    _ = mixedMoment B node996 node996Labels := by rfl

def raw26100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw26100Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw26100step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw26100step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26100 raw26100Labels = mixedMoment B node1071 node1071Labels := by
  calc
    mixedMoment B raw26100 raw26100Labels = mixedMoment B raw26100step0 raw26100step0Labels := by
      have hz : ∀ j, raw26100 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26100step0 = (fun i j => raw26100 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26100step0 raw26100; decide +kernel
      have hl : raw26100step0Labels = raw26100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26100 raw26100Labels permutation265 hz
    mixedMoment B raw26100step0 raw26100step0Labels = mixedMoment B raw26100step1 raw26100step1Labels := by
      have ha : raw26100step1 = (fun i j => raw26100step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26100step1 raw26100step0; decide +kernel
      have hl : raw26100step1Labels = raw26100step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26100step0 raw26100step0Labels permutation36 permutation2
    _ = mixedMoment B node1071 node1071Labels := by rfl

def raw26101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2], ![1, -1, 0]]
def raw26101Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2], ![1, -1, 0]]
def raw26101step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw26101step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26101 raw26101Labels = mixedMoment B node1000 node1000Labels := by
  calc
    mixedMoment B raw26101 raw26101Labels = mixedMoment B raw26101step0 raw26101step0Labels := by
      have hz : ∀ j, raw26101 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26101step0 = (fun i j => raw26101 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26101step0 raw26101; decide +kernel
      have hl : raw26101step0Labels = raw26101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26101 raw26101Labels permutation265 hz
    mixedMoment B raw26101step0 raw26101step0Labels = mixedMoment B raw26101step1 raw26101step1Labels := by
      have ha : raw26101step1 = (fun i j => raw26101step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26101step1 raw26101step0; decide +kernel
      have hl : raw26101step1Labels = raw26101step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26101step0 raw26101step0Labels permutation37 permutation2
    _ = mixedMoment B node1000 node1000Labels := by rfl

def raw26102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2], ![1, -1, 0]]
def raw26102Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2], ![1, -1, 0]]
def raw26102step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw26102step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26102 raw26102Labels = mixedMoment B node1000 node1000Labels := by
  calc
    mixedMoment B raw26102 raw26102Labels = mixedMoment B raw26102step0 raw26102step0Labels := by
      have hz : ∀ j, raw26102 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26102step0 = (fun i j => raw26102 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26102step0 raw26102; decide +kernel
      have hl : raw26102step0Labels = raw26102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26102 raw26102Labels permutation265 hz
    mixedMoment B raw26102step0 raw26102step0Labels = mixedMoment B raw26102step1 raw26102step1Labels := by
      have ha : raw26102step1 = (fun i j => raw26102step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26102step1 raw26102step0; decide +kernel
      have hl : raw26102step1Labels = raw26102step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26102step0 raw26102step0Labels permutation36 permutation2
    _ = mixedMoment B node1000 node1000Labels := by rfl

def raw26103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26103Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26103step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26103step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26103 raw26103Labels = mixedMoment B node1005 node1005Labels := by
  calc
    mixedMoment B raw26103 raw26103Labels = mixedMoment B raw26103step0 raw26103step0Labels := by
      have hz : ∀ j, raw26103 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26103step0 = (fun i j => raw26103 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26103step0 raw26103; decide +kernel
      have hl : raw26103step0Labels = raw26103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26103 raw26103Labels permutation265 hz
    mixedMoment B raw26103step0 raw26103step0Labels = mixedMoment B raw26103step1 raw26103step1Labels := by
      have ha : raw26103step1 = (fun i j => raw26103step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26103step1 raw26103step0; decide +kernel
      have hl : raw26103step1Labels = raw26103step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26103step0 raw26103step0Labels permutation34 permutation2
    _ = mixedMoment B node1005 node1005Labels := by rfl

def raw26104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26104Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26104step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26104step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26104 raw26104Labels = mixedMoment B node2000 node2000Labels := by
  calc
    mixedMoment B raw26104 raw26104Labels = mixedMoment B raw26104step0 raw26104step0Labels := by
      have ha : raw26104step0 = (fun i j => raw26104 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26104step0 raw26104; decide +kernel
      have hl : raw26104step0Labels = raw26104Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26104 raw26104Labels permutation154 permutation2
    _ = mixedMoment B node2000 node2000Labels := by rfl

def raw26105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26105Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26105step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26105step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26105 raw26105Labels = mixedMoment B node1947 node1947Labels := by
  calc
    mixedMoment B raw26105 raw26105Labels = mixedMoment B raw26105step0 raw26105step0Labels := by
      have hz : ∀ j, raw26105 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26105step0 = (fun i j => raw26105 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26105step0 raw26105; decide +kernel
      have hl : raw26105step0Labels = raw26105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26105 raw26105Labels permutation265 hz
    mixedMoment B raw26105step0 raw26105step0Labels = mixedMoment B raw26105step1 raw26105step1Labels := by
      have ha : raw26105step1 = (fun i j => raw26105step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26105step1 raw26105step0; decide +kernel
      have hl : raw26105step1Labels = raw26105step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26105step0 raw26105step0Labels permutation34 permutation2
    _ = mixedMoment B node1947 node1947Labels := by rfl

def raw26106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26106Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26106step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26106 raw26106Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw26106 raw26106Labels = mixedMoment B raw26106step0 raw26106step0Labels := by
      have hz : ∀ j, raw26106 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26106step0 = (fun i j => raw26106 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26106step0 raw26106; decide +kernel
      have hl : raw26106step0Labels = raw26106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26106 raw26106Labels permutation265 hz
    _ = mixedMoment B node2216 node2216Labels := by rfl

def raw26107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -1, -1]]
def raw26107Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -1, -1]]
def raw26107step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26107step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26107 raw26107Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw26107 raw26107Labels = mixedMoment B raw26107step0 raw26107step0Labels := by
      have hz : ∀ j, raw26107 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26107step0 = (fun i j => raw26107 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26107step0 raw26107; decide +kernel
      have hl : raw26107step0Labels = raw26107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26107 raw26107Labels permutation265 hz
    mixedMoment B raw26107step0 raw26107step0Labels = mixedMoment B raw26107step1 raw26107step1Labels := by
      have ha : raw26107step1 = (fun i j => raw26107step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26107step1 raw26107step0; decide +kernel
      have hl : raw26107step1Labels = raw26107step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26107step0 raw26107step0Labels permutation34 permutation2
    _ = mixedMoment B node2206 node2206Labels := by rfl

def raw26108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw26108Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw26108step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26108step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26108 raw26108Labels = mixedMoment B node2227 node2227Labels := by
  calc
    mixedMoment B raw26108 raw26108Labels = mixedMoment B raw26108step0 raw26108step0Labels := by
      have hz : ∀ j, raw26108 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26108step0 = (fun i j => raw26108 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26108step0 raw26108; decide +kernel
      have hl : raw26108step0Labels = raw26108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26108 raw26108Labels permutation265 hz
    mixedMoment B raw26108step0 raw26108step0Labels = mixedMoment B raw26108step1 raw26108step1Labels := by
      have ha : raw26108step1 = (fun i j => raw26108step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26108step1 raw26108step0; decide +kernel
      have hl : raw26108step1Labels = raw26108step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26108step0 raw26108step0Labels permutation35 permutation2
    _ = mixedMoment B node2227 node2227Labels := by rfl

def raw26109 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![2, -2], ![1, -1], ![1, -1]]
def raw26109Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26109step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![1, -1], ![1, -1]]
def raw26109step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26109step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw26109step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26109 raw26109Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw26109 raw26109Labels = mixedMoment B raw26109step0 raw26109step0Labels := by
      have hz : ∀ j, raw26109 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26109step0 = (fun i j => raw26109 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26109step0 raw26109; decide +kernel
      have hl : raw26109step0Labels = raw26109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26109 raw26109Labels permutation265 hz
    mixedMoment B raw26109step0 raw26109step0Labels = mixedMoment B raw26109step1 raw26109step1Labels := by
      have ha : raw26109step1 = (fun i j => raw26109step0 (permutation35 i) (permutation0 j)) := by apply Matrix.ext; unfold raw26109step1 raw26109step0; decide +kernel
      have hl : raw26109step1Labels = raw26109step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26109step0 raw26109step0Labels permutation35 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw26110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26110Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26110step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26110step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26110 raw26110Labels = mixedMoment B node879 node879Labels := by
  calc
    mixedMoment B raw26110 raw26110Labels = mixedMoment B raw26110step0 raw26110step0Labels := by
      have ha : raw26110step0 = (fun i j => raw26110 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26110step0 raw26110; decide +kernel
      have hl : raw26110step0Labels = raw26110Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26110 raw26110Labels permutation178 permutation2
    _ = mixedMoment B node879 node879Labels := by rfl

def raw26111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26111Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26111step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26111step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw26111step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26111 raw26111Labels = mixedMoment B node889 node889Labels := by
  calc
    mixedMoment B raw26111 raw26111Labels = mixedMoment B raw26111step0 raw26111step0Labels := by
      have hz : ∀ j, raw26111 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26111step0 = (fun i j => raw26111 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26111step0 raw26111; decide +kernel
      have hl : raw26111step0Labels = raw26111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26111 raw26111Labels permutation265 hz
    mixedMoment B raw26111step0 raw26111step0Labels = mixedMoment B raw26111step1 raw26111step1Labels := by
      have ha : raw26111step1 = (fun i j => raw26111step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26111step1 raw26111step0; decide +kernel
      have hl : raw26111step1Labels = raw26111step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26111step0 raw26111step0Labels permutation35 permutation2
    _ = mixedMoment B node889 node889Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
