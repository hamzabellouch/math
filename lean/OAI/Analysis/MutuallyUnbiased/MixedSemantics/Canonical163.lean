import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw20864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20864step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20864step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20864step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20864step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw20864step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20864step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw20864step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20864 raw20864Labels = mixedMoment B node4356 node4356Labels := by
  calc
    mixedMoment B raw20864 raw20864Labels = mixedMoment B raw20864step0 raw20864step0Labels := by
      have hz : ∀ j, raw20864 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20864step0 = (fun i j => raw20864 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20864step0 raw20864; decide +kernel
      have hl : raw20864step0Labels = raw20864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20864 raw20864Labels permutation346 hz
    mixedMoment B raw20864step0 raw20864step0Labels = mixedMoment B raw20864step1 raw20864step1Labels := by
      have hz : ∀ j, raw20864step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20864step1 = (fun i j => raw20864step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20864step1 raw20864step0; decide +kernel
      have hl : raw20864step1Labels = raw20864step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20864step0 raw20864step0Labels permutation56 hz
    mixedMoment B raw20864step1 raw20864step1Labels = mixedMoment B raw20864step2 raw20864step2Labels := by
      have ha : raw20864step2 = (fun i j => raw20864step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20864step2 raw20864step1; decide +kernel
      have hl : raw20864step2Labels = raw20864step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20864step1 raw20864step1Labels permutation31 permutation2
    mixedMoment B raw20864step2 raw20864step2Labels = mixedMoment B raw20864step3 raw20864step3Labels := by
      have ha : raw20864step3 = -raw20864step2 := by apply Matrix.ext; change ∀ i j, raw20864step3 i j = -(raw20864step2 i j); unfold raw20864step3 raw20864step2; decide +kernel
      have hl : raw20864step3Labels = raw20864step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4356 node4356Labels := by rfl

def raw20865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![4, -1, -3]]
def raw20865Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw20865step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20865step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw20865step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20865step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![4, -1, -3]]
def raw20865step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20865step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw20865step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20865step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw20865step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20865 raw20865Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw20865 raw20865Labels = mixedMoment B raw20865step0 raw20865step0Labels := by
      have hz : ∀ j, raw20865 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20865step0 = (fun i j => raw20865 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20865step0 raw20865; decide +kernel
      have hl : raw20865step0Labels = raw20865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20865 raw20865Labels permutation520 hz
    mixedMoment B raw20865step0 raw20865step0Labels = mixedMoment B raw20865step1 raw20865step1Labels := by
      have hz : ∀ j, raw20865step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20865step1 = (fun i j => raw20865step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20865step1 raw20865step0; decide +kernel
      have hl : raw20865step1Labels = raw20865step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20865step0 raw20865step0Labels permutation80 hz
    mixedMoment B raw20865step1 raw20865step1Labels = mixedMoment B raw20865step2 raw20865step2Labels := by
      have hz : ∀ j, raw20865step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20865step2 = (fun i j => raw20865step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20865step2 raw20865step1; decide +kernel
      have hl : raw20865step2Labels = raw20865step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20865step1 raw20865step1Labels permutation14 hz
    mixedMoment B raw20865step2 raw20865step2Labels = mixedMoment B raw20865step3 raw20865step3Labels := by
      have ha : raw20865step3 = (fun i j => raw20865step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20865step3 raw20865step2; decide +kernel
      have hl : raw20865step3Labels = raw20865step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20865step2 raw20865step2Labels permutation7 permutation2
    mixedMoment B raw20865step3 raw20865step3Labels = mixedMoment B raw20865step4 raw20865step4Labels := by
      have ha : raw20865step4 = -raw20865step3 := by apply Matrix.ext; change ∀ i j, raw20865step4 i j = -(raw20865step3 i j); unfold raw20865step4 raw20865step3; decide +kernel
      have hl : raw20865step4Labels = raw20865step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4468 node4468Labels := by rfl

def raw20866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20866Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20866step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20866step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20866step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20866step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw20866step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20866 raw20866Labels = mixedMoment B node3113 node3113Labels := by
  calc
    mixedMoment B raw20866 raw20866Labels = mixedMoment B raw20866step0 raw20866step0Labels := by
      have hz : ∀ j, raw20866 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20866step0 = (fun i j => raw20866 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20866step0 raw20866; decide +kernel
      have hl : raw20866step0Labels = raw20866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20866 raw20866Labels permutation346 hz
    mixedMoment B raw20866step0 raw20866step0Labels = mixedMoment B raw20866step1 raw20866step1Labels := by
      have hz : ∀ j, raw20866step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20866step1 = (fun i j => raw20866step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20866step1 raw20866step0; decide +kernel
      have hl : raw20866step1Labels = raw20866step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20866step0 raw20866step0Labels permutation56 hz
    mixedMoment B raw20866step1 raw20866step1Labels = mixedMoment B raw20866step2 raw20866step2Labels := by
      have ha : raw20866step2 = (fun i j => raw20866step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20866step2 raw20866step1; decide +kernel
      have hl : raw20866step2Labels = raw20866step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20866step1 raw20866step1Labels permutation8 permutation3
    _ = mixedMoment B node3113 node3113Labels := by rfl

def raw20867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20867Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20867step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20867step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20867 raw20867Labels = mixedMoment B node585 node585Labels := by
  calc
    mixedMoment B raw20867 raw20867Labels = mixedMoment B raw20867step0 raw20867step0Labels := by
      have hz : ∀ j, raw20867 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20867step0 = (fun i j => raw20867 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20867step0 raw20867; decide +kernel
      have hl : raw20867step0Labels = raw20867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20867 raw20867Labels permutation346 hz
    mixedMoment B raw20867step0 raw20867step0Labels = mixedMoment B raw20867step1 raw20867step1Labels := by
      have ha : raw20867step1 = (fun i j => raw20867step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20867step1 raw20867step0; decide +kernel
      have hl : raw20867step1Labels = raw20867step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20867step0 raw20867step0Labels permutation38 permutation3
    _ = mixedMoment B node585 node585Labels := by rfl

def raw20868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20868Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20868step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20868 raw20868Labels = mixedMoment B node1116 node1116Labels := by
  calc
    mixedMoment B raw20868 raw20868Labels = mixedMoment B raw20868step0 raw20868step0Labels := by
      have ha : raw20868step0 = (fun i j => raw20868 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20868step0 raw20868; decide +kernel
      have hl : raw20868step0Labels = raw20868Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20868 raw20868Labels permutation182 permutation3
    _ = mixedMoment B node1116 node1116Labels := by rfl

def raw20869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20869Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20869step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20869step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20869 raw20869Labels = mixedMoment B node1170 node1170Labels := by
  calc
    mixedMoment B raw20869 raw20869Labels = mixedMoment B raw20869step0 raw20869step0Labels := by
      have hz : ∀ j, raw20869 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20869step0 = (fun i j => raw20869 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20869step0 raw20869; decide +kernel
      have hl : raw20869step0Labels = raw20869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20869 raw20869Labels permutation346 hz
    mixedMoment B raw20869step0 raw20869step0Labels = mixedMoment B raw20869step1 raw20869step1Labels := by
      have ha : raw20869step1 = (fun i j => raw20869step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20869step1 raw20869step0; decide +kernel
      have hl : raw20869step1Labels = raw20869step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20869step0 raw20869step0Labels permutation38 permutation3
    _ = mixedMoment B node1170 node1170Labels := by rfl

def raw20870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw20870Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20870step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20870step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20870step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20870step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20870step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20870 raw20870Labels = mixedMoment B node1271 node1271Labels := by
  calc
    mixedMoment B raw20870 raw20870Labels = mixedMoment B raw20870step0 raw20870step0Labels := by
      have hz : ∀ j, raw20870 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20870step0 = (fun i j => raw20870 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20870step0 raw20870; decide +kernel
      have hl : raw20870step0Labels = raw20870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20870 raw20870Labels permutation520 hz
    mixedMoment B raw20870step0 raw20870step0Labels = mixedMoment B raw20870step1 raw20870step1Labels := by
      have hz : ∀ j, raw20870step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20870step1 = (fun i j => raw20870step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20870step1 raw20870step0; decide +kernel
      have hl : raw20870step1Labels = raw20870step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20870step0 raw20870step0Labels permutation80 hz
    mixedMoment B raw20870step1 raw20870step1Labels = mixedMoment B raw20870step2 raw20870step2Labels := by
      have ha : raw20870step2 = (fun i j => raw20870step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20870step2 raw20870step1; decide +kernel
      have hl : raw20870step2Labels = raw20870step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20870step1 raw20870step1Labels permutation10 permutation3
    _ = mixedMoment B node1271 node1271Labels := by rfl

def raw20871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20871Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20871step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20871step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20871step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20871 raw20871Labels = mixedMoment B node585 node585Labels := by
  calc
    mixedMoment B raw20871 raw20871Labels = mixedMoment B raw20871step0 raw20871step0Labels := by
      have hz : ∀ j, raw20871 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20871step0 = (fun i j => raw20871 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20871step0 raw20871; decide +kernel
      have hl : raw20871step0Labels = raw20871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20871 raw20871Labels permutation265 hz
    mixedMoment B raw20871step0 raw20871step0Labels = mixedMoment B raw20871step1 raw20871step1Labels := by
      have ha : raw20871step1 = (fun i j => raw20871step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20871step1 raw20871step0; decide +kernel
      have hl : raw20871step1Labels = raw20871step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20871step0 raw20871step0Labels permutation38 permutation3
    _ = mixedMoment B node585 node585Labels := by rfl

def raw20872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20872Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20872 raw20872Labels = mixedMoment B node1116 node1116Labels := by
  calc
    mixedMoment B raw20872 raw20872Labels = mixedMoment B raw20872step0 raw20872step0Labels := by
      have ha : raw20872step0 = (fun i j => raw20872 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20872step0 raw20872; decide +kernel
      have hl : raw20872step0Labels = raw20872Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20872 raw20872Labels permutation158 permutation3
    _ = mixedMoment B node1116 node1116Labels := by rfl

def raw20873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20873Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20873step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20873step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20873 raw20873Labels = mixedMoment B node1170 node1170Labels := by
  calc
    mixedMoment B raw20873 raw20873Labels = mixedMoment B raw20873step0 raw20873step0Labels := by
      have hz : ∀ j, raw20873 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20873step0 = (fun i j => raw20873 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20873step0 raw20873; decide +kernel
      have hl : raw20873step0Labels = raw20873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20873 raw20873Labels permutation265 hz
    mixedMoment B raw20873step0 raw20873step0Labels = mixedMoment B raw20873step1 raw20873step1Labels := by
      have ha : raw20873step1 = (fun i j => raw20873step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20873step1 raw20873step0; decide +kernel
      have hl : raw20873step1Labels = raw20873step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20873step0 raw20873step0Labels permutation38 permutation3
    _ = mixedMoment B node1170 node1170Labels := by rfl

def raw20874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw20874Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20874step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20874step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20874step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20874step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20874step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20874 raw20874Labels = mixedMoment B node1271 node1271Labels := by
  calc
    mixedMoment B raw20874 raw20874Labels = mixedMoment B raw20874step0 raw20874step0Labels := by
      have hz : ∀ j, raw20874 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20874step0 = (fun i j => raw20874 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20874step0 raw20874; decide +kernel
      have hl : raw20874step0Labels = raw20874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20874 raw20874Labels permutation520 hz
    mixedMoment B raw20874step0 raw20874step0Labels = mixedMoment B raw20874step1 raw20874step1Labels := by
      have hz : ∀ j, raw20874step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20874step1 = (fun i j => raw20874step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20874step1 raw20874step0; decide +kernel
      have hl : raw20874step1Labels = raw20874step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20874step0 raw20874step0Labels permutation56 hz
    mixedMoment B raw20874step1 raw20874step1Labels = mixedMoment B raw20874step2 raw20874step2Labels := by
      have ha : raw20874step2 = (fun i j => raw20874step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20874step2 raw20874step1; decide +kernel
      have hl : raw20874step2Labels = raw20874step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20874step1 raw20874step1Labels permutation10 permutation3
    _ = mixedMoment B node1271 node1271Labels := by rfl

def raw20875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20875Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20875step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20875step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20875step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20875step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20875step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20875 raw20875Labels = mixedMoment B node612 node612Labels := by
  calc
    mixedMoment B raw20875 raw20875Labels = mixedMoment B raw20875step0 raw20875step0Labels := by
      have hz : ∀ j, raw20875 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20875step0 = (fun i j => raw20875 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20875step0 raw20875; decide +kernel
      have hl : raw20875step0Labels = raw20875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20875 raw20875Labels permutation346 hz
    mixedMoment B raw20875step0 raw20875step0Labels = mixedMoment B raw20875step1 raw20875step1Labels := by
      have hz : ∀ j, raw20875step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20875step1 = (fun i j => raw20875step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20875step1 raw20875step0; decide +kernel
      have hl : raw20875step1Labels = raw20875step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20875step0 raw20875step0Labels permutation56 hz
    mixedMoment B raw20875step1 raw20875step1Labels = mixedMoment B raw20875step2 raw20875step2Labels := by
      have ha : raw20875step2 = (fun i j => raw20875step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20875step2 raw20875step1; decide +kernel
      have hl : raw20875step2Labels = raw20875step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20875step1 raw20875step1Labels permutation10 permutation3
    _ = mixedMoment B node612 node612Labels := by rfl

def raw20876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20876Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20876step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20876step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20876step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20876 raw20876Labels = mixedMoment B node1137 node1137Labels := by
  calc
    mixedMoment B raw20876 raw20876Labels = mixedMoment B raw20876step0 raw20876step0Labels := by
      have hz : ∀ j, raw20876 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20876step0 = (fun i j => raw20876 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20876step0 raw20876; decide +kernel
      have hl : raw20876step0Labels = raw20876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20876 raw20876Labels permutation346 hz
    mixedMoment B raw20876step0 raw20876step0Labels = mixedMoment B raw20876step1 raw20876step1Labels := by
      have ha : raw20876step1 = (fun i j => raw20876step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20876step1 raw20876step0; decide +kernel
      have hl : raw20876step1Labels = raw20876step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20876step0 raw20876step0Labels permutation34 permutation3
    _ = mixedMoment B node1137 node1137Labels := by rfl

def raw20877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20877Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20877step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20877step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20877 raw20877Labels = mixedMoment B node1137 node1137Labels := by
  calc
    mixedMoment B raw20877 raw20877Labels = mixedMoment B raw20877step0 raw20877step0Labels := by
      have hz : ∀ j, raw20877 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20877step0 = (fun i j => raw20877 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20877step0 raw20877; decide +kernel
      have hl : raw20877step0Labels = raw20877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20877 raw20877Labels permutation265 hz
    mixedMoment B raw20877step0 raw20877step0Labels = mixedMoment B raw20877step1 raw20877step1Labels := by
      have ha : raw20877step1 = (fun i j => raw20877step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20877step1 raw20877step0; decide +kernel
      have hl : raw20877step1Labels = raw20877step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20877step0 raw20877step0Labels permutation34 permutation3
    _ = mixedMoment B node1137 node1137Labels := by rfl

def raw20878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![3, 0, -3]]
def raw20878Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20878step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20878step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20878step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20878step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw20878step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20878step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![3, -3, 0]]
def raw20878step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20878 raw20878Labels = mixedMoment B node1308 node1308Labels := by
  calc
    mixedMoment B raw20878 raw20878Labels = mixedMoment B raw20878step0 raw20878step0Labels := by
      have hz : ∀ j, raw20878 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20878step0 = (fun i j => raw20878 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20878step0 raw20878; decide +kernel
      have hl : raw20878step0Labels = raw20878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20878 raw20878Labels permutation520 hz
    mixedMoment B raw20878step0 raw20878step0Labels = mixedMoment B raw20878step1 raw20878step1Labels := by
      have hz : ∀ j, raw20878step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20878step1 = (fun i j => raw20878step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20878step1 raw20878step0; decide +kernel
      have hl : raw20878step1Labels = raw20878step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20878step0 raw20878step0Labels permutation80 hz
    mixedMoment B raw20878step1 raw20878step1Labels = mixedMoment B raw20878step2 raw20878step2Labels := by
      have hz : ∀ j, raw20878step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20878step2 = (fun i j => raw20878step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20878step2 raw20878step1; decide +kernel
      have hl : raw20878step2Labels = raw20878step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20878step1 raw20878step1Labels permutation14 hz
    mixedMoment B raw20878step2 raw20878step2Labels = mixedMoment B raw20878step3 raw20878step3Labels := by
      have ha : raw20878step3 = (fun i j => raw20878step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20878step3 raw20878step2; decide +kernel
      have hl : raw20878step3Labels = raw20878step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20878step2 raw20878step2Labels permutation2 permutation3
    _ = mixedMoment B node1308 node1308Labels := by rfl

def raw20879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20879Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20879step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20879step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20879step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20879step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20879step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20879 raw20879Labels = mixedMoment B node590 node590Labels := by
  calc
    mixedMoment B raw20879 raw20879Labels = mixedMoment B raw20879step0 raw20879step0Labels := by
      have hz : ∀ j, raw20879 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20879step0 = (fun i j => raw20879 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20879step0 raw20879; decide +kernel
      have hl : raw20879step0Labels = raw20879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20879 raw20879Labels permutation346 hz
    mixedMoment B raw20879step0 raw20879step0Labels = mixedMoment B raw20879step1 raw20879step1Labels := by
      have hz : ∀ j, raw20879step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20879step1 = (fun i j => raw20879step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20879step1 raw20879step0; decide +kernel
      have hl : raw20879step1Labels = raw20879step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20879step0 raw20879step0Labels permutation56 hz
    mixedMoment B raw20879step1 raw20879step1Labels = mixedMoment B raw20879step2 raw20879step2Labels := by
      have ha : raw20879step2 = (fun i j => raw20879step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20879step2 raw20879step1; decide +kernel
      have hl : raw20879step2Labels = raw20879step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20879step1 raw20879step1Labels permutation8 permutation3
    _ = mixedMoment B node590 node590Labels := by rfl

def raw20880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20880Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20880step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20880step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20880 raw20880Labels = mixedMoment B node1121 node1121Labels := by
  calc
    mixedMoment B raw20880 raw20880Labels = mixedMoment B raw20880step0 raw20880step0Labels := by
      have hz : ∀ j, raw20880 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20880step0 = (fun i j => raw20880 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20880step0 raw20880; decide +kernel
      have hl : raw20880step0Labels = raw20880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20880 raw20880Labels permutation346 hz
    mixedMoment B raw20880step0 raw20880step0Labels = mixedMoment B raw20880step1 raw20880step1Labels := by
      have ha : raw20880step1 = (fun i j => raw20880step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20880step1 raw20880step0; decide +kernel
      have hl : raw20880step1Labels = raw20880step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20880step0 raw20880step0Labels permutation32 permutation3
    _ = mixedMoment B node1121 node1121Labels := by rfl

def raw20881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20881Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20881step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20881step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20881step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20881 raw20881Labels = mixedMoment B node1121 node1121Labels := by
  calc
    mixedMoment B raw20881 raw20881Labels = mixedMoment B raw20881step0 raw20881step0Labels := by
      have hz : ∀ j, raw20881 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20881step0 = (fun i j => raw20881 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20881step0 raw20881; decide +kernel
      have hl : raw20881step0Labels = raw20881Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20881 raw20881Labels permutation265 hz
    mixedMoment B raw20881step0 raw20881step0Labels = mixedMoment B raw20881step1 raw20881step1Labels := by
      have ha : raw20881step1 = (fun i j => raw20881step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20881step1 raw20881step0; decide +kernel
      have hl : raw20881step1Labels = raw20881step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20881step0 raw20881step0Labels permutation32 permutation3
    _ = mixedMoment B node1121 node1121Labels := by rfl

def raw20882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20882Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20882step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20882step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20882step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20882step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw20882step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20882 raw20882Labels = mixedMoment B node1177 node1177Labels := by
  calc
    mixedMoment B raw20882 raw20882Labels = mixedMoment B raw20882step0 raw20882step0Labels := by
      have hz : ∀ j, raw20882 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20882step0 = (fun i j => raw20882 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20882step0 raw20882; decide +kernel
      have hl : raw20882step0Labels = raw20882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20882 raw20882Labels permutation346 hz
    mixedMoment B raw20882step0 raw20882step0Labels = mixedMoment B raw20882step1 raw20882step1Labels := by
      have hz : ∀ j, raw20882step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20882step1 = (fun i j => raw20882step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20882step1 raw20882step0; decide +kernel
      have hl : raw20882step1Labels = raw20882step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20882step0 raw20882step0Labels permutation56 hz
    mixedMoment B raw20882step1 raw20882step1Labels = mixedMoment B raw20882step2 raw20882step2Labels := by
      have ha : raw20882step2 = (fun i j => raw20882step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20882step2 raw20882step1; decide +kernel
      have hl : raw20882step2Labels = raw20882step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20882step1 raw20882step1Labels permutation8 permutation3
    _ = mixedMoment B node1177 node1177Labels := by rfl

def raw20883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20883Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20883step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20883step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20883step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20883step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw20883step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20883 raw20883Labels = mixedMoment B node587 node587Labels := by
  calc
    mixedMoment B raw20883 raw20883Labels = mixedMoment B raw20883step0 raw20883step0Labels := by
      have hz : ∀ j, raw20883 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20883step0 = (fun i j => raw20883 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20883step0 raw20883; decide +kernel
      have hl : raw20883step0Labels = raw20883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20883 raw20883Labels permutation346 hz
    mixedMoment B raw20883step0 raw20883step0Labels = mixedMoment B raw20883step1 raw20883step1Labels := by
      have hz : ∀ j, raw20883step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20883step1 = (fun i j => raw20883step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20883step1 raw20883step0; decide +kernel
      have hl : raw20883step1Labels = raw20883step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20883step0 raw20883step0Labels permutation56 hz
    mixedMoment B raw20883step1 raw20883step1Labels = mixedMoment B raw20883step2 raw20883step2Labels := by
      have ha : raw20883step2 = (fun i j => raw20883step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20883step2 raw20883step1; decide +kernel
      have hl : raw20883step2Labels = raw20883step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20883step1 raw20883step1Labels permutation8 permutation3
    _ = mixedMoment B node587 node587Labels := by rfl

def raw20884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20884Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20884step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw20884step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20884 raw20884Labels = mixedMoment B node1118 node1118Labels := by
  calc
    mixedMoment B raw20884 raw20884Labels = mixedMoment B raw20884step0 raw20884step0Labels := by
      have hz : ∀ j, raw20884 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20884step0 = (fun i j => raw20884 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20884step0 raw20884; decide +kernel
      have hl : raw20884step0Labels = raw20884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20884 raw20884Labels permutation346 hz
    mixedMoment B raw20884step0 raw20884step0Labels = mixedMoment B raw20884step1 raw20884step1Labels := by
      have ha : raw20884step1 = (fun i j => raw20884step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20884step1 raw20884step0; decide +kernel
      have hl : raw20884step1Labels = raw20884step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20884step0 raw20884step0Labels permutation32 permutation3
    _ = mixedMoment B node1118 node1118Labels := by rfl

def raw20885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20885Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20885step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw20885step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20885 raw20885Labels = mixedMoment B node1118 node1118Labels := by
  calc
    mixedMoment B raw20885 raw20885Labels = mixedMoment B raw20885step0 raw20885step0Labels := by
      have hz : ∀ j, raw20885 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20885step0 = (fun i j => raw20885 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20885step0 raw20885; decide +kernel
      have hl : raw20885step0Labels = raw20885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20885 raw20885Labels permutation265 hz
    mixedMoment B raw20885step0 raw20885step0Labels = mixedMoment B raw20885step1 raw20885step1Labels := by
      have ha : raw20885step1 = (fun i j => raw20885step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20885step1 raw20885step0; decide +kernel
      have hl : raw20885step1Labels = raw20885step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20885step0 raw20885step0Labels permutation32 permutation3
    _ = mixedMoment B node1118 node1118Labels := by rfl

def raw20886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20886Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20886step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20886step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20886step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20886step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![4, -3, -1]]
def raw20886step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20886 raw20886Labels = mixedMoment B node1173 node1173Labels := by
  calc
    mixedMoment B raw20886 raw20886Labels = mixedMoment B raw20886step0 raw20886step0Labels := by
      have hz : ∀ j, raw20886 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20886step0 = (fun i j => raw20886 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20886step0 raw20886; decide +kernel
      have hl : raw20886step0Labels = raw20886Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20886 raw20886Labels permutation346 hz
    mixedMoment B raw20886step0 raw20886step0Labels = mixedMoment B raw20886step1 raw20886step1Labels := by
      have hz : ∀ j, raw20886step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20886step1 = (fun i j => raw20886step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20886step1 raw20886step0; decide +kernel
      have hl : raw20886step1Labels = raw20886step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20886step0 raw20886step0Labels permutation56 hz
    mixedMoment B raw20886step1 raw20886step1Labels = mixedMoment B raw20886step2 raw20886step2Labels := by
      have ha : raw20886step2 = (fun i j => raw20886step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20886step2 raw20886step1; decide +kernel
      have hl : raw20886step2Labels = raw20886step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20886step1 raw20886step1Labels permutation8 permutation3
    _ = mixedMoment B node1173 node1173Labels := by rfl

def raw20887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![4, -1, -3]]
def raw20887Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw20887step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20887step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw20887step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20887step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![4, -1, -3]]
def raw20887step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20887step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw20887step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20887 raw20887Labels = mixedMoment B node1275 node1275Labels := by
  calc
    mixedMoment B raw20887 raw20887Labels = mixedMoment B raw20887step0 raw20887step0Labels := by
      have hz : ∀ j, raw20887 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20887step0 = (fun i j => raw20887 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20887step0 raw20887; decide +kernel
      have hl : raw20887step0Labels = raw20887Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20887 raw20887Labels permutation520 hz
    mixedMoment B raw20887step0 raw20887step0Labels = mixedMoment B raw20887step1 raw20887step1Labels := by
      have hz : ∀ j, raw20887step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20887step1 = (fun i j => raw20887step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20887step1 raw20887step0; decide +kernel
      have hl : raw20887step1Labels = raw20887step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20887step0 raw20887step0Labels permutation80 hz
    mixedMoment B raw20887step1 raw20887step1Labels = mixedMoment B raw20887step2 raw20887step2Labels := by
      have hz : ∀ j, raw20887step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20887step2 = (fun i j => raw20887step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20887step2 raw20887step1; decide +kernel
      have hl : raw20887step2Labels = raw20887step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20887step1 raw20887step1Labels permutation14 hz
    mixedMoment B raw20887step2 raw20887step2Labels = mixedMoment B raw20887step3 raw20887step3Labels := by
      have ha : raw20887step3 = (fun i j => raw20887step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20887step3 raw20887step2; decide +kernel
      have hl : raw20887step3Labels = raw20887step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20887step2 raw20887step2Labels permutation2 permutation3
    _ = mixedMoment B node1275 node1275Labels := by rfl

def raw20888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20888Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20888step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20888step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20888step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20888step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20888step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20888step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20888step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20888 raw20888Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw20888 raw20888Labels = mixedMoment B raw20888step0 raw20888step0Labels := by
      have hz : ∀ j, raw20888 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20888step0 = (fun i j => raw20888 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20888step0 raw20888; decide +kernel
      have hl : raw20888step0Labels = raw20888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20888 raw20888Labels permutation346 hz
    mixedMoment B raw20888step0 raw20888step0Labels = mixedMoment B raw20888step1 raw20888step1Labels := by
      have hz : ∀ j, raw20888step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20888step1 = (fun i j => raw20888step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20888step1 raw20888step0; decide +kernel
      have hl : raw20888step1Labels = raw20888step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20888step0 raw20888step0Labels permutation56 hz
    mixedMoment B raw20888step1 raw20888step1Labels = mixedMoment B raw20888step2 raw20888step2Labels := by
      have ha : raw20888step2 = (fun i j => raw20888step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20888step2 raw20888step1; decide +kernel
      have hl : raw20888step2Labels = raw20888step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20888step1 raw20888step1Labels permutation31 permutation7
    mixedMoment B raw20888step2 raw20888step2Labels = mixedMoment B raw20888step3 raw20888step3Labels := by
      have ha : raw20888step3 = raw20888step2 := by apply Matrix.ext; unfold raw20888step3 raw20888step2; decide +kernel
      have hl : raw20888step2Labels = labelEmbedding1 ∘ raw20888step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20888step2 raw20888step2Labels raw20888step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

def raw20889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20889Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20889step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw20889step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20889step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw20889step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20889step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw20889step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20889 raw20889Labels = mixedMoment B node1528 node1528Labels := by
  calc
    mixedMoment B raw20889 raw20889Labels = mixedMoment B raw20889step0 raw20889step0Labels := by
      have hz : ∀ j, raw20889 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20889step0 = (fun i j => raw20889 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20889step0 raw20889; decide +kernel
      have hl : raw20889step0Labels = raw20889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20889 raw20889Labels permutation346 hz
    mixedMoment B raw20889step0 raw20889step0Labels = mixedMoment B raw20889step1 raw20889step1Labels := by
      have ha : raw20889step1 = (fun i j => raw20889step0 (permutation52 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20889step1 raw20889step0; decide +kernel
      have hl : raw20889step1Labels = raw20889step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20889step0 raw20889step0Labels permutation52 permutation5
    mixedMoment B raw20889step1 raw20889step1Labels = mixedMoment B raw20889step2 raw20889step2Labels := by
      have ha : raw20889step2 = -raw20889step1 := by apply Matrix.ext; change ∀ i j, raw20889step2 i j = -(raw20889step1 i j); unfold raw20889step2 raw20889step1; decide +kernel
      have hl : raw20889step2Labels = raw20889step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20889step2 raw20889step2Labels = mixedMoment B raw20889step3 raw20889step3Labels := by
      have ha : raw20889step3 = raw20889step2 := by apply Matrix.ext; unfold raw20889step3 raw20889step2; decide +kernel
      have hl : raw20889step2Labels = labelEmbedding1 ∘ raw20889step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20889step2 raw20889step2Labels raw20889step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1528 node1528Labels := by rfl

def raw20890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20890Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20890step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20890step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20890 raw20890Labels = mixedMoment B node2172 node2172Labels := by
  calc
    mixedMoment B raw20890 raw20890Labels = mixedMoment B raw20890step0 raw20890step0Labels := by
      have ha : raw20890step0 = (fun i j => raw20890 (permutation620 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20890step0 raw20890; decide +kernel
      have hl : raw20890step0Labels = raw20890Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20890 raw20890Labels permutation620 permutation7
    mixedMoment B raw20890step0 raw20890step0Labels = mixedMoment B raw20890step1 raw20890step1Labels := by
      have ha : raw20890step1 = raw20890step0 := by apply Matrix.ext; unfold raw20890step1 raw20890step0; decide +kernel
      have hl : raw20890step0Labels = labelEmbedding1 ∘ raw20890step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20890step0 raw20890step0Labels raw20890step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2172 node2172Labels := by rfl

def raw20891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20891Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20891step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw20891step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20891step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw20891step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20891 raw20891Labels = mixedMoment B node2184 node2184Labels := by
  calc
    mixedMoment B raw20891 raw20891Labels = mixedMoment B raw20891step0 raw20891step0Labels := by
      have hz : ∀ j, raw20891 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20891step0 = (fun i j => raw20891 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20891step0 raw20891; decide +kernel
      have hl : raw20891step0Labels = raw20891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20891 raw20891Labels permutation346 hz
    mixedMoment B raw20891step0 raw20891step0Labels = mixedMoment B raw20891step1 raw20891step1Labels := by
      have ha : raw20891step1 = (fun i j => raw20891step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20891step1 raw20891step0; decide +kernel
      have hl : raw20891step1Labels = raw20891step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20891step0 raw20891step0Labels permutation139 permutation7
    mixedMoment B raw20891step1 raw20891step1Labels = mixedMoment B raw20891step2 raw20891step2Labels := by
      have ha : raw20891step2 = raw20891step1 := by apply Matrix.ext; unfold raw20891step2 raw20891step1; decide +kernel
      have hl : raw20891step1Labels = labelEmbedding1 ∘ raw20891step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20891step1 raw20891step1Labels raw20891step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2184 node2184Labels := by rfl

def raw20892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw20892Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20892step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20892step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20892step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20892step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20892step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20892step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20892step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20892 raw20892Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw20892 raw20892Labels = mixedMoment B raw20892step0 raw20892step0Labels := by
      have hz : ∀ j, raw20892 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20892step0 = (fun i j => raw20892 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20892step0 raw20892; decide +kernel
      have hl : raw20892step0Labels = raw20892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20892 raw20892Labels permutation520 hz
    mixedMoment B raw20892step0 raw20892step0Labels = mixedMoment B raw20892step1 raw20892step1Labels := by
      have hz : ∀ j, raw20892step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20892step1 = (fun i j => raw20892step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20892step1 raw20892step0; decide +kernel
      have hl : raw20892step1Labels = raw20892step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20892step0 raw20892step0Labels permutation80 hz
    mixedMoment B raw20892step1 raw20892step1Labels = mixedMoment B raw20892step2 raw20892step2Labels := by
      have ha : raw20892step2 = (fun i j => raw20892step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20892step2 raw20892step1; decide +kernel
      have hl : raw20892step2Labels = raw20892step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20892step1 raw20892step1Labels permutation29 permutation7
    mixedMoment B raw20892step2 raw20892step2Labels = mixedMoment B raw20892step3 raw20892step3Labels := by
      have ha : raw20892step3 = raw20892step2 := by apply Matrix.ext; unfold raw20892step3 raw20892step2; decide +kernel
      have hl : raw20892step2Labels = labelEmbedding1 ∘ raw20892step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20892step2 raw20892step2Labels raw20892step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2226 node2226Labels := by rfl

def raw20893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20893Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20893step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw20893step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20893step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw20893step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20893step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw20893step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20893 raw20893Labels = mixedMoment B node1528 node1528Labels := by
  calc
    mixedMoment B raw20893 raw20893Labels = mixedMoment B raw20893step0 raw20893step0Labels := by
      have hz : ∀ j, raw20893 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20893step0 = (fun i j => raw20893 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20893step0 raw20893; decide +kernel
      have hl : raw20893step0Labels = raw20893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20893 raw20893Labels permutation265 hz
    mixedMoment B raw20893step0 raw20893step0Labels = mixedMoment B raw20893step1 raw20893step1Labels := by
      have ha : raw20893step1 = (fun i j => raw20893step0 (permutation52 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20893step1 raw20893step0; decide +kernel
      have hl : raw20893step1Labels = raw20893step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20893step0 raw20893step0Labels permutation52 permutation5
    mixedMoment B raw20893step1 raw20893step1Labels = mixedMoment B raw20893step2 raw20893step2Labels := by
      have ha : raw20893step2 = -raw20893step1 := by apply Matrix.ext; change ∀ i j, raw20893step2 i j = -(raw20893step1 i j); unfold raw20893step2 raw20893step1; decide +kernel
      have hl : raw20893step2Labels = raw20893step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20893step2 raw20893step2Labels = mixedMoment B raw20893step3 raw20893step3Labels := by
      have ha : raw20893step3 = raw20893step2 := by apply Matrix.ext; unfold raw20893step3 raw20893step2; decide +kernel
      have hl : raw20893step2Labels = labelEmbedding1 ∘ raw20893step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20893step2 raw20893step2Labels raw20893step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1528 node1528Labels := by rfl

def raw20894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20894Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20894step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20894step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20894step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20894 raw20894Labels = mixedMoment B node2172 node2172Labels := by
  calc
    mixedMoment B raw20894 raw20894Labels = mixedMoment B raw20894step0 raw20894step0Labels := by
      have ha : raw20894step0 = (fun i j => raw20894 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20894step0 raw20894; decide +kernel
      have hl : raw20894step0Labels = raw20894Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20894 raw20894Labels permutation644 permutation7
    mixedMoment B raw20894step0 raw20894step0Labels = mixedMoment B raw20894step1 raw20894step1Labels := by
      have ha : raw20894step1 = raw20894step0 := by apply Matrix.ext; unfold raw20894step1 raw20894step0; decide +kernel
      have hl : raw20894step0Labels = labelEmbedding1 ∘ raw20894step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20894step0 raw20894step0Labels raw20894step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2172 node2172Labels := by rfl

def raw20895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20895Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20895step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw20895step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20895step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw20895step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20895 raw20895Labels = mixedMoment B node2184 node2184Labels := by
  calc
    mixedMoment B raw20895 raw20895Labels = mixedMoment B raw20895step0 raw20895step0Labels := by
      have hz : ∀ j, raw20895 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20895step0 = (fun i j => raw20895 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20895step0 raw20895; decide +kernel
      have hl : raw20895step0Labels = raw20895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20895 raw20895Labels permutation265 hz
    mixedMoment B raw20895step0 raw20895step0Labels = mixedMoment B raw20895step1 raw20895step1Labels := by
      have ha : raw20895step1 = (fun i j => raw20895step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20895step1 raw20895step0; decide +kernel
      have hl : raw20895step1Labels = raw20895step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20895step0 raw20895step0Labels permutation139 permutation7
    mixedMoment B raw20895step1 raw20895step1Labels = mixedMoment B raw20895step2 raw20895step2Labels := by
      have ha : raw20895step2 = raw20895step1 := by apply Matrix.ext; unfold raw20895step2 raw20895step1; decide +kernel
      have hl : raw20895step1Labels = labelEmbedding1 ∘ raw20895step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20895step1 raw20895step1Labels raw20895step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2184 node2184Labels := by rfl

def raw20896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw20896Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20896step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20896step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20896step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20896step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20896step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20896step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20896step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20896 raw20896Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw20896 raw20896Labels = mixedMoment B raw20896step0 raw20896step0Labels := by
      have hz : ∀ j, raw20896 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20896step0 = (fun i j => raw20896 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20896step0 raw20896; decide +kernel
      have hl : raw20896step0Labels = raw20896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20896 raw20896Labels permutation520 hz
    mixedMoment B raw20896step0 raw20896step0Labels = mixedMoment B raw20896step1 raw20896step1Labels := by
      have hz : ∀ j, raw20896step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20896step1 = (fun i j => raw20896step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20896step1 raw20896step0; decide +kernel
      have hl : raw20896step1Labels = raw20896step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20896step0 raw20896step0Labels permutation56 hz
    mixedMoment B raw20896step1 raw20896step1Labels = mixedMoment B raw20896step2 raw20896step2Labels := by
      have ha : raw20896step2 = (fun i j => raw20896step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20896step2 raw20896step1; decide +kernel
      have hl : raw20896step2Labels = raw20896step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20896step1 raw20896step1Labels permutation29 permutation7
    mixedMoment B raw20896step2 raw20896step2Labels = mixedMoment B raw20896step3 raw20896step3Labels := by
      have ha : raw20896step3 = raw20896step2 := by apply Matrix.ext; unfold raw20896step3 raw20896step2; decide +kernel
      have hl : raw20896step2Labels = labelEmbedding1 ∘ raw20896step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20896step2 raw20896step2Labels raw20896step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2226 node2226Labels := by rfl

def raw20897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20897Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20897step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20897step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20897step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20897step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw20897step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20897step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw20897step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20897step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw20897step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20897 raw20897Labels = mixedMoment B node1530 node1530Labels := by
  calc
    mixedMoment B raw20897 raw20897Labels = mixedMoment B raw20897step0 raw20897step0Labels := by
      have hz : ∀ j, raw20897 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20897step0 = (fun i j => raw20897 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20897step0 raw20897; decide +kernel
      have hl : raw20897step0Labels = raw20897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20897 raw20897Labels permutation346 hz
    mixedMoment B raw20897step0 raw20897step0Labels = mixedMoment B raw20897step1 raw20897step1Labels := by
      have hz : ∀ j, raw20897step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20897step1 = (fun i j => raw20897step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20897step1 raw20897step0; decide +kernel
      have hl : raw20897step1Labels = raw20897step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20897step0 raw20897step0Labels permutation56 hz
    mixedMoment B raw20897step1 raw20897step1Labels = mixedMoment B raw20897step2 raw20897step2Labels := by
      have ha : raw20897step2 = (fun i j => raw20897step1 (permutation13 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20897step2 raw20897step1; decide +kernel
      have hl : raw20897step2Labels = raw20897step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20897step1 raw20897step1Labels permutation13 permutation5
    mixedMoment B raw20897step2 raw20897step2Labels = mixedMoment B raw20897step3 raw20897step3Labels := by
      have ha : raw20897step3 = -raw20897step2 := by apply Matrix.ext; change ∀ i j, raw20897step3 i j = -(raw20897step2 i j); unfold raw20897step3 raw20897step2; decide +kernel
      have hl : raw20897step3Labels = raw20897step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20897step3 raw20897step3Labels = mixedMoment B raw20897step4 raw20897step4Labels := by
      have ha : raw20897step4 = raw20897step3 := by apply Matrix.ext; unfold raw20897step4 raw20897step3; decide +kernel
      have hl : raw20897step3Labels = labelEmbedding1 ∘ raw20897step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20897step3 raw20897step3Labels raw20897step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1530 node1530Labels := by rfl

def raw20898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20898Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20898step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20898step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20898step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20898step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20898step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20898 raw20898Labels = mixedMoment B node2200 node2200Labels := by
  calc
    mixedMoment B raw20898 raw20898Labels = mixedMoment B raw20898step0 raw20898step0Labels := by
      have hz : ∀ j, raw20898 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20898step0 = (fun i j => raw20898 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20898step0 raw20898; decide +kernel
      have hl : raw20898step0Labels = raw20898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20898 raw20898Labels permutation346 hz
    mixedMoment B raw20898step0 raw20898step0Labels = mixedMoment B raw20898step1 raw20898step1Labels := by
      have ha : raw20898step1 = (fun i j => raw20898step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20898step1 raw20898step0; decide +kernel
      have hl : raw20898step1Labels = raw20898step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20898step0 raw20898step0Labels permutation149 permutation7
    mixedMoment B raw20898step1 raw20898step1Labels = mixedMoment B raw20898step2 raw20898step2Labels := by
      have ha : raw20898step2 = raw20898step1 := by apply Matrix.ext; unfold raw20898step2 raw20898step1; decide +kernel
      have hl : raw20898step1Labels = labelEmbedding1 ∘ raw20898step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20898step1 raw20898step1Labels raw20898step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2200 node2200Labels := by rfl

def raw20899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20899Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20899step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20899step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20899step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw20899step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20899 raw20899Labels = mixedMoment B node2200 node2200Labels := by
  calc
    mixedMoment B raw20899 raw20899Labels = mixedMoment B raw20899step0 raw20899step0Labels := by
      have hz : ∀ j, raw20899 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20899step0 = (fun i j => raw20899 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20899step0 raw20899; decide +kernel
      have hl : raw20899step0Labels = raw20899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20899 raw20899Labels permutation265 hz
    mixedMoment B raw20899step0 raw20899step0Labels = mixedMoment B raw20899step1 raw20899step1Labels := by
      have ha : raw20899step1 = (fun i j => raw20899step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20899step1 raw20899step0; decide +kernel
      have hl : raw20899step1Labels = raw20899step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20899step0 raw20899step0Labels permutation149 permutation7
    mixedMoment B raw20899step1 raw20899step1Labels = mixedMoment B raw20899step2 raw20899step2Labels := by
      have ha : raw20899step2 = raw20899step1 := by apply Matrix.ext; unfold raw20899step2 raw20899step1; decide +kernel
      have hl : raw20899step1Labels = labelEmbedding1 ∘ raw20899step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20899step1 raw20899step1Labels raw20899step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2200 node2200Labels := by rfl

def raw20900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![3, 0, -3]]
def raw20900Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20900step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20900step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20900step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20900step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw20900step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20900step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![2, 2, -4]]
def raw20900step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20900step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![2, 2, -4]]
def raw20900step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20900 raw20900Labels = mixedMoment B node2289 node2289Labels := by
  calc
    mixedMoment B raw20900 raw20900Labels = mixedMoment B raw20900step0 raw20900step0Labels := by
      have hz : ∀ j, raw20900 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20900step0 = (fun i j => raw20900 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20900step0 raw20900; decide +kernel
      have hl : raw20900step0Labels = raw20900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20900 raw20900Labels permutation520 hz
    mixedMoment B raw20900step0 raw20900step0Labels = mixedMoment B raw20900step1 raw20900step1Labels := by
      have hz : ∀ j, raw20900step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20900step1 = (fun i j => raw20900step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20900step1 raw20900step0; decide +kernel
      have hl : raw20900step1Labels = raw20900step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20900step0 raw20900step0Labels permutation80 hz
    mixedMoment B raw20900step1 raw20900step1Labels = mixedMoment B raw20900step2 raw20900step2Labels := by
      have hz : ∀ j, raw20900step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20900step2 = (fun i j => raw20900step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20900step2 raw20900step1; decide +kernel
      have hl : raw20900step2Labels = raw20900step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20900step1 raw20900step1Labels permutation14 hz
    mixedMoment B raw20900step2 raw20900step2Labels = mixedMoment B raw20900step3 raw20900step3Labels := by
      have ha : raw20900step3 = (fun i j => raw20900step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20900step3 raw20900step2; decide +kernel
      have hl : raw20900step3Labels = raw20900step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20900step2 raw20900step2Labels permutation7 permutation7
    mixedMoment B raw20900step3 raw20900step3Labels = mixedMoment B raw20900step4 raw20900step4Labels := by
      have ha : raw20900step4 = raw20900step3 := by apply Matrix.ext; unfold raw20900step4 raw20900step3; decide +kernel
      have hl : raw20900step3Labels = labelEmbedding1 ∘ raw20900step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20900step3 raw20900step3Labels raw20900step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2289 node2289Labels := by rfl

def raw20901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20901Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20901step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20901step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20901step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20901step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 1, 0], ![-2, 0, 2]]
def raw20901step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20901step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw20901step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20901step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw20901step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20901 raw20901Labels = mixedMoment B node1529 node1529Labels := by
  calc
    mixedMoment B raw20901 raw20901Labels = mixedMoment B raw20901step0 raw20901step0Labels := by
      have hz : ∀ j, raw20901 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20901step0 = (fun i j => raw20901 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20901step0 raw20901; decide +kernel
      have hl : raw20901step0Labels = raw20901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20901 raw20901Labels permutation346 hz
    mixedMoment B raw20901step0 raw20901step0Labels = mixedMoment B raw20901step1 raw20901step1Labels := by
      have hz : ∀ j, raw20901step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20901step1 = (fun i j => raw20901step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20901step1 raw20901step0; decide +kernel
      have hl : raw20901step1Labels = raw20901step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20901step0 raw20901step0Labels permutation56 hz
    mixedMoment B raw20901step1 raw20901step1Labels = mixedMoment B raw20901step2 raw20901step2Labels := by
      have ha : raw20901step2 = (fun i j => raw20901step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20901step2 raw20901step1; decide +kernel
      have hl : raw20901step2Labels = raw20901step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20901step1 raw20901step1Labels permutation12 permutation5
    mixedMoment B raw20901step2 raw20901step2Labels = mixedMoment B raw20901step3 raw20901step3Labels := by
      have ha : raw20901step3 = -raw20901step2 := by apply Matrix.ext; change ∀ i j, raw20901step3 i j = -(raw20901step2 i j); unfold raw20901step3 raw20901step2; decide +kernel
      have hl : raw20901step3Labels = raw20901step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20901step3 raw20901step3Labels = mixedMoment B raw20901step4 raw20901step4Labels := by
      have ha : raw20901step4 = raw20901step3 := by apply Matrix.ext; unfold raw20901step4 raw20901step3; decide +kernel
      have hl : raw20901step3Labels = labelEmbedding1 ∘ raw20901step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20901step3 raw20901step3Labels raw20901step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1529 node1529Labels := by rfl

def raw20902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20902Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20902step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20902step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20902step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20902step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20902 raw20902Labels = mixedMoment B node2149 node2149Labels := by
  calc
    mixedMoment B raw20902 raw20902Labels = mixedMoment B raw20902step0 raw20902step0Labels := by
      have hz : ∀ j, raw20902 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20902step0 = (fun i j => raw20902 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20902step0 raw20902; decide +kernel
      have hl : raw20902step0Labels = raw20902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20902 raw20902Labels permutation346 hz
    mixedMoment B raw20902step0 raw20902step0Labels = mixedMoment B raw20902step1 raw20902step1Labels := by
      have ha : raw20902step1 = (fun i j => raw20902step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20902step1 raw20902step0; decide +kernel
      have hl : raw20902step1Labels = raw20902step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20902step0 raw20902step0Labels permutation149 permutation7
    mixedMoment B raw20902step1 raw20902step1Labels = mixedMoment B raw20902step2 raw20902step2Labels := by
      have ha : raw20902step2 = raw20902step1 := by apply Matrix.ext; unfold raw20902step2 raw20902step1; decide +kernel
      have hl : raw20902step1Labels = labelEmbedding1 ∘ raw20902step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20902step1 raw20902step1Labels raw20902step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2149 node2149Labels := by rfl

def raw20903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20903Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20903step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20903step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20903step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20903step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20903step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20903 raw20903Labels = mixedMoment B node2149 node2149Labels := by
  calc
    mixedMoment B raw20903 raw20903Labels = mixedMoment B raw20903step0 raw20903step0Labels := by
      have hz : ∀ j, raw20903 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20903step0 = (fun i j => raw20903 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20903step0 raw20903; decide +kernel
      have hl : raw20903step0Labels = raw20903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20903 raw20903Labels permutation265 hz
    mixedMoment B raw20903step0 raw20903step0Labels = mixedMoment B raw20903step1 raw20903step1Labels := by
      have ha : raw20903step1 = (fun i j => raw20903step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20903step1 raw20903step0; decide +kernel
      have hl : raw20903step1Labels = raw20903step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20903step0 raw20903step0Labels permutation149 permutation7
    mixedMoment B raw20903step1 raw20903step1Labels = mixedMoment B raw20903step2 raw20903step2Labels := by
      have ha : raw20903step2 = raw20903step1 := by apply Matrix.ext; unfold raw20903step2 raw20903step1; decide +kernel
      have hl : raw20903step1Labels = labelEmbedding1 ∘ raw20903step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20903step1 raw20903step1Labels raw20903step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2149 node2149Labels := by rfl

def raw20904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20904Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20904step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20904step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20904step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20904step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![2, 2, -4]]
def raw20904step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20904step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![2, 2, -4]]
def raw20904step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20904 raw20904Labels = mixedMoment B node2167 node2167Labels := by
  calc
    mixedMoment B raw20904 raw20904Labels = mixedMoment B raw20904step0 raw20904step0Labels := by
      have hz : ∀ j, raw20904 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20904step0 = (fun i j => raw20904 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20904step0 raw20904; decide +kernel
      have hl : raw20904step0Labels = raw20904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20904 raw20904Labels permutation346 hz
    mixedMoment B raw20904step0 raw20904step0Labels = mixedMoment B raw20904step1 raw20904step1Labels := by
      have hz : ∀ j, raw20904step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20904step1 = (fun i j => raw20904step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20904step1 raw20904step0; decide +kernel
      have hl : raw20904step1Labels = raw20904step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20904step0 raw20904step0Labels permutation56 hz
    mixedMoment B raw20904step1 raw20904step1Labels = mixedMoment B raw20904step2 raw20904step2Labels := by
      have ha : raw20904step2 = (fun i j => raw20904step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20904step2 raw20904step1; decide +kernel
      have hl : raw20904step2Labels = raw20904step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20904step1 raw20904step1Labels permutation31 permutation7
    mixedMoment B raw20904step2 raw20904step2Labels = mixedMoment B raw20904step3 raw20904step3Labels := by
      have ha : raw20904step3 = raw20904step2 := by apply Matrix.ext; unfold raw20904step3 raw20904step2; decide +kernel
      have hl : raw20904step2Labels = labelEmbedding1 ∘ raw20904step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20904step2 raw20904step2Labels raw20904step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2167 node2167Labels := by rfl

def raw20905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20905Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20905step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20905step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20905step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20905step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, -3, 4]]
def raw20905step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20905step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw20905step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20905step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, -1, 0], ![1, 0, -1], ![1, 3, -4]]
def raw20905step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20905 raw20905Labels = mixedMoment B node1532 node1532Labels := by
  calc
    mixedMoment B raw20905 raw20905Labels = mixedMoment B raw20905step0 raw20905step0Labels := by
      have hz : ∀ j, raw20905 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20905step0 = (fun i j => raw20905 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20905step0 raw20905; decide +kernel
      have hl : raw20905step0Labels = raw20905Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20905 raw20905Labels permutation346 hz
    mixedMoment B raw20905step0 raw20905step0Labels = mixedMoment B raw20905step1 raw20905step1Labels := by
      have hz : ∀ j, raw20905step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20905step1 = (fun i j => raw20905step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20905step1 raw20905step0; decide +kernel
      have hl : raw20905step1Labels = raw20905step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20905step0 raw20905step0Labels permutation56 hz
    mixedMoment B raw20905step1 raw20905step1Labels = mixedMoment B raw20905step2 raw20905step2Labels := by
      have ha : raw20905step2 = (fun i j => raw20905step1 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20905step2 raw20905step1; decide +kernel
      have hl : raw20905step2Labels = raw20905step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20905step1 raw20905step1Labels permutation8 permutation5
    mixedMoment B raw20905step2 raw20905step2Labels = mixedMoment B raw20905step3 raw20905step3Labels := by
      have ha : raw20905step3 = -raw20905step2 := by apply Matrix.ext; change ∀ i j, raw20905step3 i j = -(raw20905step2 i j); unfold raw20905step3 raw20905step2; decide +kernel
      have hl : raw20905step3Labels = raw20905step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20905step3 raw20905step3Labels = mixedMoment B raw20905step4 raw20905step4Labels := by
      have ha : raw20905step4 = raw20905step3 := by apply Matrix.ext; unfold raw20905step4 raw20905step3; decide +kernel
      have hl : raw20905step3Labels = labelEmbedding1 ∘ raw20905step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20905step3 raw20905step3Labels raw20905step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1532 node1532Labels := by rfl

def raw20906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20906Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20906step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20906step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20906step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20906step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20906step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20906 raw20906Labels = mixedMoment B node1672 node1672Labels := by
  calc
    mixedMoment B raw20906 raw20906Labels = mixedMoment B raw20906step0 raw20906step0Labels := by
      have hz : ∀ j, raw20906 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20906step0 = (fun i j => raw20906 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20906step0 raw20906; decide +kernel
      have hl : raw20906step0Labels = raw20906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20906 raw20906Labels permutation346 hz
    mixedMoment B raw20906step0 raw20906step0Labels = mixedMoment B raw20906step1 raw20906step1Labels := by
      have ha : raw20906step1 = (fun i j => raw20906step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20906step1 raw20906step0; decide +kernel
      have hl : raw20906step1Labels = raw20906step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20906step0 raw20906step0Labels permutation149 permutation7
    mixedMoment B raw20906step1 raw20906step1Labels = mixedMoment B raw20906step2 raw20906step2Labels := by
      have ha : raw20906step2 = raw20906step1 := by apply Matrix.ext; unfold raw20906step2 raw20906step1; decide +kernel
      have hl : raw20906step1Labels = labelEmbedding1 ∘ raw20906step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20906step1 raw20906step1Labels raw20906step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1672 node1672Labels := by rfl

def raw20907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20907Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20907step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20907step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20907step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw20907step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20907 raw20907Labels = mixedMoment B node1672 node1672Labels := by
  calc
    mixedMoment B raw20907 raw20907Labels = mixedMoment B raw20907step0 raw20907step0Labels := by
      have hz : ∀ j, raw20907 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20907step0 = (fun i j => raw20907 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20907step0 raw20907; decide +kernel
      have hl : raw20907step0Labels = raw20907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20907 raw20907Labels permutation265 hz
    mixedMoment B raw20907step0 raw20907step0Labels = mixedMoment B raw20907step1 raw20907step1Labels := by
      have ha : raw20907step1 = (fun i j => raw20907step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20907step1 raw20907step0; decide +kernel
      have hl : raw20907step1Labels = raw20907step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20907step0 raw20907step0Labels permutation149 permutation7
    mixedMoment B raw20907step1 raw20907step1Labels = mixedMoment B raw20907step2 raw20907step2Labels := by
      have ha : raw20907step2 = raw20907step1 := by apply Matrix.ext; unfold raw20907step2 raw20907step1; decide +kernel
      have hl : raw20907step1Labels = labelEmbedding1 ∘ raw20907step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20907step1 raw20907step1Labels raw20907step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1672 node1672Labels := by rfl

def raw20908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20908Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20908step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20908step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20908step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20908step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw20908step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20908step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw20908step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20908 raw20908Labels = mixedMoment B node1692 node1692Labels := by
  calc
    mixedMoment B raw20908 raw20908Labels = mixedMoment B raw20908step0 raw20908step0Labels := by
      have hz : ∀ j, raw20908 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20908step0 = (fun i j => raw20908 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20908step0 raw20908; decide +kernel
      have hl : raw20908step0Labels = raw20908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20908 raw20908Labels permutation346 hz
    mixedMoment B raw20908step0 raw20908step0Labels = mixedMoment B raw20908step1 raw20908step1Labels := by
      have hz : ∀ j, raw20908step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20908step1 = (fun i j => raw20908step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20908step1 raw20908step0; decide +kernel
      have hl : raw20908step1Labels = raw20908step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20908step0 raw20908step0Labels permutation56 hz
    mixedMoment B raw20908step1 raw20908step1Labels = mixedMoment B raw20908step2 raw20908step2Labels := by
      have ha : raw20908step2 = (fun i j => raw20908step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20908step2 raw20908step1; decide +kernel
      have hl : raw20908step2Labels = raw20908step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20908step1 raw20908step1Labels permutation31 permutation7
    mixedMoment B raw20908step2 raw20908step2Labels = mixedMoment B raw20908step3 raw20908step3Labels := by
      have ha : raw20908step3 = raw20908step2 := by apply Matrix.ext; unfold raw20908step3 raw20908step2; decide +kernel
      have hl : raw20908step2Labels = labelEmbedding1 ∘ raw20908step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20908step2 raw20908step2Labels raw20908step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1692 node1692Labels := by rfl

def raw20909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![4, -1, -3]]
def raw20909Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw20909step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20909step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw20909step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20909step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![4, -1, -3]]
def raw20909step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20909step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw20909step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20909step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw20909step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20909 raw20909Labels = mixedMoment B node1752 node1752Labels := by
  calc
    mixedMoment B raw20909 raw20909Labels = mixedMoment B raw20909step0 raw20909step0Labels := by
      have hz : ∀ j, raw20909 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20909step0 = (fun i j => raw20909 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20909step0 raw20909; decide +kernel
      have hl : raw20909step0Labels = raw20909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20909 raw20909Labels permutation520 hz
    mixedMoment B raw20909step0 raw20909step0Labels = mixedMoment B raw20909step1 raw20909step1Labels := by
      have hz : ∀ j, raw20909step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20909step1 = (fun i j => raw20909step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20909step1 raw20909step0; decide +kernel
      have hl : raw20909step1Labels = raw20909step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20909step0 raw20909step0Labels permutation80 hz
    mixedMoment B raw20909step1 raw20909step1Labels = mixedMoment B raw20909step2 raw20909step2Labels := by
      have hz : ∀ j, raw20909step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20909step2 = (fun i j => raw20909step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20909step2 raw20909step1; decide +kernel
      have hl : raw20909step2Labels = raw20909step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20909step1 raw20909step1Labels permutation14 hz
    mixedMoment B raw20909step2 raw20909step2Labels = mixedMoment B raw20909step3 raw20909step3Labels := by
      have ha : raw20909step3 = (fun i j => raw20909step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20909step3 raw20909step2; decide +kernel
      have hl : raw20909step3Labels = raw20909step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20909step2 raw20909step2Labels permutation7 permutation7
    mixedMoment B raw20909step3 raw20909step3Labels = mixedMoment B raw20909step4 raw20909step4Labels := by
      have ha : raw20909step4 = raw20909step3 := by apply Matrix.ext; unfold raw20909step4 raw20909step3; decide +kernel
      have hl : raw20909step3Labels = labelEmbedding1 ∘ raw20909step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20909step3 raw20909step3Labels raw20909step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1752 node1752Labels := by rfl

def raw20910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20910step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20910step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20910 raw20910Labels = mixedMoment B node1239 node1239Labels := by
  calc
    mixedMoment B raw20910 raw20910Labels = mixedMoment B raw20910step0 raw20910step0Labels := by
      have hz : ∀ j, raw20910 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20910step0 = (fun i j => raw20910 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20910step0 raw20910; decide +kernel
      have hl : raw20910step0Labels = raw20910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20910 raw20910Labels permutation346 hz
    mixedMoment B raw20910step0 raw20910step0Labels = mixedMoment B raw20910step1 raw20910step1Labels := by
      have hz : ∀ j, raw20910step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20910step1 = (fun i j => raw20910step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20910step1 raw20910step0; decide +kernel
      have hl : raw20910step1Labels = raw20910step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20910step0 raw20910step0Labels permutation56 hz
    _ = mixedMoment B node1239 node1239Labels := by rfl

def raw20911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20911Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20911step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20911 raw20911Labels = mixedMoment B node624 node624Labels := by
  calc
    mixedMoment B raw20911 raw20911Labels = mixedMoment B raw20911step0 raw20911step0Labels := by
      have hz : ∀ j, raw20911 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20911step0 = (fun i j => raw20911 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20911step0 raw20911; decide +kernel
      have hl : raw20911step0Labels = raw20911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20911 raw20911Labels permutation346 hz
    mixedMoment B raw20911step0 raw20911step0Labels = mixedMoment B raw20911step1 raw20911step1Labels := by
      have ha : raw20911step1 = (fun i j => raw20911step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20911step1 raw20911step0; decide +kernel
      have hl : raw20911step1Labels = raw20911step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20911step0 raw20911step0Labels permutation38 permutation2
    _ = mixedMoment B node624 node624Labels := by rfl

def raw20912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20912step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20912step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20912 raw20912Labels = mixedMoment B node624 node624Labels := by
  calc
    mixedMoment B raw20912 raw20912Labels = mixedMoment B raw20912step0 raw20912step0Labels := by
      have hz : ∀ j, raw20912 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20912step0 = (fun i j => raw20912 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20912step0 raw20912; decide +kernel
      have hl : raw20912step0Labels = raw20912Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20912 raw20912Labels permutation265 hz
    mixedMoment B raw20912step0 raw20912step0Labels = mixedMoment B raw20912step1 raw20912step1Labels := by
      have ha : raw20912step1 = (fun i j => raw20912step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20912step1 raw20912step0; decide +kernel
      have hl : raw20912step1Labels = raw20912step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20912step0 raw20912step0Labels permutation38 permutation2
    _ = mixedMoment B node624 node624Labels := by rfl

def raw20913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20913Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20913step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20913step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20913step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20913 raw20913Labels = mixedMoment B node639 node639Labels := by
  calc
    mixedMoment B raw20913 raw20913Labels = mixedMoment B raw20913step0 raw20913step0Labels := by
      have hz : ∀ j, raw20913 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20913step0 = (fun i j => raw20913 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20913step0 raw20913; decide +kernel
      have hl : raw20913step0Labels = raw20913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20913 raw20913Labels permutation346 hz
    mixedMoment B raw20913step0 raw20913step0Labels = mixedMoment B raw20913step1 raw20913step1Labels := by
      have hz : ∀ j, raw20913step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20913step1 = (fun i j => raw20913step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20913step1 raw20913step0; decide +kernel
      have hl : raw20913step1Labels = raw20913step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20913step0 raw20913step0Labels permutation56 hz
    _ = mixedMoment B node639 node639Labels := by rfl

def raw20914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20914Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20914step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20914step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20914step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20914 raw20914Labels = mixedMoment B node634 node634Labels := by
  calc
    mixedMoment B raw20914 raw20914Labels = mixedMoment B raw20914step0 raw20914step0Labels := by
      have hz : ∀ j, raw20914 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20914step0 = (fun i j => raw20914 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20914step0 raw20914; decide +kernel
      have hl : raw20914step0Labels = raw20914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20914 raw20914Labels permutation346 hz
    mixedMoment B raw20914step0 raw20914step0Labels = mixedMoment B raw20914step1 raw20914step1Labels := by
      have hz : ∀ j, raw20914step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20914step1 = (fun i j => raw20914step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20914step1 raw20914step0; decide +kernel
      have hl : raw20914step1Labels = raw20914step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20914step0 raw20914step0Labels permutation56 hz
    _ = mixedMoment B node634 node634Labels := by rfl

def raw20915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20915Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20915step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20915step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20915step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20915 raw20915Labels = mixedMoment B node628 node628Labels := by
  calc
    mixedMoment B raw20915 raw20915Labels = mixedMoment B raw20915step0 raw20915step0Labels := by
      have hz : ∀ j, raw20915 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20915step0 = (fun i j => raw20915 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20915step0 raw20915; decide +kernel
      have hl : raw20915step0Labels = raw20915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20915 raw20915Labels permutation346 hz
    mixedMoment B raw20915step0 raw20915step0Labels = mixedMoment B raw20915step1 raw20915step1Labels := by
      have hz : ∀ j, raw20915step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20915step1 = (fun i j => raw20915step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20915step1 raw20915step0; decide +kernel
      have hl : raw20915step1Labels = raw20915step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20915step0 raw20915step0Labels permutation56 hz
    _ = mixedMoment B node628 node628Labels := by rfl

def raw20916 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![-1, 1], ![0, 0], ![3, -3]]
def raw20916Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20916step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![-1, 1], ![3, -3]]
def raw20916step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20916step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![3, -3]]
def raw20916step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20916step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw20916step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20916step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw20916step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20916step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw20916step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20916 raw20916Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw20916 raw20916Labels = mixedMoment B raw20916step0 raw20916step0Labels := by
      have hz : ∀ j, raw20916 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20916step0 = (fun i j => raw20916 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20916step0 raw20916; decide +kernel
      have hl : raw20916step0Labels = raw20916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20916 raw20916Labels permutation520 hz
    mixedMoment B raw20916step0 raw20916step0Labels = mixedMoment B raw20916step1 raw20916step1Labels := by
      have hz : ∀ j, raw20916step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20916step1 = (fun i j => raw20916step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20916step1 raw20916step0; decide +kernel
      have hl : raw20916step1Labels = raw20916step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20916step0 raw20916step0Labels permutation80 hz
    mixedMoment B raw20916step1 raw20916step1Labels = mixedMoment B raw20916step2 raw20916step2Labels := by
      have hz : ∀ j, raw20916step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20916step2 = (fun i j => raw20916step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20916step2 raw20916step1; decide +kernel
      have hl : raw20916step2Labels = raw20916step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20916step1 raw20916step1Labels permutation14 hz
    mixedMoment B raw20916step2 raw20916step2Labels = mixedMoment B raw20916step3 raw20916step3Labels := by
      have ha : raw20916step3 = (fun i j => raw20916step2 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20916step3 raw20916step2; decide +kernel
      have hl : raw20916step3Labels = raw20916step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20916step2 raw20916step2Labels permutation7 permutation0
    mixedMoment B raw20916step3 raw20916step3Labels = mixedMoment B raw20916step4 raw20916step4Labels := by
      have ha : raw20916step4 = -raw20916step3 := by apply Matrix.ext; change ∀ i j, raw20916step4 i j = -(raw20916step3 i j); unfold raw20916step4 raw20916step3; decide +kernel
      have hl : raw20916step4Labels = raw20916step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw20917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20917Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20917step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20917 raw20917Labels = mixedMoment B node1147 node1147Labels := by
  calc
    mixedMoment B raw20917 raw20917Labels = mixedMoment B raw20917step0 raw20917step0Labels := by
      have ha : raw20917step0 = (fun i j => raw20917 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20917step0 raw20917; decide +kernel
      have hl : raw20917step0Labels = raw20917Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20917 raw20917Labels permutation182 permutation2
    _ = mixedMoment B node1147 node1147Labels := by rfl

def raw20918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20918Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20918step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20918step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20918 raw20918Labels = mixedMoment B node1128 node1128Labels := by
  calc
    mixedMoment B raw20918 raw20918Labels = mixedMoment B raw20918step0 raw20918step0Labels := by
      have hz : ∀ j, raw20918 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20918step0 = (fun i j => raw20918 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20918step0 raw20918; decide +kernel
      have hl : raw20918step0Labels = raw20918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20918 raw20918Labels permutation346 hz
    mixedMoment B raw20918step0 raw20918step0Labels = mixedMoment B raw20918step1 raw20918step1Labels := by
      have ha : raw20918step1 = (fun i j => raw20918step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20918step1 raw20918step0; decide +kernel
      have hl : raw20918step1Labels = raw20918step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20918step0 raw20918step0Labels permutation38 permutation2
    _ = mixedMoment B node1128 node1128Labels := by rfl

def raw20919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw20919Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20919step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20919step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20919step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20919step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20919step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20919 raw20919Labels = mixedMoment B node1239 node1239Labels := by
  calc
    mixedMoment B raw20919 raw20919Labels = mixedMoment B raw20919step0 raw20919step0Labels := by
      have hz : ∀ j, raw20919 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20919step0 = (fun i j => raw20919 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20919step0 raw20919; decide +kernel
      have hl : raw20919step0Labels = raw20919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20919 raw20919Labels permutation520 hz
    mixedMoment B raw20919step0 raw20919step0Labels = mixedMoment B raw20919step1 raw20919step1Labels := by
      have hz : ∀ j, raw20919step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20919step1 = (fun i j => raw20919step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20919step1 raw20919step0; decide +kernel
      have hl : raw20919step1Labels = raw20919step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20919step0 raw20919step0Labels permutation80 hz
    mixedMoment B raw20919step1 raw20919step1Labels = mixedMoment B raw20919step2 raw20919step2Labels := by
      have ha : raw20919step2 = (fun i j => raw20919step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20919step2 raw20919step1; decide +kernel
      have hl : raw20919step2Labels = raw20919step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20919step1 raw20919step1Labels permutation10 permutation2
    _ = mixedMoment B node1239 node1239Labels := by rfl

def raw20920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20920Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20920step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20920step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw20920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20920 raw20920Labels = mixedMoment B node1234 node1234Labels := by
  calc
    mixedMoment B raw20920 raw20920Labels = mixedMoment B raw20920step0 raw20920step0Labels := by
      have hz : ∀ j, raw20920 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20920step0 = (fun i j => raw20920 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20920step0 raw20920; decide +kernel
      have hl : raw20920step0Labels = raw20920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20920 raw20920Labels permutation346 hz
    mixedMoment B raw20920step0 raw20920step0Labels = mixedMoment B raw20920step1 raw20920step1Labels := by
      have ha : raw20920step1 = (fun i j => raw20920step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20920step1 raw20920step0; decide +kernel
      have hl : raw20920step1Labels = raw20920step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20920step0 raw20920step0Labels permutation38 permutation2
    _ = mixedMoment B node1234 node1234Labels := by rfl

def raw20921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20921Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20921step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw20921step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20921step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20921step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20921 raw20921Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw20921 raw20921Labels = mixedMoment B raw20921step0 raw20921step0Labels := by
      have hz : ∀ j, raw20921 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20921step0 = (fun i j => raw20921 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20921step0 raw20921; decide +kernel
      have hl : raw20921step0Labels = raw20921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20921 raw20921Labels permutation346 hz
    mixedMoment B raw20921step0 raw20921step0Labels = mixedMoment B raw20921step1 raw20921step1Labels := by
      have ha : raw20921step1 = (fun i j => raw20921step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20921step1 raw20921step0; decide +kernel
      have hl : raw20921step1Labels = raw20921step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20921step0 raw20921step0Labels permutation151 permutation2
    mixedMoment B raw20921step1 raw20921step1Labels = mixedMoment B raw20921step2 raw20921step2Labels := by
      have ha : raw20921step2 = -raw20921step1 := by apply Matrix.ext; change ∀ i j, raw20921step2 i j = -(raw20921step1 i j); unfold raw20921step2 raw20921step1; decide +kernel
      have hl : raw20921step2Labels = raw20921step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2022 node2022Labels := by rfl

def raw20922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20922Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20922step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20922step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20922 raw20922Labels = mixedMoment B node1147 node1147Labels := by
  calc
    mixedMoment B raw20922 raw20922Labels = mixedMoment B raw20922step0 raw20922step0Labels := by
      have ha : raw20922step0 = (fun i j => raw20922 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20922step0 raw20922; decide +kernel
      have hl : raw20922step0Labels = raw20922Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20922 raw20922Labels permutation158 permutation2
    _ = mixedMoment B node1147 node1147Labels := by rfl

def raw20923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20923Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20923step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20923 raw20923Labels = mixedMoment B node1157 node1157Labels := by
  calc
    mixedMoment B raw20923 raw20923Labels = mixedMoment B raw20923step0 raw20923step0Labels := by
      have hz : ∀ j, raw20923 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20923step0 = (fun i j => raw20923 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20923step0 raw20923; decide +kernel
      have hl : raw20923step0Labels = raw20923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20923 raw20923Labels permutation346 hz
    _ = mixedMoment B node1157 node1157Labels := by rfl

def raw20924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20924Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20924step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20924 raw20924Labels = mixedMoment B node1153 node1153Labels := by
  calc
    mixedMoment B raw20924 raw20924Labels = mixedMoment B raw20924step0 raw20924step0Labels := by
      have hz : ∀ j, raw20924 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20924step0 = (fun i j => raw20924 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20924step0 raw20924; decide +kernel
      have hl : raw20924step0Labels = raw20924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20924 raw20924Labels permutation346 hz
    _ = mixedMoment B node1153 node1153Labels := by rfl

def raw20925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20925Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20925step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20925step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw20925step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20925step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20925step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20925 raw20925Labels = mixedMoment B node908 node908Labels := by
  calc
    mixedMoment B raw20925 raw20925Labels = mixedMoment B raw20925step0 raw20925step0Labels := by
      have hz : ∀ j, raw20925 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20925step0 = (fun i j => raw20925 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20925step0 raw20925; decide +kernel
      have hl : raw20925step0Labels = raw20925Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20925 raw20925Labels permutation346 hz
    mixedMoment B raw20925step0 raw20925step0Labels = mixedMoment B raw20925step1 raw20925step1Labels := by
      have ha : raw20925step1 = (fun i j => raw20925step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20925step1 raw20925step0; decide +kernel
      have hl : raw20925step1Labels = raw20925step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20925step0 raw20925step0Labels permutation151 permutation2
    mixedMoment B raw20925step1 raw20925step1Labels = mixedMoment B raw20925step2 raw20925step2Labels := by
      have ha : raw20925step2 = -raw20925step1 := by apply Matrix.ext; change ∀ i j, raw20925step2 i j = -(raw20925step1 i j); unfold raw20925step2 raw20925step1; decide +kernel
      have hl : raw20925step2Labels = raw20925step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node908 node908Labels := by rfl

def raw20926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20926Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20926step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20926step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20926step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20926step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw20926step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20926step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20926step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20926 raw20926Labels = mixedMoment B node2060 node2060Labels := by
  calc
    mixedMoment B raw20926 raw20926Labels = mixedMoment B raw20926step0 raw20926step0Labels := by
      have hz : ∀ j, raw20926 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20926step0 = (fun i j => raw20926 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20926step0 raw20926; decide +kernel
      have hl : raw20926step0Labels = raw20926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20926 raw20926Labels permutation346 hz
    mixedMoment B raw20926step0 raw20926step0Labels = mixedMoment B raw20926step1 raw20926step1Labels := by
      have hz : ∀ j, raw20926step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20926step1 = (fun i j => raw20926step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20926step1 raw20926step0; decide +kernel
      have hl : raw20926step1Labels = raw20926step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20926step0 raw20926step0Labels permutation56 hz
    mixedMoment B raw20926step1 raw20926step1Labels = mixedMoment B raw20926step2 raw20926step2Labels := by
      have ha : raw20926step2 = (fun i j => raw20926step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20926step2 raw20926step1; decide +kernel
      have hl : raw20926step2Labels = raw20926step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20926step1 raw20926step1Labels permutation31 permutation2
    mixedMoment B raw20926step2 raw20926step2Labels = mixedMoment B raw20926step3 raw20926step3Labels := by
      have ha : raw20926step3 = -raw20926step2 := by apply Matrix.ext; change ∀ i j, raw20926step3 i j = -(raw20926step2 i j); unfold raw20926step3 raw20926step2; decide +kernel
      have hl : raw20926step3Labels = raw20926step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2060 node2060Labels := by rfl

def raw20927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20927Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20927step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20927step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20927 raw20927Labels = mixedMoment B node1128 node1128Labels := by
  calc
    mixedMoment B raw20927 raw20927Labels = mixedMoment B raw20927step0 raw20927step0Labels := by
      have hz : ∀ j, raw20927 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20927step0 = (fun i j => raw20927 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20927step0 raw20927; decide +kernel
      have hl : raw20927step0Labels = raw20927Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20927 raw20927Labels permutation265 hz
    mixedMoment B raw20927step0 raw20927step0Labels = mixedMoment B raw20927step1 raw20927step1Labels := by
      have ha : raw20927step1 = (fun i j => raw20927step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20927step1 raw20927step0; decide +kernel
      have hl : raw20927step1Labels = raw20927step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20927step0 raw20927step0Labels permutation38 permutation2
    _ = mixedMoment B node1128 node1128Labels := by rfl

def raw20928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20928Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20928step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20928step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20928step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20928 raw20928Labels = mixedMoment B node1143 node1143Labels := by
  calc
    mixedMoment B raw20928 raw20928Labels = mixedMoment B raw20928step0 raw20928step0Labels := by
      have hz : ∀ j, raw20928 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20928step0 = (fun i j => raw20928 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20928step0 raw20928; decide +kernel
      have hl : raw20928step0Labels = raw20928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20928 raw20928Labels permutation346 hz
    mixedMoment B raw20928step0 raw20928step0Labels = mixedMoment B raw20928step1 raw20928step1Labels := by
      have hz : ∀ j, raw20928step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20928step1 = (fun i j => raw20928step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20928step1 raw20928step0; decide +kernel
      have hl : raw20928step1Labels = raw20928step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20928step0 raw20928step0Labels permutation56 hz
    _ = mixedMoment B node1143 node1143Labels := by rfl

def raw20929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20929Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20929step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20929step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20929step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20929step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw20929step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20929step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw20929step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20929 raw20929Labels = mixedMoment B node934 node934Labels := by
  calc
    mixedMoment B raw20929 raw20929Labels = mixedMoment B raw20929step0 raw20929step0Labels := by
      have hz : ∀ j, raw20929 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20929step0 = (fun i j => raw20929 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20929step0 raw20929; decide +kernel
      have hl : raw20929step0Labels = raw20929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20929 raw20929Labels permutation346 hz
    mixedMoment B raw20929step0 raw20929step0Labels = mixedMoment B raw20929step1 raw20929step1Labels := by
      have hz : ∀ j, raw20929step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20929step1 = (fun i j => raw20929step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20929step1 raw20929step0; decide +kernel
      have hl : raw20929step1Labels = raw20929step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20929step0 raw20929step0Labels permutation56 hz
    mixedMoment B raw20929step1 raw20929step1Labels = mixedMoment B raw20929step2 raw20929step2Labels := by
      have ha : raw20929step2 = (fun i j => raw20929step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20929step2 raw20929step1; decide +kernel
      have hl : raw20929step2Labels = raw20929step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20929step1 raw20929step1Labels permutation31 permutation2
    mixedMoment B raw20929step2 raw20929step2Labels = mixedMoment B raw20929step3 raw20929step3Labels := by
      have ha : raw20929step3 = -raw20929step2 := by apply Matrix.ext; change ∀ i j, raw20929step3 i j = -(raw20929step2 i j); unfold raw20929step3 raw20929step2; decide +kernel
      have hl : raw20929step3Labels = raw20929step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node934 node934Labels := by rfl

def raw20930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20930step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20930step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20930step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20930step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20930step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20930 raw20930Labels = mixedMoment B node4140 node4140Labels := by
  calc
    mixedMoment B raw20930 raw20930Labels = mixedMoment B raw20930step0 raw20930step0Labels := by
      have hz : ∀ j, raw20930 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20930step0 = (fun i j => raw20930 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20930step0 raw20930; decide +kernel
      have hl : raw20930step0Labels = raw20930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20930 raw20930Labels permutation346 hz
    mixedMoment B raw20930step0 raw20930step0Labels = mixedMoment B raw20930step1 raw20930step1Labels := by
      have ha : raw20930step1 = (fun i j => raw20930step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20930step1 raw20930step0; decide +kernel
      have hl : raw20930step1Labels = raw20930step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20930step0 raw20930step0Labels permutation40 permutation3
    mixedMoment B raw20930step1 raw20930step1Labels = mixedMoment B raw20930step2 raw20930step2Labels := by
      have ha : raw20930step2 = raw20930step1 := by apply Matrix.ext; unfold raw20930step2 raw20930step1; decide +kernel
      have hl : raw20930step1Labels = labelEmbedding6 ∘ raw20930step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20930step1 raw20930step1Labels raw20930step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4140 node4140Labels := by rfl

def raw20931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20931Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20931step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20931step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20931step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20931step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20931 raw20931Labels = mixedMoment B node4521 node4521Labels := by
  calc
    mixedMoment B raw20931 raw20931Labels = mixedMoment B raw20931step0 raw20931step0Labels := by
      have ha : raw20931step0 = (fun i j => raw20931 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20931step0 raw20931; decide +kernel
      have hl : raw20931step0Labels = raw20931Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20931 raw20931Labels permutation184 permutation3
    mixedMoment B raw20931step0 raw20931step0Labels = mixedMoment B raw20931step1 raw20931step1Labels := by
      have ha : raw20931step1 = raw20931step0 := by apply Matrix.ext; unfold raw20931step1 raw20931step0; decide +kernel
      have hl : raw20931step0Labels = labelEmbedding6 ∘ raw20931step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20931step0 raw20931step0Labels raw20931step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4521 node4521Labels := by rfl

def raw20932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20932step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20932step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20932step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20932step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20932step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20932 raw20932Labels = mixedMoment B node4514 node4514Labels := by
  calc
    mixedMoment B raw20932 raw20932Labels = mixedMoment B raw20932step0 raw20932step0Labels := by
      have hz : ∀ j, raw20932 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20932step0 = (fun i j => raw20932 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20932step0 raw20932; decide +kernel
      have hl : raw20932step0Labels = raw20932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20932 raw20932Labels permutation346 hz
    mixedMoment B raw20932step0 raw20932step0Labels = mixedMoment B raw20932step1 raw20932step1Labels := by
      have ha : raw20932step1 = (fun i j => raw20932step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20932step1 raw20932step0; decide +kernel
      have hl : raw20932step1Labels = raw20932step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20932step0 raw20932step0Labels permutation40 permutation3
    mixedMoment B raw20932step1 raw20932step1Labels = mixedMoment B raw20932step2 raw20932step2Labels := by
      have ha : raw20932step2 = raw20932step1 := by apply Matrix.ext; unfold raw20932step2 raw20932step1; decide +kernel
      have hl : raw20932step1Labels = labelEmbedding6 ∘ raw20932step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20932step1 raw20932step1Labels raw20932step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4514 node4514Labels := by rfl

def raw20933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20933step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20933step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20933step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20933step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20933step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20933 raw20933Labels = mixedMoment B node4140 node4140Labels := by
  calc
    mixedMoment B raw20933 raw20933Labels = mixedMoment B raw20933step0 raw20933step0Labels := by
      have hz : ∀ j, raw20933 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20933step0 = (fun i j => raw20933 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20933step0 raw20933; decide +kernel
      have hl : raw20933step0Labels = raw20933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20933 raw20933Labels permutation265 hz
    mixedMoment B raw20933step0 raw20933step0Labels = mixedMoment B raw20933step1 raw20933step1Labels := by
      have ha : raw20933step1 = (fun i j => raw20933step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20933step1 raw20933step0; decide +kernel
      have hl : raw20933step1Labels = raw20933step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20933step0 raw20933step0Labels permutation40 permutation3
    mixedMoment B raw20933step1 raw20933step1Labels = mixedMoment B raw20933step2 raw20933step2Labels := by
      have ha : raw20933step2 = raw20933step1 := by apply Matrix.ext; unfold raw20933step2 raw20933step1; decide +kernel
      have hl : raw20933step1Labels = labelEmbedding6 ∘ raw20933step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20933step1 raw20933step1Labels raw20933step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4140 node4140Labels := by rfl

def raw20934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20934Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20934step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20934step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20934step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20934step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20934 raw20934Labels = mixedMoment B node4521 node4521Labels := by
  calc
    mixedMoment B raw20934 raw20934Labels = mixedMoment B raw20934step0 raw20934step0Labels := by
      have ha : raw20934step0 = (fun i j => raw20934 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20934step0 raw20934; decide +kernel
      have hl : raw20934step0Labels = raw20934Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20934 raw20934Labels permutation160 permutation3
    mixedMoment B raw20934step0 raw20934step0Labels = mixedMoment B raw20934step1 raw20934step1Labels := by
      have ha : raw20934step1 = raw20934step0 := by apply Matrix.ext; unfold raw20934step1 raw20934step0; decide +kernel
      have hl : raw20934step0Labels = labelEmbedding6 ∘ raw20934step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20934step0 raw20934step0Labels raw20934step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4521 node4521Labels := by rfl

def raw20935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20935step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20935step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20935step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20935step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20935step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20935 raw20935Labels = mixedMoment B node4514 node4514Labels := by
  calc
    mixedMoment B raw20935 raw20935Labels = mixedMoment B raw20935step0 raw20935step0Labels := by
      have hz : ∀ j, raw20935 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20935step0 = (fun i j => raw20935 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20935step0 raw20935; decide +kernel
      have hl : raw20935step0Labels = raw20935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20935 raw20935Labels permutation265 hz
    mixedMoment B raw20935step0 raw20935step0Labels = mixedMoment B raw20935step1 raw20935step1Labels := by
      have ha : raw20935step1 = (fun i j => raw20935step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20935step1 raw20935step0; decide +kernel
      have hl : raw20935step1Labels = raw20935step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20935step0 raw20935step0Labels permutation40 permutation3
    mixedMoment B raw20935step1 raw20935step1Labels = mixedMoment B raw20935step2 raw20935step2Labels := by
      have ha : raw20935step2 = raw20935step1 := by apply Matrix.ext; unfold raw20935step2 raw20935step1; decide +kernel
      have hl : raw20935step1Labels = labelEmbedding6 ∘ raw20935step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20935step1 raw20935step1Labels raw20935step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4514 node4514Labels := by rfl

def raw20936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20936step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20936step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20936step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20936step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20936step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20936step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20936 raw20936Labels = mixedMoment B node4174 node4174Labels := by
  calc
    mixedMoment B raw20936 raw20936Labels = mixedMoment B raw20936step0 raw20936step0Labels := by
      have hz : ∀ j, raw20936 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20936step0 = (fun i j => raw20936 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20936step0 raw20936; decide +kernel
      have hl : raw20936step0Labels = raw20936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20936 raw20936Labels permutation346 hz
    mixedMoment B raw20936step0 raw20936step0Labels = mixedMoment B raw20936step1 raw20936step1Labels := by
      have hz : ∀ j, raw20936step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20936step1 = (fun i j => raw20936step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20936step1 raw20936step0; decide +kernel
      have hl : raw20936step1Labels = raw20936step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20936step0 raw20936step0Labels permutation56 hz
    mixedMoment B raw20936step1 raw20936step1Labels = mixedMoment B raw20936step2 raw20936step2Labels := by
      have ha : raw20936step2 = (fun i j => raw20936step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20936step2 raw20936step1; decide +kernel
      have hl : raw20936step2Labels = raw20936step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20936step1 raw20936step1Labels permutation8 permutation3
    mixedMoment B raw20936step2 raw20936step2Labels = mixedMoment B raw20936step3 raw20936step3Labels := by
      have ha : raw20936step3 = raw20936step2 := by apply Matrix.ext; unfold raw20936step3 raw20936step2; decide +kernel
      have hl : raw20936step2Labels = labelEmbedding6 ∘ raw20936step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20936step2 raw20936step2Labels raw20936step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4174 node4174Labels := by rfl

def raw20937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20937Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20937step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20937step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20937step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20937step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20937 raw20937Labels = mixedMoment B node4543 node4543Labels := by
  calc
    mixedMoment B raw20937 raw20937Labels = mixedMoment B raw20937step0 raw20937step0Labels := by
      have hz : ∀ j, raw20937 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20937step0 = (fun i j => raw20937 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20937step0 raw20937; decide +kernel
      have hl : raw20937step0Labels = raw20937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20937 raw20937Labels permutation346 hz
    mixedMoment B raw20937step0 raw20937step0Labels = mixedMoment B raw20937step1 raw20937step1Labels := by
      have ha : raw20937step1 = (fun i j => raw20937step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20937step1 raw20937step0; decide +kernel
      have hl : raw20937step1Labels = raw20937step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20937step0 raw20937step0Labels permutation32 permutation3
    mixedMoment B raw20937step1 raw20937step1Labels = mixedMoment B raw20937step2 raw20937step2Labels := by
      have ha : raw20937step2 = raw20937step1 := by apply Matrix.ext; unfold raw20937step2 raw20937step1; decide +kernel
      have hl : raw20937step1Labels = labelEmbedding6 ∘ raw20937step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20937step1 raw20937step1Labels raw20937step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4543 node4543Labels := by rfl

def raw20938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20938step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20938step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20938step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20938step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20938 raw20938Labels = mixedMoment B node4543 node4543Labels := by
  calc
    mixedMoment B raw20938 raw20938Labels = mixedMoment B raw20938step0 raw20938step0Labels := by
      have hz : ∀ j, raw20938 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20938step0 = (fun i j => raw20938 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20938step0 raw20938; decide +kernel
      have hl : raw20938step0Labels = raw20938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20938 raw20938Labels permutation265 hz
    mixedMoment B raw20938step0 raw20938step0Labels = mixedMoment B raw20938step1 raw20938step1Labels := by
      have ha : raw20938step1 = (fun i j => raw20938step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20938step1 raw20938step0; decide +kernel
      have hl : raw20938step1Labels = raw20938step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20938step0 raw20938step0Labels permutation32 permutation3
    mixedMoment B raw20938step1 raw20938step1Labels = mixedMoment B raw20938step2 raw20938step2Labels := by
      have ha : raw20938step2 = raw20938step1 := by apply Matrix.ext; unfold raw20938step2 raw20938step1; decide +kernel
      have hl : raw20938step1Labels = labelEmbedding6 ∘ raw20938step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20938step1 raw20938step1Labels raw20938step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4543 node4543Labels := by rfl

def raw20939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20939step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20939step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20939step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw20939step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20939step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw20939step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20939 raw20939Labels = mixedMoment B node4147 node4147Labels := by
  calc
    mixedMoment B raw20939 raw20939Labels = mixedMoment B raw20939step0 raw20939step0Labels := by
      have hz : ∀ j, raw20939 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20939step0 = (fun i j => raw20939 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20939step0 raw20939; decide +kernel
      have hl : raw20939step0Labels = raw20939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20939 raw20939Labels permutation346 hz
    mixedMoment B raw20939step0 raw20939step0Labels = mixedMoment B raw20939step1 raw20939step1Labels := by
      have hz : ∀ j, raw20939step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20939step1 = (fun i j => raw20939step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20939step1 raw20939step0; decide +kernel
      have hl : raw20939step1Labels = raw20939step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20939step0 raw20939step0Labels permutation56 hz
    mixedMoment B raw20939step1 raw20939step1Labels = mixedMoment B raw20939step2 raw20939step2Labels := by
      have ha : raw20939step2 = (fun i j => raw20939step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20939step2 raw20939step1; decide +kernel
      have hl : raw20939step2Labels = raw20939step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20939step1 raw20939step1Labels permutation8 permutation3
    mixedMoment B raw20939step2 raw20939step2Labels = mixedMoment B raw20939step3 raw20939step3Labels := by
      have ha : raw20939step3 = raw20939step2 := by apply Matrix.ext; unfold raw20939step3 raw20939step2; decide +kernel
      have hl : raw20939step2Labels = labelEmbedding6 ∘ raw20939step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20939step2 raw20939step2Labels raw20939step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4147 node4147Labels := by rfl

def raw20940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20940step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw20940step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20940step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw20940step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20940 raw20940Labels = mixedMoment B node4525 node4525Labels := by
  calc
    mixedMoment B raw20940 raw20940Labels = mixedMoment B raw20940step0 raw20940step0Labels := by
      have hz : ∀ j, raw20940 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20940step0 = (fun i j => raw20940 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20940step0 raw20940; decide +kernel
      have hl : raw20940step0Labels = raw20940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20940 raw20940Labels permutation346 hz
    mixedMoment B raw20940step0 raw20940step0Labels = mixedMoment B raw20940step1 raw20940step1Labels := by
      have ha : raw20940step1 = (fun i j => raw20940step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20940step1 raw20940step0; decide +kernel
      have hl : raw20940step1Labels = raw20940step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20940step0 raw20940step0Labels permutation32 permutation3
    mixedMoment B raw20940step1 raw20940step1Labels = mixedMoment B raw20940step2 raw20940step2Labels := by
      have ha : raw20940step2 = raw20940step1 := by apply Matrix.ext; unfold raw20940step2 raw20940step1; decide +kernel
      have hl : raw20940step1Labels = labelEmbedding6 ∘ raw20940step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20940step1 raw20940step1Labels raw20940step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4525 node4525Labels := by rfl

def raw20941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20941step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw20941step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20941step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw20941step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20941 raw20941Labels = mixedMoment B node4525 node4525Labels := by
  calc
    mixedMoment B raw20941 raw20941Labels = mixedMoment B raw20941step0 raw20941step0Labels := by
      have hz : ∀ j, raw20941 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20941step0 = (fun i j => raw20941 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20941step0 raw20941; decide +kernel
      have hl : raw20941step0Labels = raw20941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20941 raw20941Labels permutation265 hz
    mixedMoment B raw20941step0 raw20941step0Labels = mixedMoment B raw20941step1 raw20941step1Labels := by
      have ha : raw20941step1 = (fun i j => raw20941step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20941step1 raw20941step0; decide +kernel
      have hl : raw20941step1Labels = raw20941step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20941step0 raw20941step0Labels permutation32 permutation3
    mixedMoment B raw20941step1 raw20941step1Labels = mixedMoment B raw20941step2 raw20941step2Labels := by
      have ha : raw20941step2 = raw20941step1 := by apply Matrix.ext; unfold raw20941step2 raw20941step1; decide +kernel
      have hl : raw20941step1Labels = labelEmbedding6 ∘ raw20941step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20941step1 raw20941step1Labels raw20941step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4525 node4525Labels := by rfl

def raw20942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20942step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20942step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20942step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw20942step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20942step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw20942step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20942 raw20942Labels = mixedMoment B node4519 node4519Labels := by
  calc
    mixedMoment B raw20942 raw20942Labels = mixedMoment B raw20942step0 raw20942step0Labels := by
      have hz : ∀ j, raw20942 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20942step0 = (fun i j => raw20942 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20942step0 raw20942; decide +kernel
      have hl : raw20942step0Labels = raw20942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20942 raw20942Labels permutation346 hz
    mixedMoment B raw20942step0 raw20942step0Labels = mixedMoment B raw20942step1 raw20942step1Labels := by
      have hz : ∀ j, raw20942step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20942step1 = (fun i j => raw20942step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20942step1 raw20942step0; decide +kernel
      have hl : raw20942step1Labels = raw20942step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20942step0 raw20942step0Labels permutation56 hz
    mixedMoment B raw20942step1 raw20942step1Labels = mixedMoment B raw20942step2 raw20942step2Labels := by
      have ha : raw20942step2 = (fun i j => raw20942step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20942step2 raw20942step1; decide +kernel
      have hl : raw20942step2Labels = raw20942step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20942step1 raw20942step1Labels permutation8 permutation3
    mixedMoment B raw20942step2 raw20942step2Labels = mixedMoment B raw20942step3 raw20942step3Labels := by
      have ha : raw20942step3 = raw20942step2 := by apply Matrix.ext; unfold raw20942step3 raw20942step2; decide +kernel
      have hl : raw20942step2Labels = labelEmbedding6 ∘ raw20942step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20942step2 raw20942step2Labels raw20942step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4519 node4519Labels := by rfl

def raw20943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20943Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20943step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20943step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20943step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![4, 0, -4]]
def raw20943step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20943step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![4, 0, -4]]
def raw20943step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20943 raw20943Labels = mixedMoment B node4142 node4142Labels := by
  calc
    mixedMoment B raw20943 raw20943Labels = mixedMoment B raw20943step0 raw20943step0Labels := by
      have hz : ∀ j, raw20943 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20943step0 = (fun i j => raw20943 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20943step0 raw20943; decide +kernel
      have hl : raw20943step0Labels = raw20943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20943 raw20943Labels permutation346 hz
    mixedMoment B raw20943step0 raw20943step0Labels = mixedMoment B raw20943step1 raw20943step1Labels := by
      have hz : ∀ j, raw20943step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20943step1 = (fun i j => raw20943step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20943step1 raw20943step0; decide +kernel
      have hl : raw20943step1Labels = raw20943step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20943step0 raw20943step0Labels permutation56 hz
    mixedMoment B raw20943step1 raw20943step1Labels = mixedMoment B raw20943step2 raw20943step2Labels := by
      have ha : raw20943step2 = (fun i j => raw20943step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20943step2 raw20943step1; decide +kernel
      have hl : raw20943step2Labels = raw20943step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20943step1 raw20943step1Labels permutation8 permutation3
    mixedMoment B raw20943step2 raw20943step2Labels = mixedMoment B raw20943step3 raw20943step3Labels := by
      have ha : raw20943step3 = raw20943step2 := by apply Matrix.ext; unfold raw20943step3 raw20943step2; decide +kernel
      have hl : raw20943step2Labels = labelEmbedding6 ∘ raw20943step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20943step2 raw20943step2Labels raw20943step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4142 node4142Labels := by rfl

def raw20944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20944Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20944step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20944step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20944step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20944step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20944step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20944step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20944 raw20944Labels = mixedMoment B node4202 node4202Labels := by
  calc
    mixedMoment B raw20944 raw20944Labels = mixedMoment B raw20944step0 raw20944step0Labels := by
      have hz : ∀ j, raw20944 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20944step0 = (fun i j => raw20944 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20944step0 raw20944; decide +kernel
      have hl : raw20944step0Labels = raw20944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20944 raw20944Labels permutation346 hz
    mixedMoment B raw20944step0 raw20944step0Labels = mixedMoment B raw20944step1 raw20944step1Labels := by
      have ha : raw20944step1 = (fun i j => raw20944step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20944step1 raw20944step0; decide +kernel
      have hl : raw20944step1Labels = raw20944step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20944step0 raw20944step0Labels permutation151 permutation3
    mixedMoment B raw20944step1 raw20944step1Labels = mixedMoment B raw20944step2 raw20944step2Labels := by
      have ha : raw20944step2 = -raw20944step1 := by apply Matrix.ext; change ∀ i j, raw20944step2 i j = -(raw20944step1 i j); unfold raw20944step2 raw20944step1; decide +kernel
      have hl : raw20944step2Labels = raw20944step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20944step2 raw20944step2Labels = mixedMoment B raw20944step3 raw20944step3Labels := by
      have ha : raw20944step3 = raw20944step2 := by apply Matrix.ext; unfold raw20944step3 raw20944step2; decide +kernel
      have hl : raw20944step2Labels = labelEmbedding6 ∘ raw20944step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20944step2 raw20944step2Labels raw20944step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4202 node4202Labels := by rfl

def raw20945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20945Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20945step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20945step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20945step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20945step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20945step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20945step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20945 raw20945Labels = mixedMoment B node4202 node4202Labels := by
  calc
    mixedMoment B raw20945 raw20945Labels = mixedMoment B raw20945step0 raw20945step0Labels := by
      have hz : ∀ j, raw20945 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20945step0 = (fun i j => raw20945 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20945step0 raw20945; decide +kernel
      have hl : raw20945step0Labels = raw20945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20945 raw20945Labels permutation265 hz
    mixedMoment B raw20945step0 raw20945step0Labels = mixedMoment B raw20945step1 raw20945step1Labels := by
      have ha : raw20945step1 = (fun i j => raw20945step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20945step1 raw20945step0; decide +kernel
      have hl : raw20945step1Labels = raw20945step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20945step0 raw20945step0Labels permutation151 permutation3
    mixedMoment B raw20945step1 raw20945step1Labels = mixedMoment B raw20945step2 raw20945step2Labels := by
      have ha : raw20945step2 = -raw20945step1 := by apply Matrix.ext; change ∀ i j, raw20945step2 i j = -(raw20945step1 i j); unfold raw20945step2 raw20945step1; decide +kernel
      have hl : raw20945step2Labels = raw20945step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20945step2 raw20945step2Labels = mixedMoment B raw20945step3 raw20945step3Labels := by
      have ha : raw20945step3 = raw20945step2 := by apply Matrix.ext; unfold raw20945step3 raw20945step2; decide +kernel
      have hl : raw20945step2Labels = labelEmbedding6 ∘ raw20945step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20945step2 raw20945step2Labels raw20945step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4202 node4202Labels := by rfl

def raw20946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20946Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20946step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20946step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20946step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20946step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, -1, 2], ![-4, 2, 2]]
def raw20946step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20946step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw20946step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20946step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw20946step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20946 raw20946Labels = mixedMoment B node4225 node4225Labels := by
  calc
    mixedMoment B raw20946 raw20946Labels = mixedMoment B raw20946step0 raw20946step0Labels := by
      have hz : ∀ j, raw20946 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20946step0 = (fun i j => raw20946 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20946step0 raw20946; decide +kernel
      have hl : raw20946step0Labels = raw20946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20946 raw20946Labels permutation346 hz
    mixedMoment B raw20946step0 raw20946step0Labels = mixedMoment B raw20946step1 raw20946step1Labels := by
      have hz : ∀ j, raw20946step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20946step1 = (fun i j => raw20946step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20946step1 raw20946step0; decide +kernel
      have hl : raw20946step1Labels = raw20946step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20946step0 raw20946step0Labels permutation56 hz
    mixedMoment B raw20946step1 raw20946step1Labels = mixedMoment B raw20946step2 raw20946step2Labels := by
      have ha : raw20946step2 = (fun i j => raw20946step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20946step2 raw20946step1; decide +kernel
      have hl : raw20946step2Labels = raw20946step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20946step1 raw20946step1Labels permutation31 permutation3
    mixedMoment B raw20946step2 raw20946step2Labels = mixedMoment B raw20946step3 raw20946step3Labels := by
      have ha : raw20946step3 = -raw20946step2 := by apply Matrix.ext; change ∀ i j, raw20946step3 i j = -(raw20946step2 i j); unfold raw20946step3 raw20946step2; decide +kernel
      have hl : raw20946step3Labels = raw20946step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20946step3 raw20946step3Labels = mixedMoment B raw20946step4 raw20946step4Labels := by
      have ha : raw20946step4 = raw20946step3 := by apply Matrix.ext; unfold raw20946step4 raw20946step3; decide +kernel
      have hl : raw20946step3Labels = labelEmbedding6 ∘ raw20946step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20946step3 raw20946step3Labels raw20946step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4225 node4225Labels := by rfl

def raw20947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20947Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20947step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20947step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20947step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20947 raw20947Labels = mixedMoment B node568 node568Labels := by
  calc
    mixedMoment B raw20947 raw20947Labels = mixedMoment B raw20947step0 raw20947step0Labels := by
      have hz : ∀ j, raw20947 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20947step0 = (fun i j => raw20947 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20947step0 raw20947; decide +kernel
      have hl : raw20947step0Labels = raw20947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20947 raw20947Labels permutation346 hz
    mixedMoment B raw20947step0 raw20947step0Labels = mixedMoment B raw20947step1 raw20947step1Labels := by
      have ha : raw20947step1 = (fun i j => raw20947step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20947step1 raw20947step0; decide +kernel
      have hl : raw20947step1Labels = raw20947step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20947step0 raw20947step0Labels permutation40 permutation3
    _ = mixedMoment B node568 node568Labels := by rfl

def raw20948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20948Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20948step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20948step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20948 raw20948Labels = mixedMoment B node1105 node1105Labels := by
  calc
    mixedMoment B raw20948 raw20948Labels = mixedMoment B raw20948step0 raw20948step0Labels := by
      have ha : raw20948step0 = (fun i j => raw20948 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20948step0 raw20948; decide +kernel
      have hl : raw20948step0Labels = raw20948Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20948 raw20948Labels permutation184 permutation3
    _ = mixedMoment B node1105 node1105Labels := by rfl

def raw20949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20949Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20949step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20949step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20949 raw20949Labels = mixedMoment B node1098 node1098Labels := by
  calc
    mixedMoment B raw20949 raw20949Labels = mixedMoment B raw20949step0 raw20949step0Labels := by
      have hz : ∀ j, raw20949 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20949step0 = (fun i j => raw20949 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20949step0 raw20949; decide +kernel
      have hl : raw20949step0Labels = raw20949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20949 raw20949Labels permutation346 hz
    mixedMoment B raw20949step0 raw20949step0Labels = mixedMoment B raw20949step1 raw20949step1Labels := by
      have ha : raw20949step1 = (fun i j => raw20949step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20949step1 raw20949step0; decide +kernel
      have hl : raw20949step1Labels = raw20949step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20949step0 raw20949step0Labels permutation40 permutation3
    _ = mixedMoment B node1098 node1098Labels := by rfl

def raw20950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20950Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20950step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20950step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20950step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20950 raw20950Labels = mixedMoment B node568 node568Labels := by
  calc
    mixedMoment B raw20950 raw20950Labels = mixedMoment B raw20950step0 raw20950step0Labels := by
      have hz : ∀ j, raw20950 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20950step0 = (fun i j => raw20950 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20950step0 raw20950; decide +kernel
      have hl : raw20950step0Labels = raw20950Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20950 raw20950Labels permutation265 hz
    mixedMoment B raw20950step0 raw20950step0Labels = mixedMoment B raw20950step1 raw20950step1Labels := by
      have ha : raw20950step1 = (fun i j => raw20950step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20950step1 raw20950step0; decide +kernel
      have hl : raw20950step1Labels = raw20950step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20950step0 raw20950step0Labels permutation40 permutation3
    _ = mixedMoment B node568 node568Labels := by rfl

def raw20951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20951Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20951step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20951step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20951 raw20951Labels = mixedMoment B node1105 node1105Labels := by
  calc
    mixedMoment B raw20951 raw20951Labels = mixedMoment B raw20951step0 raw20951step0Labels := by
      have ha : raw20951step0 = (fun i j => raw20951 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20951step0 raw20951; decide +kernel
      have hl : raw20951step0Labels = raw20951Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20951 raw20951Labels permutation160 permutation3
    _ = mixedMoment B node1105 node1105Labels := by rfl

def raw20952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20952Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20952step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20952step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20952 raw20952Labels = mixedMoment B node1098 node1098Labels := by
  calc
    mixedMoment B raw20952 raw20952Labels = mixedMoment B raw20952step0 raw20952step0Labels := by
      have hz : ∀ j, raw20952 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20952step0 = (fun i j => raw20952 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20952step0 raw20952; decide +kernel
      have hl : raw20952step0Labels = raw20952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20952 raw20952Labels permutation265 hz
    mixedMoment B raw20952step0 raw20952step0Labels = mixedMoment B raw20952step1 raw20952step1Labels := by
      have ha : raw20952step1 = (fun i j => raw20952step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20952step1 raw20952step0; decide +kernel
      have hl : raw20952step1Labels = raw20952step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20952step0 raw20952step0Labels permutation40 permutation3
    _ = mixedMoment B node1098 node1098Labels := by rfl

def raw20953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20953Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20953step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20953step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20953step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20953step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20953step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20953 raw20953Labels = mixedMoment B node602 node602Labels := by
  calc
    mixedMoment B raw20953 raw20953Labels = mixedMoment B raw20953step0 raw20953step0Labels := by
      have hz : ∀ j, raw20953 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20953step0 = (fun i j => raw20953 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20953step0 raw20953; decide +kernel
      have hl : raw20953step0Labels = raw20953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20953 raw20953Labels permutation346 hz
    mixedMoment B raw20953step0 raw20953step0Labels = mixedMoment B raw20953step1 raw20953step1Labels := by
      have hz : ∀ j, raw20953step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20953step1 = (fun i j => raw20953step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20953step1 raw20953step0; decide +kernel
      have hl : raw20953step1Labels = raw20953step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20953step0 raw20953step0Labels permutation56 hz
    mixedMoment B raw20953step1 raw20953step1Labels = mixedMoment B raw20953step2 raw20953step2Labels := by
      have ha : raw20953step2 = (fun i j => raw20953step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20953step2 raw20953step1; decide +kernel
      have hl : raw20953step2Labels = raw20953step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20953step1 raw20953step1Labels permutation8 permutation3
    _ = mixedMoment B node602 node602Labels := by rfl

def raw20954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20954Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20954step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20954step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20954 raw20954Labels = mixedMoment B node1128 node1128Labels := by
  calc
    mixedMoment B raw20954 raw20954Labels = mixedMoment B raw20954step0 raw20954step0Labels := by
      have hz : ∀ j, raw20954 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20954step0 = (fun i j => raw20954 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20954step0 raw20954; decide +kernel
      have hl : raw20954step0Labels = raw20954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20954 raw20954Labels permutation346 hz
    mixedMoment B raw20954step0 raw20954step0Labels = mixedMoment B raw20954step1 raw20954step1Labels := by
      have ha : raw20954step1 = (fun i j => raw20954step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20954step1 raw20954step0; decide +kernel
      have hl : raw20954step1Labels = raw20954step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20954step0 raw20954step0Labels permutation32 permutation3
    _ = mixedMoment B node1128 node1128Labels := by rfl

def raw20955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20955Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20955step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20955step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20955step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20955 raw20955Labels = mixedMoment B node1128 node1128Labels := by
  calc
    mixedMoment B raw20955 raw20955Labels = mixedMoment B raw20955step0 raw20955step0Labels := by
      have hz : ∀ j, raw20955 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20955step0 = (fun i j => raw20955 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20955step0 raw20955; decide +kernel
      have hl : raw20955step0Labels = raw20955Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20955 raw20955Labels permutation265 hz
    mixedMoment B raw20955step0 raw20955step0Labels = mixedMoment B raw20955step1 raw20955step1Labels := by
      have ha : raw20955step1 = (fun i j => raw20955step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20955step1 raw20955step0; decide +kernel
      have hl : raw20955step1Labels = raw20955step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20955step0 raw20955step0Labels permutation32 permutation3
    _ = mixedMoment B node1128 node1128Labels := by rfl

def raw20956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20956Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20956step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20956step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20956step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20956step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw20956step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20956 raw20956Labels = mixedMoment B node575 node575Labels := by
  calc
    mixedMoment B raw20956 raw20956Labels = mixedMoment B raw20956step0 raw20956step0Labels := by
      have hz : ∀ j, raw20956 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20956step0 = (fun i j => raw20956 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20956step0 raw20956; decide +kernel
      have hl : raw20956step0Labels = raw20956Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20956 raw20956Labels permutation346 hz
    mixedMoment B raw20956step0 raw20956step0Labels = mixedMoment B raw20956step1 raw20956step1Labels := by
      have hz : ∀ j, raw20956step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20956step1 = (fun i j => raw20956step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20956step1 raw20956step0; decide +kernel
      have hl : raw20956step1Labels = raw20956step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20956step0 raw20956step0Labels permutation56 hz
    mixedMoment B raw20956step1 raw20956step1Labels = mixedMoment B raw20956step2 raw20956step2Labels := by
      have ha : raw20956step2 = (fun i j => raw20956step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20956step2 raw20956step1; decide +kernel
      have hl : raw20956step2Labels = raw20956step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20956step1 raw20956step1Labels permutation8 permutation3
    _ = mixedMoment B node575 node575Labels := by rfl

def raw20957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20957Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20957step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20957step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw20957step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20957 raw20957Labels = mixedMoment B node1109 node1109Labels := by
  calc
    mixedMoment B raw20957 raw20957Labels = mixedMoment B raw20957step0 raw20957step0Labels := by
      have hz : ∀ j, raw20957 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20957step0 = (fun i j => raw20957 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20957step0 raw20957; decide +kernel
      have hl : raw20957step0Labels = raw20957Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20957 raw20957Labels permutation346 hz
    mixedMoment B raw20957step0 raw20957step0Labels = mixedMoment B raw20957step1 raw20957step1Labels := by
      have ha : raw20957step1 = (fun i j => raw20957step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20957step1 raw20957step0; decide +kernel
      have hl : raw20957step1Labels = raw20957step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20957step0 raw20957step0Labels permutation32 permutation3
    _ = mixedMoment B node1109 node1109Labels := by rfl

def raw20958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20958Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20958step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw20958step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20958 raw20958Labels = mixedMoment B node1109 node1109Labels := by
  calc
    mixedMoment B raw20958 raw20958Labels = mixedMoment B raw20958step0 raw20958step0Labels := by
      have hz : ∀ j, raw20958 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20958step0 = (fun i j => raw20958 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20958step0 raw20958; decide +kernel
      have hl : raw20958step0Labels = raw20958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20958 raw20958Labels permutation265 hz
    mixedMoment B raw20958step0 raw20958step0Labels = mixedMoment B raw20958step1 raw20958step1Labels := by
      have ha : raw20958step1 = (fun i j => raw20958step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20958step1 raw20958step0; decide +kernel
      have hl : raw20958step1Labels = raw20958step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20958step0 raw20958step0Labels permutation32 permutation3
    _ = mixedMoment B node1109 node1109Labels := by rfl

def raw20959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20959Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20959step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20959step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![2, -1, -1], ![3, -3, 0]]
def raw20959step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20959step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw20959step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20959 raw20959Labels = mixedMoment B node1103 node1103Labels := by
  calc
    mixedMoment B raw20959 raw20959Labels = mixedMoment B raw20959step0 raw20959step0Labels := by
      have hz : ∀ j, raw20959 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20959step0 = (fun i j => raw20959 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20959step0 raw20959; decide +kernel
      have hl : raw20959step0Labels = raw20959Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20959 raw20959Labels permutation346 hz
    mixedMoment B raw20959step0 raw20959step0Labels = mixedMoment B raw20959step1 raw20959step1Labels := by
      have hz : ∀ j, raw20959step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20959step1 = (fun i j => raw20959step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20959step1 raw20959step0; decide +kernel
      have hl : raw20959step1Labels = raw20959step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20959step0 raw20959step0Labels permutation56 hz
    mixedMoment B raw20959step1 raw20959step1Labels = mixedMoment B raw20959step2 raw20959step2Labels := by
      have ha : raw20959step2 = (fun i j => raw20959step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20959step2 raw20959step1; decide +kernel
      have hl : raw20959step2Labels = raw20959step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20959step1 raw20959step1Labels permutation8 permutation3
    _ = mixedMoment B node1103 node1103Labels := by rfl

def raw20960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20960Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20960step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20960step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20960step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20960step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![4, 0, -4]]
def raw20960step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20960 raw20960Labels = mixedMoment B node570 node570Labels := by
  calc
    mixedMoment B raw20960 raw20960Labels = mixedMoment B raw20960step0 raw20960step0Labels := by
      have hz : ∀ j, raw20960 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20960step0 = (fun i j => raw20960 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20960step0 raw20960; decide +kernel
      have hl : raw20960step0Labels = raw20960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20960 raw20960Labels permutation346 hz
    mixedMoment B raw20960step0 raw20960step0Labels = mixedMoment B raw20960step1 raw20960step1Labels := by
      have hz : ∀ j, raw20960step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20960step1 = (fun i j => raw20960step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20960step1 raw20960step0; decide +kernel
      have hl : raw20960step1Labels = raw20960step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20960step0 raw20960step0Labels permutation56 hz
    mixedMoment B raw20960step1 raw20960step1Labels = mixedMoment B raw20960step2 raw20960step2Labels := by
      have ha : raw20960step2 = (fun i j => raw20960step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20960step2 raw20960step1; decide +kernel
      have hl : raw20960step2Labels = raw20960step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20960step1 raw20960step1Labels permutation8 permutation3
    _ = mixedMoment B node570 node570Labels := by rfl

def raw20961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20961Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20961step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20961step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20961step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20961step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20961 raw20961Labels = mixedMoment B node705 node705Labels := by
  calc
    mixedMoment B raw20961 raw20961Labels = mixedMoment B raw20961step0 raw20961step0Labels := by
      have hz : ∀ j, raw20961 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20961step0 = (fun i j => raw20961 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20961step0 raw20961; decide +kernel
      have hl : raw20961step0Labels = raw20961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20961 raw20961Labels permutation346 hz
    mixedMoment B raw20961step0 raw20961step0Labels = mixedMoment B raw20961step1 raw20961step1Labels := by
      have ha : raw20961step1 = (fun i j => raw20961step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20961step1 raw20961step0; decide +kernel
      have hl : raw20961step1Labels = raw20961step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20961step0 raw20961step0Labels permutation151 permutation3
    mixedMoment B raw20961step1 raw20961step1Labels = mixedMoment B raw20961step2 raw20961step2Labels := by
      have ha : raw20961step2 = -raw20961step1 := by apply Matrix.ext; change ∀ i j, raw20961step2 i j = -(raw20961step1 i j); unfold raw20961step2 raw20961step1; decide +kernel
      have hl : raw20961step2Labels = raw20961step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node705 node705Labels := by rfl

def raw20962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20962Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20962step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20962step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20962step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20962step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20962 raw20962Labels = mixedMoment B node705 node705Labels := by
  calc
    mixedMoment B raw20962 raw20962Labels = mixedMoment B raw20962step0 raw20962step0Labels := by
      have hz : ∀ j, raw20962 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20962step0 = (fun i j => raw20962 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20962step0 raw20962; decide +kernel
      have hl : raw20962step0Labels = raw20962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20962 raw20962Labels permutation265 hz
    mixedMoment B raw20962step0 raw20962step0Labels = mixedMoment B raw20962step1 raw20962step1Labels := by
      have ha : raw20962step1 = (fun i j => raw20962step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20962step1 raw20962step0; decide +kernel
      have hl : raw20962step1Labels = raw20962step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20962step0 raw20962step0Labels permutation151 permutation3
    mixedMoment B raw20962step1 raw20962step1Labels = mixedMoment B raw20962step2 raw20962step2Labels := by
      have ha : raw20962step2 = -raw20962step1 := by apply Matrix.ext; change ∀ i j, raw20962step2 i j = -(raw20962step1 i j); unfold raw20962step2 raw20962step1; decide +kernel
      have hl : raw20962step2Labels = raw20962step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node705 node705Labels := by rfl

def raw20963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20963Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20963step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20963step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, 0, -1], ![4, -4, 0]]
def raw20963step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20963step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, -1, 2], ![-4, 2, 2]]
def raw20963step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20963step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw20963step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20963 raw20963Labels = mixedMoment B node726 node726Labels := by
  calc
    mixedMoment B raw20963 raw20963Labels = mixedMoment B raw20963step0 raw20963step0Labels := by
      have hz : ∀ j, raw20963 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20963step0 = (fun i j => raw20963 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20963step0 raw20963; decide +kernel
      have hl : raw20963step0Labels = raw20963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20963 raw20963Labels permutation346 hz
    mixedMoment B raw20963step0 raw20963step0Labels = mixedMoment B raw20963step1 raw20963step1Labels := by
      have hz : ∀ j, raw20963step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20963step1 = (fun i j => raw20963step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20963step1 raw20963step0; decide +kernel
      have hl : raw20963step1Labels = raw20963step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20963step0 raw20963step0Labels permutation56 hz
    mixedMoment B raw20963step1 raw20963step1Labels = mixedMoment B raw20963step2 raw20963step2Labels := by
      have ha : raw20963step2 = (fun i j => raw20963step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20963step2 raw20963step1; decide +kernel
      have hl : raw20963step2Labels = raw20963step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20963step1 raw20963step1Labels permutation31 permutation3
    mixedMoment B raw20963step2 raw20963step2Labels = mixedMoment B raw20963step3 raw20963step3Labels := by
      have ha : raw20963step3 = -raw20963step2 := by apply Matrix.ext; change ∀ i j, raw20963step3 i j = -(raw20963step2 i j); unfold raw20963step3 raw20963step2; decide +kernel
      have hl : raw20963step3Labels = raw20963step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node726 node726Labels := by rfl

def raw20964 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20964Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20964step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20964step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20964step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20964step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20964 raw20964Labels = mixedMoment B node4442 node4442Labels := by
  calc
    mixedMoment B raw20964 raw20964Labels = mixedMoment B raw20964step0 raw20964step0Labels := by
      have hz : ∀ j, raw20964 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20964step0 = (fun i j => raw20964 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20964step0 raw20964; decide +kernel
      have hl : raw20964step0Labels = raw20964Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20964 raw20964Labels permutation346 hz
    mixedMoment B raw20964step0 raw20964step0Labels = mixedMoment B raw20964step1 raw20964step1Labels := by
      have ha : raw20964step1 = (fun i j => raw20964step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20964step1 raw20964step0; decide +kernel
      have hl : raw20964step1Labels = raw20964step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20964step0 raw20964step0Labels permutation32 permutation7
    mixedMoment B raw20964step1 raw20964step1Labels = mixedMoment B raw20964step2 raw20964step2Labels := by
      have ha : raw20964step2 = raw20964step1 := by apply Matrix.ext; unfold raw20964step2 raw20964step1; decide +kernel
      have hl : raw20964step1Labels = labelEmbedding10 ∘ raw20964step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20964step1 raw20964step1Labels raw20964step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4442 node4442Labels := by rfl

def raw20965 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20965Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20965step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20965step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20965step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20965step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20965 raw20965Labels = mixedMoment B node4442 node4442Labels := by
  calc
    mixedMoment B raw20965 raw20965Labels = mixedMoment B raw20965step0 raw20965step0Labels := by
      have hz : ∀ j, raw20965 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20965step0 = (fun i j => raw20965 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20965step0 raw20965; decide +kernel
      have hl : raw20965step0Labels = raw20965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20965 raw20965Labels permutation265 hz
    mixedMoment B raw20965step0 raw20965step0Labels = mixedMoment B raw20965step1 raw20965step1Labels := by
      have ha : raw20965step1 = (fun i j => raw20965step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20965step1 raw20965step0; decide +kernel
      have hl : raw20965step1Labels = raw20965step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20965step0 raw20965step0Labels permutation32 permutation7
    mixedMoment B raw20965step1 raw20965step1Labels = mixedMoment B raw20965step2 raw20965step2Labels := by
      have ha : raw20965step2 = raw20965step1 := by apply Matrix.ext; unfold raw20965step2 raw20965step1; decide +kernel
      have hl : raw20965step1Labels = labelEmbedding10 ∘ raw20965step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20965step1 raw20965step1Labels raw20965step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4442 node4442Labels := by rfl

def raw20966 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20966Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20966step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20966step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20966step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20966step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw20966step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20966step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw20966step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20966 raw20966Labels = mixedMoment B node4478 node4478Labels := by
  calc
    mixedMoment B raw20966 raw20966Labels = mixedMoment B raw20966step0 raw20966step0Labels := by
      have hz : ∀ j, raw20966 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20966step0 = (fun i j => raw20966 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20966step0 raw20966; decide +kernel
      have hl : raw20966step0Labels = raw20966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20966 raw20966Labels permutation346 hz
    mixedMoment B raw20966step0 raw20966step0Labels = mixedMoment B raw20966step1 raw20966step1Labels := by
      have hz : ∀ j, raw20966step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20966step1 = (fun i j => raw20966step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20966step1 raw20966step0; decide +kernel
      have hl : raw20966step1Labels = raw20966step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20966step0 raw20966step0Labels permutation56 hz
    mixedMoment B raw20966step1 raw20966step1Labels = mixedMoment B raw20966step2 raw20966step2Labels := by
      have ha : raw20966step2 = (fun i j => raw20966step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20966step2 raw20966step1; decide +kernel
      have hl : raw20966step2Labels = raw20966step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20966step1 raw20966step1Labels permutation8 permutation7
    mixedMoment B raw20966step2 raw20966step2Labels = mixedMoment B raw20966step3 raw20966step3Labels := by
      have ha : raw20966step3 = raw20966step2 := by apply Matrix.ext; unfold raw20966step3 raw20966step2; decide +kernel
      have hl : raw20966step2Labels = labelEmbedding10 ∘ raw20966step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20966step2 raw20966step2Labels raw20966step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4478 node4478Labels := by rfl

def raw20967 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20967Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20967step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20967step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20967step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20967step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20967 raw20967Labels = mixedMoment B node4398 node4398Labels := by
  calc
    mixedMoment B raw20967 raw20967Labels = mixedMoment B raw20967step0 raw20967step0Labels := by
      have hz : ∀ j, raw20967 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20967step0 = (fun i j => raw20967 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20967step0 raw20967; decide +kernel
      have hl : raw20967step0Labels = raw20967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20967 raw20967Labels permutation346 hz
    mixedMoment B raw20967step0 raw20967step0Labels = mixedMoment B raw20967step1 raw20967step1Labels := by
      have ha : raw20967step1 = (fun i j => raw20967step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20967step1 raw20967step0; decide +kernel
      have hl : raw20967step1Labels = raw20967step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20967step0 raw20967step0Labels permutation38 permutation6
    mixedMoment B raw20967step1 raw20967step1Labels = mixedMoment B raw20967step2 raw20967step2Labels := by
      have ha : raw20967step2 = raw20967step1 := by apply Matrix.ext; unfold raw20967step2 raw20967step1; decide +kernel
      have hl : raw20967step1Labels = labelEmbedding9 ∘ raw20967step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20967step1 raw20967step1Labels raw20967step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4398 node4398Labels := by rfl

def raw20968 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20968Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20968step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20968step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20968step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20968 raw20968Labels = mixedMoment B node4576 node4576Labels := by
  calc
    mixedMoment B raw20968 raw20968Labels = mixedMoment B raw20968step0 raw20968step0Labels := by
      have ha : raw20968step0 = (fun i j => raw20968 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20968step0 raw20968; decide +kernel
      have hl : raw20968step0Labels = raw20968Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20968 raw20968Labels permutation182 permutation6
    mixedMoment B raw20968step0 raw20968step0Labels = mixedMoment B raw20968step1 raw20968step1Labels := by
      have ha : raw20968step1 = raw20968step0 := by apply Matrix.ext; unfold raw20968step1 raw20968step0; decide +kernel
      have hl : raw20968step0Labels = labelEmbedding9 ∘ raw20968step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20968step0 raw20968step0Labels raw20968step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4576 node4576Labels := by rfl

def raw20969 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20969Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20969step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20969step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20969step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20969step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20969step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20969 raw20969Labels = mixedMoment B node4562 node4562Labels := by
  calc
    mixedMoment B raw20969 raw20969Labels = mixedMoment B raw20969step0 raw20969step0Labels := by
      have hz : ∀ j, raw20969 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20969step0 = (fun i j => raw20969 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20969step0 raw20969; decide +kernel
      have hl : raw20969step0Labels = raw20969Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20969 raw20969Labels permutation346 hz
    mixedMoment B raw20969step0 raw20969step0Labels = mixedMoment B raw20969step1 raw20969step1Labels := by
      have ha : raw20969step1 = (fun i j => raw20969step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20969step1 raw20969step0; decide +kernel
      have hl : raw20969step1Labels = raw20969step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20969step0 raw20969step0Labels permutation38 permutation6
    mixedMoment B raw20969step1 raw20969step1Labels = mixedMoment B raw20969step2 raw20969step2Labels := by
      have ha : raw20969step2 = raw20969step1 := by apply Matrix.ext; unfold raw20969step2 raw20969step1; decide +kernel
      have hl : raw20969step1Labels = labelEmbedding9 ∘ raw20969step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20969step1 raw20969step1Labels raw20969step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4562 node4562Labels := by rfl

def raw20970 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20970Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20970step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20970step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20970step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20970step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20970 raw20970Labels = mixedMoment B node4398 node4398Labels := by
  calc
    mixedMoment B raw20970 raw20970Labels = mixedMoment B raw20970step0 raw20970step0Labels := by
      have hz : ∀ j, raw20970 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20970step0 = (fun i j => raw20970 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20970step0 raw20970; decide +kernel
      have hl : raw20970step0Labels = raw20970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20970 raw20970Labels permutation265 hz
    mixedMoment B raw20970step0 raw20970step0Labels = mixedMoment B raw20970step1 raw20970step1Labels := by
      have ha : raw20970step1 = (fun i j => raw20970step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20970step1 raw20970step0; decide +kernel
      have hl : raw20970step1Labels = raw20970step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20970step0 raw20970step0Labels permutation38 permutation6
    mixedMoment B raw20970step1 raw20970step1Labels = mixedMoment B raw20970step2 raw20970step2Labels := by
      have ha : raw20970step2 = raw20970step1 := by apply Matrix.ext; unfold raw20970step2 raw20970step1; decide +kernel
      have hl : raw20970step1Labels = labelEmbedding9 ∘ raw20970step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20970step1 raw20970step1Labels raw20970step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4398 node4398Labels := by rfl

def raw20971 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20971Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20971step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20971step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20971step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20971step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20971 raw20971Labels = mixedMoment B node4576 node4576Labels := by
  calc
    mixedMoment B raw20971 raw20971Labels = mixedMoment B raw20971step0 raw20971step0Labels := by
      have ha : raw20971step0 = (fun i j => raw20971 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20971step0 raw20971; decide +kernel
      have hl : raw20971step0Labels = raw20971Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20971 raw20971Labels permutation158 permutation6
    mixedMoment B raw20971step0 raw20971step0Labels = mixedMoment B raw20971step1 raw20971step1Labels := by
      have ha : raw20971step1 = raw20971step0 := by apply Matrix.ext; unfold raw20971step1 raw20971step0; decide +kernel
      have hl : raw20971step0Labels = labelEmbedding9 ∘ raw20971step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20971step0 raw20971step0Labels raw20971step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4576 node4576Labels := by rfl

def raw20972 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20972Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20972step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20972step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20972step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20972step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20972 raw20972Labels = mixedMoment B node4562 node4562Labels := by
  calc
    mixedMoment B raw20972 raw20972Labels = mixedMoment B raw20972step0 raw20972step0Labels := by
      have hz : ∀ j, raw20972 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20972step0 = (fun i j => raw20972 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20972step0 raw20972; decide +kernel
      have hl : raw20972step0Labels = raw20972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20972 raw20972Labels permutation265 hz
    mixedMoment B raw20972step0 raw20972step0Labels = mixedMoment B raw20972step1 raw20972step1Labels := by
      have ha : raw20972step1 = (fun i j => raw20972step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20972step1 raw20972step0; decide +kernel
      have hl : raw20972step1Labels = raw20972step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20972step0 raw20972step0Labels permutation38 permutation6
    mixedMoment B raw20972step1 raw20972step1Labels = mixedMoment B raw20972step2 raw20972step2Labels := by
      have ha : raw20972step2 = raw20972step1 := by apply Matrix.ext; unfold raw20972step2 raw20972step1; decide +kernel
      have hl : raw20972step1Labels = labelEmbedding9 ∘ raw20972step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20972step1 raw20972step1Labels raw20972step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4562 node4562Labels := by rfl

def raw20973 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw20973Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw20973step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20973step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw20973step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20973step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw20973step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw20973step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw20973step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20973 raw20973Labels = mixedMoment B node4421 node4421Labels := by
  calc
    mixedMoment B raw20973 raw20973Labels = mixedMoment B raw20973step0 raw20973step0Labels := by
      have hz : ∀ j, raw20973 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20973step0 = (fun i j => raw20973 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20973step0 raw20973; decide +kernel
      have hl : raw20973step0Labels = raw20973Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20973 raw20973Labels permutation346 hz
    mixedMoment B raw20973step0 raw20973step0Labels = mixedMoment B raw20973step1 raw20973step1Labels := by
      have hz : ∀ j, raw20973step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20973step1 = (fun i j => raw20973step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20973step1 raw20973step0; decide +kernel
      have hl : raw20973step1Labels = raw20973step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20973step0 raw20973step0Labels permutation56 hz
    mixedMoment B raw20973step1 raw20973step1Labels = mixedMoment B raw20973step2 raw20973step2Labels := by
      have ha : raw20973step2 = (fun i j => raw20973step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20973step2 raw20973step1; decide +kernel
      have hl : raw20973step2Labels = raw20973step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20973step1 raw20973step1Labels permutation31 permutation4
    mixedMoment B raw20973step2 raw20973step2Labels = mixedMoment B raw20973step3 raw20973step3Labels := by
      have ha : raw20973step3 = raw20973step2 := by apply Matrix.ext; unfold raw20973step3 raw20973step2; decide +kernel
      have hl : raw20973step2Labels = labelEmbedding7 ∘ raw20973step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20973step2 raw20973step2Labels raw20973step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4421 node4421Labels := by rfl

def raw20974 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw20974Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw20974step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw20974step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw20974step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw20974step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20974 raw20974Labels = mixedMoment B node4416 node4416Labels := by
  calc
    mixedMoment B raw20974 raw20974Labels = mixedMoment B raw20974step0 raw20974step0Labels := by
      have hz : ∀ j, raw20974 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20974step0 = (fun i j => raw20974 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20974step0 raw20974; decide +kernel
      have hl : raw20974step0Labels = raw20974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20974 raw20974Labels permutation346 hz
    mixedMoment B raw20974step0 raw20974step0Labels = mixedMoment B raw20974step1 raw20974step1Labels := by
      have ha : raw20974step1 = (fun i j => raw20974step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20974step1 raw20974step0; decide +kernel
      have hl : raw20974step1Labels = raw20974step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20974step0 raw20974step0Labels permutation149 permutation4
    mixedMoment B raw20974step1 raw20974step1Labels = mixedMoment B raw20974step2 raw20974step2Labels := by
      have ha : raw20974step2 = raw20974step1 := by apply Matrix.ext; unfold raw20974step2 raw20974step1; decide +kernel
      have hl : raw20974step1Labels = labelEmbedding7 ∘ raw20974step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20974step1 raw20974step1Labels raw20974step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4416 node4416Labels := by rfl

def raw20975 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw20975Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw20975step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20975step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw20975step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw20975step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw20975step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20975 raw20975Labels = mixedMoment B node4416 node4416Labels := by
  calc
    mixedMoment B raw20975 raw20975Labels = mixedMoment B raw20975step0 raw20975step0Labels := by
      have hz : ∀ j, raw20975 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20975step0 = (fun i j => raw20975 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20975step0 raw20975; decide +kernel
      have hl : raw20975step0Labels = raw20975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20975 raw20975Labels permutation265 hz
    mixedMoment B raw20975step0 raw20975step0Labels = mixedMoment B raw20975step1 raw20975step1Labels := by
      have ha : raw20975step1 = (fun i j => raw20975step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20975step1 raw20975step0; decide +kernel
      have hl : raw20975step1Labels = raw20975step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20975step0 raw20975step0Labels permutation149 permutation4
    mixedMoment B raw20975step1 raw20975step1Labels = mixedMoment B raw20975step2 raw20975step2Labels := by
      have ha : raw20975step2 = raw20975step1 := by apply Matrix.ext; unfold raw20975step2 raw20975step1; decide +kernel
      have hl : raw20975step1Labels = labelEmbedding7 ∘ raw20975step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20975step1 raw20975step1Labels raw20975step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4416 node4416Labels := by rfl

def raw20976 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw20976Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw20976step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw20976step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20976step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw20976step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw20976step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw20976step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20976 raw20976Labels = mixedMoment B node4430 node4430Labels := by
  calc
    mixedMoment B raw20976 raw20976Labels = mixedMoment B raw20976step0 raw20976step0Labels := by
      have hz : ∀ j, raw20976 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20976step0 = (fun i j => raw20976 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20976step0 raw20976; decide +kernel
      have hl : raw20976step0Labels = raw20976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20976 raw20976Labels permutation346 hz
    mixedMoment B raw20976step0 raw20976step0Labels = mixedMoment B raw20976step1 raw20976step1Labels := by
      have hz : ∀ j, raw20976step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20976step1 = (fun i j => raw20976step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20976step1 raw20976step0; decide +kernel
      have hl : raw20976step1Labels = raw20976step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20976step0 raw20976step0Labels permutation56 hz
    mixedMoment B raw20976step1 raw20976step1Labels = mixedMoment B raw20976step2 raw20976step2Labels := by
      have ha : raw20976step2 = (fun i j => raw20976step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20976step2 raw20976step1; decide +kernel
      have hl : raw20976step2Labels = raw20976step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20976step1 raw20976step1Labels permutation31 permutation4
    mixedMoment B raw20976step2 raw20976step2Labels = mixedMoment B raw20976step3 raw20976step3Labels := by
      have ha : raw20976step3 = raw20976step2 := by apply Matrix.ext; unfold raw20976step3 raw20976step2; decide +kernel
      have hl : raw20976step2Labels = labelEmbedding7 ∘ raw20976step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20976step2 raw20976step2Labels raw20976step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4430 node4430Labels := by rfl

def raw20977 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20977Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20977step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20977step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20977step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20977step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20977 raw20977Labels = mixedMoment B node1024 node1024Labels := by
  calc
    mixedMoment B raw20977 raw20977Labels = mixedMoment B raw20977step0 raw20977step0Labels := by
      have hz : ∀ j, raw20977 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20977step0 = (fun i j => raw20977 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20977step0 raw20977; decide +kernel
      have hl : raw20977step0Labels = raw20977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20977 raw20977Labels permutation346 hz
    mixedMoment B raw20977step0 raw20977step0Labels = mixedMoment B raw20977step1 raw20977step1Labels := by
      have ha : raw20977step1 = (fun i j => raw20977step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20977step1 raw20977step0; decide +kernel
      have hl : raw20977step1Labels = raw20977step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20977step0 raw20977step0Labels permutation32 permutation7
    mixedMoment B raw20977step1 raw20977step1Labels = mixedMoment B raw20977step2 raw20977step2Labels := by
      have ha : raw20977step2 = raw20977step1 := by apply Matrix.ext; unfold raw20977step2 raw20977step1; decide +kernel
      have hl : raw20977step1Labels = labelEmbedding1 ∘ raw20977step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20977step1 raw20977step1Labels raw20977step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1024 node1024Labels := by rfl

def raw20978 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20978Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20978step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20978step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20978step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20978step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20978 raw20978Labels = mixedMoment B node1024 node1024Labels := by
  calc
    mixedMoment B raw20978 raw20978Labels = mixedMoment B raw20978step0 raw20978step0Labels := by
      have hz : ∀ j, raw20978 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20978step0 = (fun i j => raw20978 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20978step0 raw20978; decide +kernel
      have hl : raw20978step0Labels = raw20978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20978 raw20978Labels permutation265 hz
    mixedMoment B raw20978step0 raw20978step0Labels = mixedMoment B raw20978step1 raw20978step1Labels := by
      have ha : raw20978step1 = (fun i j => raw20978step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20978step1 raw20978step0; decide +kernel
      have hl : raw20978step1Labels = raw20978step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20978step0 raw20978step0Labels permutation32 permutation7
    mixedMoment B raw20978step1 raw20978step1Labels = mixedMoment B raw20978step2 raw20978step2Labels := by
      have ha : raw20978step2 = raw20978step1 := by apply Matrix.ext; unfold raw20978step2 raw20978step1; decide +kernel
      have hl : raw20978step1Labels = labelEmbedding1 ∘ raw20978step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20978step1 raw20978step1Labels raw20978step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1024 node1024Labels := by rfl

def raw20979 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20979Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20979step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20979step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20979step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20979step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw20979step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20979step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw20979step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20979 raw20979Labels = mixedMoment B node1061 node1061Labels := by
  calc
    mixedMoment B raw20979 raw20979Labels = mixedMoment B raw20979step0 raw20979step0Labels := by
      have hz : ∀ j, raw20979 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20979step0 = (fun i j => raw20979 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20979step0 raw20979; decide +kernel
      have hl : raw20979step0Labels = raw20979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20979 raw20979Labels permutation346 hz
    mixedMoment B raw20979step0 raw20979step0Labels = mixedMoment B raw20979step1 raw20979step1Labels := by
      have hz : ∀ j, raw20979step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20979step1 = (fun i j => raw20979step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20979step1 raw20979step0; decide +kernel
      have hl : raw20979step1Labels = raw20979step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20979step0 raw20979step0Labels permutation56 hz
    mixedMoment B raw20979step1 raw20979step1Labels = mixedMoment B raw20979step2 raw20979step2Labels := by
      have ha : raw20979step2 = (fun i j => raw20979step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20979step2 raw20979step1; decide +kernel
      have hl : raw20979step2Labels = raw20979step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20979step1 raw20979step1Labels permutation8 permutation7
    mixedMoment B raw20979step2 raw20979step2Labels = mixedMoment B raw20979step3 raw20979step3Labels := by
      have ha : raw20979step3 = raw20979step2 := by apply Matrix.ext; unfold raw20979step3 raw20979step2; decide +kernel
      have hl : raw20979step2Labels = labelEmbedding1 ∘ raw20979step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20979step2 raw20979step2Labels raw20979step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1061 node1061Labels := by rfl

def raw20980 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20980Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20980step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20980step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20980step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20980step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20980 raw20980Labels = mixedMoment B node1399 node1399Labels := by
  calc
    mixedMoment B raw20980 raw20980Labels = mixedMoment B raw20980step0 raw20980step0Labels := by
      have hz : ∀ j, raw20980 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20980step0 = (fun i j => raw20980 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20980step0 raw20980; decide +kernel
      have hl : raw20980step0Labels = raw20980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20980 raw20980Labels permutation346 hz
    mixedMoment B raw20980step0 raw20980step0Labels = mixedMoment B raw20980step1 raw20980step1Labels := by
      have ha : raw20980step1 = (fun i j => raw20980step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20980step1 raw20980step0; decide +kernel
      have hl : raw20980step1Labels = raw20980step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20980step0 raw20980step0Labels permutation32 permutation7
    mixedMoment B raw20980step1 raw20980step1Labels = mixedMoment B raw20980step2 raw20980step2Labels := by
      have ha : raw20980step2 = raw20980step1 := by apply Matrix.ext; unfold raw20980step2 raw20980step1; decide +kernel
      have hl : raw20980step1Labels = labelEmbedding1 ∘ raw20980step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20980step1 raw20980step1Labels raw20980step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1399 node1399Labels := by rfl

def raw20981 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20981Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20981step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20981step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20981step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20981step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20981 raw20981Labels = mixedMoment B node1207 node1207Labels := by
  calc
    mixedMoment B raw20981 raw20981Labels = mixedMoment B raw20981step0 raw20981step0Labels := by
      have ha : raw20981step0 = (fun i j => raw20981 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20981step0 raw20981; decide +kernel
      have hl : raw20981step0Labels = raw20981Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20981 raw20981Labels permutation152 permutation7
    mixedMoment B raw20981step0 raw20981step0Labels = mixedMoment B raw20981step1 raw20981step1Labels := by
      have ha : raw20981step1 = raw20981step0 := by apply Matrix.ext; unfold raw20981step1 raw20981step0; decide +kernel
      have hl : raw20981step0Labels = labelEmbedding1 ∘ raw20981step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20981step0 raw20981step0Labels raw20981step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1207 node1207Labels := by rfl

def raw20982 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20982Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20982step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw20982step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20982step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw20982step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20982 raw20982Labels = mixedMoment B node1225 node1225Labels := by
  calc
    mixedMoment B raw20982 raw20982Labels = mixedMoment B raw20982step0 raw20982step0Labels := by
      have hz : ∀ j, raw20982 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20982step0 = (fun i j => raw20982 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20982step0 raw20982; decide +kernel
      have hl : raw20982step0Labels = raw20982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20982 raw20982Labels permutation346 hz
    mixedMoment B raw20982step0 raw20982step0Labels = mixedMoment B raw20982step1 raw20982step1Labels := by
      have ha : raw20982step1 = (fun i j => raw20982step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20982step1 raw20982step0; decide +kernel
      have hl : raw20982step1Labels = raw20982step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20982step0 raw20982step0Labels permutation32 permutation7
    mixedMoment B raw20982step1 raw20982step1Labels = mixedMoment B raw20982step2 raw20982step2Labels := by
      have ha : raw20982step2 = raw20982step1 := by apply Matrix.ext; unfold raw20982step2 raw20982step1; decide +kernel
      have hl : raw20982step1Labels = labelEmbedding1 ∘ raw20982step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20982step1 raw20982step1Labels raw20982step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1225 node1225Labels := by rfl

def raw20983 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20983Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20983step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20983step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20983step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20983step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20983step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20983 raw20983Labels = mixedMoment B node1399 node1399Labels := by
  calc
    mixedMoment B raw20983 raw20983Labels = mixedMoment B raw20983step0 raw20983step0Labels := by
      have hz : ∀ j, raw20983 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20983step0 = (fun i j => raw20983 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20983step0 raw20983; decide +kernel
      have hl : raw20983step0Labels = raw20983Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20983 raw20983Labels permutation265 hz
    mixedMoment B raw20983step0 raw20983step0Labels = mixedMoment B raw20983step1 raw20983step1Labels := by
      have ha : raw20983step1 = (fun i j => raw20983step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20983step1 raw20983step0; decide +kernel
      have hl : raw20983step1Labels = raw20983step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20983step0 raw20983step0Labels permutation32 permutation7
    mixedMoment B raw20983step1 raw20983step1Labels = mixedMoment B raw20983step2 raw20983step2Labels := by
      have ha : raw20983step2 = raw20983step1 := by apply Matrix.ext; unfold raw20983step2 raw20983step1; decide +kernel
      have hl : raw20983step1Labels = labelEmbedding1 ∘ raw20983step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20983step1 raw20983step1Labels raw20983step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1399 node1399Labels := by rfl

def raw20984 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20984Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20984step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20984step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20984step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20984 raw20984Labels = mixedMoment B node1207 node1207Labels := by
  calc
    mixedMoment B raw20984 raw20984Labels = mixedMoment B raw20984step0 raw20984step0Labels := by
      have ha : raw20984step0 = (fun i j => raw20984 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20984step0 raw20984; decide +kernel
      have hl : raw20984step0Labels = raw20984Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20984 raw20984Labels permutation176 permutation7
    mixedMoment B raw20984step0 raw20984step0Labels = mixedMoment B raw20984step1 raw20984step1Labels := by
      have ha : raw20984step1 = raw20984step0 := by apply Matrix.ext; unfold raw20984step1 raw20984step0; decide +kernel
      have hl : raw20984step0Labels = labelEmbedding1 ∘ raw20984step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20984step0 raw20984step0Labels raw20984step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1207 node1207Labels := by rfl

def raw20985 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20985Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20985step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw20985step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20985step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw20985step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20985 raw20985Labels = mixedMoment B node1225 node1225Labels := by
  calc
    mixedMoment B raw20985 raw20985Labels = mixedMoment B raw20985step0 raw20985step0Labels := by
      have hz : ∀ j, raw20985 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20985step0 = (fun i j => raw20985 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20985step0 raw20985; decide +kernel
      have hl : raw20985step0Labels = raw20985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20985 raw20985Labels permutation265 hz
    mixedMoment B raw20985step0 raw20985step0Labels = mixedMoment B raw20985step1 raw20985step1Labels := by
      have ha : raw20985step1 = (fun i j => raw20985step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20985step1 raw20985step0; decide +kernel
      have hl : raw20985step1Labels = raw20985step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20985step0 raw20985step0Labels permutation32 permutation7
    mixedMoment B raw20985step1 raw20985step1Labels = mixedMoment B raw20985step2 raw20985step2Labels := by
      have ha : raw20985step2 = raw20985step1 := by apply Matrix.ext; unfold raw20985step2 raw20985step1; decide +kernel
      have hl : raw20985step1Labels = labelEmbedding1 ∘ raw20985step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20985step1 raw20985step1Labels raw20985step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1225 node1225Labels := by rfl

def raw20986 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20986Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20986step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20986step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20986step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20986step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw20986step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20986step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw20986step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20986 raw20986Labels = mixedMoment B node1428 node1428Labels := by
  calc
    mixedMoment B raw20986 raw20986Labels = mixedMoment B raw20986step0 raw20986step0Labels := by
      have hz : ∀ j, raw20986 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20986step0 = (fun i j => raw20986 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20986step0 raw20986; decide +kernel
      have hl : raw20986step0Labels = raw20986Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20986 raw20986Labels permutation346 hz
    mixedMoment B raw20986step0 raw20986step0Labels = mixedMoment B raw20986step1 raw20986step1Labels := by
      have hz : ∀ j, raw20986step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20986step1 = (fun i j => raw20986step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20986step1 raw20986step0; decide +kernel
      have hl : raw20986step1Labels = raw20986step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20986step0 raw20986step0Labels permutation56 hz
    mixedMoment B raw20986step1 raw20986step1Labels = mixedMoment B raw20986step2 raw20986step2Labels := by
      have ha : raw20986step2 = (fun i j => raw20986step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20986step2 raw20986step1; decide +kernel
      have hl : raw20986step2Labels = raw20986step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20986step1 raw20986step1Labels permutation8 permutation7
    mixedMoment B raw20986step2 raw20986step2Labels = mixedMoment B raw20986step3 raw20986step3Labels := by
      have ha : raw20986step3 = raw20986step2 := by apply Matrix.ext; unfold raw20986step3 raw20986step2; decide +kernel
      have hl : raw20986step2Labels = labelEmbedding1 ∘ raw20986step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20986step2 raw20986step2Labels raw20986step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1428 node1428Labels := by rfl

def raw20987 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20987Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20987step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw20987step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20987step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw20987step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20987 raw20987Labels = mixedMoment B node1251 node1251Labels := by
  calc
    mixedMoment B raw20987 raw20987Labels = mixedMoment B raw20987step0 raw20987step0Labels := by
      have hz : ∀ j, raw20987 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20987step0 = (fun i j => raw20987 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20987step0 raw20987; decide +kernel
      have hl : raw20987step0Labels = raw20987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20987 raw20987Labels permutation346 hz
    mixedMoment B raw20987step0 raw20987step0Labels = mixedMoment B raw20987step1 raw20987step1Labels := by
      have ha : raw20987step1 = (fun i j => raw20987step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20987step1 raw20987step0; decide +kernel
      have hl : raw20987step1Labels = raw20987step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20987step0 raw20987step0Labels permutation32 permutation7
    mixedMoment B raw20987step1 raw20987step1Labels = mixedMoment B raw20987step2 raw20987step2Labels := by
      have ha : raw20987step2 = raw20987step1 := by apply Matrix.ext; unfold raw20987step2 raw20987step1; decide +kernel
      have hl : raw20987step1Labels = labelEmbedding1 ∘ raw20987step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20987step1 raw20987step1Labels raw20987step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1251 node1251Labels := by rfl

def raw20988 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20988Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20988step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw20988step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20988step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw20988step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20988 raw20988Labels = mixedMoment B node1251 node1251Labels := by
  calc
    mixedMoment B raw20988 raw20988Labels = mixedMoment B raw20988step0 raw20988step0Labels := by
      have hz : ∀ j, raw20988 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20988step0 = (fun i j => raw20988 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20988step0 raw20988; decide +kernel
      have hl : raw20988step0Labels = raw20988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20988 raw20988Labels permutation265 hz
    mixedMoment B raw20988step0 raw20988step0Labels = mixedMoment B raw20988step1 raw20988step1Labels := by
      have ha : raw20988step1 = (fun i j => raw20988step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20988step1 raw20988step0; decide +kernel
      have hl : raw20988step1Labels = raw20988step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20988step0 raw20988step0Labels permutation32 permutation7
    mixedMoment B raw20988step1 raw20988step1Labels = mixedMoment B raw20988step2 raw20988step2Labels := by
      have ha : raw20988step2 = raw20988step1 := by apply Matrix.ext; unfold raw20988step2 raw20988step1; decide +kernel
      have hl : raw20988step1Labels = labelEmbedding1 ∘ raw20988step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20988step1 raw20988step1Labels raw20988step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1251 node1251Labels := by rfl

def raw20989 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20989Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20989step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20989step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20989step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20989step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw20989step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20989step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw20989step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20989 raw20989Labels = mixedMoment B node1281 node1281Labels := by
  calc
    mixedMoment B raw20989 raw20989Labels = mixedMoment B raw20989step0 raw20989step0Labels := by
      have hz : ∀ j, raw20989 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20989step0 = (fun i j => raw20989 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20989step0 raw20989; decide +kernel
      have hl : raw20989step0Labels = raw20989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20989 raw20989Labels permutation346 hz
    mixedMoment B raw20989step0 raw20989step0Labels = mixedMoment B raw20989step1 raw20989step1Labels := by
      have hz : ∀ j, raw20989step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20989step1 = (fun i j => raw20989step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20989step1 raw20989step0; decide +kernel
      have hl : raw20989step1Labels = raw20989step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20989step0 raw20989step0Labels permutation56 hz
    mixedMoment B raw20989step1 raw20989step1Labels = mixedMoment B raw20989step2 raw20989step2Labels := by
      have ha : raw20989step2 = (fun i j => raw20989step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20989step2 raw20989step1; decide +kernel
      have hl : raw20989step2Labels = raw20989step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20989step1 raw20989step1Labels permutation8 permutation7
    mixedMoment B raw20989step2 raw20989step2Labels = mixedMoment B raw20989step3 raw20989step3Labels := by
      have ha : raw20989step3 = raw20989step2 := by apply Matrix.ext; unfold raw20989step3 raw20989step2; decide +kernel
      have hl : raw20989step2Labels = labelEmbedding1 ∘ raw20989step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20989step2 raw20989step2Labels raw20989step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1281 node1281Labels := by rfl

def raw20990 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw20990Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw20990step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20990step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw20990step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20990step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw20990step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20990step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw20990step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20990 raw20990Labels = mixedMoment B node1429 node1429Labels := by
  calc
    mixedMoment B raw20990 raw20990Labels = mixedMoment B raw20990step0 raw20990step0Labels := by
      have hz : ∀ j, raw20990 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20990step0 = (fun i j => raw20990 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20990step0 raw20990; decide +kernel
      have hl : raw20990step0Labels = raw20990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20990 raw20990Labels permutation346 hz
    mixedMoment B raw20990step0 raw20990step0Labels = mixedMoment B raw20990step1 raw20990step1Labels := by
      have hz : ∀ j, raw20990step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20990step1 = (fun i j => raw20990step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20990step1 raw20990step0; decide +kernel
      have hl : raw20990step1Labels = raw20990step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20990step0 raw20990step0Labels permutation56 hz
    mixedMoment B raw20990step1 raw20990step1Labels = mixedMoment B raw20990step2 raw20990step2Labels := by
      have ha : raw20990step2 = (fun i j => raw20990step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw20990step2 raw20990step1; decide +kernel
      have hl : raw20990step2Labels = raw20990step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20990step1 raw20990step1Labels permutation31 permutation5
    mixedMoment B raw20990step2 raw20990step2Labels = mixedMoment B raw20990step3 raw20990step3Labels := by
      have ha : raw20990step3 = raw20990step2 := by apply Matrix.ext; unfold raw20990step3 raw20990step2; decide +kernel
      have hl : raw20990step2Labels = labelEmbedding1 ∘ raw20990step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20990step2 raw20990step2Labels raw20990step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1429 node1429Labels := by rfl

def raw20991 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw20991Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw20991step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw20991step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20991step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw20991step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20991 raw20991Labels = mixedMoment B node1252 node1252Labels := by
  calc
    mixedMoment B raw20991 raw20991Labels = mixedMoment B raw20991step0 raw20991step0Labels := by
      have hz : ∀ j, raw20991 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20991step0 = (fun i j => raw20991 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20991step0 raw20991; decide +kernel
      have hl : raw20991step0Labels = raw20991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20991 raw20991Labels permutation346 hz
    mixedMoment B raw20991step0 raw20991step0Labels = mixedMoment B raw20991step1 raw20991step1Labels := by
      have ha : raw20991step1 = (fun i j => raw20991step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20991step1 raw20991step0; decide +kernel
      have hl : raw20991step1Labels = raw20991step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20991step0 raw20991step0Labels permutation32 permutation7
    mixedMoment B raw20991step1 raw20991step1Labels = mixedMoment B raw20991step2 raw20991step2Labels := by
      have ha : raw20991step2 = raw20991step1 := by apply Matrix.ext; unfold raw20991step2 raw20991step1; decide +kernel
      have hl : raw20991step1Labels = labelEmbedding1 ∘ raw20991step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20991step1 raw20991step1Labels raw20991step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1252 node1252Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
