import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw28928 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28928Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28928step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 0, 3]]
def raw28928step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw28928step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw28928step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw28928step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw28928step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28928 raw28928Labels = mixedMoment B node4800 node4800Labels := by
  calc
    mixedMoment B raw28928 raw28928Labels = mixedMoment B raw28928step0 raw28928step0Labels := by
      have hz : ∀ j, raw28928 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28928step0 = (fun i j => raw28928 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28928step0 raw28928; decide +kernel
      have hl : raw28928step0Labels = raw28928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28928 raw28928Labels permutation346 hz
    mixedMoment B raw28928step0 raw28928step0Labels = mixedMoment B raw28928step1 raw28928step1Labels := by
      have ha : raw28928step1 = (fun i j => raw28928step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28928step1 raw28928step0; decide +kernel
      have hl : raw28928step1Labels = raw28928step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28928step0 raw28928step0Labels permutation40 permutation4
    mixedMoment B raw28928step1 raw28928step1Labels = mixedMoment B raw28928step2 raw28928step2Labels := by
      have ha : raw28928step2 = -raw28928step1 := by apply Matrix.ext; change ∀ i j, raw28928step2 i j = -(raw28928step1 i j); unfold raw28928step2 raw28928step1; decide +kernel
      have hl : raw28928step2Labels = raw28928step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28928step2 raw28928step2Labels = mixedMoment B raw28928step3 raw28928step3Labels := by
      have ha : raw28928step3 = raw28928step2 := by apply Matrix.ext; unfold raw28928step3 raw28928step2; decide +kernel
      have hl : raw28928step2Labels = labelEmbedding7 ∘ raw28928step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28928step2 raw28928step2Labels raw28928step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4800 node4800Labels := by rfl

def raw28929 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28929step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw28929step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28929step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw28929step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28929step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw28929step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28929 raw28929Labels = mixedMoment B node4791 node4791Labels := by
  calc
    mixedMoment B raw28929 raw28929Labels = mixedMoment B raw28929step0 raw28929step0Labels := by
      have ha : raw28929step0 = (fun i j => raw28929 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28929step0 raw28929; decide +kernel
      have hl : raw28929step0Labels = raw28929Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28929 raw28929Labels permutation682 permutation6
    mixedMoment B raw28929step0 raw28929step0Labels = mixedMoment B raw28929step1 raw28929step1Labels := by
      have ha : raw28929step1 = -raw28929step0 := by apply Matrix.ext; change ∀ i j, raw28929step1 i j = -(raw28929step0 i j); unfold raw28929step1 raw28929step0; decide +kernel
      have hl : raw28929step1Labels = raw28929step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28929step1 raw28929step1Labels = mixedMoment B raw28929step2 raw28929step2Labels := by
      have ha : raw28929step2 = raw28929step1 := by apply Matrix.ext; unfold raw28929step2 raw28929step1; decide +kernel
      have hl : raw28929step1Labels = labelEmbedding9 ∘ raw28929step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28929step1 raw28929step1Labels raw28929step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4791 node4791Labels := by rfl

def raw28930 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-2, 2, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28930step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28930step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-3, 1, 2]]
def raw28930step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28930step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw28930step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28930step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw28930step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28930 raw28930Labels = mixedMoment B node4814 node4814Labels := by
  calc
    mixedMoment B raw28930 raw28930Labels = mixedMoment B raw28930step0 raw28930step0Labels := by
      have hz : ∀ j, raw28930 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28930step0 = (fun i j => raw28930 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28930step0 raw28930; decide +kernel
      have hl : raw28930step0Labels = raw28930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28930 raw28930Labels permutation346 hz
    mixedMoment B raw28930step0 raw28930step0Labels = mixedMoment B raw28930step1 raw28930step1Labels := by
      have ha : raw28930step1 = (fun i j => raw28930step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28930step1 raw28930step0; decide +kernel
      have hl : raw28930step1Labels = raw28930step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28930step0 raw28930step0Labels permutation151 permutation6
    mixedMoment B raw28930step1 raw28930step1Labels = mixedMoment B raw28930step2 raw28930step2Labels := by
      have ha : raw28930step2 = -raw28930step1 := by apply Matrix.ext; change ∀ i j, raw28930step2 i j = -(raw28930step1 i j); unfold raw28930step2 raw28930step1; decide +kernel
      have hl : raw28930step2Labels = raw28930step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28930step2 raw28930step2Labels = mixedMoment B raw28930step3 raw28930step3Labels := by
      have ha : raw28930step3 = raw28930step2 := by apply Matrix.ext; unfold raw28930step3 raw28930step2; decide +kernel
      have hl : raw28930step2Labels = labelEmbedding9 ∘ raw28930step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28930step2 raw28930step2Labels raw28930step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4814 node4814Labels := by rfl

def raw28931 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28931Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28931step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw28931step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw28931step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw28931step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28931 raw28931Labels = mixedMoment B node4778 node4778Labels := by
  calc
    mixedMoment B raw28931 raw28931Labels = mixedMoment B raw28931step0 raw28931step0Labels := by
      have ha : raw28931step0 = (fun i j => raw28931 (permutation644 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28931step0 raw28931; decide +kernel
      have hl : raw28931step0Labels = raw28931Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28931 raw28931Labels permutation644 permutation4
    mixedMoment B raw28931step0 raw28931step0Labels = mixedMoment B raw28931step1 raw28931step1Labels := by
      have ha : raw28931step1 = raw28931step0 := by apply Matrix.ext; unfold raw28931step1 raw28931step0; decide +kernel
      have hl : raw28931step0Labels = labelEmbedding7 ∘ raw28931step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28931step0 raw28931step0Labels raw28931step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4778 node4778Labels := by rfl

def raw28932 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28932step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw28932step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28932step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28932step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28932step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28932step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28932 raw28932Labels = mixedMoment B node4779 node4779Labels := by
  calc
    mixedMoment B raw28932 raw28932Labels = mixedMoment B raw28932step0 raw28932step0Labels := by
      have ha : raw28932step0 = (fun i j => raw28932 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28932step0 raw28932; decide +kernel
      have hl : raw28932step0Labels = raw28932Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28932 raw28932Labels permutation682 permutation6
    mixedMoment B raw28932step0 raw28932step0Labels = mixedMoment B raw28932step1 raw28932step1Labels := by
      have ha : raw28932step1 = -raw28932step0 := by apply Matrix.ext; change ∀ i j, raw28932step1 i j = -(raw28932step0 i j); unfold raw28932step1 raw28932step0; decide +kernel
      have hl : raw28932step1Labels = raw28932step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28932step1 raw28932step1Labels = mixedMoment B raw28932step2 raw28932step2Labels := by
      have ha : raw28932step2 = raw28932step1 := by apply Matrix.ext; unfold raw28932step2 raw28932step1; decide +kernel
      have hl : raw28932step1Labels = labelEmbedding9 ∘ raw28932step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28932step1 raw28932step1Labels raw28932step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4779 node4779Labels := by rfl

def raw28933 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28933step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw28933step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw28933step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw28933step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28933 raw28933Labels = mixedMoment B node4781 node4781Labels := by
  calc
    mixedMoment B raw28933 raw28933Labels = mixedMoment B raw28933step0 raw28933step0Labels := by
      have ha : raw28933step0 = (fun i j => raw28933 (permutation644 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28933step0 raw28933; decide +kernel
      have hl : raw28933step0Labels = raw28933Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28933 raw28933Labels permutation644 permutation4
    mixedMoment B raw28933step0 raw28933step0Labels = mixedMoment B raw28933step1 raw28933step1Labels := by
      have ha : raw28933step1 = raw28933step0 := by apply Matrix.ext; unfold raw28933step1 raw28933step0; decide +kernel
      have hl : raw28933step0Labels = labelEmbedding7 ∘ raw28933step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28933step0 raw28933step0Labels raw28933step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4781 node4781Labels := by rfl

def raw28934 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28934Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28934step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28934step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-2, 1, 1], ![0, -3, 3]]
def raw28934step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28934step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw28934step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28934step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28934step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw28934step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw28934step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28934 raw28934Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw28934 raw28934Labels = mixedMoment B raw28934step0 raw28934step0Labels := by
      have hz : ∀ j, raw28934 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28934step0 = (fun i j => raw28934 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28934step0 raw28934; decide +kernel
      have hl : raw28934step0Labels = raw28934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28934 raw28934Labels permutation434 hz
    mixedMoment B raw28934step0 raw28934step0Labels = mixedMoment B raw28934step1 raw28934step1Labels := by
      have hz : ∀ j, raw28934step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28934step1 = (fun i j => raw28934step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28934step1 raw28934step0; decide +kernel
      have hl : raw28934step1Labels = raw28934step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28934step0 raw28934step0Labels permutation80 hz
    mixedMoment B raw28934step1 raw28934step1Labels = mixedMoment B raw28934step2 raw28934step2Labels := by
      have ha : raw28934step2 = (fun i j => raw28934step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28934step2 raw28934step1; decide +kernel
      have hl : raw28934step2Labels = raw28934step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28934step1 raw28934step1Labels permutation31 permutation6
    mixedMoment B raw28934step2 raw28934step2Labels = mixedMoment B raw28934step3 raw28934step3Labels := by
      have ha : raw28934step3 = -raw28934step2 := by apply Matrix.ext; change ∀ i j, raw28934step3 i j = -(raw28934step2 i j); unfold raw28934step3 raw28934step2; decide +kernel
      have hl : raw28934step3Labels = raw28934step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28934step3 raw28934step3Labels = mixedMoment B raw28934step4 raw28934step4Labels := by
      have ha : raw28934step4 = raw28934step3 := by apply Matrix.ext; unfold raw28934step4 raw28934step3; decide +kernel
      have hl : raw28934step3Labels = labelEmbedding9 ∘ raw28934step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28934step3 raw28934step3Labels raw28934step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4868 node4868Labels := by rfl

def raw28935 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw28935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw28935step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28935step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw28935step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw28935step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw28935step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28935 raw28935Labels = mixedMoment B node4398 node4398Labels := by
  calc
    mixedMoment B raw28935 raw28935Labels = mixedMoment B raw28935step0 raw28935step0Labels := by
      have hz : ∀ j, raw28935 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28935step0 = (fun i j => raw28935 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28935step0 raw28935; decide +kernel
      have hl : raw28935step0Labels = raw28935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28935 raw28935Labels permutation346 hz
    mixedMoment B raw28935step0 raw28935step0Labels = mixedMoment B raw28935step1 raw28935step1Labels := by
      have ha : raw28935step1 = (fun i j => raw28935step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28935step1 raw28935step0; decide +kernel
      have hl : raw28935step1Labels = raw28935step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28935step0 raw28935step0Labels permutation149 permutation4
    mixedMoment B raw28935step1 raw28935step1Labels = mixedMoment B raw28935step2 raw28935step2Labels := by
      have ha : raw28935step2 = raw28935step1 := by apply Matrix.ext; unfold raw28935step2 raw28935step1; decide +kernel
      have hl : raw28935step1Labels = labelEmbedding7 ∘ raw28935step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28935step1 raw28935step1Labels raw28935step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4398 node4398Labels := by rfl

def raw28936 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw28936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw28936step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw28936step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw28936step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw28936step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28936 raw28936Labels = mixedMoment B node4418 node4418Labels := by
  calc
    mixedMoment B raw28936 raw28936Labels = mixedMoment B raw28936step0 raw28936step0Labels := by
      have hz : ∀ j, raw28936 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28936step0 = (fun i j => raw28936 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28936step0 raw28936; decide +kernel
      have hl : raw28936step0Labels = raw28936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28936 raw28936Labels permutation346 hz
    mixedMoment B raw28936step0 raw28936step0Labels = mixedMoment B raw28936step1 raw28936step1Labels := by
      have ha : raw28936step1 = (fun i j => raw28936step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28936step1 raw28936step0; decide +kernel
      have hl : raw28936step1Labels = raw28936step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28936step0 raw28936step0Labels permutation151 permutation4
    mixedMoment B raw28936step1 raw28936step1Labels = mixedMoment B raw28936step2 raw28936step2Labels := by
      have ha : raw28936step2 = raw28936step1 := by apply Matrix.ext; unfold raw28936step2 raw28936step1; decide +kernel
      have hl : raw28936step1Labels = labelEmbedding7 ∘ raw28936step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28936step1 raw28936step1Labels raw28936step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4418 node4418Labels := by rfl

def raw28937 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw28937Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28937step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28937step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw28937step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw28937step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28937 raw28937Labels = mixedMoment B node4395 node4395Labels := by
  calc
    mixedMoment B raw28937 raw28937Labels = mixedMoment B raw28937step0 raw28937step0Labels := by
      have ha : raw28937step0 = (fun i j => raw28937 (permutation674 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28937step0 raw28937; decide +kernel
      have hl : raw28937step0Labels = raw28937Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28937 raw28937Labels permutation674 permutation4
    mixedMoment B raw28937step0 raw28937step0Labels = mixedMoment B raw28937step1 raw28937step1Labels := by
      have ha : raw28937step1 = raw28937step0 := by apply Matrix.ext; unfold raw28937step1 raw28937step0; decide +kernel
      have hl : raw28937step0Labels = labelEmbedding7 ∘ raw28937step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28937step0 raw28937step0Labels raw28937step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4395 node4395Labels := by rfl

def raw28938 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw28938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-2, 2, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw28938step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw28938step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw28938step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw28938step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28938 raw28938Labels = mixedMoment B node4403 node4403Labels := by
  calc
    mixedMoment B raw28938 raw28938Labels = mixedMoment B raw28938step0 raw28938step0Labels := by
      have hz : ∀ j, raw28938 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28938step0 = (fun i j => raw28938 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28938step0 raw28938; decide +kernel
      have hl : raw28938step0Labels = raw28938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28938 raw28938Labels permutation346 hz
    mixedMoment B raw28938step0 raw28938step0Labels = mixedMoment B raw28938step1 raw28938step1Labels := by
      have ha : raw28938step1 = (fun i j => raw28938step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28938step1 raw28938step0; decide +kernel
      have hl : raw28938step1Labels = raw28938step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28938step0 raw28938step0Labels permutation149 permutation4
    mixedMoment B raw28938step1 raw28938step1Labels = mixedMoment B raw28938step2 raw28938step2Labels := by
      have ha : raw28938step2 = raw28938step1 := by apply Matrix.ext; unfold raw28938step2 raw28938step1; decide +kernel
      have hl : raw28938step1Labels = labelEmbedding7 ∘ raw28938step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28938step1 raw28938step1Labels raw28938step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4403 node4403Labels := by rfl

def raw28939 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28939Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28939step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28939step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28939step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28939step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28939step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28939 raw28939Labels = mixedMoment B node2574 node2574Labels := by
  calc
    mixedMoment B raw28939 raw28939Labels = mixedMoment B raw28939step0 raw28939step0Labels := by
      have hz : ∀ j, raw28939 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28939step0 = (fun i j => raw28939 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28939step0 raw28939; decide +kernel
      have hl : raw28939step0Labels = raw28939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28939 raw28939Labels permutation346 hz
    mixedMoment B raw28939step0 raw28939step0Labels = mixedMoment B raw28939step1 raw28939step1Labels := by
      have ha : raw28939step1 = (fun i j => raw28939step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28939step1 raw28939step0; decide +kernel
      have hl : raw28939step1Labels = raw28939step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28939step0 raw28939step0Labels permutation32 permutation7
    mixedMoment B raw28939step1 raw28939step1Labels = mixedMoment B raw28939step2 raw28939step2Labels := by
      have ha : raw28939step2 = raw28939step1 := by apply Matrix.ext; unfold raw28939step2 raw28939step1; decide +kernel
      have hl : raw28939step1Labels = labelEmbedding1 ∘ raw28939step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28939step1 raw28939step1Labels raw28939step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2574 node2574Labels := by rfl

def raw28940 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28940Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28940step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28940step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28940step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28940step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28940 raw28940Labels = mixedMoment B node2471 node2471Labels := by
  calc
    mixedMoment B raw28940 raw28940Labels = mixedMoment B raw28940step0 raw28940step0Labels := by
      have ha : raw28940step0 = (fun i j => raw28940 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28940step0 raw28940; decide +kernel
      have hl : raw28940step0Labels = raw28940Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28940 raw28940Labels permutation152 permutation7
    mixedMoment B raw28940step0 raw28940step0Labels = mixedMoment B raw28940step1 raw28940step1Labels := by
      have ha : raw28940step1 = raw28940step0 := by apply Matrix.ext; unfold raw28940step1 raw28940step0; decide +kernel
      have hl : raw28940step0Labels = labelEmbedding1 ∘ raw28940step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28940step0 raw28940step0Labels raw28940step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2471 node2471Labels := by rfl

def raw28941 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28941Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-2, 2, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28941step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw28941step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28941step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw28941step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28941 raw28941Labels = mixedMoment B node2497 node2497Labels := by
  calc
    mixedMoment B raw28941 raw28941Labels = mixedMoment B raw28941step0 raw28941step0Labels := by
      have hz : ∀ j, raw28941 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28941step0 = (fun i j => raw28941 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28941step0 raw28941; decide +kernel
      have hl : raw28941step0Labels = raw28941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28941 raw28941Labels permutation346 hz
    mixedMoment B raw28941step0 raw28941step0Labels = mixedMoment B raw28941step1 raw28941step1Labels := by
      have ha : raw28941step1 = (fun i j => raw28941step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28941step1 raw28941step0; decide +kernel
      have hl : raw28941step1Labels = raw28941step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28941step0 raw28941step0Labels permutation32 permutation7
    mixedMoment B raw28941step1 raw28941step1Labels = mixedMoment B raw28941step2 raw28941step2Labels := by
      have ha : raw28941step2 = raw28941step1 := by apply Matrix.ext; unfold raw28941step2 raw28941step1; decide +kernel
      have hl : raw28941step1Labels = labelEmbedding1 ∘ raw28941step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28941step1 raw28941step1Labels raw28941step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2497 node2497Labels := by rfl

def raw28942 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw28942Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw28942step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28942step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28942step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28942step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28942step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28942 raw28942Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw28942 raw28942Labels = mixedMoment B raw28942step0 raw28942step0Labels := by
      have hz : ∀ j, raw28942 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28942step0 = (fun i j => raw28942 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28942step0 raw28942; decide +kernel
      have hl : raw28942step0Labels = raw28942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28942 raw28942Labels permutation346 hz
    mixedMoment B raw28942step0 raw28942step0Labels = mixedMoment B raw28942step1 raw28942step1Labels := by
      have ha : raw28942step1 = (fun i j => raw28942step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28942step1 raw28942step0; decide +kernel
      have hl : raw28942step1Labels = raw28942step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28942step0 raw28942step0Labels permutation32 permutation7
    mixedMoment B raw28942step1 raw28942step1Labels = mixedMoment B raw28942step2 raw28942step2Labels := by
      have ha : raw28942step2 = raw28942step1 := by apply Matrix.ext; unfold raw28942step2 raw28942step1; decide +kernel
      have hl : raw28942step1Labels = labelEmbedding1 ∘ raw28942step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28942step1 raw28942step1Labels raw28942step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw28943 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28943Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28943step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28943step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28943step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28943step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28943 raw28943Labels = mixedMoment B node3177 node3177Labels := by
  calc
    mixedMoment B raw28943 raw28943Labels = mixedMoment B raw28943step0 raw28943step0Labels := by
      have hz : ∀ j, raw28943 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28943step0 = (fun i j => raw28943 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28943step0 raw28943; decide +kernel
      have hl : raw28943step0Labels = raw28943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28943 raw28943Labels permutation346 hz
    mixedMoment B raw28943step0 raw28943step0Labels = mixedMoment B raw28943step1 raw28943step1Labels := by
      have ha : raw28943step1 = (fun i j => raw28943step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28943step1 raw28943step0; decide +kernel
      have hl : raw28943step1Labels = raw28943step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28943step0 raw28943step0Labels permutation139 permutation5
    mixedMoment B raw28943step1 raw28943step1Labels = mixedMoment B raw28943step2 raw28943step2Labels := by
      have ha : raw28943step2 = raw28943step1 := by apply Matrix.ext; unfold raw28943step2 raw28943step1; decide +kernel
      have hl : raw28943step1Labels = labelEmbedding1 ∘ raw28943step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28943step1 raw28943step1Labels raw28943step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3177 node3177Labels := by rfl

def raw28944 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28944Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28944step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28944step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28944step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28944step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28944 raw28944Labels = mixedMoment B node2858 node2858Labels := by
  calc
    mixedMoment B raw28944 raw28944Labels = mixedMoment B raw28944step0 raw28944step0Labels := by
      have ha : raw28944step0 = (fun i j => raw28944 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28944step0 raw28944; decide +kernel
      have hl : raw28944step0Labels = raw28944Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28944 raw28944Labels permutation152 permutation7
    mixedMoment B raw28944step0 raw28944step0Labels = mixedMoment B raw28944step1 raw28944step1Labels := by
      have ha : raw28944step1 = raw28944step0 := by apply Matrix.ext; unfold raw28944step1 raw28944step0; decide +kernel
      have hl : raw28944step0Labels = labelEmbedding1 ∘ raw28944step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28944step0 raw28944step0Labels raw28944step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2858 node2858Labels := by rfl

def raw28945 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28945Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-2, 2, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28945step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw28945step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28945step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw28945step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28945 raw28945Labels = mixedMoment B node2872 node2872Labels := by
  calc
    mixedMoment B raw28945 raw28945Labels = mixedMoment B raw28945step0 raw28945step0Labels := by
      have hz : ∀ j, raw28945 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28945step0 = (fun i j => raw28945 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28945step0 raw28945; decide +kernel
      have hl : raw28945step0Labels = raw28945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28945 raw28945Labels permutation346 hz
    mixedMoment B raw28945step0 raw28945step0Labels = mixedMoment B raw28945step1 raw28945step1Labels := by
      have ha : raw28945step1 = (fun i j => raw28945step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28945step1 raw28945step0; decide +kernel
      have hl : raw28945step1Labels = raw28945step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28945step0 raw28945step0Labels permutation32 permutation7
    mixedMoment B raw28945step1 raw28945step1Labels = mixedMoment B raw28945step2 raw28945step2Labels := by
      have ha : raw28945step2 = raw28945step1 := by apply Matrix.ext; unfold raw28945step2 raw28945step1; decide +kernel
      have hl : raw28945step1Labels = labelEmbedding1 ∘ raw28945step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28945step1 raw28945step1Labels raw28945step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2872 node2872Labels := by rfl

def raw28946 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw28946Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw28946step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28946step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28946step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28946step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28946step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28946 raw28946Labels = mixedMoment B node2865 node2865Labels := by
  calc
    mixedMoment B raw28946 raw28946Labels = mixedMoment B raw28946step0 raw28946step0Labels := by
      have hz : ∀ j, raw28946 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28946step0 = (fun i j => raw28946 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28946step0 raw28946; decide +kernel
      have hl : raw28946step0Labels = raw28946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28946 raw28946Labels permutation346 hz
    mixedMoment B raw28946step0 raw28946step0Labels = mixedMoment B raw28946step1 raw28946step1Labels := by
      have ha : raw28946step1 = (fun i j => raw28946step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28946step1 raw28946step0; decide +kernel
      have hl : raw28946step1Labels = raw28946step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28946step0 raw28946step0Labels permutation32 permutation7
    mixedMoment B raw28946step1 raw28946step1Labels = mixedMoment B raw28946step2 raw28946step2Labels := by
      have ha : raw28946step2 = raw28946step1 := by apply Matrix.ext; unfold raw28946step2 raw28946step1; decide +kernel
      have hl : raw28946step1Labels = labelEmbedding1 ∘ raw28946step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28946step1 raw28946step1Labels raw28946step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2865 node2865Labels := by rfl

def raw28947 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28947Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28947step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28947step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28947step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28947step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28947 raw28947Labels = mixedMoment B node3200 node3200Labels := by
  calc
    mixedMoment B raw28947 raw28947Labels = mixedMoment B raw28947step0 raw28947step0Labels := by
      have ha : raw28947step0 = (fun i j => raw28947 (permutation634 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28947step0 raw28947; decide +kernel
      have hl : raw28947step0Labels = raw28947Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28947 raw28947Labels permutation634 permutation5
    mixedMoment B raw28947step0 raw28947step0Labels = mixedMoment B raw28947step1 raw28947step1Labels := by
      have ha : raw28947step1 = raw28947step0 := by apply Matrix.ext; unfold raw28947step1 raw28947step0; decide +kernel
      have hl : raw28947step0Labels = labelEmbedding1 ∘ raw28947step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28947step0 raw28947step0Labels raw28947step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3200 node3200Labels := by rfl

def raw28948 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28948Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28948step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28948step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28948step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28948step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28948 raw28948Labels = mixedMoment B node2982 node2982Labels := by
  calc
    mixedMoment B raw28948 raw28948Labels = mixedMoment B raw28948step0 raw28948step0Labels := by
      have ha : raw28948step0 = (fun i j => raw28948 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28948step0 raw28948; decide +kernel
      have hl : raw28948step0Labels = raw28948Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28948 raw28948Labels permutation152 permutation7
    mixedMoment B raw28948step0 raw28948step0Labels = mixedMoment B raw28948step1 raw28948step1Labels := by
      have ha : raw28948step1 = raw28948step0 := by apply Matrix.ext; unfold raw28948step1 raw28948step0; decide +kernel
      have hl : raw28948step0Labels = labelEmbedding1 ∘ raw28948step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28948step0 raw28948step0Labels raw28948step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2982 node2982Labels := by rfl

def raw28949 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw28949Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28949step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw28949step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28949step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw28949step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28949 raw28949Labels = mixedMoment B node2919 node2919Labels := by
  calc
    mixedMoment B raw28949 raw28949Labels = mixedMoment B raw28949step0 raw28949step0Labels := by
      have ha : raw28949step0 = (fun i j => raw28949 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28949step0 raw28949; decide +kernel
      have hl : raw28949step0Labels = raw28949Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28949 raw28949Labels permutation152 permutation7
    mixedMoment B raw28949step0 raw28949step0Labels = mixedMoment B raw28949step1 raw28949step1Labels := by
      have ha : raw28949step1 = raw28949step0 := by apply Matrix.ext; unfold raw28949step1 raw28949step0; decide +kernel
      have hl : raw28949step0Labels = labelEmbedding1 ∘ raw28949step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28949step0 raw28949step0Labels raw28949step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2919 node2919Labels := by rfl

def raw28950 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw28950Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28950step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28950step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28950step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28950 raw28950Labels = mixedMoment B node2914 node2914Labels := by
  calc
    mixedMoment B raw28950 raw28950Labels = mixedMoment B raw28950step0 raw28950step0Labels := by
      have ha : raw28950step0 = (fun i j => raw28950 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28950step0 raw28950; decide +kernel
      have hl : raw28950step0Labels = raw28950Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28950 raw28950Labels permutation152 permutation7
    mixedMoment B raw28950step0 raw28950step0Labels = mixedMoment B raw28950step1 raw28950step1Labels := by
      have ha : raw28950step1 = raw28950step0 := by apply Matrix.ext; unfold raw28950step1 raw28950step0; decide +kernel
      have hl : raw28950step0Labels = labelEmbedding1 ∘ raw28950step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28950step0 raw28950step0Labels raw28950step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2914 node2914Labels := by rfl

def raw28951 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28951Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw28951step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-2, 1, 1], ![0, -3, 3]]
def raw28951step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28951step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw28951step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28951step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw28951step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28951 raw28951Labels = mixedMoment B node2966 node2966Labels := by
  calc
    mixedMoment B raw28951 raw28951Labels = mixedMoment B raw28951step0 raw28951step0Labels := by
      have hz : ∀ j, raw28951 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28951step0 = (fun i j => raw28951 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28951step0 raw28951; decide +kernel
      have hl : raw28951step0Labels = raw28951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28951 raw28951Labels permutation434 hz
    mixedMoment B raw28951step0 raw28951step0Labels = mixedMoment B raw28951step1 raw28951step1Labels := by
      have hz : ∀ j, raw28951step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28951step1 = (fun i j => raw28951step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28951step1 raw28951step0; decide +kernel
      have hl : raw28951step1Labels = raw28951step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28951step0 raw28951step0Labels permutation80 hz
    mixedMoment B raw28951step1 raw28951step1Labels = mixedMoment B raw28951step2 raw28951step2Labels := by
      have ha : raw28951step2 = (fun i j => raw28951step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28951step2 raw28951step1; decide +kernel
      have hl : raw28951step2Labels = raw28951step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28951step1 raw28951step1Labels permutation8 permutation7
    mixedMoment B raw28951step2 raw28951step2Labels = mixedMoment B raw28951step3 raw28951step3Labels := by
      have ha : raw28951step3 = raw28951step2 := by apply Matrix.ext; unfold raw28951step3 raw28951step2; decide +kernel
      have hl : raw28951step2Labels = labelEmbedding1 ∘ raw28951step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28951step2 raw28951step2Labels raw28951step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2966 node2966Labels := by rfl

def raw28952 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw28952Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw28952step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 3, 0]]
def raw28952step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28952step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw28952step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28952step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw28952step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28952 raw28952Labels = mixedMoment B node3208 node3208Labels := by
  calc
    mixedMoment B raw28952 raw28952Labels = mixedMoment B raw28952step0 raw28952step0Labels := by
      have hz : ∀ j, raw28952 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28952step0 = (fun i j => raw28952 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28952step0 raw28952; decide +kernel
      have hl : raw28952step0Labels = raw28952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28952 raw28952Labels permutation346 hz
    mixedMoment B raw28952step0 raw28952step0Labels = mixedMoment B raw28952step1 raw28952step1Labels := by
      have ha : raw28952step1 = (fun i j => raw28952step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28952step1 raw28952step0; decide +kernel
      have hl : raw28952step1Labels = raw28952step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28952step0 raw28952step0Labels permutation38 permutation5
    mixedMoment B raw28952step1 raw28952step1Labels = mixedMoment B raw28952step2 raw28952step2Labels := by
      have ha : raw28952step2 = -raw28952step1 := by apply Matrix.ext; change ∀ i j, raw28952step2 i j = -(raw28952step1 i j); unfold raw28952step2 raw28952step1; decide +kernel
      have hl : raw28952step2Labels = raw28952step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28952step2 raw28952step2Labels = mixedMoment B raw28952step3 raw28952step3Labels := by
      have ha : raw28952step3 = raw28952step2 := by apply Matrix.ext; unfold raw28952step3 raw28952step2; decide +kernel
      have hl : raw28952step2Labels = labelEmbedding1 ∘ raw28952step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28952step2 raw28952step2Labels raw28952step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3208 node3208Labels := by rfl

def raw28953 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw28953Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw28953step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw28953step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28953step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw28953step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28953 raw28953Labels = mixedMoment B node2993 node2993Labels := by
  calc
    mixedMoment B raw28953 raw28953Labels = mixedMoment B raw28953step0 raw28953step0Labels := by
      have hz : ∀ j, raw28953 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28953step0 = (fun i j => raw28953 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28953step0 raw28953; decide +kernel
      have hl : raw28953step0Labels = raw28953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28953 raw28953Labels permutation346 hz
    mixedMoment B raw28953step0 raw28953step0Labels = mixedMoment B raw28953step1 raw28953step1Labels := by
      have ha : raw28953step1 = (fun i j => raw28953step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28953step1 raw28953step0; decide +kernel
      have hl : raw28953step1Labels = raw28953step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28953step0 raw28953step0Labels permutation32 permutation7
    mixedMoment B raw28953step1 raw28953step1Labels = mixedMoment B raw28953step2 raw28953step2Labels := by
      have ha : raw28953step2 = raw28953step1 := by apply Matrix.ext; unfold raw28953step2 raw28953step1; decide +kernel
      have hl : raw28953step1Labels = labelEmbedding1 ∘ raw28953step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28953step1 raw28953step1Labels raw28953step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2993 node2993Labels := by rfl

def raw28954 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw28954Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28954step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw28954step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28954step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw28954step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28954 raw28954Labels = mixedMoment B node2932 node2932Labels := by
  calc
    mixedMoment B raw28954 raw28954Labels = mixedMoment B raw28954step0 raw28954step0Labels := by
      have ha : raw28954step0 = (fun i j => raw28954 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28954step0 raw28954; decide +kernel
      have hl : raw28954step0Labels = raw28954Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28954 raw28954Labels permutation152 permutation7
    mixedMoment B raw28954step0 raw28954step0Labels = mixedMoment B raw28954step1 raw28954step1Labels := by
      have ha : raw28954step1 = raw28954step0 := by apply Matrix.ext; unfold raw28954step1 raw28954step0; decide +kernel
      have hl : raw28954step0Labels = labelEmbedding1 ∘ raw28954step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28954step0 raw28954step0Labels raw28954step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2932 node2932Labels := by rfl

def raw28955 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -3, 3]]
def raw28955Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-2, 2, 0], ![0, -1, 1], ![0, -3, 3]]
def raw28955step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28955step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw28955step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28955step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw28955step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28955 raw28955Labels = mixedMoment B node2948 node2948Labels := by
  calc
    mixedMoment B raw28955 raw28955Labels = mixedMoment B raw28955step0 raw28955step0Labels := by
      have hz : ∀ j, raw28955 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28955step0 = (fun i j => raw28955 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28955step0 raw28955; decide +kernel
      have hl : raw28955step0Labels = raw28955Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28955 raw28955Labels permutation346 hz
    mixedMoment B raw28955step0 raw28955step0Labels = mixedMoment B raw28955step1 raw28955step1Labels := by
      have ha : raw28955step1 = (fun i j => raw28955step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28955step1 raw28955step0; decide +kernel
      have hl : raw28955step1Labels = raw28955step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28955step0 raw28955step0Labels permutation32 permutation7
    mixedMoment B raw28955step1 raw28955step1Labels = mixedMoment B raw28955step2 raw28955step2Labels := by
      have ha : raw28955step2 = raw28955step1 := by apply Matrix.ext; unfold raw28955step2 raw28955step1; decide +kernel
      have hl : raw28955step1Labels = labelEmbedding1 ∘ raw28955step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28955step1 raw28955step1Labels raw28955step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2948 node2948Labels := by rfl

def raw28956 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw28956Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw28956step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28956step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28956step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28956step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28956step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28956 raw28956Labels = mixedMoment B node2939 node2939Labels := by
  calc
    mixedMoment B raw28956 raw28956Labels = mixedMoment B raw28956step0 raw28956step0Labels := by
      have hz : ∀ j, raw28956 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28956step0 = (fun i j => raw28956 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28956step0 raw28956; decide +kernel
      have hl : raw28956step0Labels = raw28956Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28956 raw28956Labels permutation346 hz
    mixedMoment B raw28956step0 raw28956step0Labels = mixedMoment B raw28956step1 raw28956step1Labels := by
      have ha : raw28956step1 = (fun i j => raw28956step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw28956step1 raw28956step0; decide +kernel
      have hl : raw28956step1Labels = raw28956step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28956step0 raw28956step0Labels permutation32 permutation7
    mixedMoment B raw28956step1 raw28956step1Labels = mixedMoment B raw28956step2 raw28956step2Labels := by
      have ha : raw28956step2 = raw28956step1 := by apply Matrix.ext; unfold raw28956step2 raw28956step1; decide +kernel
      have hl : raw28956step1Labels = labelEmbedding1 ∘ raw28956step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28956step1 raw28956step1Labels raw28956step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2939 node2939Labels := by rfl

def raw28957 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw28957Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw28957step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28957step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28957step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28957step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw28957step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28957 raw28957Labels = mixedMoment B node1399 node1399Labels := by
  calc
    mixedMoment B raw28957 raw28957Labels = mixedMoment B raw28957step0 raw28957step0Labels := by
      have hz : ∀ j, raw28957 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28957step0 = (fun i j => raw28957 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28957step0 raw28957; decide +kernel
      have hl : raw28957step0Labels = raw28957Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28957 raw28957Labels permutation346 hz
    mixedMoment B raw28957step0 raw28957step0Labels = mixedMoment B raw28957step1 raw28957step1Labels := by
      have ha : raw28957step1 = (fun i j => raw28957step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28957step1 raw28957step0; decide +kernel
      have hl : raw28957step1Labels = raw28957step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28957step0 raw28957step0Labels permutation139 permutation5
    mixedMoment B raw28957step1 raw28957step1Labels = mixedMoment B raw28957step2 raw28957step2Labels := by
      have ha : raw28957step2 = raw28957step1 := by apply Matrix.ext; unfold raw28957step2 raw28957step1; decide +kernel
      have hl : raw28957step1Labels = labelEmbedding1 ∘ raw28957step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28957step1 raw28957step1Labels raw28957step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1399 node1399Labels := by rfl

def raw28958 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw28958Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw28958step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw28958step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28958step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw28958step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28958 raw28958Labels = mixedMoment B node1427 node1427Labels := by
  calc
    mixedMoment B raw28958 raw28958Labels = mixedMoment B raw28958step0 raw28958step0Labels := by
      have hz : ∀ j, raw28958 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28958step0 = (fun i j => raw28958 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28958step0 raw28958; decide +kernel
      have hl : raw28958step0Labels = raw28958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28958 raw28958Labels permutation346 hz
    mixedMoment B raw28958step0 raw28958step0Labels = mixedMoment B raw28958step1 raw28958step1Labels := by
      have ha : raw28958step1 = (fun i j => raw28958step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28958step1 raw28958step0; decide +kernel
      have hl : raw28958step1Labels = raw28958step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28958step0 raw28958step0Labels permutation149 permutation5
    mixedMoment B raw28958step1 raw28958step1Labels = mixedMoment B raw28958step2 raw28958step2Labels := by
      have ha : raw28958step2 = raw28958step1 := by apply Matrix.ext; unfold raw28958step2 raw28958step1; decide +kernel
      have hl : raw28958step1Labels = labelEmbedding1 ∘ raw28958step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28958step1 raw28958step1Labels raw28958step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1427 node1427Labels := by rfl

def raw28959 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw28959Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28959step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw28959step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28959step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw28959step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28959 raw28959Labels = mixedMoment B node1398 node1398Labels := by
  calc
    mixedMoment B raw28959 raw28959Labels = mixedMoment B raw28959step0 raw28959step0Labels := by
      have ha : raw28959step0 = (fun i j => raw28959 (permutation620 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28959step0 raw28959; decide +kernel
      have hl : raw28959step0Labels = raw28959Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28959 raw28959Labels permutation620 permutation5
    mixedMoment B raw28959step0 raw28959step0Labels = mixedMoment B raw28959step1 raw28959step1Labels := by
      have ha : raw28959step1 = raw28959step0 := by apply Matrix.ext; unfold raw28959step1 raw28959step0; decide +kernel
      have hl : raw28959step0Labels = labelEmbedding1 ∘ raw28959step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28959step0 raw28959step0Labels raw28959step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1398 node1398Labels := by rfl

def raw28960 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw28960Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-2, 2, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw28960step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw28960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw28960step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw28960step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw28960step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28960 raw28960Labels = mixedMoment B node1400 node1400Labels := by
  calc
    mixedMoment B raw28960 raw28960Labels = mixedMoment B raw28960step0 raw28960step0Labels := by
      have hz : ∀ j, raw28960 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28960step0 = (fun i j => raw28960 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28960step0 raw28960; decide +kernel
      have hl : raw28960step0Labels = raw28960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28960 raw28960Labels permutation346 hz
    mixedMoment B raw28960step0 raw28960step0Labels = mixedMoment B raw28960step1 raw28960step1Labels := by
      have ha : raw28960step1 = (fun i j => raw28960step0 (permutation138 i) (permutation5 j)) := by apply Matrix.ext; unfold raw28960step1 raw28960step0; decide +kernel
      have hl : raw28960step1Labels = raw28960step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28960step0 raw28960step0Labels permutation138 permutation5
    mixedMoment B raw28960step1 raw28960step1Labels = mixedMoment B raw28960step2 raw28960step2Labels := by
      have ha : raw28960step2 = raw28960step1 := by apply Matrix.ext; unfold raw28960step2 raw28960step1; decide +kernel
      have hl : raw28960step1Labels = labelEmbedding1 ∘ raw28960step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28960step1 raw28960step1Labels raw28960step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1400 node1400Labels := by rfl

def raw28961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw28961Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw28961step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw28961step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28961step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw28961step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28961 raw28961Labels = mixedMoment B node2394 node2394Labels := by
  calc
    mixedMoment B raw28961 raw28961Labels = mixedMoment B raw28961step0 raw28961step0Labels := by
      have hz : ∀ j, raw28961 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28961step0 = (fun i j => raw28961 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28961step0 raw28961; decide +kernel
      have hl : raw28961step0Labels = raw28961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28961 raw28961Labels permutation346 hz
    mixedMoment B raw28961step0 raw28961step0Labels = mixedMoment B raw28961step1 raw28961step1Labels := by
      have ha : raw28961step1 = (fun i j => raw28961step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28961step1 raw28961step0; decide +kernel
      have hl : raw28961step1Labels = raw28961step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28961step0 raw28961step0Labels permutation151 permutation2
    mixedMoment B raw28961step1 raw28961step1Labels = mixedMoment B raw28961step2 raw28961step2Labels := by
      have ha : raw28961step2 = -raw28961step1 := by apply Matrix.ext; change ∀ i j, raw28961step2 i j = -(raw28961step1 i j); unfold raw28961step2 raw28961step1; decide +kernel
      have hl : raw28961step2Labels = raw28961step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2394 node2394Labels := by rfl

def raw28962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw28962Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28962step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw28962step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28962step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw28962step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28962 raw28962Labels = mixedMoment B node2389 node2389Labels := by
  calc
    mixedMoment B raw28962 raw28962Labels = mixedMoment B raw28962step0 raw28962step0Labels := by
      have ha : raw28962step0 = (fun i j => raw28962 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28962step0 raw28962; decide +kernel
      have hl : raw28962step0Labels = raw28962Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28962 raw28962Labels permutation686 permutation2
    mixedMoment B raw28962step0 raw28962step0Labels = mixedMoment B raw28962step1 raw28962step1Labels := by
      have ha : raw28962step1 = -raw28962step0 := by apply Matrix.ext; change ∀ i j, raw28962step1 i j = -(raw28962step0 i j); unfold raw28962step1 raw28962step0; decide +kernel
      have hl : raw28962step1Labels = raw28962step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2389 node2389Labels := by rfl

def raw28963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw28963Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw28963step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw28963step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28963step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw28963step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28963 raw28963Labels = mixedMoment B node2400 node2400Labels := by
  calc
    mixedMoment B raw28963 raw28963Labels = mixedMoment B raw28963step0 raw28963step0Labels := by
      have hz : ∀ j, raw28963 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28963step0 = (fun i j => raw28963 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28963step0 raw28963; decide +kernel
      have hl : raw28963step0Labels = raw28963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28963 raw28963Labels permutation346 hz
    mixedMoment B raw28963step0 raw28963step0Labels = mixedMoment B raw28963step1 raw28963step1Labels := by
      have ha : raw28963step1 = (fun i j => raw28963step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28963step1 raw28963step0; decide +kernel
      have hl : raw28963step1Labels = raw28963step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28963step0 raw28963step0Labels permutation149 permutation2
    mixedMoment B raw28963step1 raw28963step1Labels = mixedMoment B raw28963step2 raw28963step2Labels := by
      have ha : raw28963step2 = -raw28963step1 := by apply Matrix.ext; change ∀ i j, raw28963step2 i j = -(raw28963step1 i j); unfold raw28963step2 raw28963step1; decide +kernel
      have hl : raw28963step2Labels = raw28963step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2400 node2400Labels := by rfl

def raw28964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw28964Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw28964step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw28964step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28964step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28964step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28964 raw28964Labels = mixedMoment B node2677 node2677Labels := by
  calc
    mixedMoment B raw28964 raw28964Labels = mixedMoment B raw28964step0 raw28964step0Labels := by
      have hz : ∀ j, raw28964 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28964step0 = (fun i j => raw28964 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28964step0 raw28964; decide +kernel
      have hl : raw28964step0Labels = raw28964Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28964 raw28964Labels permutation346 hz
    mixedMoment B raw28964step0 raw28964step0Labels = mixedMoment B raw28964step1 raw28964step1Labels := by
      have ha : raw28964step1 = (fun i j => raw28964step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28964step1 raw28964step0; decide +kernel
      have hl : raw28964step1Labels = raw28964step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28964step0 raw28964step0Labels permutation151 permutation2
    mixedMoment B raw28964step1 raw28964step1Labels = mixedMoment B raw28964step2 raw28964step2Labels := by
      have ha : raw28964step2 = -raw28964step1 := by apply Matrix.ext; change ∀ i j, raw28964step2 i j = -(raw28964step1 i j); unfold raw28964step2 raw28964step1; decide +kernel
      have hl : raw28964step2Labels = raw28964step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2677 node2677Labels := by rfl

def raw28965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw28965Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw28965step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw28965step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28965step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28965step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28965 raw28965Labels = mixedMoment B node3770 node3770Labels := by
  calc
    mixedMoment B raw28965 raw28965Labels = mixedMoment B raw28965step0 raw28965step0Labels := by
      have hz : ∀ j, raw28965 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28965step0 = (fun i j => raw28965 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28965step0 raw28965; decide +kernel
      have hl : raw28965step0Labels = raw28965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28965 raw28965Labels permutation346 hz
    mixedMoment B raw28965step0 raw28965step0Labels = mixedMoment B raw28965step1 raw28965step1Labels := by
      have ha : raw28965step1 = (fun i j => raw28965step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28965step1 raw28965step0; decide +kernel
      have hl : raw28965step1Labels = raw28965step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28965step0 raw28965step0Labels permutation151 permutation2
    mixedMoment B raw28965step1 raw28965step1Labels = mixedMoment B raw28965step2 raw28965step2Labels := by
      have ha : raw28965step2 = -raw28965step1 := by apply Matrix.ext; change ∀ i j, raw28965step2 i j = -(raw28965step1 i j); unfold raw28965step2 raw28965step1; decide +kernel
      have hl : raw28965step2Labels = raw28965step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3770 node3770Labels := by rfl

def raw28966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw28966Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28966step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw28966step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28966 raw28966Labels = mixedMoment B node2535 node2535Labels := by
  calc
    mixedMoment B raw28966 raw28966Labels = mixedMoment B raw28966step0 raw28966step0Labels := by
      have ha : raw28966step0 = (fun i j => raw28966 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28966step0 raw28966; decide +kernel
      have hl : raw28966step0Labels = raw28966Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28966 raw28966Labels permutation158 permutation2
    _ = mixedMoment B node2535 node2535Labels := by rfl

def raw28967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw28967Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw28967step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28967 raw28967Labels = mixedMoment B node2585 node2585Labels := by
  calc
    mixedMoment B raw28967 raw28967Labels = mixedMoment B raw28967step0 raw28967step0Labels := by
      have hz : ∀ j, raw28967 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28967step0 = (fun i j => raw28967 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28967step0 raw28967; decide +kernel
      have hl : raw28967step0Labels = raw28967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28967 raw28967Labels permutation346 hz
    _ = mixedMoment B node2585 node2585Labels := by rfl

def raw28968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw28968Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw28968step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28968step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw28968step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28968step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw28968step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28968 raw28968Labels = mixedMoment B node1928 node1928Labels := by
  calc
    mixedMoment B raw28968 raw28968Labels = mixedMoment B raw28968step0 raw28968step0Labels := by
      have hz : ∀ j, raw28968 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28968step0 = (fun i j => raw28968 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28968step0 raw28968; decide +kernel
      have hl : raw28968step0Labels = raw28968Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28968 raw28968Labels permutation346 hz
    mixedMoment B raw28968step0 raw28968step0Labels = mixedMoment B raw28968step1 raw28968step1Labels := by
      have ha : raw28968step1 = (fun i j => raw28968step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28968step1 raw28968step0; decide +kernel
      have hl : raw28968step1Labels = raw28968step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28968step0 raw28968step0Labels permutation151 permutation2
    mixedMoment B raw28968step1 raw28968step1Labels = mixedMoment B raw28968step2 raw28968step2Labels := by
      have ha : raw28968step2 = -raw28968step1 := by apply Matrix.ext; change ∀ i j, raw28968step2 i j = -(raw28968step1 i j); unfold raw28968step2 raw28968step1; decide +kernel
      have hl : raw28968step2Labels = raw28968step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1928 node1928Labels := by rfl

def raw28969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw28969Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw28969step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28969step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw28969step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28969 raw28969Labels = mixedMoment B node1921 node1921Labels := by
  calc
    mixedMoment B raw28969 raw28969Labels = mixedMoment B raw28969step0 raw28969step0Labels := by
      have ha : raw28969step0 = (fun i j => raw28969 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28969step0 raw28969; decide +kernel
      have hl : raw28969step0Labels = raw28969Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28969 raw28969Labels permutation686 permutation2
    mixedMoment B raw28969step0 raw28969step0Labels = mixedMoment B raw28969step1 raw28969step1Labels := by
      have ha : raw28969step1 = -raw28969step0 := by apply Matrix.ext; change ∀ i j, raw28969step1 i j = -(raw28969step0 i j); unfold raw28969step1 raw28969step0; decide +kernel
      have hl : raw28969step1Labels = raw28969step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1921 node1921Labels := by rfl

def raw28970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw28970Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw28970step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw28970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28970step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw28970step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28970 raw28970Labels = mixedMoment B node1945 node1945Labels := by
  calc
    mixedMoment B raw28970 raw28970Labels = mixedMoment B raw28970step0 raw28970step0Labels := by
      have hz : ∀ j, raw28970 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28970step0 = (fun i j => raw28970 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28970step0 raw28970; decide +kernel
      have hl : raw28970step0Labels = raw28970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28970 raw28970Labels permutation346 hz
    mixedMoment B raw28970step0 raw28970step0Labels = mixedMoment B raw28970step1 raw28970step1Labels := by
      have ha : raw28970step1 = (fun i j => raw28970step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28970step1 raw28970step0; decide +kernel
      have hl : raw28970step1Labels = raw28970step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28970step0 raw28970step0Labels permutation149 permutation2
    mixedMoment B raw28970step1 raw28970step1Labels = mixedMoment B raw28970step2 raw28970step2Labels := by
      have ha : raw28970step2 = -raw28970step1 := by apply Matrix.ext; change ∀ i j, raw28970step2 i j = -(raw28970step1 i j); unfold raw28970step2 raw28970step1; decide +kernel
      have hl : raw28970step2Labels = raw28970step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1945 node1945Labels := by rfl

def raw28971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, 0, -3]]
def raw28971Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![3, 0, -3]]
def raw28971step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw28971step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28971step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28971step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28971 raw28971Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw28971 raw28971Labels = mixedMoment B raw28971step0 raw28971step0Labels := by
      have hz : ∀ j, raw28971 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28971step0 = (fun i j => raw28971 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28971step0 raw28971; decide +kernel
      have hl : raw28971step0Labels = raw28971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28971 raw28971Labels permutation346 hz
    mixedMoment B raw28971step0 raw28971step0Labels = mixedMoment B raw28971step1 raw28971step1Labels := by
      have ha : raw28971step1 = (fun i j => raw28971step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28971step1 raw28971step0; decide +kernel
      have hl : raw28971step1Labels = raw28971step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28971step0 raw28971step0Labels permutation151 permutation2
    mixedMoment B raw28971step1 raw28971step1Labels = mixedMoment B raw28971step2 raw28971step2Labels := by
      have ha : raw28971step2 = -raw28971step1 := by apply Matrix.ext; change ∀ i j, raw28971step2 i j = -(raw28971step1 i j); unfold raw28971step2 raw28971step1; decide +kernel
      have hl : raw28971step2Labels = raw28971step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2215 node2215Labels := by rfl

def raw28972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw28972Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw28972step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw28972step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28972step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw28972step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28972 raw28972Labels = mixedMoment B node3478 node3478Labels := by
  calc
    mixedMoment B raw28972 raw28972Labels = mixedMoment B raw28972step0 raw28972step0Labels := by
      have hz : ∀ j, raw28972 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28972step0 = (fun i j => raw28972 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28972step0 raw28972; decide +kernel
      have hl : raw28972step0Labels = raw28972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28972 raw28972Labels permutation346 hz
    mixedMoment B raw28972step0 raw28972step0Labels = mixedMoment B raw28972step1 raw28972step1Labels := by
      have ha : raw28972step1 = (fun i j => raw28972step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28972step1 raw28972step0; decide +kernel
      have hl : raw28972step1Labels = raw28972step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28972step0 raw28972step0Labels permutation151 permutation2
    mixedMoment B raw28972step1 raw28972step1Labels = mixedMoment B raw28972step2 raw28972step2Labels := by
      have ha : raw28972step2 = -raw28972step1 := by apply Matrix.ext; change ∀ i j, raw28972step2 i j = -(raw28972step1 i j); unfold raw28972step2 raw28972step1; decide +kernel
      have hl : raw28972step2Labels = raw28972step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3478 node3478Labels := by rfl

def raw28973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw28973Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw28973step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28973step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28973step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28973 raw28973Labels = mixedMoment B node1863 node1863Labels := by
  calc
    mixedMoment B raw28973 raw28973Labels = mixedMoment B raw28973step0 raw28973step0Labels := by
      have ha : raw28973step0 = (fun i j => raw28973 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28973step0 raw28973; decide +kernel
      have hl : raw28973step0Labels = raw28973Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28973 raw28973Labels permutation680 permutation2
    mixedMoment B raw28973step0 raw28973step0Labels = mixedMoment B raw28973step1 raw28973step1Labels := by
      have ha : raw28973step1 = -raw28973step0 := by apply Matrix.ext; change ∀ i j, raw28973step1 i j = -(raw28973step0 i j); unfold raw28973step1 raw28973step0; decide +kernel
      have hl : raw28973step1Labels = raw28973step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1863 node1863Labels := by rfl

def raw28974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw28974Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw28974step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw28974step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28974step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28974step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28974 raw28974Labels = mixedMoment B node1773 node1773Labels := by
  calc
    mixedMoment B raw28974 raw28974Labels = mixedMoment B raw28974step0 raw28974step0Labels := by
      have hz : ∀ j, raw28974 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28974step0 = (fun i j => raw28974 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28974step0 raw28974; decide +kernel
      have hl : raw28974step0Labels = raw28974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28974 raw28974Labels permutation346 hz
    mixedMoment B raw28974step0 raw28974step0Labels = mixedMoment B raw28974step1 raw28974step1Labels := by
      have ha : raw28974step1 = (fun i j => raw28974step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28974step1 raw28974step0; decide +kernel
      have hl : raw28974step1Labels = raw28974step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28974step0 raw28974step0Labels permutation149 permutation2
    mixedMoment B raw28974step1 raw28974step1Labels = mixedMoment B raw28974step2 raw28974step2Labels := by
      have ha : raw28974step2 = -raw28974step1 := by apply Matrix.ext; change ∀ i j, raw28974step2 i j = -(raw28974step1 i j); unfold raw28974step2 raw28974step1; decide +kernel
      have hl : raw28974step2Labels = raw28974step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1773 node1773Labels := by rfl

def raw28975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![4, -1, -3]]
def raw28975Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, -1, 2], ![1, 0, -1], ![4, -1, -3]]
def raw28975step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28975step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw28975step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28975step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw28975step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28975 raw28975Labels = mixedMoment B node881 node881Labels := by
  calc
    mixedMoment B raw28975 raw28975Labels = mixedMoment B raw28975step0 raw28975step0Labels := by
      have hz : ∀ j, raw28975 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28975step0 = (fun i j => raw28975 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28975step0 raw28975; decide +kernel
      have hl : raw28975step0Labels = raw28975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28975 raw28975Labels permutation346 hz
    mixedMoment B raw28975step0 raw28975step0Labels = mixedMoment B raw28975step1 raw28975step1Labels := by
      have ha : raw28975step1 = (fun i j => raw28975step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28975step1 raw28975step0; decide +kernel
      have hl : raw28975step1Labels = raw28975step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28975step0 raw28975step0Labels permutation149 permutation2
    mixedMoment B raw28975step1 raw28975step1Labels = mixedMoment B raw28975step2 raw28975step2Labels := by
      have ha : raw28975step2 = -raw28975step1 := by apply Matrix.ext; change ∀ i j, raw28975step2 i j = -(raw28975step1 i j); unfold raw28975step2 raw28975step1; decide +kernel
      have hl : raw28975step2Labels = raw28975step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node881 node881Labels := by rfl

def raw28976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw28976Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw28976step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28976 raw28976Labels = mixedMoment B node2534 node2534Labels := by
  calc
    mixedMoment B raw28976 raw28976Labels = mixedMoment B raw28976step0 raw28976step0Labels := by
      have ha : raw28976step0 = (fun i j => raw28976 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28976step0 raw28976; decide +kernel
      have hl : raw28976step0Labels = raw28976Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28976 raw28976Labels permutation158 permutation2
    _ = mixedMoment B node2534 node2534Labels := by rfl

def raw28977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw28977Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw28977step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28977 raw28977Labels = mixedMoment B node2584 node2584Labels := by
  calc
    mixedMoment B raw28977 raw28977Labels = mixedMoment B raw28977step0 raw28977step0Labels := by
      have hz : ∀ j, raw28977 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28977step0 = (fun i j => raw28977 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28977step0 raw28977; decide +kernel
      have hl : raw28977step0Labels = raw28977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28977 raw28977Labels permutation346 hz
    _ = mixedMoment B node2584 node2584Labels := by rfl

def raw28978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw28978Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw28978step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28978 raw28978Labels = mixedMoment B node2538 node2538Labels := by
  calc
    mixedMoment B raw28978 raw28978Labels = mixedMoment B raw28978step0 raw28978step0Labels := by
      have hz : ∀ j, raw28978 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28978step0 = (fun i j => raw28978 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28978step0 raw28978; decide +kernel
      have hl : raw28978step0Labels = raw28978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28978 raw28978Labels permutation346 hz
    _ = mixedMoment B node2538 node2538Labels := by rfl

def raw28979 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -3, 3]]
def raw28979Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-2, 2, 0], ![0, -1, 1], ![0, -3, 3]]
def raw28979step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28979step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw28979step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28979 raw28979Labels = mixedMoment B node1917 node1917Labels := by
  calc
    mixedMoment B raw28979 raw28979Labels = mixedMoment B raw28979step0 raw28979step0Labels := by
      have hz : ∀ j, raw28979 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28979step0 = (fun i j => raw28979 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28979step0 raw28979; decide +kernel
      have hl : raw28979step0Labels = raw28979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28979 raw28979Labels permutation346 hz
    mixedMoment B raw28979step0 raw28979step0Labels = mixedMoment B raw28979step1 raw28979step1Labels := by
      have ha : raw28979step1 = (fun i j => raw28979step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28979step1 raw28979step0; decide +kernel
      have hl : raw28979step1Labels = raw28979step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28979step0 raw28979step0Labels permutation149 permutation4
    _ = mixedMoment B node1917 node1917Labels := by rfl

def raw28980 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -3, 3]]
def raw28980Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-2, 2, 0], ![0, -1, 1], ![0, -3, 3]]
def raw28980step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-3, 0, 3]]
def raw28980step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28980step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw28980step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28980 raw28980Labels = mixedMoment B node1799 node1799Labels := by
  calc
    mixedMoment B raw28980 raw28980Labels = mixedMoment B raw28980step0 raw28980step0Labels := by
      have hz : ∀ j, raw28980 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28980step0 = (fun i j => raw28980 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28980step0 raw28980; decide +kernel
      have hl : raw28980step0Labels = raw28980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28980 raw28980Labels permutation346 hz
    mixedMoment B raw28980step0 raw28980step0Labels = mixedMoment B raw28980step1 raw28980step1Labels := by
      have ha : raw28980step1 = (fun i j => raw28980step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28980step1 raw28980step0; decide +kernel
      have hl : raw28980step1Labels = raw28980step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28980step0 raw28980step0Labels permutation38 permutation4
    mixedMoment B raw28980step1 raw28980step1Labels = mixedMoment B raw28980step2 raw28980step2Labels := by
      have ha : raw28980step2 = -raw28980step1 := by apply Matrix.ext; change ∀ i j, raw28980step2 i j = -(raw28980step1 i j); unfold raw28980step2 raw28980step1; decide +kernel
      have hl : raw28980step2Labels = raw28980step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1799 node1799Labels := by rfl

def raw28981 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -3, 3]]
def raw28981Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28981step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw28981step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28981step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw28981step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28981 raw28981Labels = mixedMoment B node1784 node1784Labels := by
  calc
    mixedMoment B raw28981 raw28981Labels = mixedMoment B raw28981step0 raw28981step0Labels := by
      have ha : raw28981step0 = (fun i j => raw28981 (permutation200 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28981step0 raw28981; decide +kernel
      have hl : raw28981step0Labels = raw28981Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28981 raw28981Labels permutation200 permutation4
    mixedMoment B raw28981step0 raw28981step0Labels = mixedMoment B raw28981step1 raw28981step1Labels := by
      have ha : raw28981step1 = -raw28981step0 := by apply Matrix.ext; change ∀ i j, raw28981step1 i j = -(raw28981step0 i j); unfold raw28981step1 raw28981step0; decide +kernel
      have hl : raw28981step1Labels = raw28981step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1784 node1784Labels := by rfl

def raw28982 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw28982Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw28982step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw28982step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28982 raw28982Labels = mixedMoment B node1911 node1911Labels := by
  calc
    mixedMoment B raw28982 raw28982Labels = mixedMoment B raw28982step0 raw28982step0Labels := by
      have hz : ∀ j, raw28982 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28982step0 = (fun i j => raw28982 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28982step0 raw28982; decide +kernel
      have hl : raw28982step0Labels = raw28982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28982 raw28982Labels permutation346 hz
    mixedMoment B raw28982step0 raw28982step0Labels = mixedMoment B raw28982step1 raw28982step1Labels := by
      have ha : raw28982step1 = (fun i j => raw28982step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28982step1 raw28982step0; decide +kernel
      have hl : raw28982step1Labels = raw28982step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28982step0 raw28982step0Labels permutation149 permutation4
    _ = mixedMoment B node1911 node1911Labels := by rfl

def raw28983 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -3, 3]]
def raw28983Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-2, 2, 0], ![1, -2, 1], ![0, -3, 3]]
def raw28983step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28983step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw28983step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28983 raw28983Labels = mixedMoment B node1765 node1765Labels := by
  calc
    mixedMoment B raw28983 raw28983Labels = mixedMoment B raw28983step0 raw28983step0Labels := by
      have hz : ∀ j, raw28983 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28983step0 = (fun i j => raw28983 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28983step0 raw28983; decide +kernel
      have hl : raw28983step0Labels = raw28983Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28983 raw28983Labels permutation346 hz
    mixedMoment B raw28983step0 raw28983step0Labels = mixedMoment B raw28983step1 raw28983step1Labels := by
      have ha : raw28983step1 = (fun i j => raw28983step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28983step1 raw28983step0; decide +kernel
      have hl : raw28983step1Labels = raw28983step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28983step0 raw28983step0Labels permutation149 permutation4
    _ = mixedMoment B node1765 node1765Labels := by rfl

def raw28984 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![1, -4, 3]]
def raw28984Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-2, 2, 0], ![0, -1, 1], ![1, -4, 3]]
def raw28984step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw28984step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28984 raw28984Labels = mixedMoment B node872 node872Labels := by
  calc
    mixedMoment B raw28984 raw28984Labels = mixedMoment B raw28984step0 raw28984step0Labels := by
      have hz : ∀ j, raw28984 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28984step0 = (fun i j => raw28984 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28984step0 raw28984; decide +kernel
      have hl : raw28984step0Labels = raw28984Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28984 raw28984Labels permutation346 hz
    mixedMoment B raw28984step0 raw28984step0Labels = mixedMoment B raw28984step1 raw28984step1Labels := by
      have ha : raw28984step1 = (fun i j => raw28984step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28984step1 raw28984step0; decide +kernel
      have hl : raw28984step1Labels = raw28984step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28984step0 raw28984step0Labels permutation149 permutation4
    _ = mixedMoment B node872 node872Labels := by rfl

def raw28985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw28985Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28985step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw28985step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28985step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw28985step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28985 raw28985Labels = mixedMoment B node2379 node2379Labels := by
  calc
    mixedMoment B raw28985 raw28985Labels = mixedMoment B raw28985step0 raw28985step0Labels := by
      have ha : raw28985step0 = (fun i j => raw28985 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28985step0 raw28985; decide +kernel
      have hl : raw28985step0Labels = raw28985Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28985 raw28985Labels permutation682 permutation2
    mixedMoment B raw28985step0 raw28985step0Labels = mixedMoment B raw28985step1 raw28985step1Labels := by
      have ha : raw28985step1 = -raw28985step0 := by apply Matrix.ext; change ∀ i j, raw28985step1 i j = -(raw28985step0 i j); unfold raw28985step1 raw28985step0; decide +kernel
      have hl : raw28985step1Labels = raw28985step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2379 node2379Labels := by rfl

def raw28986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw28986Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw28986step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28986step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28986step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28986 raw28986Labels = mixedMoment B node2382 node2382Labels := by
  calc
    mixedMoment B raw28986 raw28986Labels = mixedMoment B raw28986step0 raw28986step0Labels := by
      have ha : raw28986step0 = (fun i j => raw28986 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28986step0 raw28986; decide +kernel
      have hl : raw28986step0Labels = raw28986Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28986 raw28986Labels permutation686 permutation2
    mixedMoment B raw28986step0 raw28986step0Labels = mixedMoment B raw28986step1 raw28986step1Labels := by
      have ha : raw28986step1 = -raw28986step0 := by apply Matrix.ext; change ∀ i j, raw28986step1 i j = -(raw28986step0 i j); unfold raw28986step1 raw28986step0; decide +kernel
      have hl : raw28986step1Labels = raw28986step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2382 node2382Labels := by rfl

def raw28987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw28987Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28987step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw28987step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28987step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28987step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28987 raw28987Labels = mixedMoment B node2382 node2382Labels := by
  calc
    mixedMoment B raw28987 raw28987Labels = mixedMoment B raw28987step0 raw28987step0Labels := by
      have ha : raw28987step0 = (fun i j => raw28987 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28987step0 raw28987; decide +kernel
      have hl : raw28987step0Labels = raw28987Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28987 raw28987Labels permutation680 permutation2
    mixedMoment B raw28987step0 raw28987step0Labels = mixedMoment B raw28987step1 raw28987step1Labels := by
      have ha : raw28987step1 = -raw28987step0 := by apply Matrix.ext; change ∀ i j, raw28987step1 i j = -(raw28987step0 i j); unfold raw28987step1 raw28987step0; decide +kernel
      have hl : raw28987step1Labels = raw28987step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2382 node2382Labels := by rfl

def raw28988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw28988Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28988step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28988step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28988step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28988step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28988 raw28988Labels = mixedMoment B node2661 node2661Labels := by
  calc
    mixedMoment B raw28988 raw28988Labels = mixedMoment B raw28988step0 raw28988step0Labels := by
      have ha : raw28988step0 = (fun i j => raw28988 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28988step0 raw28988; decide +kernel
      have hl : raw28988step0Labels = raw28988Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28988 raw28988Labels permutation682 permutation2
    mixedMoment B raw28988step0 raw28988step0Labels = mixedMoment B raw28988step1 raw28988step1Labels := by
      have ha : raw28988step1 = -raw28988step0 := by apply Matrix.ext; change ∀ i j, raw28988step1 i j = -(raw28988step0 i j); unfold raw28988step1 raw28988step0; decide +kernel
      have hl : raw28988step1Labels = raw28988step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2661 node2661Labels := by rfl

def raw28989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28989Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28989step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28989step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28989step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28989step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28989 raw28989Labels = mixedMoment B node3757 node3757Labels := by
  calc
    mixedMoment B raw28989 raw28989Labels = mixedMoment B raw28989step0 raw28989step0Labels := by
      have ha : raw28989step0 = (fun i j => raw28989 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28989step0 raw28989; decide +kernel
      have hl : raw28989step0Labels = raw28989Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28989 raw28989Labels permutation682 permutation2
    mixedMoment B raw28989step0 raw28989step0Labels = mixedMoment B raw28989step1 raw28989step1Labels := by
      have ha : raw28989step1 = -raw28989step0 := by apply Matrix.ext; change ∀ i j, raw28989step1 i j = -(raw28989step0 i j); unfold raw28989step1 raw28989step0; decide +kernel
      have hl : raw28989step1Labels = raw28989step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3757 node3757Labels := by rfl

def raw28990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28990Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28990step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28990step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28990 raw28990Labels = mixedMoment B node2551 node2551Labels := by
  calc
    mixedMoment B raw28990 raw28990Labels = mixedMoment B raw28990step0 raw28990step0Labels := by
      have ha : raw28990step0 = (fun i j => raw28990 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28990step0 raw28990; decide +kernel
      have hl : raw28990step0Labels = raw28990Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28990 raw28990Labels permutation158 permutation2
    _ = mixedMoment B node2551 node2551Labels := by rfl

def raw28991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28991Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28991 raw28991Labels = mixedMoment B node2551 node2551Labels := by
  calc
    _ = mixedMoment B node2551 node2551Labels := by rfl

def raw28992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw28992Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28992step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw28992step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28992step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28992step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28992 raw28992Labels = mixedMoment B node1908 node1908Labels := by
  calc
    mixedMoment B raw28992 raw28992Labels = mixedMoment B raw28992step0 raw28992step0Labels := by
      have ha : raw28992step0 = (fun i j => raw28992 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28992step0 raw28992; decide +kernel
      have hl : raw28992step0Labels = raw28992Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28992 raw28992Labels permutation686 permutation2
    mixedMoment B raw28992step0 raw28992step0Labels = mixedMoment B raw28992step1 raw28992step1Labels := by
      have ha : raw28992step1 = -raw28992step0 := by apply Matrix.ext; change ∀ i j, raw28992step1 i j = -(raw28992step0 i j); unfold raw28992step1 raw28992step0; decide +kernel
      have hl : raw28992step1Labels = raw28992step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1908 node1908Labels := by rfl

def raw28993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw28993Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28993step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28993step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28993step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28993step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28993 raw28993Labels = mixedMoment B node1875 node1875Labels := by
  calc
    mixedMoment B raw28993 raw28993Labels = mixedMoment B raw28993step0 raw28993step0Labels := by
      have ha : raw28993step0 = (fun i j => raw28993 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28993step0 raw28993; decide +kernel
      have hl : raw28993step0Labels = raw28993Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28993 raw28993Labels permutation686 permutation2
    mixedMoment B raw28993step0 raw28993step0Labels = mixedMoment B raw28993step1 raw28993step1Labels := by
      have ha : raw28993step1 = -raw28993step0 := by apply Matrix.ext; change ∀ i j, raw28993step1 i j = -(raw28993step0 i j); unfold raw28993step1 raw28993step0; decide +kernel
      have hl : raw28993step1Labels = raw28993step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1875 node1875Labels := by rfl

def raw28994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw28994Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28994step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28994step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28994step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28994step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28994 raw28994Labels = mixedMoment B node1760 node1760Labels := by
  calc
    mixedMoment B raw28994 raw28994Labels = mixedMoment B raw28994step0 raw28994step0Labels := by
      have ha : raw28994step0 = (fun i j => raw28994 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28994step0 raw28994; decide +kernel
      have hl : raw28994step0Labels = raw28994Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28994 raw28994Labels permutation686 permutation2
    mixedMoment B raw28994step0 raw28994step0Labels = mixedMoment B raw28994step1 raw28994step1Labels := by
      have ha : raw28994step1 = -raw28994step0 := by apply Matrix.ext; change ∀ i j, raw28994step1 i j = -(raw28994step0 i j); unfold raw28994step1 raw28994step0; decide +kernel
      have hl : raw28994step1Labels = raw28994step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1760 node1760Labels := by rfl

def raw28995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw28995Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28995step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw28995step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28995step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28995step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28995 raw28995Labels = mixedMoment B node865 node865Labels := by
  calc
    mixedMoment B raw28995 raw28995Labels = mixedMoment B raw28995step0 raw28995step0Labels := by
      have ha : raw28995step0 = (fun i j => raw28995 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28995step0 raw28995; decide +kernel
      have hl : raw28995step0Labels = raw28995Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28995 raw28995Labels permutation686 permutation2
    mixedMoment B raw28995step0 raw28995step0Labels = mixedMoment B raw28995step1 raw28995step1Labels := by
      have ha : raw28995step1 = -raw28995step0 := by apply Matrix.ext; change ∀ i j, raw28995step1 i j = -(raw28995step0 i j); unfold raw28995step1 raw28995step0; decide +kernel
      have hl : raw28995step1Labels = raw28995step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node865 node865Labels := by rfl

def raw28996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw28996Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28996step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw28996step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28996step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw28996step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28996 raw28996Labels = mixedMoment B node3459 node3459Labels := by
  calc
    mixedMoment B raw28996 raw28996Labels = mixedMoment B raw28996step0 raw28996step0Labels := by
      have ha : raw28996step0 = (fun i j => raw28996 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28996step0 raw28996; decide +kernel
      have hl : raw28996step0Labels = raw28996Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28996 raw28996Labels permutation682 permutation2
    mixedMoment B raw28996step0 raw28996step0Labels = mixedMoment B raw28996step1 raw28996step1Labels := by
      have ha : raw28996step1 = -raw28996step0 := by apply Matrix.ext; change ∀ i j, raw28996step1 i j = -(raw28996step0 i j); unfold raw28996step1 raw28996step0; decide +kernel
      have hl : raw28996step1Labels = raw28996step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3459 node3459Labels := by rfl

def raw28997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw28997Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28997step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw28997step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28997 raw28997Labels = mixedMoment B node2550 node2550Labels := by
  calc
    mixedMoment B raw28997 raw28997Labels = mixedMoment B raw28997step0 raw28997step0Labels := by
      have ha : raw28997step0 = (fun i j => raw28997 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28997step0 raw28997; decide +kernel
      have hl : raw28997step0Labels = raw28997Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28997 raw28997Labels permutation158 permutation2
    _ = mixedMoment B node2550 node2550Labels := by rfl

def raw28998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw28998Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28998 raw28998Labels = mixedMoment B node2550 node2550Labels := by
  calc
    _ = mixedMoment B node2550 node2550Labels := by rfl

def raw28999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw28999Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28999 raw28999Labels = mixedMoment B node2540 node2540Labels := by
  calc
    _ = mixedMoment B node2540 node2540Labels := by rfl

def raw29000 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29000Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29000step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29000step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29000 raw29000Labels = mixedMoment B node1907 node1907Labels := by
  calc
    mixedMoment B raw29000 raw29000Labels = mixedMoment B raw29000step0 raw29000step0Labels := by
      have ha : raw29000step0 = (fun i j => raw29000 (permutation674 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29000step0 raw29000; decide +kernel
      have hl : raw29000step0Labels = raw29000Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29000 raw29000Labels permutation674 permutation4
    _ = mixedMoment B node1907 node1907Labels := by rfl

def raw29001 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29001Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29001step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29001step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29001 raw29001Labels = mixedMoment B node1874 node1874Labels := by
  calc
    mixedMoment B raw29001 raw29001Labels = mixedMoment B raw29001step0 raw29001step0Labels := by
      have ha : raw29001step0 = (fun i j => raw29001 (permutation674 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29001step0 raw29001; decide +kernel
      have hl : raw29001step0Labels = raw29001Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29001 raw29001Labels permutation674 permutation4
    _ = mixedMoment B node1874 node1874Labels := by rfl

def raw29002 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29002Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29002step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw29002step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29002 raw29002Labels = mixedMoment B node1911 node1911Labels := by
  calc
    mixedMoment B raw29002 raw29002Labels = mixedMoment B raw29002step0 raw29002step0Labels := by
      have hz : ∀ j, raw29002 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29002step0 = (fun i j => raw29002 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29002step0 raw29002; decide +kernel
      have hl : raw29002step0Labels = raw29002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29002 raw29002Labels permutation434 hz
    mixedMoment B raw29002step0 raw29002step0Labels = mixedMoment B raw29002step1 raw29002step1Labels := by
      have ha : raw29002step1 = (fun i j => raw29002step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29002step1 raw29002step0; decide +kernel
      have hl : raw29002step1Labels = raw29002step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29002step0 raw29002step0Labels permutation149 permutation4
    _ = mixedMoment B node1911 node1911Labels := by rfl

def raw29003 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw29003Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29003step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29003step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29003 raw29003Labels = mixedMoment B node1759 node1759Labels := by
  calc
    mixedMoment B raw29003 raw29003Labels = mixedMoment B raw29003step0 raw29003step0Labels := by
      have ha : raw29003step0 = (fun i j => raw29003 (permutation674 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29003step0 raw29003; decide +kernel
      have hl : raw29003step0Labels = raw29003Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29003 raw29003Labels permutation674 permutation4
    _ = mixedMoment B node1759 node1759Labels := by rfl

def raw29004 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -4, 3]]
def raw29004Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29004step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29004step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29004 raw29004Labels = mixedMoment B node864 node864Labels := by
  calc
    mixedMoment B raw29004 raw29004Labels = mixedMoment B raw29004step0 raw29004step0Labels := by
      have ha : raw29004step0 = (fun i j => raw29004 (permutation674 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29004step0 raw29004; decide +kernel
      have hl : raw29004step0Labels = raw29004Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29004 raw29004Labels permutation674 permutation4
    _ = mixedMoment B node864 node864Labels := by rfl

def raw29005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw29005Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw29005step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29005step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29005step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29005step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw29005step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29005 raw29005Labels = mixedMoment B node2079 node2079Labels := by
  calc
    mixedMoment B raw29005 raw29005Labels = mixedMoment B raw29005step0 raw29005step0Labels := by
      have hz : ∀ j, raw29005 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29005step0 = (fun i j => raw29005 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29005step0 raw29005; decide +kernel
      have hl : raw29005step0Labels = raw29005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29005 raw29005Labels permutation434 hz
    mixedMoment B raw29005step0 raw29005step0Labels = mixedMoment B raw29005step1 raw29005step1Labels := by
      have ha : raw29005step1 = (fun i j => raw29005step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29005step1 raw29005step0; decide +kernel
      have hl : raw29005step1Labels = raw29005step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29005step0 raw29005step0Labels permutation151 permutation2
    mixedMoment B raw29005step1 raw29005step1Labels = mixedMoment B raw29005step2 raw29005step2Labels := by
      have ha : raw29005step2 = -raw29005step1 := by apply Matrix.ext; change ∀ i j, raw29005step2 i j = -(raw29005step1 i j); unfold raw29005step2 raw29005step1; decide +kernel
      have hl : raw29005step2Labels = raw29005step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2079 node2079Labels := by rfl

def raw29006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw29006Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw29006step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw29006step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29006step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29006step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29006 raw29006Labels = mixedMoment B node2082 node2082Labels := by
  calc
    mixedMoment B raw29006 raw29006Labels = mixedMoment B raw29006step0 raw29006step0Labels := by
      have hz : ∀ j, raw29006 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29006step0 = (fun i j => raw29006 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29006step0 raw29006; decide +kernel
      have hl : raw29006step0Labels = raw29006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29006 raw29006Labels permutation434 hz
    mixedMoment B raw29006step0 raw29006step0Labels = mixedMoment B raw29006step1 raw29006step1Labels := by
      have ha : raw29006step1 = (fun i j => raw29006step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29006step1 raw29006step0; decide +kernel
      have hl : raw29006step1Labels = raw29006step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29006step0 raw29006step0Labels permutation151 permutation2
    mixedMoment B raw29006step1 raw29006step1Labels = mixedMoment B raw29006step2 raw29006step2Labels := by
      have ha : raw29006step2 = -raw29006step1 := by apply Matrix.ext; change ∀ i j, raw29006step2 i j = -(raw29006step1 i j); unfold raw29006step2 raw29006step1; decide +kernel
      have hl : raw29006step2Labels = raw29006step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2082 node2082Labels := by rfl

def raw29007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw29007Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw29007step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw29007step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29007step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29007step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29007 raw29007Labels = mixedMoment B node2101 node2101Labels := by
  calc
    mixedMoment B raw29007 raw29007Labels = mixedMoment B raw29007step0 raw29007step0Labels := by
      have hz : ∀ j, raw29007 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29007step0 = (fun i j => raw29007 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29007step0 raw29007; decide +kernel
      have hl : raw29007step0Labels = raw29007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29007 raw29007Labels permutation434 hz
    mixedMoment B raw29007step0 raw29007step0Labels = mixedMoment B raw29007step1 raw29007step1Labels := by
      have ha : raw29007step1 = (fun i j => raw29007step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29007step1 raw29007step0; decide +kernel
      have hl : raw29007step1Labels = raw29007step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29007step0 raw29007step0Labels permutation151 permutation2
    mixedMoment B raw29007step1 raw29007step1Labels = mixedMoment B raw29007step2 raw29007step2Labels := by
      have ha : raw29007step2 = -raw29007step1 := by apply Matrix.ext; change ∀ i j, raw29007step2 i j = -(raw29007step1 i j); unfold raw29007step2 raw29007step1; decide +kernel
      have hl : raw29007step2Labels = raw29007step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2101 node2101Labels := by rfl

def raw29008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw29008Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw29008step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29008step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29008 raw29008Labels = mixedMoment B node2075 node2075Labels := by
  calc
    mixedMoment B raw29008 raw29008Labels = mixedMoment B raw29008step0 raw29008step0Labels := by
      have ha : raw29008step0 = (fun i j => raw29008 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29008step0 raw29008; decide +kernel
      have hl : raw29008step0Labels = raw29008Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29008 raw29008Labels permutation682 permutation2
    mixedMoment B raw29008step0 raw29008step0Labels = mixedMoment B raw29008step1 raw29008step1Labels := by
      have ha : raw29008step1 = -raw29008step0 := by apply Matrix.ext; change ∀ i j, raw29008step1 i j = -(raw29008step0 i j); unfold raw29008step1 raw29008step0; decide +kernel
      have hl : raw29008step1Labels = raw29008step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2075 node2075Labels := by rfl

def raw29009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw29009Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![3, 0, -3]]
def raw29009step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw29009step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29009step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29009step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29009 raw29009Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw29009 raw29009Labels = mixedMoment B raw29009step0 raw29009step0Labels := by
      have hz : ∀ j, raw29009 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29009step0 = (fun i j => raw29009 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29009step0 raw29009; decide +kernel
      have hl : raw29009step0Labels = raw29009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29009 raw29009Labels permutation434 hz
    mixedMoment B raw29009step0 raw29009step0Labels = mixedMoment B raw29009step1 raw29009step1Labels := by
      have ha : raw29009step1 = (fun i j => raw29009step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29009step1 raw29009step0; decide +kernel
      have hl : raw29009step1Labels = raw29009step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29009step0 raw29009step0Labels permutation145 permutation2
    mixedMoment B raw29009step1 raw29009step1Labels = mixedMoment B raw29009step2 raw29009step2Labels := by
      have ha : raw29009step2 = -raw29009step1 := by apply Matrix.ext; change ∀ i j, raw29009step2 i j = -(raw29009step1 i j); unfold raw29009step2 raw29009step1; decide +kernel
      have hl : raw29009step2Labels = raw29009step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2205 node2205Labels := by rfl

def raw29010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw29010Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw29010step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw29010step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29010step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29010step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29010 raw29010Labels = mixedMoment B node3564 node3564Labels := by
  calc
    mixedMoment B raw29010 raw29010Labels = mixedMoment B raw29010step0 raw29010step0Labels := by
      have hz : ∀ j, raw29010 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29010step0 = (fun i j => raw29010 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29010step0 raw29010; decide +kernel
      have hl : raw29010step0Labels = raw29010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29010 raw29010Labels permutation434 hz
    mixedMoment B raw29010step0 raw29010step0Labels = mixedMoment B raw29010step1 raw29010step1Labels := by
      have ha : raw29010step1 = (fun i j => raw29010step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29010step1 raw29010step0; decide +kernel
      have hl : raw29010step1Labels = raw29010step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29010step0 raw29010step0Labels permutation151 permutation2
    mixedMoment B raw29010step1 raw29010step1Labels = mixedMoment B raw29010step2 raw29010step2Labels := by
      have ha : raw29010step2 = -raw29010step1 := by apply Matrix.ext; change ∀ i j, raw29010step2 i j = -(raw29010step1 i j); unfold raw29010step2 raw29010step1; decide +kernel
      have hl : raw29010step2Labels = raw29010step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3564 node3564Labels := by rfl

def raw29011 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![0, 0], ![-1, 1], ![3, -3]]
def raw29011Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29011step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![-1, 1], ![3, -3]]
def raw29011step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29011step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw29011step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29011step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw29011step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29011 raw29011Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw29011 raw29011Labels = mixedMoment B raw29011step0 raw29011step0Labels := by
      have hz : ∀ j, raw29011 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29011step0 = (fun i j => raw29011 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29011step0 raw29011; decide +kernel
      have hl : raw29011step0Labels = raw29011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29011 raw29011Labels permutation434 hz
    mixedMoment B raw29011step0 raw29011step0Labels = mixedMoment B raw29011step1 raw29011step1Labels := by
      have ha : raw29011step1 = (fun i j => raw29011step0 (permutation143 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29011step1 raw29011step0; decide +kernel
      have hl : raw29011step1Labels = raw29011step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29011step0 raw29011step0Labels permutation143 permutation0
    mixedMoment B raw29011step1 raw29011step1Labels = mixedMoment B raw29011step2 raw29011step2Labels := by
      have ha : raw29011step2 = -raw29011step1 := by apply Matrix.ext; change ∀ i j, raw29011step2 i j = -(raw29011step1 i j); unfold raw29011step2 raw29011step1; decide +kernel
      have hl : raw29011step2Labels = raw29011step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw29012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw29012Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![3, 0, -3]]
def raw29012step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29012step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29012 raw29012Labels = mixedMoment B node1123 node1123Labels := by
  calc
    mixedMoment B raw29012 raw29012Labels = mixedMoment B raw29012step0 raw29012step0Labels := by
      have hz : ∀ j, raw29012 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29012step0 = (fun i j => raw29012 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29012step0 raw29012; decide +kernel
      have hl : raw29012step0Labels = raw29012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29012 raw29012Labels permutation434 hz
    mixedMoment B raw29012step0 raw29012step0Labels = mixedMoment B raw29012step1 raw29012step1Labels := by
      have ha : raw29012step1 = (fun i j => raw29012step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29012step1 raw29012step0; decide +kernel
      have hl : raw29012step1Labels = raw29012step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29012step0 raw29012step0Labels permutation34 permutation2
    _ = mixedMoment B node1123 node1123Labels := by rfl

def raw29013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw29013Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![3, 0, -3]]
def raw29013step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw29013step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29013step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw29013step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29013 raw29013Labels = mixedMoment B node1880 node1880Labels := by
  calc
    mixedMoment B raw29013 raw29013Labels = mixedMoment B raw29013step0 raw29013step0Labels := by
      have hz : ∀ j, raw29013 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29013step0 = (fun i j => raw29013 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29013step0 raw29013; decide +kernel
      have hl : raw29013step0Labels = raw29013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29013 raw29013Labels permutation434 hz
    mixedMoment B raw29013step0 raw29013step0Labels = mixedMoment B raw29013step1 raw29013step1Labels := by
      have ha : raw29013step1 = (fun i j => raw29013step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29013step1 raw29013step0; decide +kernel
      have hl : raw29013step1Labels = raw29013step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29013step0 raw29013step0Labels permutation145 permutation2
    mixedMoment B raw29013step1 raw29013step1Labels = mixedMoment B raw29013step2 raw29013step2Labels := by
      have ha : raw29013step2 = -raw29013step1 := by apply Matrix.ext; change ∀ i j, raw29013step2 i j = -(raw29013step1 i j); unfold raw29013step2 raw29013step1; decide +kernel
      have hl : raw29013step2Labels = raw29013step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1880 node1880Labels := by rfl

def raw29014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw29014Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29014step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29014step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29014step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29014step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29014 raw29014Labels = mixedMoment B node1875 node1875Labels := by
  calc
    mixedMoment B raw29014 raw29014Labels = mixedMoment B raw29014step0 raw29014step0Labels := by
      have ha : raw29014step0 = (fun i j => raw29014 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29014step0 raw29014; decide +kernel
      have hl : raw29014step0Labels = raw29014Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29014 raw29014Labels permutation646 permutation2
    mixedMoment B raw29014step0 raw29014step0Labels = mixedMoment B raw29014step1 raw29014step1Labels := by
      have ha : raw29014step1 = -raw29014step0 := by apply Matrix.ext; change ∀ i j, raw29014step1 i j = -(raw29014step0 i j); unfold raw29014step1 raw29014step0; decide +kernel
      have hl : raw29014step1Labels = raw29014step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1875 node1875Labels := by rfl

def raw29015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw29015Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![3, 0, -3]]
def raw29015step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29015step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29015step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29015step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29015 raw29015Labels = mixedMoment B node1914 node1914Labels := by
  calc
    mixedMoment B raw29015 raw29015Labels = mixedMoment B raw29015step0 raw29015step0Labels := by
      have hz : ∀ j, raw29015 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29015step0 = (fun i j => raw29015 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29015step0 raw29015; decide +kernel
      have hl : raw29015step0Labels = raw29015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29015 raw29015Labels permutation434 hz
    mixedMoment B raw29015step0 raw29015step0Labels = mixedMoment B raw29015step1 raw29015step1Labels := by
      have ha : raw29015step1 = (fun i j => raw29015step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29015step1 raw29015step0; decide +kernel
      have hl : raw29015step1Labels = raw29015step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29015step0 raw29015step0Labels permutation145 permutation2
    mixedMoment B raw29015step1 raw29015step1Labels = mixedMoment B raw29015step2 raw29015step2Labels := by
      have ha : raw29015step2 = -raw29015step1 := by apply Matrix.ext; change ∀ i j, raw29015step2 i j = -(raw29015step1 i j); unfold raw29015step2 raw29015step1; decide +kernel
      have hl : raw29015step2Labels = raw29015step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1914 node1914Labels := by rfl

def raw29016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw29016Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw29016step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29016step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29016 raw29016Labels = mixedMoment B node2504 node2504Labels := by
  calc
    mixedMoment B raw29016 raw29016Labels = mixedMoment B raw29016step0 raw29016step0Labels := by
      have hz : ∀ j, raw29016 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29016step0 = (fun i j => raw29016 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29016step0 raw29016; decide +kernel
      have hl : raw29016step0Labels = raw29016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29016 raw29016Labels permutation434 hz
    mixedMoment B raw29016step0 raw29016step0Labels = mixedMoment B raw29016step1 raw29016step1Labels := by
      have ha : raw29016step1 = (fun i j => raw29016step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29016step1 raw29016step0; decide +kernel
      have hl : raw29016step1Labels = raw29016step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29016step0 raw29016step0Labels permutation34 permutation2
    _ = mixedMoment B node2504 node2504Labels := by rfl

def raw29017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw29017Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw29017step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29017 raw29017Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw29017 raw29017Labels = mixedMoment B raw29017step0 raw29017step0Labels := by
      have hz : ∀ j, raw29017 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29017step0 = (fun i j => raw29017 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29017step0 raw29017; decide +kernel
      have hl : raw29017step0Labels = raw29017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29017 raw29017Labels permutation434 hz
    _ = mixedMoment B node2719 node2719Labels := by rfl

def raw29018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw29018Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29018step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw29018step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29018 raw29018Labels = mixedMoment B node2476 node2476Labels := by
  calc
    mixedMoment B raw29018 raw29018Labels = mixedMoment B raw29018step0 raw29018step0Labels := by
      have ha : raw29018step0 = (fun i j => raw29018 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29018step0 raw29018; decide +kernel
      have hl : raw29018step0Labels = raw29018Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29018 raw29018Labels permutation154 permutation2
    _ = mixedMoment B node2476 node2476Labels := by rfl

def raw29019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![2, 1, -3]]
def raw29019Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw29019step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29019 raw29019Labels = mixedMoment B node2487 node2487Labels := by
  calc
    mixedMoment B raw29019 raw29019Labels = mixedMoment B raw29019step0 raw29019step0Labels := by
      have hz : ∀ j, raw29019 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29019step0 = (fun i j => raw29019 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29019step0 raw29019; decide +kernel
      have hl : raw29019step0Labels = raw29019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29019 raw29019Labels permutation434 hz
    _ = mixedMoment B node2487 node2487Labels := by rfl

def raw29020 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw29020Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw29020step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29020step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29020step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29020 raw29020Labels = mixedMoment B node2047 node2047Labels := by
  calc
    mixedMoment B raw29020 raw29020Labels = mixedMoment B raw29020step0 raw29020step0Labels := by
      have hz : ∀ j, raw29020 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29020step0 = (fun i j => raw29020 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29020step0 raw29020; decide +kernel
      have hl : raw29020step0Labels = raw29020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29020 raw29020Labels permutation434 hz
    mixedMoment B raw29020step0 raw29020step0Labels = mixedMoment B raw29020step1 raw29020step1Labels := by
      have ha : raw29020step1 = (fun i j => raw29020step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29020step1 raw29020step0; decide +kernel
      have hl : raw29020step1Labels = raw29020step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29020step0 raw29020step0Labels permutation145 permutation4
    _ = mixedMoment B node2047 node2047Labels := by rfl

def raw29021 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw29021Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw29021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29021step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw29021step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29021 raw29021Labels = mixedMoment B node2018 node2018Labels := by
  calc
    mixedMoment B raw29021 raw29021Labels = mixedMoment B raw29021step0 raw29021step0Labels := by
      have hz : ∀ j, raw29021 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29021step0 = (fun i j => raw29021 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29021step0 raw29021; decide +kernel
      have hl : raw29021step0Labels = raw29021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29021 raw29021Labels permutation434 hz
    mixedMoment B raw29021step0 raw29021step0Labels = mixedMoment B raw29021step1 raw29021step1Labels := by
      have ha : raw29021step1 = (fun i j => raw29021step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29021step1 raw29021step0; decide +kernel
      have hl : raw29021step1Labels = raw29021step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29021step0 raw29021step0Labels permutation143 permutation4
    _ = mixedMoment B node2018 node2018Labels := by rfl

def raw29022 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw29022Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw29022step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29022step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29022 raw29022Labels = mixedMoment B node1799 node1799Labels := by
  calc
    mixedMoment B raw29022 raw29022Labels = mixedMoment B raw29022step0 raw29022step0Labels := by
      have hz : ∀ j, raw29022 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29022step0 = (fun i j => raw29022 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29022step0 raw29022; decide +kernel
      have hl : raw29022step0Labels = raw29022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29022 raw29022Labels permutation434 hz
    mixedMoment B raw29022step0 raw29022step0Labels = mixedMoment B raw29022step1 raw29022step1Labels := by
      have ha : raw29022step1 = (fun i j => raw29022step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29022step1 raw29022step0; decide +kernel
      have hl : raw29022step1Labels = raw29022step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29022step0 raw29022step0Labels permutation145 permutation4
    _ = mixedMoment B node1799 node1799Labels := by rfl

def raw29023 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw29023Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw29023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29023step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29023step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29023 raw29023Labels = mixedMoment B node1874 node1874Labels := by
  calc
    mixedMoment B raw29023 raw29023Labels = mixedMoment B raw29023step0 raw29023step0Labels := by
      have ha : raw29023step0 = (fun i j => raw29023 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29023step0 raw29023; decide +kernel
      have hl : raw29023step0Labels = raw29023Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29023 raw29023Labels permutation164 permutation4
    mixedMoment B raw29023step0 raw29023step0Labels = mixedMoment B raw29023step1 raw29023step1Labels := by
      have ha : raw29023step1 = -raw29023step0 := by apply Matrix.ext; change ∀ i j, raw29023step1 i j = -(raw29023step0 i j); unfold raw29023step1 raw29023step0; decide +kernel
      have hl : raw29023step1Labels = raw29023step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1874 node1874Labels := by rfl

def raw29024 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw29024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw29024step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw29024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29024step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw29024step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29024 raw29024Labels = mixedMoment B node1911 node1911Labels := by
  calc
    mixedMoment B raw29024 raw29024Labels = mixedMoment B raw29024step0 raw29024step0Labels := by
      have hz : ∀ j, raw29024 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29024step0 = (fun i j => raw29024 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29024step0 raw29024; decide +kernel
      have hl : raw29024step0Labels = raw29024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29024 raw29024Labels permutation434 hz
    mixedMoment B raw29024step0 raw29024step0Labels = mixedMoment B raw29024step1 raw29024step1Labels := by
      have ha : raw29024step1 = (fun i j => raw29024step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29024step1 raw29024step0; decide +kernel
      have hl : raw29024step1Labels = raw29024step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29024step0 raw29024step0Labels permutation34 permutation4
    mixedMoment B raw29024step1 raw29024step1Labels = mixedMoment B raw29024step2 raw29024step2Labels := by
      have ha : raw29024step2 = -raw29024step1 := by apply Matrix.ext; change ∀ i j, raw29024step2 i j = -(raw29024step1 i j); unfold raw29024step2 raw29024step1; decide +kernel
      have hl : raw29024step2Labels = raw29024step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1911 node1911Labels := by rfl

def raw29025 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw29025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![1, -4, 3]]
def raw29025step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29025step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29025 raw29025Labels = mixedMoment B node916 node916Labels := by
  calc
    mixedMoment B raw29025 raw29025Labels = mixedMoment B raw29025step0 raw29025step0Labels := by
      have hz : ∀ j, raw29025 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29025step0 = (fun i j => raw29025 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29025step0 raw29025; decide +kernel
      have hl : raw29025step0Labels = raw29025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29025 raw29025Labels permutation434 hz
    mixedMoment B raw29025step0 raw29025step0Labels = mixedMoment B raw29025step1 raw29025step1Labels := by
      have ha : raw29025step1 = (fun i j => raw29025step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29025step1 raw29025step0; decide +kernel
      have hl : raw29025step1Labels = raw29025step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29025step0 raw29025step0Labels permutation145 permutation4
    _ = mixedMoment B node916 node916Labels := by rfl

def raw29026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw29026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29026step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29026step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29026 raw29026Labels = mixedMoment B node2449 node2449Labels := by
  calc
    mixedMoment B raw29026 raw29026Labels = mixedMoment B raw29026step0 raw29026step0Labels := by
      have ha : raw29026step0 = (fun i j => raw29026 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29026step0 raw29026; decide +kernel
      have hl : raw29026step0Labels = raw29026Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29026 raw29026Labels permutation158 permutation2
    _ = mixedMoment B node2449 node2449Labels := by rfl

def raw29027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw29027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29027step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw29027step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29027step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw29027step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29027 raw29027Labels = mixedMoment B node2452 node2452Labels := by
  calc
    mixedMoment B raw29027 raw29027Labels = mixedMoment B raw29027step0 raw29027step0Labels := by
      have ha : raw29027step0 = (fun i j => raw29027 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29027step0 raw29027; decide +kernel
      have hl : raw29027step0Labels = raw29027Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29027 raw29027Labels permutation682 permutation2
    mixedMoment B raw29027step0 raw29027step0Labels = mixedMoment B raw29027step1 raw29027step1Labels := by
      have ha : raw29027step1 = -raw29027step0 := by apply Matrix.ext; change ∀ i j, raw29027step1 i j = -(raw29027step0 i j); unfold raw29027step1 raw29027step0; decide +kernel
      have hl : raw29027step1Labels = raw29027step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2452 node2452Labels := by rfl

def raw29028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw29028Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29028step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw29028step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29028step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29028step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29028 raw29028Labels = mixedMoment B node2477 node2477Labels := by
  calc
    mixedMoment B raw29028 raw29028Labels = mixedMoment B raw29028step0 raw29028step0Labels := by
      have ha : raw29028step0 = (fun i j => raw29028 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29028step0 raw29028; decide +kernel
      have hl : raw29028step0Labels = raw29028Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29028 raw29028Labels permutation688 permutation2
    mixedMoment B raw29028step0 raw29028step0Labels = mixedMoment B raw29028step1 raw29028step1Labels := by
      have ha : raw29028step1 = -raw29028step0 := by apply Matrix.ext; change ∀ i j, raw29028step1 i j = -(raw29028step0 i j); unfold raw29028step1 raw29028step0; decide +kernel
      have hl : raw29028step1Labels = raw29028step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2477 node2477Labels := by rfl

def raw29029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw29029Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29029step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw29029step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29029step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29029step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29029 raw29029Labels = mixedMoment B node2461 node2461Labels := by
  calc
    mixedMoment B raw29029 raw29029Labels = mixedMoment B raw29029step0 raw29029step0Labels := by
      have ha : raw29029step0 = (fun i j => raw29029 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29029step0 raw29029; decide +kernel
      have hl : raw29029step0Labels = raw29029Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29029 raw29029Labels permutation680 permutation2
    mixedMoment B raw29029step0 raw29029step0Labels = mixedMoment B raw29029step1 raw29029step1Labels := by
      have ha : raw29029step1 = -raw29029step0 := by apply Matrix.ext; change ∀ i j, raw29029step1 i j = -(raw29029step0 i j); unfold raw29029step1 raw29029step0; decide +kernel
      have hl : raw29029step1Labels = raw29029step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2461 node2461Labels := by rfl

def raw29030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw29030Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw29030step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29030step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29030step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29030 raw29030Labels = mixedMoment B node2694 node2694Labels := by
  calc
    mixedMoment B raw29030 raw29030Labels = mixedMoment B raw29030step0 raw29030step0Labels := by
      have ha : raw29030step0 = (fun i j => raw29030 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29030step0 raw29030; decide +kernel
      have hl : raw29030step0Labels = raw29030Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29030 raw29030Labels permutation646 permutation2
    mixedMoment B raw29030step0 raw29030step0Labels = mixedMoment B raw29030step1 raw29030step1Labels := by
      have ha : raw29030step1 = -raw29030step0 := by apply Matrix.ext; change ∀ i j, raw29030step1 i j = -(raw29030step0 i j); unfold raw29030step1 raw29030step0; decide +kernel
      have hl : raw29030step1Labels = raw29030step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2694 node2694Labels := by rfl

def raw29031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29031Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29031step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29031step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29031 raw29031Labels = mixedMoment B node3793 node3793Labels := by
  calc
    mixedMoment B raw29031 raw29031Labels = mixedMoment B raw29031step0 raw29031step0Labels := by
      have ha : raw29031step0 = (fun i j => raw29031 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29031step0 raw29031; decide +kernel
      have hl : raw29031step0Labels = raw29031Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29031 raw29031Labels permutation158 permutation2
    _ = mixedMoment B node3793 node3793Labels := by rfl

def raw29032 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![-1, 1], ![1, -1], ![2, -2]]
def raw29032Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29032step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw29032step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29032 raw29032Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw29032 raw29032Labels = mixedMoment B raw29032step0 raw29032step0Labels := by
      have ha : raw29032step0 = (fun i j => raw29032 (permutation158 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29032step0 raw29032; decide +kernel
      have hl : raw29032step0Labels = raw29032Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29032 raw29032Labels permutation158 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

def raw29033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw29033Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29033step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29033step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29033 raw29033Labels = mixedMoment B node1107 node1107Labels := by
  calc
    mixedMoment B raw29033 raw29033Labels = mixedMoment B raw29033step0 raw29033step0Labels := by
      have ha : raw29033step0 = (fun i j => raw29033 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29033step0 raw29033; decide +kernel
      have hl : raw29033step0Labels = raw29033Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29033 raw29033Labels permutation158 permutation2
    _ = mixedMoment B node1107 node1107Labels := by rfl

def raw29034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw29034Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29034step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29034 raw29034Labels = mixedMoment B node2317 node2317Labels := by
  calc
    mixedMoment B raw29034 raw29034Labels = mixedMoment B raw29034step0 raw29034step0Labels := by
      have ha : raw29034step0 = (fun i j => raw29034 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29034step0 raw29034; decide +kernel
      have hl : raw29034step0Labels = raw29034Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29034 raw29034Labels permutation158 permutation2
    _ = mixedMoment B node2317 node2317Labels := by rfl

def raw29035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw29035Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29035step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29035 raw29035Labels = mixedMoment B node2415 node2415Labels := by
  calc
    mixedMoment B raw29035 raw29035Labels = mixedMoment B raw29035step0 raw29035step0Labels := by
      have ha : raw29035step0 = (fun i j => raw29035 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29035step0 raw29035; decide +kernel
      have hl : raw29035step0Labels = raw29035Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29035 raw29035Labels permutation158 permutation2
    _ = mixedMoment B node2415 node2415Labels := by rfl

def raw29036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw29036Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29036step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29036 raw29036Labels = mixedMoment B node2449 node2449Labels := by
  calc
    mixedMoment B raw29036 raw29036Labels = mixedMoment B raw29036step0 raw29036step0Labels := by
      have ha : raw29036step0 = (fun i j => raw29036 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29036step0 raw29036; decide +kernel
      have hl : raw29036step0Labels = raw29036Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29036 raw29036Labels permutation160 permutation2
    _ = mixedMoment B node2449 node2449Labels := by rfl

def raw29037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw29037Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29037step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29037 raw29037Labels = mixedMoment B node2461 node2461Labels := by
  calc
    mixedMoment B raw29037 raw29037Labels = mixedMoment B raw29037step0 raw29037step0Labels := by
      have ha : raw29037step0 = (fun i j => raw29037 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29037step0 raw29037; decide +kernel
      have hl : raw29037step0Labels = raw29037Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29037 raw29037Labels permutation158 permutation2
    _ = mixedMoment B node2461 node2461Labels := by rfl

def raw29038 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw29038Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw29038step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29038 raw29038Labels = mixedMoment B node3432 node3432Labels := by
  calc
    mixedMoment B raw29038 raw29038Labels = mixedMoment B raw29038step0 raw29038step0Labels := by
      have ha : raw29038step0 = (fun i j => raw29038 (permutation682 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29038step0 raw29038; decide +kernel
      have hl : raw29038step0Labels = raw29038Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29038 raw29038Labels permutation682 permutation4
    _ = mixedMoment B node3432 node3432Labels := by rfl

def raw29039 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw29039Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw29039step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29039step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw29039step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29039 raw29039Labels = mixedMoment B node1996 node1996Labels := by
  calc
    mixedMoment B raw29039 raw29039Labels = mixedMoment B raw29039step0 raw29039step0Labels := by
      have ha : raw29039step0 = (fun i j => raw29039 (permutation200 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29039step0 raw29039; decide +kernel
      have hl : raw29039step0Labels = raw29039Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29039 raw29039Labels permutation200 permutation4
    mixedMoment B raw29039step0 raw29039step0Labels = mixedMoment B raw29039step1 raw29039step1Labels := by
      have ha : raw29039step1 = -raw29039step0 := by apply Matrix.ext; change ∀ i j, raw29039step1 i j = -(raw29039step0 i j); unfold raw29039step1 raw29039step0; decide +kernel
      have hl : raw29039step1Labels = raw29039step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1996 node1996Labels := by rfl

def raw29040 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw29040Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29040step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw29040step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29040step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw29040step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29040 raw29040Labels = mixedMoment B node1868 node1868Labels := by
  calc
    mixedMoment B raw29040 raw29040Labels = mixedMoment B raw29040step0 raw29040step0Labels := by
      have ha : raw29040step0 = (fun i j => raw29040 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29040step0 raw29040; decide +kernel
      have hl : raw29040step0Labels = raw29040Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29040 raw29040Labels permutation160 permutation4
    mixedMoment B raw29040step0 raw29040step0Labels = mixedMoment B raw29040step1 raw29040step1Labels := by
      have ha : raw29040step1 = -raw29040step0 := by apply Matrix.ext; change ∀ i j, raw29040step1 i j = -(raw29040step0 i j); unfold raw29040step1 raw29040step0; decide +kernel
      have hl : raw29040step1Labels = raw29040step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1868 node1868Labels := by rfl

def raw29041 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw29041Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw29041step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29041step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw29041step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29041step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw29041step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29041 raw29041Labels = mixedMoment B node1944 node1944Labels := by
  calc
    mixedMoment B raw29041 raw29041Labels = mixedMoment B raw29041step0 raw29041step0Labels := by
      have hz : ∀ j, raw29041 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29041step0 = (fun i j => raw29041 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29041step0 raw29041; decide +kernel
      have hl : raw29041step0Labels = raw29041Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29041 raw29041Labels permutation434 hz
    mixedMoment B raw29041step0 raw29041step0Labels = mixedMoment B raw29041step1 raw29041step1Labels := by
      have ha : raw29041step1 = (fun i j => raw29041step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29041step1 raw29041step0; decide +kernel
      have hl : raw29041step1Labels = raw29041step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29041step0 raw29041step0Labels permutation32 permutation4
    mixedMoment B raw29041step1 raw29041step1Labels = mixedMoment B raw29041step2 raw29041step2Labels := by
      have ha : raw29041step2 = -raw29041step1 := by apply Matrix.ext; change ∀ i j, raw29041step2 i j = -(raw29041step1 i j); unfold raw29041step2 raw29041step1; decide +kernel
      have hl : raw29041step2Labels = raw29041step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1944 node1944Labels := by rfl

def raw29042 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw29042Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29042step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw29042step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29042step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29042step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29042 raw29042Labels = mixedMoment B node1864 node1864Labels := by
  calc
    mixedMoment B raw29042 raw29042Labels = mixedMoment B raw29042step0 raw29042step0Labels := by
      have ha : raw29042step0 = (fun i j => raw29042 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29042step0 raw29042; decide +kernel
      have hl : raw29042step0Labels = raw29042Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29042 raw29042Labels permutation158 permutation4
    mixedMoment B raw29042step0 raw29042step0Labels = mixedMoment B raw29042step1 raw29042step1Labels := by
      have ha : raw29042step1 = -raw29042step0 := by apply Matrix.ext; change ∀ i j, raw29042step1 i j = -(raw29042step0 i j); unfold raw29042step1 raw29042step0; decide +kernel
      have hl : raw29042step1Labels = raw29042step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1864 node1864Labels := by rfl

def raw29043 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29043Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29043step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29043step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29043 raw29043Labels = mixedMoment B node1862 node1862Labels := by
  calc
    mixedMoment B raw29043 raw29043Labels = mixedMoment B raw29043step0 raw29043step0Labels := by
      have ha : raw29043step0 = (fun i j => raw29043 (permutation682 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29043step0 raw29043; decide +kernel
      have hl : raw29043step0Labels = raw29043Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29043 raw29043Labels permutation682 permutation4
    _ = mixedMoment B node1862 node1862Labels := by rfl

def raw29044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw29044Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29044step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29044step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29044 raw29044Labels = mixedMoment B node1105 node1105Labels := by
  calc
    mixedMoment B raw29044 raw29044Labels = mixedMoment B raw29044step0 raw29044step0Labels := by
      have ha : raw29044step0 = (fun i j => raw29044 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29044step0 raw29044; decide +kernel
      have hl : raw29044step0Labels = raw29044Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29044 raw29044Labels permutation160 permutation2
    _ = mixedMoment B node1105 node1105Labels := by rfl

def raw29045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw29045Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29045step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw29045step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29045step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw29045step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29045 raw29045Labels = mixedMoment B node1860 node1860Labels := by
  calc
    mixedMoment B raw29045 raw29045Labels = mixedMoment B raw29045step0 raw29045step0Labels := by
      have ha : raw29045step0 = (fun i j => raw29045 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29045step0 raw29045; decide +kernel
      have hl : raw29045step0Labels = raw29045Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29045 raw29045Labels permutation646 permutation2
    mixedMoment B raw29045step0 raw29045step0Labels = mixedMoment B raw29045step1 raw29045step1Labels := by
      have ha : raw29045step1 = -raw29045step0 := by apply Matrix.ext; change ∀ i j, raw29045step1 i j = -(raw29045step0 i j); unfold raw29045step1 raw29045step0; decide +kernel
      have hl : raw29045step1Labels = raw29045step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1860 node1860Labels := by rfl

def raw29046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw29046Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29046step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29046step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29046step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29046 raw29046Labels = mixedMoment B node1987 node1987Labels := by
  calc
    mixedMoment B raw29046 raw29046Labels = mixedMoment B raw29046step0 raw29046step0Labels := by
      have ha : raw29046step0 = (fun i j => raw29046 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29046step0 raw29046; decide +kernel
      have hl : raw29046step0Labels = raw29046Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29046 raw29046Labels permutation682 permutation2
    mixedMoment B raw29046step0 raw29046step0Labels = mixedMoment B raw29046step1 raw29046step1Labels := by
      have ha : raw29046step1 = -raw29046step0 := by apply Matrix.ext; change ∀ i j, raw29046step1 i j = -(raw29046step0 i j); unfold raw29046step1 raw29046step0; decide +kernel
      have hl : raw29046step1Labels = raw29046step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1987 node1987Labels := by rfl

def raw29047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw29047Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29047step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29047step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29047step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29047step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29047 raw29047Labels = mixedMoment B node1866 node1866Labels := by
  calc
    mixedMoment B raw29047 raw29047Labels = mixedMoment B raw29047step0 raw29047step0Labels := by
      have ha : raw29047step0 = (fun i j => raw29047 (permutation644 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29047step0 raw29047; decide +kernel
      have hl : raw29047step0Labels = raw29047Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29047 raw29047Labels permutation644 permutation2
    mixedMoment B raw29047step0 raw29047step0Labels = mixedMoment B raw29047step1 raw29047step1Labels := by
      have ha : raw29047step1 = -raw29047step0 := by apply Matrix.ext; change ∀ i j, raw29047step1 i j = -(raw29047step0 i j); unfold raw29047step1 raw29047step0; decide +kernel
      have hl : raw29047step1Labels = raw29047step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1866 node1866Labels := by rfl

def raw29048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw29048Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![3, 0, -3]]
def raw29048step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29048step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29048step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29048step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29048step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29048 raw29048Labels = mixedMoment B node1914 node1914Labels := by
  calc
    mixedMoment B raw29048 raw29048Labels = mixedMoment B raw29048step0 raw29048step0Labels := by
      have hz : ∀ j, raw29048 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29048step0 = (fun i j => raw29048 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29048step0 raw29048; decide +kernel
      have hl : raw29048step0Labels = raw29048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29048 raw29048Labels permutation520 hz
    mixedMoment B raw29048step0 raw29048step0Labels = mixedMoment B raw29048step1 raw29048step1Labels := by
      have ha : raw29048step1 = (fun i j => raw29048step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29048step1 raw29048step0; decide +kernel
      have hl : raw29048step1Labels = raw29048step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29048step0 raw29048step0Labels permutation145 permutation2
    mixedMoment B raw29048step1 raw29048step1Labels = mixedMoment B raw29048step2 raw29048step2Labels := by
      have ha : raw29048step2 = -raw29048step1 := by apply Matrix.ext; change ∀ i j, raw29048step2 i j = -(raw29048step1 i j); unfold raw29048step2 raw29048step1; decide +kernel
      have hl : raw29048step2Labels = raw29048step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1914 node1914Labels := by rfl

def raw29049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw29049Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29049step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw29049step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29049 raw29049Labels = mixedMoment B node2458 node2458Labels := by
  calc
    mixedMoment B raw29049 raw29049Labels = mixedMoment B raw29049step0 raw29049step0Labels := by
      have ha : raw29049step0 = (fun i j => raw29049 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29049step0 raw29049; decide +kernel
      have hl : raw29049step0Labels = raw29049Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29049 raw29049Labels permutation160 permutation2
    _ = mixedMoment B node2458 node2458Labels := by rfl

def raw29050 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![-1, 1], ![0, 0], ![3, -3]]
def raw29050Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29050step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![-1, 1], ![3, -3]]
def raw29050step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29050step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw29050step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29050step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw29050step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29050 raw29050Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw29050 raw29050Labels = mixedMoment B raw29050step0 raw29050step0Labels := by
      have hz : ∀ j, raw29050 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29050step0 = (fun i j => raw29050 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29050step0 raw29050; decide +kernel
      have hl : raw29050step0Labels = raw29050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29050 raw29050Labels permutation520 hz
    mixedMoment B raw29050step0 raw29050step0Labels = mixedMoment B raw29050step1 raw29050step1Labels := by
      have ha : raw29050step1 = (fun i j => raw29050step0 (permutation143 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29050step1 raw29050step0; decide +kernel
      have hl : raw29050step1Labels = raw29050step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29050step0 raw29050step0Labels permutation143 permutation0
    mixedMoment B raw29050step1 raw29050step1Labels = mixedMoment B raw29050step2 raw29050step2Labels := by
      have ha : raw29050step2 = -raw29050step1 := by apply Matrix.ext; change ∀ i j, raw29050step2 i j = -(raw29050step1 i j); unfold raw29050step2 raw29050step1; decide +kernel
      have hl : raw29050step2Labels = raw29050step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw29051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw29051Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw29051step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29051step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29051step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29051 raw29051Labels = mixedMoment B node1999 node1999Labels := by
  calc
    mixedMoment B raw29051 raw29051Labels = mixedMoment B raw29051step0 raw29051step0Labels := by
      have ha : raw29051step0 = (fun i j => raw29051 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29051step0 raw29051; decide +kernel
      have hl : raw29051step0Labels = raw29051Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29051 raw29051Labels permutation680 permutation2
    mixedMoment B raw29051step0 raw29051step0Labels = mixedMoment B raw29051step1 raw29051step1Labels := by
      have ha : raw29051step1 = -raw29051step0 := by apply Matrix.ext; change ∀ i j, raw29051step1 i j = -(raw29051step0 i j); unfold raw29051step1 raw29051step0; decide +kernel
      have hl : raw29051step1Labels = raw29051step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1999 node1999Labels := by rfl

def raw29052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw29052Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29052step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29052step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29052step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29052step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29052 raw29052Labels = mixedMoment B node1987 node1987Labels := by
  calc
    mixedMoment B raw29052 raw29052Labels = mixedMoment B raw29052step0 raw29052step0Labels := by
      have ha : raw29052step0 = (fun i j => raw29052 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29052step0 raw29052; decide +kernel
      have hl : raw29052step0Labels = raw29052Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29052 raw29052Labels permutation680 permutation2
    mixedMoment B raw29052step0 raw29052step0Labels = mixedMoment B raw29052step1 raw29052step1Labels := by
      have ha : raw29052step1 = -raw29052step0 := by apply Matrix.ext; change ∀ i j, raw29052step1 i j = -(raw29052step0 i j); unfold raw29052step1 raw29052step0; decide +kernel
      have hl : raw29052step1Labels = raw29052step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1987 node1987Labels := by rfl

def raw29053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw29053Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29053step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29053step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29053step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29053step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29053 raw29053Labels = mixedMoment B node1786 node1786Labels := by
  calc
    mixedMoment B raw29053 raw29053Labels = mixedMoment B raw29053step0 raw29053step0Labels := by
      have ha : raw29053step0 = (fun i j => raw29053 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29053step0 raw29053; decide +kernel
      have hl : raw29053step0Labels = raw29053Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29053 raw29053Labels permutation680 permutation2
    mixedMoment B raw29053step0 raw29053step0Labels = mixedMoment B raw29053step1 raw29053step1Labels := by
      have ha : raw29053step1 = -raw29053step0 := by apply Matrix.ext; change ∀ i j, raw29053step1 i j = -(raw29053step0 i j); unfold raw29053step1 raw29053step0; decide +kernel
      have hl : raw29053step1Labels = raw29053step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1786 node1786Labels := by rfl

def raw29054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![4, -1, -3]]
def raw29054Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29054step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29054step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29054step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29054step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29054 raw29054Labels = mixedMoment B node900 node900Labels := by
  calc
    mixedMoment B raw29054 raw29054Labels = mixedMoment B raw29054step0 raw29054step0Labels := by
      have ha : raw29054step0 = (fun i j => raw29054 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29054step0 raw29054; decide +kernel
      have hl : raw29054step0Labels = raw29054Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29054 raw29054Labels permutation680 permutation2
    mixedMoment B raw29054step0 raw29054step0Labels = mixedMoment B raw29054step1 raw29054step1Labels := by
      have ha : raw29054step1 = -raw29054step0 := by apply Matrix.ext; change ∀ i j, raw29054step1 i j = -(raw29054step0 i j); unfold raw29054step1 raw29054step0; decide +kernel
      have hl : raw29054step1Labels = raw29054step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node900 node900Labels := by rfl

def raw29055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw29055Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29055step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw29055step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29055step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw29055step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29055 raw29055Labels = mixedMoment B node3514 node3514Labels := by
  calc
    mixedMoment B raw29055 raw29055Labels = mixedMoment B raw29055step0 raw29055step0Labels := by
      have ha : raw29055step0 = (fun i j => raw29055 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29055step0 raw29055; decide +kernel
      have hl : raw29055step0Labels = raw29055Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29055 raw29055Labels permutation682 permutation2
    mixedMoment B raw29055step0 raw29055step0Labels = mixedMoment B raw29055step1 raw29055step1Labels := by
      have ha : raw29055step1 = -raw29055step0 := by apply Matrix.ext; change ∀ i j, raw29055step1 i j = -(raw29055step0 i j); unfold raw29055step1 raw29055step0; decide +kernel
      have hl : raw29055step1Labels = raw29055step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3514 node3514Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
