import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw1152 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![-2, 4, -2]]
def raw1152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1152step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw1152step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1152step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw1152step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1152 raw1152Labels = mixedMoment B node4356 node4356Labels := by
  calc
    mixedMoment B raw1152 raw1152Labels = mixedMoment B raw1152step0 raw1152step0Labels := by
      have ha : raw1152step0 = (fun i j => raw1152 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1152step0 raw1152; decide +kernel
      have hl : raw1152step0Labels = raw1152Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1152 raw1152Labels permutation8 permutation4
    mixedMoment B raw1152step0 raw1152step0Labels = mixedMoment B raw1152step1 raw1152step1Labels := by
      have ha : raw1152step1 = raw1152step0 := by apply Matrix.ext; unfold raw1152step1 raw1152step0; decide +kernel
      have hl : raw1152step0Labels = labelEmbedding7 ∘ raw1152step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1152step0 raw1152step0Labels raw1152step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4356 node4356Labels := by rfl

def raw1153 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![-2, 4, -2]]
def raw1153Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1153step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw1153step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1153 raw1153Labels = mixedMoment B node934 node934Labels := by
  calc
    mixedMoment B raw1153 raw1153Labels = mixedMoment B raw1153step0 raw1153step0Labels := by
      have ha : raw1153step0 = (fun i j => raw1153 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1153step0 raw1153; decide +kernel
      have hl : raw1153step0Labels = raw1153Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1153 raw1153Labels permutation8 permutation4
    _ = mixedMoment B node934 node934Labels := by rfl

def raw1154 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 1, -1], ![-2, 4, -2]]
def raw1154Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1154step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-2, -2, 4]]
def raw1154step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1154step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw1154step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1154step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw1154step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1154 raw1154Labels = mixedMoment B node1692 node1692Labels := by
  calc
    mixedMoment B raw1154 raw1154Labels = mixedMoment B raw1154step0 raw1154step0Labels := by
      have ha : raw1154step0 = (fun i j => raw1154 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1154step0 raw1154; decide +kernel
      have hl : raw1154step0Labels = raw1154Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1154 raw1154Labels permutation8 permutation6
    mixedMoment B raw1154step0 raw1154step0Labels = mixedMoment B raw1154step1 raw1154step1Labels := by
      have ha : raw1154step1 = -raw1154step0 := by apply Matrix.ext; change ∀ i j, raw1154step1 i j = -(raw1154step0 i j); unfold raw1154step1 raw1154step0; decide +kernel
      have hl : raw1154step1Labels = raw1154step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1154step1 raw1154step1Labels = mixedMoment B raw1154step2 raw1154step2Labels := by
      have ha : raw1154step2 = raw1154step1 := by apply Matrix.ext; unfold raw1154step2 raw1154step1; decide +kernel
      have hl : raw1154step1Labels = labelEmbedding1 ∘ raw1154step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1154step1 raw1154step1Labels raw1154step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1692 node1692Labels := by rfl

def raw1155 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-2, 2, 0], ![0, 3, -3]]
def raw1155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1155step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw1155step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1155step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw1155step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1155 raw1155Labels = mixedMoment B node4359 node4359Labels := by
  calc
    mixedMoment B raw1155 raw1155Labels = mixedMoment B raw1155step0 raw1155step0Labels := by
      have ha : raw1155step0 = (fun i j => raw1155 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1155step0 raw1155; decide +kernel
      have hl : raw1155step0Labels = raw1155Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1155 raw1155Labels permutation8 permutation4
    mixedMoment B raw1155step0 raw1155step0Labels = mixedMoment B raw1155step1 raw1155step1Labels := by
      have ha : raw1155step1 = raw1155step0 := by apply Matrix.ext; unfold raw1155step1 raw1155step0; decide +kernel
      have hl : raw1155step0Labels = labelEmbedding7 ∘ raw1155step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1155step0 raw1155step0Labels raw1155step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4359 node4359Labels := by rfl

def raw1156 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-2, 2, 0], ![0, 3, -3]]
def raw1156Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1156step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw1156step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1156 raw1156Labels = mixedMoment B node937 node937Labels := by
  calc
    mixedMoment B raw1156 raw1156Labels = mixedMoment B raw1156step0 raw1156step0Labels := by
      have ha : raw1156step0 = (fun i j => raw1156 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1156step0 raw1156; decide +kernel
      have hl : raw1156step0Labels = raw1156Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1156 raw1156Labels permutation8 permutation4
    _ = mixedMoment B node937 node937Labels := by rfl

def raw1157 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-2, 2, 0], ![0, 3, -3]]
def raw1157Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1157step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-3, 0, 3]]
def raw1157step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1157step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw1157step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1157step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw1157step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1157 raw1157Labels = mixedMoment B node1683 node1683Labels := by
  calc
    mixedMoment B raw1157 raw1157Labels = mixedMoment B raw1157step0 raw1157step0Labels := by
      have ha : raw1157step0 = (fun i j => raw1157 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1157step0 raw1157; decide +kernel
      have hl : raw1157step0Labels = raw1157Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1157 raw1157Labels permutation8 permutation6
    mixedMoment B raw1157step0 raw1157step0Labels = mixedMoment B raw1157step1 raw1157step1Labels := by
      have ha : raw1157step1 = -raw1157step0 := by apply Matrix.ext; change ∀ i j, raw1157step1 i j = -(raw1157step0 i j); unfold raw1157step1 raw1157step0; decide +kernel
      have hl : raw1157step1Labels = raw1157step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1157step1 raw1157step1Labels = mixedMoment B raw1157step2 raw1157step2Labels := by
      have ha : raw1157step2 = raw1157step1 := by apply Matrix.ext; unfold raw1157step2 raw1157step1; decide +kernel
      have hl : raw1157step1Labels = labelEmbedding1 ∘ raw1157step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1157step1 raw1157step1Labels raw1157step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1683 node1683Labels := by rfl

def raw1158 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 2, -1], ![-1, 3, -2]]
def raw1158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1158step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw1158step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1158step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw1158step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1158 raw1158Labels = mixedMoment B node4360 node4360Labels := by
  calc
    mixedMoment B raw1158 raw1158Labels = mixedMoment B raw1158step0 raw1158step0Labels := by
      have ha : raw1158step0 = (fun i j => raw1158 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1158step0 raw1158; decide +kernel
      have hl : raw1158step0Labels = raw1158Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1158 raw1158Labels permutation8 permutation4
    mixedMoment B raw1158step0 raw1158step0Labels = mixedMoment B raw1158step1 raw1158step1Labels := by
      have ha : raw1158step1 = raw1158step0 := by apply Matrix.ext; unfold raw1158step1 raw1158step0; decide +kernel
      have hl : raw1158step0Labels = labelEmbedding7 ∘ raw1158step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1158step0 raw1158step0Labels raw1158step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4360 node4360Labels := by rfl

def raw1159 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 2, -1], ![-1, 3, -2]]
def raw1159Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1159step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw1159step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1159 raw1159Labels = mixedMoment B node938 node938Labels := by
  calc
    mixedMoment B raw1159 raw1159Labels = mixedMoment B raw1159step0 raw1159step0Labels := by
      have ha : raw1159step0 = (fun i j => raw1159 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1159step0 raw1159; decide +kernel
      have hl : raw1159step0Labels = raw1159Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1159 raw1159Labels permutation8 permutation4
    _ = mixedMoment B node938 node938Labels := by rfl

def raw1160 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![-1, 2, -1], ![-1, 3, -2]]
def raw1160Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1160step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw1160step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1160step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw1160step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1160step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw1160step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1160 raw1160Labels = mixedMoment B node1693 node1693Labels := by
  calc
    mixedMoment B raw1160 raw1160Labels = mixedMoment B raw1160step0 raw1160step0Labels := by
      have ha : raw1160step0 = (fun i j => raw1160 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1160step0 raw1160; decide +kernel
      have hl : raw1160step0Labels = raw1160Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1160 raw1160Labels permutation8 permutation6
    mixedMoment B raw1160step0 raw1160step0Labels = mixedMoment B raw1160step1 raw1160step1Labels := by
      have ha : raw1160step1 = -raw1160step0 := by apply Matrix.ext; change ∀ i j, raw1160step1 i j = -(raw1160step0 i j); unfold raw1160step1 raw1160step0; decide +kernel
      have hl : raw1160step1Labels = raw1160step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1160step1 raw1160step1Labels = mixedMoment B raw1160step2 raw1160step2Labels := by
      have ha : raw1160step2 = raw1160step1 := by apply Matrix.ext; unfold raw1160step2 raw1160step1; decide +kernel
      have hl : raw1160step1Labels = labelEmbedding1 ∘ raw1160step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1160step1 raw1160step1Labels raw1160step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1693 node1693Labels := by rfl

def raw1161 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 2, -2], ![-2, 3, -1]]
def raw1161Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1161step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw1161step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1161step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw1161step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1161 raw1161Labels = mixedMoment B node4361 node4361Labels := by
  calc
    mixedMoment B raw1161 raw1161Labels = mixedMoment B raw1161step0 raw1161step0Labels := by
      have ha : raw1161step0 = (fun i j => raw1161 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1161step0 raw1161; decide +kernel
      have hl : raw1161step0Labels = raw1161Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1161 raw1161Labels permutation8 permutation4
    mixedMoment B raw1161step0 raw1161step0Labels = mixedMoment B raw1161step1 raw1161step1Labels := by
      have ha : raw1161step1 = raw1161step0 := by apply Matrix.ext; unfold raw1161step1 raw1161step0; decide +kernel
      have hl : raw1161step0Labels = labelEmbedding7 ∘ raw1161step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1161step0 raw1161step0Labels raw1161step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4361 node4361Labels := by rfl

def raw1162 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 2, -2], ![-2, 3, -1]]
def raw1162Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1162step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw1162step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1162 raw1162Labels = mixedMoment B node939 node939Labels := by
  calc
    mixedMoment B raw1162 raw1162Labels = mixedMoment B raw1162step0 raw1162step0Labels := by
      have ha : raw1162step0 = (fun i j => raw1162 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1162step0 raw1162; decide +kernel
      have hl : raw1162step0Labels = raw1162Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1162 raw1162Labels permutation8 permutation4
    _ = mixedMoment B node939 node939Labels := by rfl

def raw1163 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, -1, 0], ![0, 2, -2], ![-2, 3, -1]]
def raw1163Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1163step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw1163step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1163step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw1163step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1163step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw1163step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1163 raw1163Labels = mixedMoment B node1694 node1694Labels := by
  calc
    mixedMoment B raw1163 raw1163Labels = mixedMoment B raw1163step0 raw1163step0Labels := by
      have ha : raw1163step0 = (fun i j => raw1163 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1163step0 raw1163; decide +kernel
      have hl : raw1163step0Labels = raw1163Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1163 raw1163Labels permutation9 permutation6
    mixedMoment B raw1163step0 raw1163step0Labels = mixedMoment B raw1163step1 raw1163step1Labels := by
      have ha : raw1163step1 = -raw1163step0 := by apply Matrix.ext; change ∀ i j, raw1163step1 i j = -(raw1163step0 i j); unfold raw1163step1 raw1163step0; decide +kernel
      have hl : raw1163step1Labels = raw1163step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1163step1 raw1163step1Labels = mixedMoment B raw1163step2 raw1163step2Labels := by
      have ha : raw1163step2 = raw1163step1 := by apply Matrix.ext; unfold raw1163step2 raw1163step1; decide +kernel
      have hl : raw1163step1Labels = labelEmbedding1 ∘ raw1163step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1163step1 raw1163step1Labels raw1163step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1694 node1694Labels := by rfl

def raw1164 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1164Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1164step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1164step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1164step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1164step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1164 raw1164Labels = mixedMoment B node4376 node4376Labels := by
  calc
    mixedMoment B raw1164 raw1164Labels = mixedMoment B raw1164step0 raw1164step0Labels := by
      have ha : raw1164step0 = (fun i j => raw1164 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1164step0 raw1164; decide +kernel
      have hl : raw1164step0Labels = raw1164Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1164 raw1164Labels permutation152 permutation4
    mixedMoment B raw1164step0 raw1164step0Labels = mixedMoment B raw1164step1 raw1164step1Labels := by
      have ha : raw1164step1 = raw1164step0 := by apply Matrix.ext; unfold raw1164step1 raw1164step0; decide +kernel
      have hl : raw1164step0Labels = labelEmbedding7 ∘ raw1164step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1164step0 raw1164step0Labels raw1164step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4376 node4376Labels := by rfl

def raw1165 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1165Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1165step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1165step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1165 raw1165Labels = mixedMoment B node955 node955Labels := by
  calc
    mixedMoment B raw1165 raw1165Labels = mixedMoment B raw1165step0 raw1165step0Labels := by
      have ha : raw1165step0 = (fun i j => raw1165 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1165step0 raw1165; decide +kernel
      have hl : raw1165step0Labels = raw1165Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1165 raw1165Labels permutation152 permutation4
    _ = mixedMoment B node955 node955Labels := by rfl

def raw1166 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1166Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1166step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1166step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1166step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1166step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1166step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1166 raw1166Labels = mixedMoment B node1542 node1542Labels := by
  calc
    mixedMoment B raw1166 raw1166Labels = mixedMoment B raw1166step0 raw1166step0Labels := by
      have ha : raw1166step0 = (fun i j => raw1166 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1166step0 raw1166; decide +kernel
      have hl : raw1166step0Labels = raw1166Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1166 raw1166Labels permutation152 permutation6
    mixedMoment B raw1166step0 raw1166step0Labels = mixedMoment B raw1166step1 raw1166step1Labels := by
      have ha : raw1166step1 = -raw1166step0 := by apply Matrix.ext; change ∀ i j, raw1166step1 i j = -(raw1166step0 i j); unfold raw1166step1 raw1166step0; decide +kernel
      have hl : raw1166step1Labels = raw1166step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1166step1 raw1166step1Labels = mixedMoment B raw1166step2 raw1166step2Labels := by
      have ha : raw1166step2 = raw1166step1 := by apply Matrix.ext; unfold raw1166step2 raw1166step1; decide +kernel
      have hl : raw1166step1Labels = labelEmbedding1 ∘ raw1166step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1166step1 raw1166step1Labels raw1166step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1542 node1542Labels := by rfl

def raw1167 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![0, 3, -3]]
def raw1167Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw1167step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw1167step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1167 raw1167Labels = mixedMoment B node4377 node4377Labels := by
  calc
    mixedMoment B raw1167 raw1167Labels = mixedMoment B raw1167step0 raw1167step0Labels := by
      have ha : raw1167step0 = (fun i j => raw1167 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1167step0 raw1167; decide +kernel
      have hl : raw1167step0Labels = raw1167Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1167 raw1167Labels permutation32 permutation4
    mixedMoment B raw1167step0 raw1167step0Labels = mixedMoment B raw1167step1 raw1167step1Labels := by
      have ha : raw1167step1 = raw1167step0 := by apply Matrix.ext; unfold raw1167step1 raw1167step0; decide +kernel
      have hl : raw1167step0Labels = labelEmbedding7 ∘ raw1167step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1167step0 raw1167step0Labels raw1167step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4377 node4377Labels := by rfl

def raw1168 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![0, 3, -3]]
def raw1168Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw1168step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1168 raw1168Labels = mixedMoment B node956 node956Labels := by
  calc
    mixedMoment B raw1168 raw1168Labels = mixedMoment B raw1168step0 raw1168step0Labels := by
      have ha : raw1168step0 = (fun i j => raw1168 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1168step0 raw1168; decide +kernel
      have hl : raw1168step0Labels = raw1168Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1168 raw1168Labels permutation32 permutation4
    _ = mixedMoment B node956 node956Labels := by rfl

def raw1169 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![0, 3, -3]]
def raw1169Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw1169step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw1169step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1169step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw1169step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1169 raw1169Labels = mixedMoment B node1543 node1543Labels := by
  calc
    mixedMoment B raw1169 raw1169Labels = mixedMoment B raw1169step0 raw1169step0Labels := by
      have ha : raw1169step0 = (fun i j => raw1169 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1169step0 raw1169; decide +kernel
      have hl : raw1169step0Labels = raw1169Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1169 raw1169Labels permutation32 permutation6
    mixedMoment B raw1169step0 raw1169step0Labels = mixedMoment B raw1169step1 raw1169step1Labels := by
      have ha : raw1169step1 = -raw1169step0 := by apply Matrix.ext; change ∀ i j, raw1169step1 i j = -(raw1169step0 i j); unfold raw1169step1 raw1169step0; decide +kernel
      have hl : raw1169step1Labels = raw1169step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1169step1 raw1169step1Labels = mixedMoment B raw1169step2 raw1169step2Labels := by
      have ha : raw1169step2 = raw1169step1 := by apply Matrix.ext; unfold raw1169step2 raw1169step1; decide +kernel
      have hl : raw1169step1Labels = labelEmbedding1 ∘ raw1169step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1169step1 raw1169step1Labels raw1169step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1543 node1543Labels := by rfl

def raw1170 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 0, 2], ![1, 0, -1], ![0, 2, -2], ![0, 2, -2]]
def raw1170Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1170step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1170step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1170 raw1170Labels = mixedMoment B node4378 node4378Labels := by
  calc
    mixedMoment B raw1170 raw1170Labels = mixedMoment B raw1170step0 raw1170step0Labels := by
      have ha : raw1170step0 = (fun i j => raw1170 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1170step0 raw1170; decide +kernel
      have hl : raw1170step0Labels = raw1170Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1170 raw1170Labels permutation32 permutation4
    mixedMoment B raw1170step0 raw1170step0Labels = mixedMoment B raw1170step1 raw1170step1Labels := by
      have ha : raw1170step1 = raw1170step0 := by apply Matrix.ext; unfold raw1170step1 raw1170step0; decide +kernel
      have hl : raw1170step0Labels = labelEmbedding7 ∘ raw1170step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1170step0 raw1170step0Labels raw1170step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4378 node4378Labels := by rfl

def raw1171 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 0, 2], ![1, 0, -1], ![0, 2, -2], ![0, 2, -2]]
def raw1171Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1171step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1171 raw1171Labels = mixedMoment B node957 node957Labels := by
  calc
    mixedMoment B raw1171 raw1171Labels = mixedMoment B raw1171step0 raw1171step0Labels := by
      have ha : raw1171step0 = (fun i j => raw1171 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1171step0 raw1171; decide +kernel
      have hl : raw1171step0Labels = raw1171Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1171 raw1171Labels permutation32 permutation4
    _ = mixedMoment B node957 node957Labels := by rfl

def raw1172 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 0, 2], ![1, 0, -1], ![0, 2, -2], ![0, 2, -2]]
def raw1172Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw1172step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1172step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1172step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1172step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1172 raw1172Labels = mixedMoment B node1544 node1544Labels := by
  calc
    mixedMoment B raw1172 raw1172Labels = mixedMoment B raw1172step0 raw1172step0Labels := by
      have ha : raw1172step0 = (fun i j => raw1172 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1172step0 raw1172; decide +kernel
      have hl : raw1172step0Labels = raw1172Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1172 raw1172Labels permutation32 permutation6
    mixedMoment B raw1172step0 raw1172step0Labels = mixedMoment B raw1172step1 raw1172step1Labels := by
      have ha : raw1172step1 = -raw1172step0 := by apply Matrix.ext; change ∀ i j, raw1172step1 i j = -(raw1172step0 i j); unfold raw1172step1 raw1172step0; decide +kernel
      have hl : raw1172step1Labels = raw1172step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1172step1 raw1172step1Labels = mixedMoment B raw1172step2 raw1172step2Labels := by
      have ha : raw1172step2 = raw1172step1 := by apply Matrix.ext; unfold raw1172step2 raw1172step1; decide +kernel
      have hl : raw1172step1Labels = labelEmbedding1 ∘ raw1172step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1172step1 raw1172step1Labels raw1172step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1544 node1544Labels := by rfl

def raw1173 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw1173Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1173step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1173step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1173step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1173 raw1173Labels = mixedMoment B node4379 node4379Labels := by
  calc
    mixedMoment B raw1173 raw1173Labels = mixedMoment B raw1173step0 raw1173step0Labels := by
      have ha : raw1173step0 = (fun i j => raw1173 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1173step0 raw1173; decide +kernel
      have hl : raw1173step0Labels = raw1173Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1173 raw1173Labels permutation152 permutation4
    mixedMoment B raw1173step0 raw1173step0Labels = mixedMoment B raw1173step1 raw1173step1Labels := by
      have ha : raw1173step1 = raw1173step0 := by apply Matrix.ext; unfold raw1173step1 raw1173step0; decide +kernel
      have hl : raw1173step0Labels = labelEmbedding7 ∘ raw1173step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1173step0 raw1173step0Labels raw1173step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4379 node4379Labels := by rfl

def raw1174 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw1174Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1174step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1174step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1174 raw1174Labels = mixedMoment B node958 node958Labels := by
  calc
    mixedMoment B raw1174 raw1174Labels = mixedMoment B raw1174step0 raw1174step0Labels := by
      have ha : raw1174step0 = (fun i j => raw1174 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1174step0 raw1174; decide +kernel
      have hl : raw1174step0Labels = raw1174Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1174 raw1174Labels permutation152 permutation4
    _ = mixedMoment B node958 node958Labels := by rfl

def raw1175 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw1175Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1175step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw1175step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1175step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1175step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1175step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1175step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1175 raw1175Labels = mixedMoment B node1545 node1545Labels := by
  calc
    mixedMoment B raw1175 raw1175Labels = mixedMoment B raw1175step0 raw1175step0Labels := by
      have ha : raw1175step0 = (fun i j => raw1175 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1175step0 raw1175; decide +kernel
      have hl : raw1175step0Labels = raw1175Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1175 raw1175Labels permutation152 permutation6
    mixedMoment B raw1175step0 raw1175step0Labels = mixedMoment B raw1175step1 raw1175step1Labels := by
      have ha : raw1175step1 = -raw1175step0 := by apply Matrix.ext; change ∀ i j, raw1175step1 i j = -(raw1175step0 i j); unfold raw1175step1 raw1175step0; decide +kernel
      have hl : raw1175step1Labels = raw1175step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1175step1 raw1175step1Labels = mixedMoment B raw1175step2 raw1175step2Labels := by
      have ha : raw1175step2 = raw1175step1 := by apply Matrix.ext; unfold raw1175step2 raw1175step1; decide +kernel
      have hl : raw1175step1Labels = labelEmbedding1 ∘ raw1175step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1175step1 raw1175step1Labels raw1175step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1545 node1545Labels := by rfl

def raw1176 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, 2, -3]]
def raw1176Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1176step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1176step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1176step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1176 raw1176Labels = mixedMoment B node4380 node4380Labels := by
  calc
    mixedMoment B raw1176 raw1176Labels = mixedMoment B raw1176step0 raw1176step0Labels := by
      have ha : raw1176step0 = (fun i j => raw1176 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1176step0 raw1176; decide +kernel
      have hl : raw1176step0Labels = raw1176Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1176 raw1176Labels permutation32 permutation4
    mixedMoment B raw1176step0 raw1176step0Labels = mixedMoment B raw1176step1 raw1176step1Labels := by
      have ha : raw1176step1 = raw1176step0 := by apply Matrix.ext; unfold raw1176step1 raw1176step0; decide +kernel
      have hl : raw1176step0Labels = labelEmbedding7 ∘ raw1176step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1176step0 raw1176step0Labels raw1176step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4380 node4380Labels := by rfl

def raw1177 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, 2, -3]]
def raw1177Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1177step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1177 raw1177Labels = mixedMoment B node959 node959Labels := by
  calc
    mixedMoment B raw1177 raw1177Labels = mixedMoment B raw1177step0 raw1177step0Labels := by
      have ha : raw1177step0 = (fun i j => raw1177 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1177step0 raw1177; decide +kernel
      have hl : raw1177step0Labels = raw1177Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1177 raw1177Labels permutation32 permutation4
    _ = mixedMoment B node959 node959Labels := by rfl

def raw1178 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, 2, -3]]
def raw1178Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw1178step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1178step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1178step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1178step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1178 raw1178Labels = mixedMoment B node1546 node1546Labels := by
  calc
    mixedMoment B raw1178 raw1178Labels = mixedMoment B raw1178step0 raw1178step0Labels := by
      have ha : raw1178step0 = (fun i j => raw1178 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1178step0 raw1178; decide +kernel
      have hl : raw1178step0Labels = raw1178Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1178 raw1178Labels permutation32 permutation6
    mixedMoment B raw1178step0 raw1178step0Labels = mixedMoment B raw1178step1 raw1178step1Labels := by
      have ha : raw1178step1 = -raw1178step0 := by apply Matrix.ext; change ∀ i j, raw1178step1 i j = -(raw1178step0 i j); unfold raw1178step1 raw1178step0; decide +kernel
      have hl : raw1178step1Labels = raw1178step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1178step1 raw1178step1Labels = mixedMoment B raw1178step2 raw1178step2Labels := by
      have ha : raw1178step2 = raw1178step1 := by apply Matrix.ext; unfold raw1178step2 raw1178step1; decide +kernel
      have hl : raw1178step1Labels = labelEmbedding1 ∘ raw1178step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1178step1 raw1178step1Labels raw1178step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1546 node1546Labels := by rfl

def raw1179 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 0, 2], ![0, 1, -1], ![1, 1, -2], ![0, 2, -2]]
def raw1179Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1179step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1179step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1179step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1179 raw1179Labels = mixedMoment B node4381 node4381Labels := by
  calc
    mixedMoment B raw1179 raw1179Labels = mixedMoment B raw1179step0 raw1179step0Labels := by
      have ha : raw1179step0 = (fun i j => raw1179 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1179step0 raw1179; decide +kernel
      have hl : raw1179step0Labels = raw1179Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1179 raw1179Labels permutation32 permutation4
    mixedMoment B raw1179step0 raw1179step0Labels = mixedMoment B raw1179step1 raw1179step1Labels := by
      have ha : raw1179step1 = raw1179step0 := by apply Matrix.ext; unfold raw1179step1 raw1179step0; decide +kernel
      have hl : raw1179step0Labels = labelEmbedding7 ∘ raw1179step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1179step0 raw1179step0Labels raw1179step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4381 node4381Labels := by rfl

def raw1180 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 0, 2], ![0, 1, -1], ![1, 1, -2], ![0, 2, -2]]
def raw1180Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1180step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1180 raw1180Labels = mixedMoment B node960 node960Labels := by
  calc
    mixedMoment B raw1180 raw1180Labels = mixedMoment B raw1180step0 raw1180step0Labels := by
      have ha : raw1180step0 = (fun i j => raw1180 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1180step0 raw1180; decide +kernel
      have hl : raw1180step0Labels = raw1180Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1180 raw1180Labels permutation32 permutation4
    _ = mixedMoment B node960 node960Labels := by rfl

def raw1181 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 0, 2], ![0, 1, -1], ![1, 1, -2], ![0, 2, -2]]
def raw1181Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw1181step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1181step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1181step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1181step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1181step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1181 raw1181Labels = mixedMoment B node1547 node1547Labels := by
  calc
    mixedMoment B raw1181 raw1181Labels = mixedMoment B raw1181step0 raw1181step0Labels := by
      have ha : raw1181step0 = (fun i j => raw1181 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1181step0 raw1181; decide +kernel
      have hl : raw1181step0Labels = raw1181Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1181 raw1181Labels permutation32 permutation6
    mixedMoment B raw1181step0 raw1181step0Labels = mixedMoment B raw1181step1 raw1181step1Labels := by
      have ha : raw1181step1 = -raw1181step0 := by apply Matrix.ext; change ∀ i j, raw1181step1 i j = -(raw1181step0 i j); unfold raw1181step1 raw1181step0; decide +kernel
      have hl : raw1181step1Labels = raw1181step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1181step1 raw1181step1Labels = mixedMoment B raw1181step2 raw1181step2Labels := by
      have ha : raw1181step2 = raw1181step1 := by apply Matrix.ext; unfold raw1181step2 raw1181step1; decide +kernel
      have hl : raw1181step1Labels = labelEmbedding1 ∘ raw1181step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1181step1 raw1181step1Labels raw1181step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1547 node1547Labels := by rfl

def raw1182 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 0, 2], ![1, 1, -2], ![0, 3, -3]]
def raw1182Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1182step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 1, -2], ![3, 0, -3]]
def raw1182step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1182step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 1, -2], ![3, 0, -3]]
def raw1182step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1182 raw1182Labels = mixedMoment B node4382 node4382Labels := by
  calc
    mixedMoment B raw1182 raw1182Labels = mixedMoment B raw1182step0 raw1182step0Labels := by
      have ha : raw1182step0 = (fun i j => raw1182 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1182step0 raw1182; decide +kernel
      have hl : raw1182step0Labels = raw1182Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1182 raw1182Labels permutation8 permutation4
    mixedMoment B raw1182step0 raw1182step0Labels = mixedMoment B raw1182step1 raw1182step1Labels := by
      have ha : raw1182step1 = raw1182step0 := by apply Matrix.ext; unfold raw1182step1 raw1182step0; decide +kernel
      have hl : raw1182step0Labels = labelEmbedding7 ∘ raw1182step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1182step0 raw1182step0Labels raw1182step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4382 node4382Labels := by rfl

def raw1183 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 0, 2], ![1, 1, -2], ![0, 3, -3]]
def raw1183Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1183step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 1, -2], ![3, 0, -3]]
def raw1183step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1183 raw1183Labels = mixedMoment B node962 node962Labels := by
  calc
    mixedMoment B raw1183 raw1183Labels = mixedMoment B raw1183step0 raw1183step0Labels := by
      have ha : raw1183step0 = (fun i j => raw1183 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1183step0 raw1183; decide +kernel
      have hl : raw1183step0Labels = raw1183Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1183 raw1183Labels permutation8 permutation4
    _ = mixedMoment B node962 node962Labels := by rfl

def raw1184 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 0, 2], ![1, 1, -2], ![0, 3, -3]]
def raw1184Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1184step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-2, 1, 1], ![-3, 0, 3]]
def raw1184step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1184step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![2, -1, -1], ![3, 0, -3]]
def raw1184step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1184step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![2, -1, -1], ![3, 0, -3]]
def raw1184step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1184 raw1184Labels = mixedMoment B node1548 node1548Labels := by
  calc
    mixedMoment B raw1184 raw1184Labels = mixedMoment B raw1184step0 raw1184step0Labels := by
      have ha : raw1184step0 = (fun i j => raw1184 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1184step0 raw1184; decide +kernel
      have hl : raw1184step0Labels = raw1184Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1184 raw1184Labels permutation8 permutation6
    mixedMoment B raw1184step0 raw1184step0Labels = mixedMoment B raw1184step1 raw1184step1Labels := by
      have ha : raw1184step1 = -raw1184step0 := by apply Matrix.ext; change ∀ i j, raw1184step1 i j = -(raw1184step0 i j); unfold raw1184step1 raw1184step0; decide +kernel
      have hl : raw1184step1Labels = raw1184step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1184step1 raw1184step1Labels = mixedMoment B raw1184step2 raw1184step2Labels := by
      have ha : raw1184step2 = raw1184step1 := by apply Matrix.ext; unfold raw1184step2 raw1184step1; decide +kernel
      have hl : raw1184step1Labels = labelEmbedding1 ∘ raw1184step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1184step1 raw1184step1Labels raw1184step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1548 node1548Labels := by rfl

def raw1185 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 0, 2], ![0, 2, -2], ![1, 2, -3]]
def raw1185Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1185step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![2, 0, -2], ![2, 1, -3]]
def raw1185step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1185step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![2, 0, -2], ![2, 1, -3]]
def raw1185step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1185 raw1185Labels = mixedMoment B node4383 node4383Labels := by
  calc
    mixedMoment B raw1185 raw1185Labels = mixedMoment B raw1185step0 raw1185step0Labels := by
      have ha : raw1185step0 = (fun i j => raw1185 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1185step0 raw1185; decide +kernel
      have hl : raw1185step0Labels = raw1185Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1185 raw1185Labels permutation8 permutation4
    mixedMoment B raw1185step0 raw1185step0Labels = mixedMoment B raw1185step1 raw1185step1Labels := by
      have ha : raw1185step1 = raw1185step0 := by apply Matrix.ext; unfold raw1185step1 raw1185step0; decide +kernel
      have hl : raw1185step0Labels = labelEmbedding7 ∘ raw1185step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1185step0 raw1185step0Labels raw1185step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4383 node4383Labels := by rfl

def raw1186 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 0, 2], ![0, 2, -2], ![1, 2, -3]]
def raw1186Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1186step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![2, 0, -2], ![2, 1, -3]]
def raw1186step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1186 raw1186Labels = mixedMoment B node963 node963Labels := by
  calc
    mixedMoment B raw1186 raw1186Labels = mixedMoment B raw1186step0 raw1186step0Labels := by
      have ha : raw1186step0 = (fun i j => raw1186 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1186step0 raw1186; decide +kernel
      have hl : raw1186step0Labels = raw1186Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1186 raw1186Labels permutation8 permutation4
    _ = mixedMoment B node963 node963Labels := by rfl

def raw1187 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 0, 2], ![0, 2, -2], ![1, 2, -3]]
def raw1187Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1187step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-2, 0, 2], ![-3, 1, 2]]
def raw1187step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1187step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![2, 0, -2], ![3, -1, -2]]
def raw1187step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1187step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![2, 0, -2], ![3, -1, -2]]
def raw1187step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1187 raw1187Labels = mixedMoment B node1549 node1549Labels := by
  calc
    mixedMoment B raw1187 raw1187Labels = mixedMoment B raw1187step0 raw1187step0Labels := by
      have ha : raw1187step0 = (fun i j => raw1187 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1187step0 raw1187; decide +kernel
      have hl : raw1187step0Labels = raw1187Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1187 raw1187Labels permutation8 permutation6
    mixedMoment B raw1187step0 raw1187step0Labels = mixedMoment B raw1187step1 raw1187step1Labels := by
      have ha : raw1187step1 = -raw1187step0 := by apply Matrix.ext; change ∀ i j, raw1187step1 i j = -(raw1187step0 i j); unfold raw1187step1 raw1187step0; decide +kernel
      have hl : raw1187step1Labels = raw1187step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1187step1 raw1187step1Labels = mixedMoment B raw1187step2 raw1187step2Labels := by
      have ha : raw1187step2 = raw1187step1 := by apply Matrix.ext; unfold raw1187step2 raw1187step1; decide +kernel
      have hl : raw1187step1Labels = labelEmbedding1 ∘ raw1187step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1187step1 raw1187step1Labels raw1187step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1549 node1549Labels := by rfl

def raw1188 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![0, 3, -3]]
def raw1188Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1188step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw1188step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1188step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw1188step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1188 raw1188Labels = mixedMoment B node4384 node4384Labels := by
  calc
    mixedMoment B raw1188 raw1188Labels = mixedMoment B raw1188step0 raw1188step0Labels := by
      have ha : raw1188step0 = (fun i j => raw1188 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1188step0 raw1188; decide +kernel
      have hl : raw1188step0Labels = raw1188Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1188 raw1188Labels permutation152 permutation4
    mixedMoment B raw1188step0 raw1188step0Labels = mixedMoment B raw1188step1 raw1188step1Labels := by
      have ha : raw1188step1 = raw1188step0 := by apply Matrix.ext; unfold raw1188step1 raw1188step0; decide +kernel
      have hl : raw1188step0Labels = labelEmbedding7 ∘ raw1188step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1188step0 raw1188step0Labels raw1188step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4384 node4384Labels := by rfl

def raw1189 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![0, 3, -3]]
def raw1189Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1189step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw1189step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1189 raw1189Labels = mixedMoment B node964 node964Labels := by
  calc
    mixedMoment B raw1189 raw1189Labels = mixedMoment B raw1189step0 raw1189step0Labels := by
      have ha : raw1189step0 = (fun i j => raw1189 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1189step0 raw1189; decide +kernel
      have hl : raw1189step0Labels = raw1189Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1189 raw1189Labels permutation152 permutation4
    _ = mixedMoment B node964 node964Labels := by rfl

def raw1190 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![0, 3, -3]]
def raw1190Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1190step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw1190step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1190step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw1190step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1190step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw1190step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1190 raw1190Labels = mixedMoment B node1580 node1580Labels := by
  calc
    mixedMoment B raw1190 raw1190Labels = mixedMoment B raw1190step0 raw1190step0Labels := by
      have ha : raw1190step0 = (fun i j => raw1190 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1190step0 raw1190; decide +kernel
      have hl : raw1190step0Labels = raw1190Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1190 raw1190Labels permutation152 permutation6
    mixedMoment B raw1190step0 raw1190step0Labels = mixedMoment B raw1190step1 raw1190step1Labels := by
      have ha : raw1190step1 = -raw1190step0 := by apply Matrix.ext; change ∀ i j, raw1190step1 i j = -(raw1190step0 i j); unfold raw1190step1 raw1190step0; decide +kernel
      have hl : raw1190step1Labels = raw1190step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1190step1 raw1190step1Labels = mixedMoment B raw1190step2 raw1190step2Labels := by
      have ha : raw1190step2 = raw1190step1 := by apply Matrix.ext; unfold raw1190step2 raw1190step1; decide +kernel
      have hl : raw1190step1Labels = labelEmbedding1 ∘ raw1190step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1190step1 raw1190step1Labels raw1190step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1580 node1580Labels := by rfl

def raw1191 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 2, -2], ![0, 2, -2]]
def raw1191Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1191step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1191step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1191step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1191step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1191 raw1191Labels = mixedMoment B node4385 node4385Labels := by
  calc
    mixedMoment B raw1191 raw1191Labels = mixedMoment B raw1191step0 raw1191step0Labels := by
      have ha : raw1191step0 = (fun i j => raw1191 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1191step0 raw1191; decide +kernel
      have hl : raw1191step0Labels = raw1191Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1191 raw1191Labels permutation152 permutation4
    mixedMoment B raw1191step0 raw1191step0Labels = mixedMoment B raw1191step1 raw1191step1Labels := by
      have ha : raw1191step1 = raw1191step0 := by apply Matrix.ext; unfold raw1191step1 raw1191step0; decide +kernel
      have hl : raw1191step0Labels = labelEmbedding7 ∘ raw1191step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1191step0 raw1191step0Labels raw1191step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4385 node4385Labels := by rfl

def raw1192 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 2, -2], ![0, 2, -2]]
def raw1192Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1192step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1192 raw1192Labels = mixedMoment B node965 node965Labels := by
  calc
    mixedMoment B raw1192 raw1192Labels = mixedMoment B raw1192step0 raw1192step0Labels := by
      have ha : raw1192step0 = (fun i j => raw1192 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1192step0 raw1192; decide +kernel
      have hl : raw1192step0Labels = raw1192Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1192 raw1192Labels permutation152 permutation4
    _ = mixedMoment B node965 node965Labels := by rfl

def raw1193 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 2, -2], ![0, 2, -2]]
def raw1193Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1193step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw1193step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1193step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1193step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1193step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1193step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1193 raw1193Labels = mixedMoment B node1581 node1581Labels := by
  calc
    mixedMoment B raw1193 raw1193Labels = mixedMoment B raw1193step0 raw1193step0Labels := by
      have ha : raw1193step0 = (fun i j => raw1193 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1193step0 raw1193; decide +kernel
      have hl : raw1193step0Labels = raw1193Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1193 raw1193Labels permutation152 permutation6
    mixedMoment B raw1193step0 raw1193step0Labels = mixedMoment B raw1193step1 raw1193step1Labels := by
      have ha : raw1193step1 = -raw1193step0 := by apply Matrix.ext; change ∀ i j, raw1193step1 i j = -(raw1193step0 i j); unfold raw1193step1 raw1193step0; decide +kernel
      have hl : raw1193step1Labels = raw1193step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1193step1 raw1193step1Labels = mixedMoment B raw1193step2 raw1193step2Labels := by
      have ha : raw1193step2 = raw1193step1 := by apply Matrix.ext; unfold raw1193step2 raw1193step1; decide +kernel
      have hl : raw1193step1Labels = labelEmbedding1 ∘ raw1193step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1193step1 raw1193step1Labels raw1193step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1581 node1581Labels := by rfl

def raw1194 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 2, -3]]
def raw1194Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1194step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1194step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1194step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1194 raw1194Labels = mixedMoment B node4386 node4386Labels := by
  calc
    mixedMoment B raw1194 raw1194Labels = mixedMoment B raw1194step0 raw1194step0Labels := by
      have ha : raw1194step0 = (fun i j => raw1194 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1194step0 raw1194; decide +kernel
      have hl : raw1194step0Labels = raw1194Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1194 raw1194Labels permutation152 permutation4
    mixedMoment B raw1194step0 raw1194step0Labels = mixedMoment B raw1194step1 raw1194step1Labels := by
      have ha : raw1194step1 = raw1194step0 := by apply Matrix.ext; unfold raw1194step1 raw1194step0; decide +kernel
      have hl : raw1194step0Labels = labelEmbedding7 ∘ raw1194step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1194step0 raw1194step0Labels raw1194step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4386 node4386Labels := by rfl

def raw1195 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 2, -3]]
def raw1195Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1195step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1195step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1195 raw1195Labels = mixedMoment B node966 node966Labels := by
  calc
    mixedMoment B raw1195 raw1195Labels = mixedMoment B raw1195step0 raw1195step0Labels := by
      have ha : raw1195step0 = (fun i j => raw1195 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1195step0 raw1195; decide +kernel
      have hl : raw1195step0Labels = raw1195Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1195 raw1195Labels permutation152 permutation4
    _ = mixedMoment B node966 node966Labels := by rfl

def raw1196 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 2, -3]]
def raw1196Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw1196step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1196step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1196step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1196step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1196step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1196 raw1196Labels = mixedMoment B node1582 node1582Labels := by
  calc
    mixedMoment B raw1196 raw1196Labels = mixedMoment B raw1196step0 raw1196step0Labels := by
      have ha : raw1196step0 = (fun i j => raw1196 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1196step0 raw1196; decide +kernel
      have hl : raw1196step0Labels = raw1196Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1196 raw1196Labels permutation152 permutation6
    mixedMoment B raw1196step0 raw1196step0Labels = mixedMoment B raw1196step1 raw1196step1Labels := by
      have ha : raw1196step1 = -raw1196step0 := by apply Matrix.ext; change ∀ i j, raw1196step1 i j = -(raw1196step0 i j); unfold raw1196step1 raw1196step0; decide +kernel
      have hl : raw1196step1Labels = raw1196step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1196step1 raw1196step1Labels = mixedMoment B raw1196step2 raw1196step2Labels := by
      have ha : raw1196step2 = raw1196step1 := by apply Matrix.ext; unfold raw1196step2 raw1196step1; decide +kernel
      have hl : raw1196step1Labels = labelEmbedding1 ∘ raw1196step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1196step1 raw1196step1Labels raw1196step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1582 node1582Labels := by rfl

def raw1197 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![0, 2, -2]]
def raw1197Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1197step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1197step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1197step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1197step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1197 raw1197Labels = mixedMoment B node4387 node4387Labels := by
  calc
    mixedMoment B raw1197 raw1197Labels = mixedMoment B raw1197step0 raw1197step0Labels := by
      have ha : raw1197step0 = (fun i j => raw1197 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1197step0 raw1197; decide +kernel
      have hl : raw1197step0Labels = raw1197Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1197 raw1197Labels permutation152 permutation4
    mixedMoment B raw1197step0 raw1197step0Labels = mixedMoment B raw1197step1 raw1197step1Labels := by
      have ha : raw1197step1 = raw1197step0 := by apply Matrix.ext; unfold raw1197step1 raw1197step0; decide +kernel
      have hl : raw1197step0Labels = labelEmbedding7 ∘ raw1197step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1197step0 raw1197step0Labels raw1197step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4387 node4387Labels := by rfl

def raw1198 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![0, 2, -2]]
def raw1198Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1198step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1198step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1198 raw1198Labels = mixedMoment B node967 node967Labels := by
  calc
    mixedMoment B raw1198 raw1198Labels = mixedMoment B raw1198step0 raw1198step0Labels := by
      have ha : raw1198step0 = (fun i j => raw1198 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1198step0 raw1198; decide +kernel
      have hl : raw1198step0Labels = raw1198Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1198 raw1198Labels permutation152 permutation4
    _ = mixedMoment B node967 node967Labels := by rfl

def raw1199 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![0, 2, -2]]
def raw1199Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw1199step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1199step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1199step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1199step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1199step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1199 raw1199Labels = mixedMoment B node1583 node1583Labels := by
  calc
    mixedMoment B raw1199 raw1199Labels = mixedMoment B raw1199step0 raw1199step0Labels := by
      have ha : raw1199step0 = (fun i j => raw1199 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1199step0 raw1199; decide +kernel
      have hl : raw1199step0Labels = raw1199Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1199 raw1199Labels permutation152 permutation6
    mixedMoment B raw1199step0 raw1199step0Labels = mixedMoment B raw1199step1 raw1199step1Labels := by
      have ha : raw1199step1 = -raw1199step0 := by apply Matrix.ext; change ∀ i j, raw1199step1 i j = -(raw1199step0 i j); unfold raw1199step1 raw1199step0; decide +kernel
      have hl : raw1199step1Labels = raw1199step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1199step1 raw1199step1Labels = mixedMoment B raw1199step2 raw1199step2Labels := by
      have ha : raw1199step2 = raw1199step1 := by apply Matrix.ext; unfold raw1199step2 raw1199step1; decide +kernel
      have hl : raw1199step1Labels = labelEmbedding1 ∘ raw1199step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1199step1 raw1199step1Labels raw1199step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1583 node1583Labels := by rfl

def raw1200 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![0, 3, -3]]
def raw1200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def raw1200step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def raw1200step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1200 raw1200Labels = mixedMoment B node4388 node4388Labels := by
  calc
    mixedMoment B raw1200 raw1200Labels = mixedMoment B raw1200step0 raw1200step0Labels := by
      have ha : raw1200step0 = (fun i j => raw1200 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1200step0 raw1200; decide +kernel
      have hl : raw1200step0Labels = raw1200Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1200 raw1200Labels permutation32 permutation4
    mixedMoment B raw1200step0 raw1200step0Labels = mixedMoment B raw1200step1 raw1200step1Labels := by
      have ha : raw1200step1 = raw1200step0 := by apply Matrix.ext; unfold raw1200step1 raw1200step0; decide +kernel
      have hl : raw1200step0Labels = labelEmbedding7 ∘ raw1200step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1200step0 raw1200step0Labels raw1200step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4388 node4388Labels := by rfl

def raw1201 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![0, 3, -3]]
def raw1201Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def raw1201step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1201 raw1201Labels = mixedMoment B node969 node969Labels := by
  calc
    mixedMoment B raw1201 raw1201Labels = mixedMoment B raw1201step0 raw1201step0Labels := by
      have ha : raw1201step0 = (fun i j => raw1201 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1201step0 raw1201; decide +kernel
      have hl : raw1201step0Labels = raw1201Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1201 raw1201Labels permutation32 permutation4
    _ = mixedMoment B node969 node969Labels := by rfl

def raw1202 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![0, 3, -3]]
def raw1202Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-3, 0, 3]]
def raw1202step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, 0, -3]]
def raw1202step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1202step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, 0, -3]]
def raw1202step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1202 raw1202Labels = mixedMoment B node1584 node1584Labels := by
  calc
    mixedMoment B raw1202 raw1202Labels = mixedMoment B raw1202step0 raw1202step0Labels := by
      have ha : raw1202step0 = (fun i j => raw1202 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1202step0 raw1202; decide +kernel
      have hl : raw1202step0Labels = raw1202Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1202 raw1202Labels permutation32 permutation6
    mixedMoment B raw1202step0 raw1202step0Labels = mixedMoment B raw1202step1 raw1202step1Labels := by
      have ha : raw1202step1 = -raw1202step0 := by apply Matrix.ext; change ∀ i j, raw1202step1 i j = -(raw1202step0 i j); unfold raw1202step1 raw1202step0; decide +kernel
      have hl : raw1202step1Labels = raw1202step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1202step1 raw1202step1Labels = mixedMoment B raw1202step2 raw1202step2Labels := by
      have ha : raw1202step2 = raw1202step1 := by apply Matrix.ext; unfold raw1202step2 raw1202step1; decide +kernel
      have hl : raw1202step1Labels = labelEmbedding1 ∘ raw1202step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1202step1 raw1202step1Labels raw1202step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1584 node1584Labels := by rfl

def raw1203 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 2, -3]]
def raw1203Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw1203step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw1203step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1203 raw1203Labels = mixedMoment B node4389 node4389Labels := by
  calc
    mixedMoment B raw1203 raw1203Labels = mixedMoment B raw1203step0 raw1203step0Labels := by
      have ha : raw1203step0 = (fun i j => raw1203 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1203step0 raw1203; decide +kernel
      have hl : raw1203step0Labels = raw1203Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1203 raw1203Labels permutation32 permutation4
    mixedMoment B raw1203step0 raw1203step0Labels = mixedMoment B raw1203step1 raw1203step1Labels := by
      have ha : raw1203step1 = raw1203step0 := by apply Matrix.ext; unfold raw1203step1 raw1203step0; decide +kernel
      have hl : raw1203step0Labels = labelEmbedding7 ∘ raw1203step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1203step0 raw1203step0Labels raw1203step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4389 node4389Labels := by rfl

def raw1204 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 2, -3]]
def raw1204Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw1204step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1204 raw1204Labels = mixedMoment B node970 node970Labels := by
  calc
    mixedMoment B raw1204 raw1204Labels = mixedMoment B raw1204step0 raw1204step0Labels := by
      have ha : raw1204step0 = (fun i j => raw1204 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1204step0 raw1204; decide +kernel
      have hl : raw1204step0Labels = raw1204Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1204 raw1204Labels permutation32 permutation4
    _ = mixedMoment B node970 node970Labels := by rfl

def raw1205 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 2, -3]]
def raw1205Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-3, 1, 2]]
def raw1205step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1205step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw1205step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1205step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw1205step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1205 raw1205Labels = mixedMoment B node1585 node1585Labels := by
  calc
    mixedMoment B raw1205 raw1205Labels = mixedMoment B raw1205step0 raw1205step0Labels := by
      have ha : raw1205step0 = (fun i j => raw1205 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1205step0 raw1205; decide +kernel
      have hl : raw1205step0Labels = raw1205Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1205 raw1205Labels permutation32 permutation6
    mixedMoment B raw1205step0 raw1205step0Labels = mixedMoment B raw1205step1 raw1205step1Labels := by
      have ha : raw1205step1 = -raw1205step0 := by apply Matrix.ext; change ∀ i j, raw1205step1 i j = -(raw1205step0 i j); unfold raw1205step1 raw1205step0; decide +kernel
      have hl : raw1205step1Labels = raw1205step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1205step1 raw1205step1Labels = mixedMoment B raw1205step2 raw1205step2Labels := by
      have ha : raw1205step2 = raw1205step1 := by apply Matrix.ext; unfold raw1205step2 raw1205step1; decide +kernel
      have hl : raw1205step1Labels = labelEmbedding1 ∘ raw1205step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1205step1 raw1205step1Labels raw1205step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1585 node1585Labels := by rfl

def raw1206 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1206Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1206step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1206step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1206step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1206 raw1206Labels = mixedMoment B node4396 node4396Labels := by
  calc
    mixedMoment B raw1206 raw1206Labels = mixedMoment B raw1206step0 raw1206step0Labels := by
      have ha : raw1206step0 = (fun i j => raw1206 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1206step0 raw1206; decide +kernel
      have hl : raw1206step0Labels = raw1206Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1206 raw1206Labels permutation152 permutation4
    mixedMoment B raw1206step0 raw1206step0Labels = mixedMoment B raw1206step1 raw1206step1Labels := by
      have ha : raw1206step1 = raw1206step0 := by apply Matrix.ext; unfold raw1206step1 raw1206step0; decide +kernel
      have hl : raw1206step0Labels = labelEmbedding7 ∘ raw1206step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1206step0 raw1206step0Labels raw1206step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4396 node4396Labels := by rfl

def raw1207 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1207Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1207step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1207 raw1207Labels = mixedMoment B node977 node977Labels := by
  calc
    mixedMoment B raw1207 raw1207Labels = mixedMoment B raw1207step0 raw1207step0Labels := by
      have ha : raw1207step0 = (fun i j => raw1207 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1207step0 raw1207; decide +kernel
      have hl : raw1207step0Labels = raw1207Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1207 raw1207Labels permutation152 permutation4
    _ = mixedMoment B node977 node977Labels := by rfl

def raw1208 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1208Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1208step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw1208step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1208step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1208step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1208step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1208step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1208 raw1208Labels = mixedMoment B node1597 node1597Labels := by
  calc
    mixedMoment B raw1208 raw1208Labels = mixedMoment B raw1208step0 raw1208step0Labels := by
      have ha : raw1208step0 = (fun i j => raw1208 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1208step0 raw1208; decide +kernel
      have hl : raw1208step0Labels = raw1208Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1208 raw1208Labels permutation158 permutation6
    mixedMoment B raw1208step0 raw1208step0Labels = mixedMoment B raw1208step1 raw1208step1Labels := by
      have ha : raw1208step1 = -raw1208step0 := by apply Matrix.ext; change ∀ i j, raw1208step1 i j = -(raw1208step0 i j); unfold raw1208step1 raw1208step0; decide +kernel
      have hl : raw1208step1Labels = raw1208step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1208step1 raw1208step1Labels = mixedMoment B raw1208step2 raw1208step2Labels := by
      have ha : raw1208step2 = raw1208step1 := by apply Matrix.ext; unfold raw1208step2 raw1208step1; decide +kernel
      have hl : raw1208step1Labels = labelEmbedding1 ∘ raw1208step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1208step1 raw1208step1Labels raw1208step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1597 node1597Labels := by rfl

def raw1209 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 3, -3]]
def raw1209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1209step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1209step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1209step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1209 raw1209Labels = mixedMoment B node4398 node4398Labels := by
  calc
    mixedMoment B raw1209 raw1209Labels = mixedMoment B raw1209step0 raw1209step0Labels := by
      have ha : raw1209step0 = (fun i j => raw1209 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1209step0 raw1209; decide +kernel
      have hl : raw1209step0Labels = raw1209Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1209 raw1209Labels permutation32 permutation4
    mixedMoment B raw1209step0 raw1209step0Labels = mixedMoment B raw1209step1 raw1209step1Labels := by
      have ha : raw1209step1 = raw1209step0 := by apply Matrix.ext; unfold raw1209step1 raw1209step0; decide +kernel
      have hl : raw1209step0Labels = labelEmbedding7 ∘ raw1209step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1209step0 raw1209step0Labels raw1209step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4398 node4398Labels := by rfl

def raw1210 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 3, -3]]
def raw1210Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1210step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1210 raw1210Labels = mixedMoment B node979 node979Labels := by
  calc
    mixedMoment B raw1210 raw1210Labels = mixedMoment B raw1210step0 raw1210step0Labels := by
      have ha : raw1210step0 = (fun i j => raw1210 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1210step0 raw1210; decide +kernel
      have hl : raw1210step0Labels = raw1210Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1210 raw1210Labels permutation32 permutation4
    _ = mixedMoment B node979 node979Labels := by rfl

def raw1211 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 3, -3]]
def raw1211Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw1211step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1211step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1211step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1211step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1211step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1211 raw1211Labels = mixedMoment B node1599 node1599Labels := by
  calc
    mixedMoment B raw1211 raw1211Labels = mixedMoment B raw1211step0 raw1211step0Labels := by
      have ha : raw1211step0 = (fun i j => raw1211 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1211step0 raw1211; decide +kernel
      have hl : raw1211step0Labels = raw1211Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1211 raw1211Labels permutation34 permutation6
    mixedMoment B raw1211step0 raw1211step0Labels = mixedMoment B raw1211step1 raw1211step1Labels := by
      have ha : raw1211step1 = -raw1211step0 := by apply Matrix.ext; change ∀ i j, raw1211step1 i j = -(raw1211step0 i j); unfold raw1211step1 raw1211step0; decide +kernel
      have hl : raw1211step1Labels = raw1211step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1211step1 raw1211step1Labels = mixedMoment B raw1211step2 raw1211step2Labels := by
      have ha : raw1211step2 = raw1211step1 := by apply Matrix.ext; unfold raw1211step2 raw1211step1; decide +kernel
      have hl : raw1211step1Labels = labelEmbedding1 ∘ raw1211step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1211step1 raw1211step1Labels raw1211step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1599 node1599Labels := by rfl

def raw1212 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1212Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1212step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1212step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1212 raw1212Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw1212 raw1212Labels = mixedMoment B raw1212step0 raw1212step0Labels := by
      have ha : raw1212step0 = (fun i j => raw1212 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1212step0 raw1212; decide +kernel
      have hl : raw1212step0Labels = raw1212Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1212 raw1212Labels permutation152 permutation4
    mixedMoment B raw1212step0 raw1212step0Labels = mixedMoment B raw1212step1 raw1212step1Labels := by
      have ha : raw1212step1 = raw1212step0 := by apply Matrix.ext; unfold raw1212step1 raw1212step0; decide +kernel
      have hl : raw1212step0Labels = labelEmbedding7 ∘ raw1212step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1212step0 raw1212step0Labels raw1212step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4399 node4399Labels := by rfl

def raw1213 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1213Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1213step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1213step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1213 raw1213Labels = mixedMoment B node980 node980Labels := by
  calc
    mixedMoment B raw1213 raw1213Labels = mixedMoment B raw1213step0 raw1213step0Labels := by
      have ha : raw1213step0 = (fun i j => raw1213 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1213step0 raw1213; decide +kernel
      have hl : raw1213step0Labels = raw1213Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1213 raw1213Labels permutation152 permutation4
    _ = mixedMoment B node980 node980Labels := by rfl

def raw1214 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1214Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1214step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw1214step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1214step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1214step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1214step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1214step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1214 raw1214Labels = mixedMoment B node1616 node1616Labels := by
  calc
    mixedMoment B raw1214 raw1214Labels = mixedMoment B raw1214step0 raw1214step0Labels := by
      have ha : raw1214step0 = (fun i j => raw1214 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1214step0 raw1214; decide +kernel
      have hl : raw1214step0Labels = raw1214Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1214 raw1214Labels permutation152 permutation6
    mixedMoment B raw1214step0 raw1214step0Labels = mixedMoment B raw1214step1 raw1214step1Labels := by
      have ha : raw1214step1 = -raw1214step0 := by apply Matrix.ext; change ∀ i j, raw1214step1 i j = -(raw1214step0 i j); unfold raw1214step1 raw1214step0; decide +kernel
      have hl : raw1214step1Labels = raw1214step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1214step1 raw1214step1Labels = mixedMoment B raw1214step2 raw1214step2Labels := by
      have ha : raw1214step2 = raw1214step1 := by apply Matrix.ext; unfold raw1214step2 raw1214step1; decide +kernel
      have hl : raw1214step1Labels = labelEmbedding1 ∘ raw1214step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1214step1 raw1214step1Labels raw1214step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1616 node1616Labels := by rfl

def raw1215 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1215step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1215step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1215step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1215 raw1215Labels = mixedMoment B node4401 node4401Labels := by
  calc
    mixedMoment B raw1215 raw1215Labels = mixedMoment B raw1215step0 raw1215step0Labels := by
      have ha : raw1215step0 = (fun i j => raw1215 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1215step0 raw1215; decide +kernel
      have hl : raw1215step0Labels = raw1215Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1215 raw1215Labels permutation32 permutation4
    mixedMoment B raw1215step0 raw1215step0Labels = mixedMoment B raw1215step1 raw1215step1Labels := by
      have ha : raw1215step1 = raw1215step0 := by apply Matrix.ext; unfold raw1215step1 raw1215step0; decide +kernel
      have hl : raw1215step0Labels = labelEmbedding7 ∘ raw1215step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1215step0 raw1215step0Labels raw1215step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4401 node4401Labels := by rfl

def raw1216 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1216Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1216step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1216 raw1216Labels = mixedMoment B node982 node982Labels := by
  calc
    mixedMoment B raw1216 raw1216Labels = mixedMoment B raw1216step0 raw1216step0Labels := by
      have ha : raw1216step0 = (fun i j => raw1216 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1216step0 raw1216; decide +kernel
      have hl : raw1216step0Labels = raw1216Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1216 raw1216Labels permutation32 permutation4
    _ = mixedMoment B node982 node982Labels := by rfl

def raw1217 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1217Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw1217step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1217step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1217step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1217step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1217 raw1217Labels = mixedMoment B node1617 node1617Labels := by
  calc
    mixedMoment B raw1217 raw1217Labels = mixedMoment B raw1217step0 raw1217step0Labels := by
      have ha : raw1217step0 = (fun i j => raw1217 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1217step0 raw1217; decide +kernel
      have hl : raw1217step0Labels = raw1217Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1217 raw1217Labels permutation32 permutation6
    mixedMoment B raw1217step0 raw1217step0Labels = mixedMoment B raw1217step1 raw1217step1Labels := by
      have ha : raw1217step1 = -raw1217step0 := by apply Matrix.ext; change ∀ i j, raw1217step1 i j = -(raw1217step0 i j); unfold raw1217step1 raw1217step0; decide +kernel
      have hl : raw1217step1Labels = raw1217step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1217step1 raw1217step1Labels = mixedMoment B raw1217step2 raw1217step2Labels := by
      have ha : raw1217step2 = raw1217step1 := by apply Matrix.ext; unfold raw1217step2 raw1217step1; decide +kernel
      have hl : raw1217step1Labels = labelEmbedding1 ∘ raw1217step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1217step1 raw1217step1Labels raw1217step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1617 node1617Labels := by rfl

def raw1218 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1218Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1218step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1218step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1218step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1218 raw1218Labels = mixedMoment B node4404 node4404Labels := by
  calc
    mixedMoment B raw1218 raw1218Labels = mixedMoment B raw1218step0 raw1218step0Labels := by
      have ha : raw1218step0 = (fun i j => raw1218 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1218step0 raw1218; decide +kernel
      have hl : raw1218step0Labels = raw1218Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1218 raw1218Labels permutation32 permutation4
    mixedMoment B raw1218step0 raw1218step0Labels = mixedMoment B raw1218step1 raw1218step1Labels := by
      have ha : raw1218step1 = raw1218step0 := by apply Matrix.ext; unfold raw1218step1 raw1218step0; decide +kernel
      have hl : raw1218step0Labels = labelEmbedding7 ∘ raw1218step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1218step0 raw1218step0Labels raw1218step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4404 node4404Labels := by rfl

def raw1219 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1219Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1219step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1219 raw1219Labels = mixedMoment B node985 node985Labels := by
  calc
    mixedMoment B raw1219 raw1219Labels = mixedMoment B raw1219step0 raw1219step0Labels := by
      have ha : raw1219step0 = (fun i j => raw1219 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1219step0 raw1219; decide +kernel
      have hl : raw1219step0Labels = raw1219Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1219 raw1219Labels permutation32 permutation4
    _ = mixedMoment B node985 node985Labels := by rfl

def raw1220 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1220Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw1220step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1220step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1220step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1220step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1220 raw1220Labels = mixedMoment B node1618 node1618Labels := by
  calc
    mixedMoment B raw1220 raw1220Labels = mixedMoment B raw1220step0 raw1220step0Labels := by
      have ha : raw1220step0 = (fun i j => raw1220 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1220step0 raw1220; decide +kernel
      have hl : raw1220step0Labels = raw1220Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1220 raw1220Labels permutation32 permutation6
    mixedMoment B raw1220step0 raw1220step0Labels = mixedMoment B raw1220step1 raw1220step1Labels := by
      have ha : raw1220step1 = -raw1220step0 := by apply Matrix.ext; change ∀ i j, raw1220step1 i j = -(raw1220step0 i j); unfold raw1220step1 raw1220step0; decide +kernel
      have hl : raw1220step1Labels = raw1220step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1220step1 raw1220step1Labels = mixedMoment B raw1220step2 raw1220step2Labels := by
      have ha : raw1220step2 = raw1220step1 := by apply Matrix.ext; unfold raw1220step2 raw1220step1; decide +kernel
      have hl : raw1220step1Labels = labelEmbedding1 ∘ raw1220step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1220step1 raw1220step1Labels raw1220step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1618 node1618Labels := by rfl

def raw1221 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![-1, 4, -3]]
def raw1221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1221step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw1221step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1221step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw1221step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1221 raw1221Labels = mixedMoment B node4405 node4405Labels := by
  calc
    mixedMoment B raw1221 raw1221Labels = mixedMoment B raw1221step0 raw1221step0Labels := by
      have ha : raw1221step0 = (fun i j => raw1221 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1221step0 raw1221; decide +kernel
      have hl : raw1221step0Labels = raw1221Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1221 raw1221Labels permutation8 permutation4
    mixedMoment B raw1221step0 raw1221step0Labels = mixedMoment B raw1221step1 raw1221step1Labels := by
      have ha : raw1221step1 = raw1221step0 := by apply Matrix.ext; unfold raw1221step1 raw1221step0; decide +kernel
      have hl : raw1221step0Labels = labelEmbedding7 ∘ raw1221step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1221step0 raw1221step0Labels raw1221step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4405 node4405Labels := by rfl

def raw1222 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![-1, 4, -3]]
def raw1222Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1222step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw1222step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1222 raw1222Labels = mixedMoment B node986 node986Labels := by
  calc
    mixedMoment B raw1222 raw1222Labels = mixedMoment B raw1222step0 raw1222step0Labels := by
      have ha : raw1222step0 = (fun i j => raw1222 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1222step0 raw1222; decide +kernel
      have hl : raw1222step0Labels = raw1222Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1222 raw1222Labels permutation8 permutation4
    _ = mixedMoment B node986 node986Labels := by rfl

def raw1223 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 0, -1], ![-1, 4, -3]]
def raw1223Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1223step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw1223step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1223step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw1223step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1223 raw1223Labels = mixedMoment B node1620 node1620Labels := by
  calc
    mixedMoment B raw1223 raw1223Labels = mixedMoment B raw1223step0 raw1223step0Labels := by
      have ha : raw1223step0 = (fun i j => raw1223 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1223step0 raw1223; decide +kernel
      have hl : raw1223step0Labels = raw1223Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1223 raw1223Labels permutation31 permutation6
    mixedMoment B raw1223step0 raw1223step0Labels = mixedMoment B raw1223step1 raw1223step1Labels := by
      have ha : raw1223step1 = raw1223step0 := by apply Matrix.ext; unfold raw1223step1 raw1223step0; decide +kernel
      have hl : raw1223step0Labels = labelEmbedding1 ∘ raw1223step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1223step0 raw1223step0Labels raw1223step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1620 node1620Labels := by rfl

def raw1224 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw1224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1224step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1224step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1224step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1224step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1224 raw1224Labels = mixedMoment B node4417 node4417Labels := by
  calc
    mixedMoment B raw1224 raw1224Labels = mixedMoment B raw1224step0 raw1224step0Labels := by
      have ha : raw1224step0 = (fun i j => raw1224 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1224step0 raw1224; decide +kernel
      have hl : raw1224step0Labels = raw1224Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1224 raw1224Labels permutation152 permutation4
    mixedMoment B raw1224step0 raw1224step0Labels = mixedMoment B raw1224step1 raw1224step1Labels := by
      have ha : raw1224step1 = raw1224step0 := by apply Matrix.ext; unfold raw1224step1 raw1224step0; decide +kernel
      have hl : raw1224step0Labels = labelEmbedding7 ∘ raw1224step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1224step0 raw1224step0Labels raw1224step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4417 node4417Labels := by rfl

def raw1225 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw1225Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1225step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1225step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1225 raw1225Labels = mixedMoment B node998 node998Labels := by
  calc
    mixedMoment B raw1225 raw1225Labels = mixedMoment B raw1225step0 raw1225step0Labels := by
      have ha : raw1225step0 = (fun i j => raw1225 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1225step0 raw1225; decide +kernel
      have hl : raw1225step0Labels = raw1225Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1225 raw1225Labels permutation152 permutation4
    _ = mixedMoment B node998 node998Labels := by rfl

def raw1226 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw1226Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1226step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw1226step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1226step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1226step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1226step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1226step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1226 raw1226Labels = mixedMoment B node1600 node1600Labels := by
  calc
    mixedMoment B raw1226 raw1226Labels = mixedMoment B raw1226step0 raw1226step0Labels := by
      have ha : raw1226step0 = (fun i j => raw1226 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1226step0 raw1226; decide +kernel
      have hl : raw1226step0Labels = raw1226Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1226 raw1226Labels permutation152 permutation6
    mixedMoment B raw1226step0 raw1226step0Labels = mixedMoment B raw1226step1 raw1226step1Labels := by
      have ha : raw1226step1 = -raw1226step0 := by apply Matrix.ext; change ∀ i j, raw1226step1 i j = -(raw1226step0 i j); unfold raw1226step1 raw1226step0; decide +kernel
      have hl : raw1226step1Labels = raw1226step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1226step1 raw1226step1Labels = mixedMoment B raw1226step2 raw1226step2Labels := by
      have ha : raw1226step2 = raw1226step1 := by apply Matrix.ext; unfold raw1226step2 raw1226step1; decide +kernel
      have hl : raw1226step1Labels = labelEmbedding1 ∘ raw1226step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1226step1 raw1226step1Labels raw1226step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1600 node1600Labels := by rfl

def raw1227 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw1227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1227step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1227step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1227step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1227 raw1227Labels = mixedMoment B node4418 node4418Labels := by
  calc
    mixedMoment B raw1227 raw1227Labels = mixedMoment B raw1227step0 raw1227step0Labels := by
      have ha : raw1227step0 = (fun i j => raw1227 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1227step0 raw1227; decide +kernel
      have hl : raw1227step0Labels = raw1227Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1227 raw1227Labels permutation32 permutation4
    mixedMoment B raw1227step0 raw1227step0Labels = mixedMoment B raw1227step1 raw1227step1Labels := by
      have ha : raw1227step1 = raw1227step0 := by apply Matrix.ext; unfold raw1227step1 raw1227step0; decide +kernel
      have hl : raw1227step0Labels = labelEmbedding7 ∘ raw1227step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1227step0 raw1227step0Labels raw1227step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4418 node4418Labels := by rfl

def raw1228 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw1228Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1228step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1228 raw1228Labels = mixedMoment B node999 node999Labels := by
  calc
    mixedMoment B raw1228 raw1228Labels = mixedMoment B raw1228step0 raw1228step0Labels := by
      have ha : raw1228step0 = (fun i j => raw1228 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1228step0 raw1228; decide +kernel
      have hl : raw1228step0Labels = raw1228Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1228 raw1228Labels permutation32 permutation4
    _ = mixedMoment B node999 node999Labels := by rfl

def raw1229 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw1229Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw1229step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1229step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1229step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1229step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1229step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1229 raw1229Labels = mixedMoment B node1602 node1602Labels := by
  calc
    mixedMoment B raw1229 raw1229Labels = mixedMoment B raw1229step0 raw1229step0Labels := by
      have ha : raw1229step0 = (fun i j => raw1229 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1229step0 raw1229; decide +kernel
      have hl : raw1229step0Labels = raw1229Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1229 raw1229Labels permutation32 permutation6
    mixedMoment B raw1229step0 raw1229step0Labels = mixedMoment B raw1229step1 raw1229step1Labels := by
      have ha : raw1229step1 = -raw1229step0 := by apply Matrix.ext; change ∀ i j, raw1229step1 i j = -(raw1229step0 i j); unfold raw1229step1 raw1229step0; decide +kernel
      have hl : raw1229step1Labels = raw1229step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1229step1 raw1229step1Labels = mixedMoment B raw1229step2 raw1229step2Labels := by
      have ha : raw1229step2 = raw1229step1 := by apply Matrix.ext; unfold raw1229step2 raw1229step1; decide +kernel
      have hl : raw1229step1Labels = labelEmbedding1 ∘ raw1229step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1229step1 raw1229step1Labels raw1229step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1602 node1602Labels := by rfl

def raw1230 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw1230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1230step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1230step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1230step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1230 raw1230Labels = mixedMoment B node4419 node4419Labels := by
  calc
    mixedMoment B raw1230 raw1230Labels = mixedMoment B raw1230step0 raw1230step0Labels := by
      have ha : raw1230step0 = (fun i j => raw1230 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1230step0 raw1230; decide +kernel
      have hl : raw1230step0Labels = raw1230Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1230 raw1230Labels permutation32 permutation4
    mixedMoment B raw1230step0 raw1230step0Labels = mixedMoment B raw1230step1 raw1230step1Labels := by
      have ha : raw1230step1 = raw1230step0 := by apply Matrix.ext; unfold raw1230step1 raw1230step0; decide +kernel
      have hl : raw1230step0Labels = labelEmbedding7 ∘ raw1230step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1230step0 raw1230step0Labels raw1230step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4419 node4419Labels := by rfl

def raw1231 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw1231Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1231step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1231 raw1231Labels = mixedMoment B node1000 node1000Labels := by
  calc
    mixedMoment B raw1231 raw1231Labels = mixedMoment B raw1231step0 raw1231step0Labels := by
      have ha : raw1231step0 = (fun i j => raw1231 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1231step0 raw1231; decide +kernel
      have hl : raw1231step0Labels = raw1231Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1231 raw1231Labels permutation32 permutation4
    _ = mixedMoment B node1000 node1000Labels := by rfl

def raw1232 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw1232Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw1232step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1232step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1232step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1232step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1232 raw1232Labels = mixedMoment B node1605 node1605Labels := by
  calc
    mixedMoment B raw1232 raw1232Labels = mixedMoment B raw1232step0 raw1232step0Labels := by
      have ha : raw1232step0 = (fun i j => raw1232 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1232step0 raw1232; decide +kernel
      have hl : raw1232step0Labels = raw1232Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1232 raw1232Labels permutation32 permutation6
    mixedMoment B raw1232step0 raw1232step0Labels = mixedMoment B raw1232step1 raw1232step1Labels := by
      have ha : raw1232step1 = -raw1232step0 := by apply Matrix.ext; change ∀ i j, raw1232step1 i j = -(raw1232step0 i j); unfold raw1232step1 raw1232step0; decide +kernel
      have hl : raw1232step1Labels = raw1232step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1232step1 raw1232step1Labels = mixedMoment B raw1232step2 raw1232step2Labels := by
      have ha : raw1232step2 = raw1232step1 := by apply Matrix.ext; unfold raw1232step2 raw1232step1; decide +kernel
      have hl : raw1232step1Labels = labelEmbedding1 ∘ raw1232step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1232step1 raw1232step1Labels raw1232step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1605 node1605Labels := by rfl

def raw1233 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 3, -4]]
def raw1233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1233step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw1233step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1233step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw1233step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1233 raw1233Labels = mixedMoment B node4421 node4421Labels := by
  calc
    mixedMoment B raw1233 raw1233Labels = mixedMoment B raw1233step0 raw1233step0Labels := by
      have ha : raw1233step0 = (fun i j => raw1233 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1233step0 raw1233; decide +kernel
      have hl : raw1233step0Labels = raw1233Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1233 raw1233Labels permutation8 permutation4
    mixedMoment B raw1233step0 raw1233step0Labels = mixedMoment B raw1233step1 raw1233step1Labels := by
      have ha : raw1233step1 = raw1233step0 := by apply Matrix.ext; unfold raw1233step1 raw1233step0; decide +kernel
      have hl : raw1233step0Labels = labelEmbedding7 ∘ raw1233step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1233step0 raw1233step0Labels raw1233step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4421 node4421Labels := by rfl

def raw1234 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 3, -4]]
def raw1234Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1234step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw1234step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1234 raw1234Labels = mixedMoment B node1002 node1002Labels := by
  calc
    mixedMoment B raw1234 raw1234Labels = mixedMoment B raw1234step0 raw1234step0Labels := by
      have ha : raw1234step0 = (fun i j => raw1234 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1234step0 raw1234; decide +kernel
      have hl : raw1234step0Labels = raw1234Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1234 raw1234Labels permutation8 permutation4
    _ = mixedMoment B node1002 node1002Labels := by rfl

def raw1235 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 3, -4]]
def raw1235Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1235step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw1235step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1235step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw1235step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1235 raw1235Labels = mixedMoment B node1002 node1002Labels := by
  calc
    mixedMoment B raw1235 raw1235Labels = mixedMoment B raw1235step0 raw1235step0Labels := by
      have ha : raw1235step0 = (fun i j => raw1235 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1235step0 raw1235; decide +kernel
      have hl : raw1235step0Labels = raw1235Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1235 raw1235Labels permutation31 permutation6
    mixedMoment B raw1235step0 raw1235step0Labels = mixedMoment B raw1235step1 raw1235step1Labels := by
      have ha : raw1235step1 = raw1235step0 := by apply Matrix.ext; unfold raw1235step1 raw1235step0; decide +kernel
      have hl : raw1235step0Labels = labelEmbedding1 ∘ raw1235step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1235step0 raw1235step0Labels raw1235step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1002 node1002Labels := by rfl

def raw1236 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw1236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1236step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1236step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1236step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1236 raw1236Labels = mixedMoment B node4424 node4424Labels := by
  calc
    mixedMoment B raw1236 raw1236Labels = mixedMoment B raw1236step0 raw1236step0Labels := by
      have ha : raw1236step0 = (fun i j => raw1236 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1236step0 raw1236; decide +kernel
      have hl : raw1236step0Labels = raw1236Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1236 raw1236Labels permutation32 permutation4
    mixedMoment B raw1236step0 raw1236step0Labels = mixedMoment B raw1236step1 raw1236step1Labels := by
      have ha : raw1236step1 = raw1236step0 := by apply Matrix.ext; unfold raw1236step1 raw1236step0; decide +kernel
      have hl : raw1236step0Labels = labelEmbedding7 ∘ raw1236step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1236step0 raw1236step0Labels raw1236step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4424 node4424Labels := by rfl

def raw1237 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw1237Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1237step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1237 raw1237Labels = mixedMoment B node1005 node1005Labels := by
  calc
    mixedMoment B raw1237 raw1237Labels = mixedMoment B raw1237step0 raw1237step0Labels := by
      have ha : raw1237step0 = (fun i j => raw1237 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1237step0 raw1237; decide +kernel
      have hl : raw1237step0Labels = raw1237Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1237 raw1237Labels permutation32 permutation4
    _ = mixedMoment B node1005 node1005Labels := by rfl

def raw1238 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw1238Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw1238step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1238step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1238step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1238step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1238step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1238 raw1238Labels = mixedMoment B node1623 node1623Labels := by
  calc
    mixedMoment B raw1238 raw1238Labels = mixedMoment B raw1238step0 raw1238step0Labels := by
      have ha : raw1238step0 = (fun i j => raw1238 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1238step0 raw1238; decide +kernel
      have hl : raw1238step0Labels = raw1238Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1238 raw1238Labels permutation33 permutation6
    mixedMoment B raw1238step0 raw1238step0Labels = mixedMoment B raw1238step1 raw1238step1Labels := by
      have ha : raw1238step1 = -raw1238step0 := by apply Matrix.ext; change ∀ i j, raw1238step1 i j = -(raw1238step0 i j); unfold raw1238step1 raw1238step0; decide +kernel
      have hl : raw1238step1Labels = raw1238step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1238step1 raw1238step1Labels = mixedMoment B raw1238step2 raw1238step2Labels := by
      have ha : raw1238step2 = raw1238step1 := by apply Matrix.ext; unfold raw1238step2 raw1238step1; decide +kernel
      have hl : raw1238step1Labels = labelEmbedding1 ∘ raw1238step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1238step1 raw1238step1Labels raw1238step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1623 node1623Labels := by rfl

def raw1239 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 1, -2], ![-1, 3, -2]]
def raw1239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1239step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw1239step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1239step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw1239step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1239 raw1239Labels = mixedMoment B node4428 node4428Labels := by
  calc
    mixedMoment B raw1239 raw1239Labels = mixedMoment B raw1239step0 raw1239step0Labels := by
      have ha : raw1239step0 = (fun i j => raw1239 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1239step0 raw1239; decide +kernel
      have hl : raw1239step0Labels = raw1239Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1239 raw1239Labels permutation8 permutation4
    mixedMoment B raw1239step0 raw1239step0Labels = mixedMoment B raw1239step1 raw1239step1Labels := by
      have ha : raw1239step1 = raw1239step0 := by apply Matrix.ext; unfold raw1239step1 raw1239step0; decide +kernel
      have hl : raw1239step0Labels = labelEmbedding7 ∘ raw1239step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1239step0 raw1239step0Labels raw1239step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4428 node4428Labels := by rfl

def raw1240 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 1, -2], ![-1, 3, -2]]
def raw1240Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1240step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw1240step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1240 raw1240Labels = mixedMoment B node1009 node1009Labels := by
  calc
    mixedMoment B raw1240 raw1240Labels = mixedMoment B raw1240step0 raw1240step0Labels := by
      have ha : raw1240step0 = (fun i j => raw1240 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1240step0 raw1240; decide +kernel
      have hl : raw1240step0Labels = raw1240Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1240 raw1240Labels permutation8 permutation4
    _ = mixedMoment B node1009 node1009Labels := by rfl

def raw1241 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![1, 1, -2], ![-1, 3, -2]]
def raw1241Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1241step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw1241step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1241step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw1241step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1241step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw1241step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1241 raw1241Labels = mixedMoment B node1630 node1630Labels := by
  calc
    mixedMoment B raw1241 raw1241Labels = mixedMoment B raw1241step0 raw1241step0Labels := by
      have ha : raw1241step0 = (fun i j => raw1241 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1241step0 raw1241; decide +kernel
      have hl : raw1241step0Labels = raw1241Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1241 raw1241Labels permutation8 permutation6
    mixedMoment B raw1241step0 raw1241step0Labels = mixedMoment B raw1241step1 raw1241step1Labels := by
      have ha : raw1241step1 = -raw1241step0 := by apply Matrix.ext; change ∀ i j, raw1241step1 i j = -(raw1241step0 i j); unfold raw1241step1 raw1241step0; decide +kernel
      have hl : raw1241step1Labels = raw1241step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1241step1 raw1241step1Labels = mixedMoment B raw1241step2 raw1241step2Labels := by
      have ha : raw1241step2 = raw1241step1 := by apply Matrix.ext; unfold raw1241step2 raw1241step1; decide +kernel
      have hl : raw1241step1Labels = labelEmbedding1 ∘ raw1241step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1241step1 raw1241step1Labels raw1241step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1630 node1630Labels := by rfl

def raw1242 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 2, -3]]
def raw1242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1242step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw1242step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1242step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw1242step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1242 raw1242Labels = mixedMoment B node4431 node4431Labels := by
  calc
    mixedMoment B raw1242 raw1242Labels = mixedMoment B raw1242step0 raw1242step0Labels := by
      have ha : raw1242step0 = (fun i j => raw1242 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1242step0 raw1242; decide +kernel
      have hl : raw1242step0Labels = raw1242Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1242 raw1242Labels permutation8 permutation4
    mixedMoment B raw1242step0 raw1242step0Labels = mixedMoment B raw1242step1 raw1242step1Labels := by
      have ha : raw1242step1 = raw1242step0 := by apply Matrix.ext; unfold raw1242step1 raw1242step0; decide +kernel
      have hl : raw1242step0Labels = labelEmbedding7 ∘ raw1242step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1242step0 raw1242step0Labels raw1242step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4431 node4431Labels := by rfl

def raw1243 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 2, -3]]
def raw1243Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1243step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw1243step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1243 raw1243Labels = mixedMoment B node1012 node1012Labels := by
  calc
    mixedMoment B raw1243 raw1243Labels = mixedMoment B raw1243step0 raw1243step0Labels := by
      have ha : raw1243step0 = (fun i j => raw1243 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1243step0 raw1243; decide +kernel
      have hl : raw1243step0Labels = raw1243Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1243 raw1243Labels permutation8 permutation4
    _ = mixedMoment B node1012 node1012Labels := by rfl

def raw1244 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 2, -3]]
def raw1244Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1244step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw1244step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1244step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw1244step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1244step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw1244step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1244 raw1244Labels = mixedMoment B node1627 node1627Labels := by
  calc
    mixedMoment B raw1244 raw1244Labels = mixedMoment B raw1244step0 raw1244step0Labels := by
      have ha : raw1244step0 = (fun i j => raw1244 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1244step0 raw1244; decide +kernel
      have hl : raw1244step0Labels = raw1244Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1244 raw1244Labels permutation8 permutation6
    mixedMoment B raw1244step0 raw1244step0Labels = mixedMoment B raw1244step1 raw1244step1Labels := by
      have ha : raw1244step1 = -raw1244step0 := by apply Matrix.ext; change ∀ i j, raw1244step1 i j = -(raw1244step0 i j); unfold raw1244step1 raw1244step0; decide +kernel
      have hl : raw1244step1Labels = raw1244step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1244step1 raw1244step1Labels = mixedMoment B raw1244step2 raw1244step2Labels := by
      have ha : raw1244step2 = raw1244step1 := by apply Matrix.ext; unfold raw1244step2 raw1244step1; decide +kernel
      have hl : raw1244step1Labels = labelEmbedding1 ∘ raw1244step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1244step1 raw1244step1Labels raw1244step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1627 node1627Labels := by rfl

def raw1245 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw1245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1245step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1245step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1245step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1245step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1245 raw1245Labels = mixedMoment B node4451 node4451Labels := by
  calc
    mixedMoment B raw1245 raw1245Labels = mixedMoment B raw1245step0 raw1245step0Labels := by
      have ha : raw1245step0 = (fun i j => raw1245 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1245step0 raw1245; decide +kernel
      have hl : raw1245step0Labels = raw1245Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1245 raw1245Labels permutation152 permutation4
    mixedMoment B raw1245step0 raw1245step0Labels = mixedMoment B raw1245step1 raw1245step1Labels := by
      have ha : raw1245step1 = raw1245step0 := by apply Matrix.ext; unfold raw1245step1 raw1245step0; decide +kernel
      have hl : raw1245step0Labels = labelEmbedding7 ∘ raw1245step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1245step0 raw1245step0Labels raw1245step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4451 node4451Labels := by rfl

def raw1246 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw1246Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1246step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1246step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1246 raw1246Labels = mixedMoment B node1034 node1034Labels := by
  calc
    mixedMoment B raw1246 raw1246Labels = mixedMoment B raw1246step0 raw1246step0Labels := by
      have ha : raw1246step0 = (fun i j => raw1246 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1246step0 raw1246; decide +kernel
      have hl : raw1246step0Labels = raw1246Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1246 raw1246Labels permutation152 permutation4
    _ = mixedMoment B node1034 node1034Labels := by rfl

def raw1247 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw1247Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1247step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw1247step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1247step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1247step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1247step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1247step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1247 raw1247Labels = mixedMoment B node1644 node1644Labels := by
  calc
    mixedMoment B raw1247 raw1247Labels = mixedMoment B raw1247step0 raw1247step0Labels := by
      have ha : raw1247step0 = (fun i j => raw1247 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1247step0 raw1247; decide +kernel
      have hl : raw1247step0Labels = raw1247Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1247 raw1247Labels permutation176 permutation6
    mixedMoment B raw1247step0 raw1247step0Labels = mixedMoment B raw1247step1 raw1247step1Labels := by
      have ha : raw1247step1 = -raw1247step0 := by apply Matrix.ext; change ∀ i j, raw1247step1 i j = -(raw1247step0 i j); unfold raw1247step1 raw1247step0; decide +kernel
      have hl : raw1247step1Labels = raw1247step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1247step1 raw1247step1Labels = mixedMoment B raw1247step2 raw1247step2Labels := by
      have ha : raw1247step2 = raw1247step1 := by apply Matrix.ext; unfold raw1247step2 raw1247step1; decide +kernel
      have hl : raw1247step1Labels = labelEmbedding1 ∘ raw1247step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1247step1 raw1247step1Labels raw1247step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1644 node1644Labels := by rfl

def raw1248 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw1248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1248step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1248step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1248 raw1248Labels = mixedMoment B node4452 node4452Labels := by
  calc
    mixedMoment B raw1248 raw1248Labels = mixedMoment B raw1248step0 raw1248step0Labels := by
      have ha : raw1248step0 = (fun i j => raw1248 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1248step0 raw1248; decide +kernel
      have hl : raw1248step0Labels = raw1248Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1248 raw1248Labels permutation32 permutation4
    mixedMoment B raw1248step0 raw1248step0Labels = mixedMoment B raw1248step1 raw1248step1Labels := by
      have ha : raw1248step1 = raw1248step0 := by apply Matrix.ext; unfold raw1248step1 raw1248step0; decide +kernel
      have hl : raw1248step0Labels = labelEmbedding7 ∘ raw1248step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1248step0 raw1248step0Labels raw1248step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4452 node4452Labels := by rfl

def raw1249 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw1249Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1249step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1249 raw1249Labels = mixedMoment B node1035 node1035Labels := by
  calc
    mixedMoment B raw1249 raw1249Labels = mixedMoment B raw1249step0 raw1249step0Labels := by
      have ha : raw1249step0 = (fun i j => raw1249 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1249step0 raw1249; decide +kernel
      have hl : raw1249step0Labels = raw1249Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1249 raw1249Labels permutation32 permutation4
    _ = mixedMoment B node1035 node1035Labels := by rfl

def raw1250 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw1250Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw1250step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1250step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1250step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1250step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1250 raw1250Labels = mixedMoment B node1645 node1645Labels := by
  calc
    mixedMoment B raw1250 raw1250Labels = mixedMoment B raw1250step0 raw1250step0Labels := by
      have ha : raw1250step0 = (fun i j => raw1250 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1250step0 raw1250; decide +kernel
      have hl : raw1250step0Labels = raw1250Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1250 raw1250Labels permutation38 permutation6
    mixedMoment B raw1250step0 raw1250step0Labels = mixedMoment B raw1250step1 raw1250step1Labels := by
      have ha : raw1250step1 = -raw1250step0 := by apply Matrix.ext; change ∀ i j, raw1250step1 i j = -(raw1250step0 i j); unfold raw1250step1 raw1250step0; decide +kernel
      have hl : raw1250step1Labels = raw1250step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1250step1 raw1250step1Labels = mixedMoment B raw1250step2 raw1250step2Labels := by
      have ha : raw1250step2 = raw1250step1 := by apply Matrix.ext; unfold raw1250step2 raw1250step1; decide +kernel
      have hl : raw1250step1Labels = labelEmbedding1 ∘ raw1250step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1250step1 raw1250step1Labels raw1250step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1645 node1645Labels := by rfl

def raw1251 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 1, 1], ![0, 3, -3]]
def raw1251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1251step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1251step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1251step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1251step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1251 raw1251Labels = mixedMoment B node4454 node4454Labels := by
  calc
    mixedMoment B raw1251 raw1251Labels = mixedMoment B raw1251step0 raw1251step0Labels := by
      have ha : raw1251step0 = (fun i j => raw1251 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1251step0 raw1251; decide +kernel
      have hl : raw1251step0Labels = raw1251Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1251 raw1251Labels permutation8 permutation4
    mixedMoment B raw1251step0 raw1251step0Labels = mixedMoment B raw1251step1 raw1251step1Labels := by
      have ha : raw1251step1 = raw1251step0 := by apply Matrix.ext; unfold raw1251step1 raw1251step0; decide +kernel
      have hl : raw1251step0Labels = labelEmbedding7 ∘ raw1251step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1251step0 raw1251step0Labels raw1251step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4454 node4454Labels := by rfl

def raw1252 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 1, 1], ![0, 3, -3]]
def raw1252Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1252step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1252step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1252 raw1252Labels = mixedMoment B node1037 node1037Labels := by
  calc
    mixedMoment B raw1252 raw1252Labels = mixedMoment B raw1252step0 raw1252step0Labels := by
      have ha : raw1252step0 = (fun i j => raw1252 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1252step0 raw1252; decide +kernel
      have hl : raw1252step0Labels = raw1252Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1252 raw1252Labels permutation8 permutation4
    _ = mixedMoment B node1037 node1037Labels := by rfl

def raw1253 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 1, 1], ![0, 3, -3]]
def raw1253Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1253step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw1253step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1253step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1253step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1253step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1253step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1253 raw1253Labels = mixedMoment B node1647 node1647Labels := by
  calc
    mixedMoment B raw1253 raw1253Labels = mixedMoment B raw1253step0 raw1253step0Labels := by
      have ha : raw1253step0 = (fun i j => raw1253 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1253step0 raw1253; decide +kernel
      have hl : raw1253step0Labels = raw1253Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1253 raw1253Labels permutation10 permutation6
    mixedMoment B raw1253step0 raw1253step0Labels = mixedMoment B raw1253step1 raw1253step1Labels := by
      have ha : raw1253step1 = -raw1253step0 := by apply Matrix.ext; change ∀ i j, raw1253step1 i j = -(raw1253step0 i j); unfold raw1253step1 raw1253step0; decide +kernel
      have hl : raw1253step1Labels = raw1253step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1253step1 raw1253step1Labels = mixedMoment B raw1253step2 raw1253step2Labels := by
      have ha : raw1253step2 = raw1253step1 := by apply Matrix.ext; unfold raw1253step2 raw1253step1; decide +kernel
      have hl : raw1253step1Labels = labelEmbedding1 ∘ raw1253step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1253step1 raw1253step1Labels raw1253step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1647 node1647Labels := by rfl

def raw1254 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw1254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1254step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1254step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1254step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1254step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1254 raw1254Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw1254 raw1254Labels = mixedMoment B raw1254step0 raw1254step0Labels := by
      have ha : raw1254step0 = (fun i j => raw1254 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1254step0 raw1254; decide +kernel
      have hl : raw1254step0Labels = raw1254Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1254 raw1254Labels permutation152 permutation4
    mixedMoment B raw1254step0 raw1254step0Labels = mixedMoment B raw1254step1 raw1254step1Labels := by
      have ha : raw1254step1 = raw1254step0 := by apply Matrix.ext; unfold raw1254step1 raw1254step0; decide +kernel
      have hl : raw1254step0Labels = labelEmbedding7 ∘ raw1254step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1254step0 raw1254step0Labels raw1254step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4456 node4456Labels := by rfl

def raw1255 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw1255Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1255step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1255step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1255 raw1255Labels = mixedMoment B node1039 node1039Labels := by
  calc
    mixedMoment B raw1255 raw1255Labels = mixedMoment B raw1255step0 raw1255step0Labels := by
      have ha : raw1255step0 = (fun i j => raw1255 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1255step0 raw1255; decide +kernel
      have hl : raw1255step0Labels = raw1255Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1255 raw1255Labels permutation152 permutation4
    _ = mixedMoment B node1039 node1039Labels := by rfl

def raw1256 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw1256Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1256step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw1256step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1256step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1256step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1256step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1256step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1256 raw1256Labels = mixedMoment B node1706 node1706Labels := by
  calc
    mixedMoment B raw1256 raw1256Labels = mixedMoment B raw1256step0 raw1256step0Labels := by
      have ha : raw1256step0 = (fun i j => raw1256 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1256step0 raw1256; decide +kernel
      have hl : raw1256step0Labels = raw1256Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1256 raw1256Labels permutation182 permutation6
    mixedMoment B raw1256step0 raw1256step0Labels = mixedMoment B raw1256step1 raw1256step1Labels := by
      have ha : raw1256step1 = -raw1256step0 := by apply Matrix.ext; change ∀ i j, raw1256step1 i j = -(raw1256step0 i j); unfold raw1256step1 raw1256step0; decide +kernel
      have hl : raw1256step1Labels = raw1256step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1256step1 raw1256step1Labels = mixedMoment B raw1256step2 raw1256step2Labels := by
      have ha : raw1256step2 = raw1256step1 := by apply Matrix.ext; unfold raw1256step2 raw1256step1; decide +kernel
      have hl : raw1256step1Labels = labelEmbedding1 ∘ raw1256step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1256step1 raw1256step1Labels raw1256step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1706 node1706Labels := by rfl

def raw1257 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1257Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1257step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1257step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1257step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1257 raw1257Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw1257 raw1257Labels = mixedMoment B raw1257step0 raw1257step0Labels := by
      have ha : raw1257step0 = (fun i j => raw1257 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1257step0 raw1257; decide +kernel
      have hl : raw1257step0Labels = raw1257Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1257 raw1257Labels permutation32 permutation4
    mixedMoment B raw1257step0 raw1257step0Labels = mixedMoment B raw1257step1 raw1257step1Labels := by
      have ha : raw1257step1 = raw1257step0 := by apply Matrix.ext; unfold raw1257step1 raw1257step0; decide +kernel
      have hl : raw1257step0Labels = labelEmbedding7 ∘ raw1257step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1257step0 raw1257step0Labels raw1257step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4457 node4457Labels := by rfl

def raw1258 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1258Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1258step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1258 raw1258Labels = mixedMoment B node1040 node1040Labels := by
  calc
    mixedMoment B raw1258 raw1258Labels = mixedMoment B raw1258step0 raw1258step0Labels := by
      have ha : raw1258step0 = (fun i j => raw1258 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1258step0 raw1258; decide +kernel
      have hl : raw1258step0Labels = raw1258Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1258 raw1258Labels permutation32 permutation4
    _ = mixedMoment B node1040 node1040Labels := by rfl

def raw1259 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1259Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw1259step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1259step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw1259step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1259step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw1259step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1259 raw1259Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw1259 raw1259Labels = mixedMoment B raw1259step0 raw1259step0Labels := by
      have ha : raw1259step0 = (fun i j => raw1259 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1259step0 raw1259; decide +kernel
      have hl : raw1259step0Labels = raw1259Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1259 raw1259Labels permutation40 permutation6
    mixedMoment B raw1259step0 raw1259step0Labels = mixedMoment B raw1259step1 raw1259step1Labels := by
      have ha : raw1259step1 = -raw1259step0 := by apply Matrix.ext; change ∀ i j, raw1259step1 i j = -(raw1259step0 i j); unfold raw1259step1 raw1259step0; decide +kernel
      have hl : raw1259step1Labels = raw1259step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1259step1 raw1259step1Labels = mixedMoment B raw1259step2 raw1259step2Labels := by
      have ha : raw1259step2 = raw1259step1 := by apply Matrix.ext; unfold raw1259step2 raw1259step1; decide +kernel
      have hl : raw1259step1Labels = labelEmbedding1 ∘ raw1259step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1259step1 raw1259step1Labels raw1259step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1707 node1707Labels := by rfl

def raw1260 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw1260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1260step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1260step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1260step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1260 raw1260Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw1260 raw1260Labels = mixedMoment B raw1260step0 raw1260step0Labels := by
      have ha : raw1260step0 = (fun i j => raw1260 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1260step0 raw1260; decide +kernel
      have hl : raw1260step0Labels = raw1260Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1260 raw1260Labels permutation32 permutation4
    mixedMoment B raw1260step0 raw1260step0Labels = mixedMoment B raw1260step1 raw1260step1Labels := by
      have ha : raw1260step1 = raw1260step0 := by apply Matrix.ext; unfold raw1260step1 raw1260step0; decide +kernel
      have hl : raw1260step0Labels = labelEmbedding7 ∘ raw1260step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1260step0 raw1260step0Labels raw1260step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw1261 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw1261Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1261step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1261 raw1261Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw1261 raw1261Labels = mixedMoment B raw1261step0 raw1261step0Labels := by
      have ha : raw1261step0 = (fun i j => raw1261 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1261step0 raw1261; decide +kernel
      have hl : raw1261step0Labels = raw1261Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1261 raw1261Labels permutation32 permutation4
    _ = mixedMoment B node1041 node1041Labels := by rfl

def raw1262 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw1262Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw1262step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw1262step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1262step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw1262step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1262 raw1262Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw1262 raw1262Labels = mixedMoment B raw1262step0 raw1262step0Labels := by
      have ha : raw1262step0 = (fun i j => raw1262 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1262step0 raw1262; decide +kernel
      have hl : raw1262step0Labels = raw1262Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1262 raw1262Labels permutation38 permutation6
    mixedMoment B raw1262step0 raw1262step0Labels = mixedMoment B raw1262step1 raw1262step1Labels := by
      have ha : raw1262step1 = -raw1262step0 := by apply Matrix.ext; change ∀ i j, raw1262step1 i j = -(raw1262step0 i j); unfold raw1262step1 raw1262step0; decide +kernel
      have hl : raw1262step1Labels = raw1262step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1262step1 raw1262step1Labels = mixedMoment B raw1262step2 raw1262step2Labels := by
      have ha : raw1262step2 = raw1262step1 := by apply Matrix.ext; unfold raw1262step2 raw1262step1; decide +kernel
      have hl : raw1262step1Labels = labelEmbedding1 ∘ raw1262step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1262step1 raw1262step1Labels raw1262step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

def raw1263 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1263step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw1263step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1263step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw1263step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1263 raw1263Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw1263 raw1263Labels = mixedMoment B raw1263step0 raw1263step0Labels := by
      have ha : raw1263step0 = (fun i j => raw1263 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1263step0 raw1263; decide +kernel
      have hl : raw1263step0Labels = raw1263Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1263 raw1263Labels permutation8 permutation4
    mixedMoment B raw1263step0 raw1263step0Labels = mixedMoment B raw1263step1 raw1263step1Labels := by
      have ha : raw1263step1 = raw1263step0 := by apply Matrix.ext; unfold raw1263step1 raw1263step0; decide +kernel
      have hl : raw1263step0Labels = labelEmbedding7 ∘ raw1263step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1263step0 raw1263step0Labels raw1263step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4460 node4460Labels := by rfl

def raw1264 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1264Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1264step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw1264step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1264 raw1264Labels = mixedMoment B node1043 node1043Labels := by
  calc
    mixedMoment B raw1264 raw1264Labels = mixedMoment B raw1264step0 raw1264step0Labels := by
      have ha : raw1264step0 = (fun i j => raw1264 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1264step0 raw1264; decide +kernel
      have hl : raw1264step0Labels = raw1264Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1264 raw1264Labels permutation8 permutation4
    _ = mixedMoment B node1043 node1043Labels := by rfl

def raw1265 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1265Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1265step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw1265step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1265step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw1265step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1265step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw1265step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1265 raw1265Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw1265 raw1265Labels = mixedMoment B raw1265step0 raw1265step0Labels := by
      have ha : raw1265step0 = (fun i j => raw1265 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1265step0 raw1265; decide +kernel
      have hl : raw1265step0Labels = raw1265Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1265 raw1265Labels permutation10 permutation6
    mixedMoment B raw1265step0 raw1265step0Labels = mixedMoment B raw1265step1 raw1265step1Labels := by
      have ha : raw1265step1 = -raw1265step0 := by apply Matrix.ext; change ∀ i j, raw1265step1 i j = -(raw1265step0 i j); unfold raw1265step1 raw1265step0; decide +kernel
      have hl : raw1265step1Labels = raw1265step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1265step1 raw1265step1Labels = mixedMoment B raw1265step2 raw1265step2Labels := by
      have ha : raw1265step2 = raw1265step1 := by apply Matrix.ext; unfold raw1265step2 raw1265step1; decide +kernel
      have hl : raw1265step1Labels = labelEmbedding1 ∘ raw1265step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1265step1 raw1265step1Labels raw1265step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

def raw1266 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1266step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1266step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1266 raw1266Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw1266 raw1266Labels = mixedMoment B raw1266step0 raw1266step0Labels := by
      have ha : raw1266step0 = (fun i j => raw1266 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1266step0 raw1266; decide +kernel
      have hl : raw1266step0Labels = raw1266Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1266 raw1266Labels permutation32 permutation4
    mixedMoment B raw1266step0 raw1266step0Labels = mixedMoment B raw1266step1 raw1266step1Labels := by
      have ha : raw1266step1 = raw1266step0 := by apply Matrix.ext; unfold raw1266step1 raw1266step0; decide +kernel
      have hl : raw1266step0Labels = labelEmbedding7 ∘ raw1266step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1266step0 raw1266step0Labels raw1266step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4461 node4461Labels := by rfl

def raw1267 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1267Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1267step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1267 raw1267Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw1267 raw1267Labels = mixedMoment B raw1267step0 raw1267step0Labels := by
      have ha : raw1267step0 = (fun i j => raw1267 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1267step0 raw1267; decide +kernel
      have hl : raw1267step0Labels = raw1267Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1267 raw1267Labels permutation32 permutation4
    _ = mixedMoment B node1044 node1044Labels := by rfl

def raw1268 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1268Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw1268step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1268step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1268step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1268step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1268 raw1268Labels = mixedMoment B node1737 node1737Labels := by
  calc
    mixedMoment B raw1268 raw1268Labels = mixedMoment B raw1268step0 raw1268step0Labels := by
      have ha : raw1268step0 = (fun i j => raw1268 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1268step0 raw1268; decide +kernel
      have hl : raw1268step0Labels = raw1268Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1268 raw1268Labels permutation50 permutation6
    mixedMoment B raw1268step0 raw1268step0Labels = mixedMoment B raw1268step1 raw1268step1Labels := by
      have ha : raw1268step1 = -raw1268step0 := by apply Matrix.ext; change ∀ i j, raw1268step1 i j = -(raw1268step0 i j); unfold raw1268step1 raw1268step0; decide +kernel
      have hl : raw1268step1Labels = raw1268step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1268step1 raw1268step1Labels = mixedMoment B raw1268step2 raw1268step2Labels := by
      have ha : raw1268step2 = raw1268step1 := by apply Matrix.ext; unfold raw1268step2 raw1268step1; decide +kernel
      have hl : raw1268step1Labels = labelEmbedding1 ∘ raw1268step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1268step1 raw1268step1Labels raw1268step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1737 node1737Labels := by rfl

def raw1269 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1269step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1269step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1269step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1269step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1269 raw1269Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw1269 raw1269Labels = mixedMoment B raw1269step0 raw1269step0Labels := by
      have ha : raw1269step0 = (fun i j => raw1269 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1269step0 raw1269; decide +kernel
      have hl : raw1269step0Labels = raw1269Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1269 raw1269Labels permutation8 permutation4
    mixedMoment B raw1269step0 raw1269step0Labels = mixedMoment B raw1269step1 raw1269step1Labels := by
      have ha : raw1269step1 = raw1269step0 := by apply Matrix.ext; unfold raw1269step1 raw1269step0; decide +kernel
      have hl : raw1269step0Labels = labelEmbedding7 ∘ raw1269step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1269step0 raw1269step0Labels raw1269step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4463 node4463Labels := by rfl

def raw1270 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1270Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1270step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1270step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1270 raw1270Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw1270 raw1270Labels = mixedMoment B raw1270step0 raw1270step0Labels := by
      have ha : raw1270step0 = (fun i j => raw1270 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1270step0 raw1270; decide +kernel
      have hl : raw1270step0Labels = raw1270Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1270 raw1270Labels permutation8 permutation4
    _ = mixedMoment B node1046 node1046Labels := by rfl

def raw1271 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1271Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1271step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw1271step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1271step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw1271step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1271step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw1271step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1271 raw1271Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw1271 raw1271Labels = mixedMoment B raw1271step0 raw1271step0Labels := by
      have ha : raw1271step0 = (fun i j => raw1271 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1271step0 raw1271; decide +kernel
      have hl : raw1271step0Labels = raw1271Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1271 raw1271Labels permutation8 permutation6
    mixedMoment B raw1271step0 raw1271step0Labels = mixedMoment B raw1271step1 raw1271step1Labels := by
      have ha : raw1271step1 = -raw1271step0 := by apply Matrix.ext; change ∀ i j, raw1271step1 i j = -(raw1271step0 i j); unfold raw1271step1 raw1271step0; decide +kernel
      have hl : raw1271step1Labels = raw1271step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1271step1 raw1271step1Labels = mixedMoment B raw1271step2 raw1271step2Labels := by
      have ha : raw1271step2 = raw1271step1 := by apply Matrix.ext; unfold raw1271step2 raw1271step1; decide +kernel
      have hl : raw1271step1Labels = labelEmbedding1 ∘ raw1271step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1271step1 raw1271step1Labels raw1271step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1750 node1750Labels := by rfl

def raw1272 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1272step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1272step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1272step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1272step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1272 raw1272Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw1272 raw1272Labels = mixedMoment B raw1272step0 raw1272step0Labels := by
      have ha : raw1272step0 = (fun i j => raw1272 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1272step0 raw1272; decide +kernel
      have hl : raw1272step0Labels = raw1272Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1272 raw1272Labels permutation8 permutation4
    mixedMoment B raw1272step0 raw1272step0Labels = mixedMoment B raw1272step1 raw1272step1Labels := by
      have ha : raw1272step1 = raw1272step0 := by apply Matrix.ext; unfold raw1272step1 raw1272step0; decide +kernel
      have hl : raw1272step0Labels = labelEmbedding7 ∘ raw1272step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1272step0 raw1272step0Labels raw1272step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4466 node4466Labels := by rfl

def raw1273 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1273Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1273step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1273step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1273 raw1273Labels = mixedMoment B node1049 node1049Labels := by
  calc
    mixedMoment B raw1273 raw1273Labels = mixedMoment B raw1273step0 raw1273step0Labels := by
      have ha : raw1273step0 = (fun i j => raw1273 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1273step0 raw1273; decide +kernel
      have hl : raw1273step0Labels = raw1273Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1273 raw1273Labels permutation8 permutation4
    _ = mixedMoment B node1049 node1049Labels := by rfl

def raw1274 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1274Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1274step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw1274step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1274step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw1274step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1274step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw1274step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1274 raw1274Labels = mixedMoment B node1738 node1738Labels := by
  calc
    mixedMoment B raw1274 raw1274Labels = mixedMoment B raw1274step0 raw1274step0Labels := by
      have ha : raw1274step0 = (fun i j => raw1274 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1274step0 raw1274; decide +kernel
      have hl : raw1274step0Labels = raw1274Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1274 raw1274Labels permutation10 permutation6
    mixedMoment B raw1274step0 raw1274step0Labels = mixedMoment B raw1274step1 raw1274step1Labels := by
      have ha : raw1274step1 = -raw1274step0 := by apply Matrix.ext; change ∀ i j, raw1274step1 i j = -(raw1274step0 i j); unfold raw1274step1 raw1274step0; decide +kernel
      have hl : raw1274step1Labels = raw1274step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1274step1 raw1274step1Labels = mixedMoment B raw1274step2 raw1274step2Labels := by
      have ha : raw1274step2 = raw1274step1 := by apply Matrix.ext; unfold raw1274step2 raw1274step1; decide +kernel
      have hl : raw1274step1Labels = labelEmbedding1 ∘ raw1274step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1274step1 raw1274step1Labels raw1274step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1738 node1738Labels := by rfl

def raw1275 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1275step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1275step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1275step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1275step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1275 raw1275Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw1275 raw1275Labels = mixedMoment B raw1275step0 raw1275step0Labels := by
      have ha : raw1275step0 = (fun i j => raw1275 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1275step0 raw1275; decide +kernel
      have hl : raw1275step0Labels = raw1275Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1275 raw1275Labels permutation8 permutation4
    mixedMoment B raw1275step0 raw1275step0Labels = mixedMoment B raw1275step1 raw1275step1Labels := by
      have ha : raw1275step1 = raw1275step0 := by apply Matrix.ext; unfold raw1275step1 raw1275step0; decide +kernel
      have hl : raw1275step0Labels = labelEmbedding7 ∘ raw1275step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1275step0 raw1275step0Labels raw1275step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4467 node4467Labels := by rfl

def raw1276 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1276Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1276step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1276step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1276 raw1276Labels = mixedMoment B node1050 node1050Labels := by
  calc
    mixedMoment B raw1276 raw1276Labels = mixedMoment B raw1276step0 raw1276step0Labels := by
      have ha : raw1276step0 = (fun i j => raw1276 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1276step0 raw1276; decide +kernel
      have hl : raw1276step0Labels = raw1276Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1276 raw1276Labels permutation8 permutation4
    _ = mixedMoment B node1050 node1050Labels := by rfl

def raw1277 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1277Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1277step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw1277step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1277step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw1277step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1277step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw1277step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1277 raw1277Labels = mixedMoment B node1751 node1751Labels := by
  calc
    mixedMoment B raw1277 raw1277Labels = mixedMoment B raw1277step0 raw1277step0Labels := by
      have ha : raw1277step0 = (fun i j => raw1277 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1277step0 raw1277; decide +kernel
      have hl : raw1277step0Labels = raw1277Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1277 raw1277Labels permutation8 permutation6
    mixedMoment B raw1277step0 raw1277step0Labels = mixedMoment B raw1277step1 raw1277step1Labels := by
      have ha : raw1277step1 = -raw1277step0 := by apply Matrix.ext; change ∀ i j, raw1277step1 i j = -(raw1277step0 i j); unfold raw1277step1 raw1277step0; decide +kernel
      have hl : raw1277step1Labels = raw1277step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1277step1 raw1277step1Labels = mixedMoment B raw1277step2 raw1277step2Labels := by
      have ha : raw1277step2 = raw1277step1 := by apply Matrix.ext; unfold raw1277step2 raw1277step1; decide +kernel
      have hl : raw1277step1Labels = labelEmbedding1 ∘ raw1277step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1277step1 raw1277step1Labels raw1277step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1751 node1751Labels := by rfl

def raw1278 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 4, -2]]
def raw1278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1278step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw1278step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1278step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw1278step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1278 raw1278Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw1278 raw1278Labels = mixedMoment B raw1278step0 raw1278step0Labels := by
      have ha : raw1278step0 = (fun i j => raw1278 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1278step0 raw1278; decide +kernel
      have hl : raw1278step0Labels = raw1278Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1278 raw1278Labels permutation2 permutation4
    mixedMoment B raw1278step0 raw1278step0Labels = mixedMoment B raw1278step1 raw1278step1Labels := by
      have ha : raw1278step1 = raw1278step0 := by apply Matrix.ext; unfold raw1278step1 raw1278step0; decide +kernel
      have hl : raw1278step0Labels = labelEmbedding7 ∘ raw1278step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1278step0 raw1278step0Labels raw1278step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

def raw1279 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 4, -2]]
def raw1279Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1279step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw1279step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1279 raw1279Labels = mixedMoment B node1051 node1051Labels := by
  calc
    mixedMoment B raw1279 raw1279Labels = mixedMoment B raw1279step0 raw1279step0Labels := by
      have ha : raw1279step0 = (fun i j => raw1279 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1279step0 raw1279; decide +kernel
      have hl : raw1279step0Labels = raw1279Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1279 raw1279Labels permutation2 permutation4
    _ = mixedMoment B node1051 node1051Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
