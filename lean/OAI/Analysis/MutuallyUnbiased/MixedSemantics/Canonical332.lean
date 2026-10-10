import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw42496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42496Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42496step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw42496step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42496step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42496step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42496step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42496step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42496 raw42496Labels = mixedMoment B node2144 node2144Labels := by
  calc
    mixedMoment B raw42496 raw42496Labels = mixedMoment B raw42496step0 raw42496step0Labels := by
      have ha : raw42496step0 = (fun i j => raw42496 (permutation420 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42496step0 raw42496; decide +kernel
      have hl : raw42496step0Labels = raw42496Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42496 raw42496Labels permutation420 permutation4
    mixedMoment B raw42496step0 raw42496step0Labels = mixedMoment B raw42496step1 raw42496step1Labels := by
      have ha : raw42496step1 = -raw42496step0 := by apply Matrix.ext; change ∀ i j, raw42496step1 i j = -(raw42496step0 i j); unfold raw42496step1 raw42496step0; decide +kernel
      have hl : raw42496step1Labels = raw42496step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42496step1 raw42496step1Labels = mixedMoment B raw42496step2 raw42496step2Labels := by
      have ha : raw42496step2 = raw42496step1 := by apply Matrix.ext; unfold raw42496step2 raw42496step1; decide +kernel
      have hl : raw42496step1Labels = labelEmbedding1 ∘ raw42496step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42496step1 raw42496step1Labels raw42496step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2144 node2144Labels := by rfl

def raw42497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42497Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw42497step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42497 raw42497Labels = mixedMoment B node4665 node4665Labels := by
  calc
    mixedMoment B raw42497 raw42497Labels = mixedMoment B raw42497step0 raw42497step0Labels := by
      have ha : raw42497step0 = (fun i j => raw42497 (permutation430 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42497step0 raw42497; decide +kernel
      have hl : raw42497step0Labels = raw42497Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42497 raw42497Labels permutation430 permutation6
    _ = mixedMoment B node4665 node4665Labels := by rfl

def raw42498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42498Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw42498step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42498step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw42498step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42498step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw42498step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42498 raw42498Labels = mixedMoment B node2171 node2171Labels := by
  calc
    mixedMoment B raw42498 raw42498Labels = mixedMoment B raw42498step0 raw42498step0Labels := by
      have ha : raw42498step0 = (fun i j => raw42498 (permutation391 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42498step0 raw42498; decide +kernel
      have hl : raw42498step0Labels = raw42498Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42498 raw42498Labels permutation391 permutation4
    mixedMoment B raw42498step0 raw42498step0Labels = mixedMoment B raw42498step1 raw42498step1Labels := by
      have ha : raw42498step1 = -raw42498step0 := by apply Matrix.ext; change ∀ i j, raw42498step1 i j = -(raw42498step0 i j); unfold raw42498step1 raw42498step0; decide +kernel
      have hl : raw42498step1Labels = raw42498step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42498step1 raw42498step1Labels = mixedMoment B raw42498step2 raw42498step2Labels := by
      have ha : raw42498step2 = raw42498step1 := by apply Matrix.ext; unfold raw42498step2 raw42498step1; decide +kernel
      have hl : raw42498step1Labels = labelEmbedding1 ∘ raw42498step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42498step1 raw42498step1Labels raw42498step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2171 node2171Labels := by rfl

def raw42499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42499Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw42499step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42499 raw42499Labels = mixedMoment B node4762 node4762Labels := by
  calc
    mixedMoment B raw42499 raw42499Labels = mixedMoment B raw42499step0 raw42499step0Labels := by
      have ha : raw42499step0 = (fun i j => raw42499 (permutation391 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42499step0 raw42499; decide +kernel
      have hl : raw42499step0Labels = raw42499Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42499 raw42499Labels permutation391 permutation6
    _ = mixedMoment B node4762 node4762Labels := by rfl

def raw42500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42500Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw42500step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42500step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42500step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42500step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42500step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42500 raw42500Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw42500 raw42500Labels = mixedMoment B raw42500step0 raw42500step0Labels := by
      have ha : raw42500step0 = (fun i j => raw42500 (permutation385 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42500step0 raw42500; decide +kernel
      have hl : raw42500step0Labels = raw42500Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42500 raw42500Labels permutation385 permutation4
    mixedMoment B raw42500step0 raw42500step0Labels = mixedMoment B raw42500step1 raw42500step1Labels := by
      have ha : raw42500step1 = -raw42500step0 := by apply Matrix.ext; change ∀ i j, raw42500step1 i j = -(raw42500step0 i j); unfold raw42500step1 raw42500step0; decide +kernel
      have hl : raw42500step1Labels = raw42500step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42500step1 raw42500step1Labels = mixedMoment B raw42500step2 raw42500step2Labels := by
      have ha : raw42500step2 = raw42500step1 := by apply Matrix.ext; unfold raw42500step2 raw42500step1; decide +kernel
      have hl : raw42500step1Labels = labelEmbedding1 ∘ raw42500step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42500step1 raw42500step1Labels raw42500step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2195 node2195Labels := by rfl

def raw42501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42501Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42501step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42501 raw42501Labels = mixedMoment B node4803 node4803Labels := by
  calc
    mixedMoment B raw42501 raw42501Labels = mixedMoment B raw42501step0 raw42501step0Labels := by
      have ha : raw42501step0 = (fun i j => raw42501 (permutation392 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42501step0 raw42501; decide +kernel
      have hl : raw42501step0Labels = raw42501Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42501 raw42501Labels permutation392 permutation6
    _ = mixedMoment B node4803 node4803Labels := by rfl

def raw42502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42502Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw42502step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42502step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42502step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42502step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42502step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42502 raw42502Labels = mixedMoment B node2252 node2252Labels := by
  calc
    mixedMoment B raw42502 raw42502Labels = mixedMoment B raw42502step0 raw42502step0Labels := by
      have ha : raw42502step0 = (fun i j => raw42502 (permutation367 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42502step0 raw42502; decide +kernel
      have hl : raw42502step0Labels = raw42502Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42502 raw42502Labels permutation367 permutation4
    mixedMoment B raw42502step0 raw42502step0Labels = mixedMoment B raw42502step1 raw42502step1Labels := by
      have ha : raw42502step1 = -raw42502step0 := by apply Matrix.ext; change ∀ i j, raw42502step1 i j = -(raw42502step0 i j); unfold raw42502step1 raw42502step0; decide +kernel
      have hl : raw42502step1Labels = raw42502step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42502step1 raw42502step1Labels = mixedMoment B raw42502step2 raw42502step2Labels := by
      have ha : raw42502step2 = raw42502step1 := by apply Matrix.ext; unfold raw42502step2 raw42502step1; decide +kernel
      have hl : raw42502step1Labels = labelEmbedding1 ∘ raw42502step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42502step1 raw42502step1Labels raw42502step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2252 node2252Labels := by rfl

def raw42503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42503Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42503step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42503step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42503 raw42503Labels = mixedMoment B node4885 node4885Labels := by
  calc
    mixedMoment B raw42503 raw42503Labels = mixedMoment B raw42503step0 raw42503step0Labels := by
      have ha : raw42503step0 = (fun i j => raw42503 (permutation394 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42503step0 raw42503; decide +kernel
      have hl : raw42503step0Labels = raw42503Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42503 raw42503Labels permutation394 permutation6
    _ = mixedMoment B node4885 node4885Labels := by rfl

def raw42504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42504Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw42504step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42504step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw42504step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42504step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw42504step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42504step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw42504step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42504 raw42504Labels = mixedMoment B node3222 node3222Labels := by
  calc
    mixedMoment B raw42504 raw42504Labels = mixedMoment B raw42504step0 raw42504step0Labels := by
      have hz : ∀ j, raw42504 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42504step0 = (fun i j => raw42504 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42504step0 raw42504; decide +kernel
      have hl : raw42504step0Labels = raw42504Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42504 raw42504Labels permutation520 hz
    mixedMoment B raw42504step0 raw42504step0Labels = mixedMoment B raw42504step1 raw42504step1Labels := by
      have ha : raw42504step1 = (fun i j => raw42504step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42504step1 raw42504step0; decide +kernel
      have hl : raw42504step1Labels = raw42504step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42504step0 raw42504step0Labels permutation145 permutation2
    mixedMoment B raw42504step1 raw42504step1Labels = mixedMoment B raw42504step2 raw42504step2Labels := by
      have ha : raw42504step2 = -raw42504step1 := by apply Matrix.ext; change ∀ i j, raw42504step2 i j = -(raw42504step1 i j); unfold raw42504step2 raw42504step1; decide +kernel
      have hl : raw42504step2Labels = raw42504step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42504step2 raw42504step2Labels = mixedMoment B raw42504step3 raw42504step3Labels := by
      have ha : raw42504step3 = raw42504step2 := by apply Matrix.ext; unfold raw42504step3 raw42504step2; decide +kernel
      have hl : raw42504step2Labels = labelEmbedding1 ∘ raw42504step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42504step2 raw42504step2Labels raw42504step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3222 node3222Labels := by rfl

def raw42505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42505Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw42505step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42505step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw42505step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42505step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42505step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42505step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42505step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42505 raw42505Labels = mixedMoment B node4891 node4891Labels := by
  calc
    mixedMoment B raw42505 raw42505Labels = mixedMoment B raw42505step0 raw42505step0Labels := by
      have hz : ∀ j, raw42505 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42505step0 = (fun i j => raw42505 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42505step0 raw42505; decide +kernel
      have hl : raw42505step0Labels = raw42505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42505 raw42505Labels permutation520 hz
    mixedMoment B raw42505step0 raw42505step0Labels = mixedMoment B raw42505step1 raw42505step1Labels := by
      have ha : raw42505step1 = (fun i j => raw42505step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42505step1 raw42505step0; decide +kernel
      have hl : raw42505step1Labels = raw42505step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42505step0 raw42505step0Labels permutation151 permutation3
    mixedMoment B raw42505step1 raw42505step1Labels = mixedMoment B raw42505step2 raw42505step2Labels := by
      have ha : raw42505step2 = -raw42505step1 := by apply Matrix.ext; change ∀ i j, raw42505step2 i j = -(raw42505step1 i j); unfold raw42505step2 raw42505step1; decide +kernel
      have hl : raw42505step2Labels = raw42505step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42505step2 raw42505step2Labels = mixedMoment B raw42505step3 raw42505step3Labels := by
      have ha : raw42505step3 = raw42505step2 := by apply Matrix.ext; unfold raw42505step3 raw42505step2; decide +kernel
      have hl : raw42505step2Labels = labelEmbedding7 ∘ raw42505step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42505step2 raw42505step2Labels raw42505step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4891 node4891Labels := by rfl

def raw42506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42506Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw42506step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42506step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw42506step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42506 raw42506Labels = mixedMoment B node3016 node3016Labels := by
  calc
    mixedMoment B raw42506 raw42506Labels = mixedMoment B raw42506step0 raw42506step0Labels := by
      have ha : raw42506step0 = (fun i j => raw42506 (permutation594 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42506step0 raw42506; decide +kernel
      have hl : raw42506step0Labels = raw42506Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42506 raw42506Labels permutation594 permutation4
    mixedMoment B raw42506step0 raw42506step0Labels = mixedMoment B raw42506step1 raw42506step1Labels := by
      have ha : raw42506step1 = raw42506step0 := by apply Matrix.ext; unfold raw42506step1 raw42506step0; decide +kernel
      have hl : raw42506step0Labels = labelEmbedding1 ∘ raw42506step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42506step0 raw42506step0Labels raw42506step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3016 node3016Labels := by rfl

def raw42507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42507Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42507step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42507step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42507step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42507 raw42507Labels = mixedMoment B node5254 node5254Labels := by
  calc
    mixedMoment B raw42507 raw42507Labels = mixedMoment B raw42507step0 raw42507step0Labels := by
      have ha : raw42507step0 = (fun i j => raw42507 (permutation672 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42507step0 raw42507; decide +kernel
      have hl : raw42507step0Labels = raw42507Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42507 raw42507Labels permutation672 permutation5
    mixedMoment B raw42507step0 raw42507step0Labels = mixedMoment B raw42507step1 raw42507step1Labels := by
      have ha : raw42507step1 = raw42507step0 := by apply Matrix.ext; unfold raw42507step1 raw42507step0; decide +kernel
      have hl : raw42507step0Labels = labelEmbedding9 ∘ raw42507step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42507step0 raw42507step0Labels raw42507step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5254 node5254Labels := by rfl

def raw42508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42508Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42508step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42508step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42508 raw42508Labels = mixedMoment B node3803 node3803Labels := by
  calc
    mixedMoment B raw42508 raw42508Labels = mixedMoment B raw42508step0 raw42508step0Labels := by
      have ha : raw42508step0 = (fun i j => raw42508 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42508step0 raw42508; decide +kernel
      have hl : raw42508step0Labels = raw42508Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42508 raw42508Labels permutation158 permutation2
    mixedMoment B raw42508step0 raw42508step0Labels = mixedMoment B raw42508step1 raw42508step1Labels := by
      have ha : raw42508step1 = raw42508step0 := by apply Matrix.ext; unfold raw42508step1 raw42508step0; decide +kernel
      have hl : raw42508step0Labels = labelEmbedding1 ∘ raw42508step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42508step0 raw42508step0Labels raw42508step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3803 node3803Labels := by rfl

def raw42509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42509Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42509step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42509step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42509step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42509 raw42509Labels = mixedMoment B node5407 node5407Labels := by
  calc
    mixedMoment B raw42509 raw42509Labels = mixedMoment B raw42509step0 raw42509step0Labels := by
      have ha : raw42509step0 = (fun i j => raw42509 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42509step0 raw42509; decide +kernel
      have hl : raw42509step0Labels = raw42509Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42509 raw42509Labels permutation158 permutation2
    mixedMoment B raw42509step0 raw42509step0Labels = mixedMoment B raw42509step1 raw42509step1Labels := by
      have ha : raw42509step1 = raw42509step0 := by apply Matrix.ext; unfold raw42509step1 raw42509step0; decide +kernel
      have hl : raw42509step0Labels = labelEmbedding8 ∘ raw42509step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42509step0 raw42509step0Labels raw42509step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5407 node5407Labels := by rfl

def raw42510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42510Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42510step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42510step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42510step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42510step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42510 raw42510Labels = mixedMoment B node3802 node3802Labels := by
  calc
    mixedMoment B raw42510 raw42510Labels = mixedMoment B raw42510step0 raw42510step0Labels := by
      have ha : raw42510step0 = (fun i j => raw42510 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42510step0 raw42510; decide +kernel
      have hl : raw42510step0Labels = raw42510Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42510 raw42510Labels permutation158 permutation2
    mixedMoment B raw42510step0 raw42510step0Labels = mixedMoment B raw42510step1 raw42510step1Labels := by
      have ha : raw42510step1 = raw42510step0 := by apply Matrix.ext; unfold raw42510step1 raw42510step0; decide +kernel
      have hl : raw42510step0Labels = labelEmbedding1 ∘ raw42510step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42510step0 raw42510step0Labels raw42510step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3802 node3802Labels := by rfl

def raw42511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42511Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42511step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42511step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42511 raw42511Labels = mixedMoment B node5402 node5402Labels := by
  calc
    mixedMoment B raw42511 raw42511Labels = mixedMoment B raw42511step0 raw42511step0Labels := by
      have ha : raw42511step0 = (fun i j => raw42511 (permutation397 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42511step0 raw42511; decide +kernel
      have hl : raw42511step0Labels = raw42511Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42511 raw42511Labels permutation397 permutation6
    _ = mixedMoment B node5402 node5402Labels := by rfl

def raw42512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw42512Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw42512step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42512step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw42512step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42512 raw42512Labels = mixedMoment B node2654 node2654Labels := by
  calc
    mixedMoment B raw42512 raw42512Labels = mixedMoment B raw42512step0 raw42512step0Labels := by
      have ha : raw42512step0 = (fun i j => raw42512 (permutation525 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42512step0 raw42512; decide +kernel
      have hl : raw42512step0Labels = raw42512Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42512 raw42512Labels permutation525 permutation4
    mixedMoment B raw42512step0 raw42512step0Labels = mixedMoment B raw42512step1 raw42512step1Labels := by
      have ha : raw42512step1 = raw42512step0 := by apply Matrix.ext; unfold raw42512step1 raw42512step0; decide +kernel
      have hl : raw42512step0Labels = labelEmbedding1 ∘ raw42512step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42512step0 raw42512step0Labels raw42512step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2654 node2654Labels := by rfl

def raw42513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw42513Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw42513step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42513step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw42513step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42513 raw42513Labels = mixedMoment B node5216 node5216Labels := by
  calc
    mixedMoment B raw42513 raw42513Labels = mixedMoment B raw42513step0 raw42513step0Labels := by
      have ha : raw42513step0 = (fun i j => raw42513 (permutation525 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42513step0 raw42513; decide +kernel
      have hl : raw42513step0Labels = raw42513Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42513 raw42513Labels permutation525 permutation4
    mixedMoment B raw42513step0 raw42513step0Labels = mixedMoment B raw42513step1 raw42513step1Labels := by
      have ha : raw42513step1 = raw42513step0 := by apply Matrix.ext; unfold raw42513step1 raw42513step0; decide +kernel
      have hl : raw42513step0Labels = labelEmbedding10 ∘ raw42513step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42513step0 raw42513step0Labels raw42513step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5216 node5216Labels := by rfl

def raw42514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42514Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw42514step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42514step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw42514step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42514step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw42514step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42514 raw42514Labels = mixedMoment B node3025 node3025Labels := by
  calc
    mixedMoment B raw42514 raw42514Labels = mixedMoment B raw42514step0 raw42514step0Labels := by
      have hz : ∀ j, raw42514 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42514step0 = (fun i j => raw42514 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42514step0 raw42514; decide +kernel
      have hl : raw42514step0Labels = raw42514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42514 raw42514Labels permutation434 hz
    mixedMoment B raw42514step0 raw42514step0Labels = mixedMoment B raw42514step1 raw42514step1Labels := by
      have ha : raw42514step1 = (fun i j => raw42514step0 (permutation129 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42514step1 raw42514step0; decide +kernel
      have hl : raw42514step1Labels = raw42514step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42514step0 raw42514step0Labels permutation129 permutation4
    mixedMoment B raw42514step1 raw42514step1Labels = mixedMoment B raw42514step2 raw42514step2Labels := by
      have ha : raw42514step2 = raw42514step1 := by apply Matrix.ext; unfold raw42514step2 raw42514step1; decide +kernel
      have hl : raw42514step1Labels = labelEmbedding1 ∘ raw42514step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42514step1 raw42514step1Labels raw42514step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3025 node3025Labels := by rfl

def raw42515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42515Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw42515step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42515step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw42515step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42515step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw42515step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42515 raw42515Labels = mixedMoment B node5287 node5287Labels := by
  calc
    mixedMoment B raw42515 raw42515Labels = mixedMoment B raw42515step0 raw42515step0Labels := by
      have hz : ∀ j, raw42515 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42515step0 = (fun i j => raw42515 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42515step0 raw42515; decide +kernel
      have hl : raw42515step0Labels = raw42515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42515 raw42515Labels permutation434 hz
    mixedMoment B raw42515step0 raw42515step0Labels = mixedMoment B raw42515step1 raw42515step1Labels := by
      have ha : raw42515step1 = (fun i j => raw42515step0 (permutation135 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42515step1 raw42515step0; decide +kernel
      have hl : raw42515step1Labels = raw42515step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42515step0 raw42515step0Labels permutation135 permutation5
    mixedMoment B raw42515step1 raw42515step1Labels = mixedMoment B raw42515step2 raw42515step2Labels := by
      have ha : raw42515step2 = raw42515step1 := by apply Matrix.ext; unfold raw42515step2 raw42515step1; decide +kernel
      have hl : raw42515step1Labels = labelEmbedding9 ∘ raw42515step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42515step1 raw42515step1Labels raw42515step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5287 node5287Labels := by rfl

def raw42516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42516Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw42516step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42516step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw42516step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42516step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw42516step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42516 raw42516Labels = mixedMoment B node2659 node2659Labels := by
  calc
    mixedMoment B raw42516 raw42516Labels = mixedMoment B raw42516step0 raw42516step0Labels := by
      have hz : ∀ j, raw42516 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42516step0 = (fun i j => raw42516 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42516step0 raw42516; decide +kernel
      have hl : raw42516step0Labels = raw42516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42516 raw42516Labels permutation434 hz
    mixedMoment B raw42516step0 raw42516step0Labels = mixedMoment B raw42516step1 raw42516step1Labels := by
      have ha : raw42516step1 = (fun i j => raw42516step0 (permutation105 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42516step1 raw42516step0; decide +kernel
      have hl : raw42516step1Labels = raw42516step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42516step0 raw42516step0Labels permutation105 permutation4
    mixedMoment B raw42516step1 raw42516step1Labels = mixedMoment B raw42516step2 raw42516step2Labels := by
      have ha : raw42516step2 = raw42516step1 := by apply Matrix.ext; unfold raw42516step2 raw42516step1; decide +kernel
      have hl : raw42516step1Labels = labelEmbedding1 ∘ raw42516step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42516step1 raw42516step1Labels raw42516step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2659 node2659Labels := by rfl

def raw42517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42517Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw42517step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw42517step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42517step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw42517step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42517 raw42517Labels = mixedMoment B node4976 node4976Labels := by
  calc
    mixedMoment B raw42517 raw42517Labels = mixedMoment B raw42517step0 raw42517step0Labels := by
      have hz : ∀ j, raw42517 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42517step0 = (fun i j => raw42517 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42517step0 raw42517; decide +kernel
      have hl : raw42517step0Labels = raw42517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42517 raw42517Labels permutation434 hz
    mixedMoment B raw42517step0 raw42517step0Labels = mixedMoment B raw42517step1 raw42517step1Labels := by
      have ha : raw42517step1 = (fun i j => raw42517step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42517step1 raw42517step0; decide +kernel
      have hl : raw42517step1Labels = raw42517step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42517step0 raw42517step0Labels permutation143 permutation7
    mixedMoment B raw42517step1 raw42517step1Labels = mixedMoment B raw42517step2 raw42517step2Labels := by
      have ha : raw42517step2 = raw42517step1 := by apply Matrix.ext; unfold raw42517step2 raw42517step1; decide +kernel
      have hl : raw42517step1Labels = labelEmbedding6 ∘ raw42517step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42517step1 raw42517step1Labels raw42517step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4976 node4976Labels := by rfl

def raw42518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42518Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw42518step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42518step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42518step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42518step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42518step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42518 raw42518Labels = mixedMoment B node3762 node3762Labels := by
  calc
    mixedMoment B raw42518 raw42518Labels = mixedMoment B raw42518step0 raw42518step0Labels := by
      have ha : raw42518step0 = (fun i j => raw42518 (permutation403 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42518step0 raw42518; decide +kernel
      have hl : raw42518step0Labels = raw42518Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42518 raw42518Labels permutation403 permutation4
    mixedMoment B raw42518step0 raw42518step0Labels = mixedMoment B raw42518step1 raw42518step1Labels := by
      have ha : raw42518step1 = -raw42518step0 := by apply Matrix.ext; change ∀ i j, raw42518step1 i j = -(raw42518step0 i j); unfold raw42518step1 raw42518step0; decide +kernel
      have hl : raw42518step1Labels = raw42518step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42518step1 raw42518step1Labels = mixedMoment B raw42518step2 raw42518step2Labels := by
      have ha : raw42518step2 = raw42518step1 := by apply Matrix.ext; unfold raw42518step2 raw42518step1; decide +kernel
      have hl : raw42518step1Labels = labelEmbedding1 ∘ raw42518step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42518step1 raw42518step1Labels raw42518step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3762 node3762Labels := by rfl

def raw42519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42519Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42519step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42519 raw42519Labels = mixedMoment B node5360 node5360Labels := by
  calc
    mixedMoment B raw42519 raw42519Labels = mixedMoment B raw42519step0 raw42519step0Labels := by
      have ha : raw42519step0 = (fun i j => raw42519 (permutation412 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42519step0 raw42519; decide +kernel
      have hl : raw42519step0Labels = raw42519Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42519 raw42519Labels permutation412 permutation6
    _ = mixedMoment B node5360 node5360Labels := by rfl

def raw42520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42520Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw42520step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42520step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw42520step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42520step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw42520step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42520 raw42520Labels = mixedMoment B node3553 node3553Labels := by
  calc
    mixedMoment B raw42520 raw42520Labels = mixedMoment B raw42520step0 raw42520step0Labels := by
      have ha : raw42520step0 = (fun i j => raw42520 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42520step0 raw42520; decide +kernel
      have hl : raw42520step0Labels = raw42520Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42520 raw42520Labels permutation682 permutation2
    mixedMoment B raw42520step0 raw42520step0Labels = mixedMoment B raw42520step1 raw42520step1Labels := by
      have ha : raw42520step1 = -raw42520step0 := by apply Matrix.ext; change ∀ i j, raw42520step1 i j = -(raw42520step0 i j); unfold raw42520step1 raw42520step0; decide +kernel
      have hl : raw42520step1Labels = raw42520step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42520step1 raw42520step1Labels = mixedMoment B raw42520step2 raw42520step2Labels := by
      have ha : raw42520step2 = raw42520step1 := by apply Matrix.ext; unfold raw42520step2 raw42520step1; decide +kernel
      have hl : raw42520step1Labels = labelEmbedding1 ∘ raw42520step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42520step1 raw42520step1Labels raw42520step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3553 node3553Labels := by rfl

def raw42521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42521Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42521step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw42521step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42521step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw42521step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42521 raw42521Labels = mixedMoment B node4963 node4963Labels := by
  calc
    mixedMoment B raw42521 raw42521Labels = mixedMoment B raw42521step0 raw42521step0Labels := by
      have ha : raw42521step0 = (fun i j => raw42521 (permutation646 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42521step0 raw42521; decide +kernel
      have hl : raw42521step0Labels = raw42521Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42521 raw42521Labels permutation646 permutation7
    mixedMoment B raw42521step0 raw42521step0Labels = mixedMoment B raw42521step1 raw42521step1Labels := by
      have ha : raw42521step1 = raw42521step0 := by apply Matrix.ext; unfold raw42521step1 raw42521step0; decide +kernel
      have hl : raw42521step0Labels = labelEmbedding6 ∘ raw42521step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42521step0 raw42521step0Labels raw42521step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4963 node4963Labels := by rfl

def raw42522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42522Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw42522step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42522step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw42522step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42522step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw42522step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42522 raw42522Labels = mixedMoment B node3509 node3509Labels := by
  calc
    mixedMoment B raw42522 raw42522Labels = mixedMoment B raw42522step0 raw42522step0Labels := by
      have ha : raw42522step0 = (fun i j => raw42522 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42522step0 raw42522; decide +kernel
      have hl : raw42522step0Labels = raw42522Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42522 raw42522Labels permutation682 permutation2
    mixedMoment B raw42522step0 raw42522step0Labels = mixedMoment B raw42522step1 raw42522step1Labels := by
      have ha : raw42522step1 = -raw42522step0 := by apply Matrix.ext; change ∀ i j, raw42522step1 i j = -(raw42522step0 i j); unfold raw42522step1 raw42522step0; decide +kernel
      have hl : raw42522step1Labels = raw42522step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42522step1 raw42522step1Labels = mixedMoment B raw42522step2 raw42522step2Labels := by
      have ha : raw42522step2 = raw42522step1 := by apply Matrix.ext; unfold raw42522step2 raw42522step1; decide +kernel
      have hl : raw42522step1Labels = labelEmbedding1 ∘ raw42522step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42522step1 raw42522step1Labels raw42522step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3509 node3509Labels := by rfl

def raw42523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42523Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw42523step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42523step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw42523step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42523 raw42523Labels = mixedMoment B node4957 node4957Labels := by
  calc
    mixedMoment B raw42523 raw42523Labels = mixedMoment B raw42523step0 raw42523step0Labels := by
      have ha : raw42523step0 = (fun i j => raw42523 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42523step0 raw42523; decide +kernel
      have hl : raw42523step0Labels = raw42523Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42523 raw42523Labels permutation644 permutation7
    mixedMoment B raw42523step0 raw42523step0Labels = mixedMoment B raw42523step1 raw42523step1Labels := by
      have ha : raw42523step1 = raw42523step0 := by apply Matrix.ext; unfold raw42523step1 raw42523step0; decide +kernel
      have hl : raw42523step0Labels = labelEmbedding6 ∘ raw42523step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42523step0 raw42523step0Labels raw42523step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4957 node4957Labels := by rfl

def raw42524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw42524Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw42524step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42524step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw42524step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42524 raw42524Labels = mixedMoment B node2653 node2653Labels := by
  calc
    mixedMoment B raw42524 raw42524Labels = mixedMoment B raw42524step0 raw42524step0Labels := by
      have ha : raw42524step0 = (fun i j => raw42524 (permutation594 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42524step0 raw42524; decide +kernel
      have hl : raw42524step0Labels = raw42524Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42524 raw42524Labels permutation594 permutation4
    mixedMoment B raw42524step0 raw42524step0Labels = mixedMoment B raw42524step1 raw42524step1Labels := by
      have ha : raw42524step1 = raw42524step0 := by apply Matrix.ext; unfold raw42524step1 raw42524step0; decide +kernel
      have hl : raw42524step0Labels = labelEmbedding1 ∘ raw42524step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42524step0 raw42524step0Labels raw42524step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2653 node2653Labels := by rfl

def raw42525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw42525Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42525step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw42525step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42525step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw42525step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42525 raw42525Labels = mixedMoment B node5215 node5215Labels := by
  calc
    mixedMoment B raw42525 raw42525Labels = mixedMoment B raw42525step0 raw42525step0Labels := by
      have ha : raw42525step0 = (fun i j => raw42525 (permutation594 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42525step0 raw42525; decide +kernel
      have hl : raw42525step0Labels = raw42525Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42525 raw42525Labels permutation594 permutation4
    mixedMoment B raw42525step0 raw42525step0Labels = mixedMoment B raw42525step1 raw42525step1Labels := by
      have ha : raw42525step1 = raw42525step0 := by apply Matrix.ext; unfold raw42525step1 raw42525step0; decide +kernel
      have hl : raw42525step0Labels = labelEmbedding10 ∘ raw42525step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42525step0 raw42525step0Labels raw42525step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5215 node5215Labels := by rfl

def raw42526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42526Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42526step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw42526step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42526step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42526step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42526step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42526step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42526 raw42526Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw42526 raw42526Labels = mixedMoment B raw42526step0 raw42526step0Labels := by
      have ha : raw42526step0 = (fun i j => raw42526 (permutation385 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42526step0 raw42526; decide +kernel
      have hl : raw42526step0Labels = raw42526Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42526 raw42526Labels permutation385 permutation4
    mixedMoment B raw42526step0 raw42526step0Labels = mixedMoment B raw42526step1 raw42526step1Labels := by
      have ha : raw42526step1 = -raw42526step0 := by apply Matrix.ext; change ∀ i j, raw42526step1 i j = -(raw42526step0 i j); unfold raw42526step1 raw42526step0; decide +kernel
      have hl : raw42526step1Labels = raw42526step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42526step1 raw42526step1Labels = mixedMoment B raw42526step2 raw42526step2Labels := by
      have ha : raw42526step2 = raw42526step1 := by apply Matrix.ext; unfold raw42526step2 raw42526step1; decide +kernel
      have hl : raw42526step1Labels = labelEmbedding1 ∘ raw42526step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42526step1 raw42526step1Labels raw42526step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3761 node3761Labels := by rfl

def raw42527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42527Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42527step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42527step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42527 raw42527Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw42527 raw42527Labels = mixedMoment B raw42527step0 raw42527step0Labels := by
      have ha : raw42527step0 = (fun i j => raw42527 (permutation392 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42527step0 raw42527; decide +kernel
      have hl : raw42527step0Labels = raw42527Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42527 raw42527Labels permutation392 permutation6
    _ = mixedMoment B node5353 node5353Labels := by rfl

def raw42528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw42528Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42528step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw42528step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42528step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw42528step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42528 raw42528Labels = mixedMoment B node3221 node3221Labels := by
  calc
    mixedMoment B raw42528 raw42528Labels = mixedMoment B raw42528step0 raw42528step0Labels := by
      have ha : raw42528step0 = (fun i j => raw42528 (permutation590 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42528step0 raw42528; decide +kernel
      have hl : raw42528step0Labels = raw42528Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42528 raw42528Labels permutation590 permutation4
    mixedMoment B raw42528step0 raw42528step0Labels = mixedMoment B raw42528step1 raw42528step1Labels := by
      have ha : raw42528step1 = raw42528step0 := by apply Matrix.ext; unfold raw42528step1 raw42528step0; decide +kernel
      have hl : raw42528step0Labels = labelEmbedding1 ∘ raw42528step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42528step0 raw42528step0Labels raw42528step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3221 node3221Labels := by rfl

def raw42529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw42529Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42529step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw42529step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42529step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42529step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42529step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42529step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42529 raw42529Labels = mixedMoment B node4885 node4885Labels := by
  calc
    mixedMoment B raw42529 raw42529Labels = mixedMoment B raw42529step0 raw42529step0Labels := by
      have ha : raw42529step0 = (fun i j => raw42529 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42529step0 raw42529; decide +kernel
      have hl : raw42529step0Labels = raw42529Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42529 raw42529Labels permutation640 permutation3
    mixedMoment B raw42529step0 raw42529step0Labels = mixedMoment B raw42529step1 raw42529step1Labels := by
      have ha : raw42529step1 = -raw42529step0 := by apply Matrix.ext; change ∀ i j, raw42529step1 i j = -(raw42529step0 i j); unfold raw42529step1 raw42529step0; decide +kernel
      have hl : raw42529step1Labels = raw42529step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42529step1 raw42529step1Labels = mixedMoment B raw42529step2 raw42529step2Labels := by
      have ha : raw42529step2 = raw42529step1 := by apply Matrix.ext; unfold raw42529step2 raw42529step1; decide +kernel
      have hl : raw42529step1Labels = labelEmbedding7 ∘ raw42529step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42529step1 raw42529step1Labels raw42529step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4885 node4885Labels := by rfl

def raw42530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42530Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42530step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw42530step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42530step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw42530step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42530 raw42530Labels = mixedMoment B node3023 node3023Labels := by
  calc
    mixedMoment B raw42530 raw42530Labels = mixedMoment B raw42530step0 raw42530step0Labels := by
      have ha : raw42530step0 = (fun i j => raw42530 (permutation590 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42530step0 raw42530; decide +kernel
      have hl : raw42530step0Labels = raw42530Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42530 raw42530Labels permutation590 permutation4
    mixedMoment B raw42530step0 raw42530step0Labels = mixedMoment B raw42530step1 raw42530step1Labels := by
      have ha : raw42530step1 = raw42530step0 := by apply Matrix.ext; unfold raw42530step1 raw42530step0; decide +kernel
      have hl : raw42530step0Labels = labelEmbedding1 ∘ raw42530step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42530step0 raw42530step0Labels raw42530step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3023 node3023Labels := by rfl

def raw42531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42531Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42531step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw42531step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42531step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw42531step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42531 raw42531Labels = mixedMoment B node5286 node5286Labels := by
  calc
    mixedMoment B raw42531 raw42531Labels = mixedMoment B raw42531step0 raw42531step0Labels := by
      have ha : raw42531step0 = (fun i j => raw42531 (permutation606 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42531step0 raw42531; decide +kernel
      have hl : raw42531step0Labels = raw42531Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42531 raw42531Labels permutation606 permutation5
    mixedMoment B raw42531step0 raw42531step0Labels = mixedMoment B raw42531step1 raw42531step1Labels := by
      have ha : raw42531step1 = raw42531step0 := by apply Matrix.ext; unfold raw42531step1 raw42531step0; decide +kernel
      have hl : raw42531step0Labels = labelEmbedding9 ∘ raw42531step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42531step0 raw42531step0Labels raw42531step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5286 node5286Labels := by rfl

def raw42532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw42532Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42532step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw42532step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42532step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw42532step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42532 raw42532Labels = mixedMoment B node2655 node2655Labels := by
  calc
    mixedMoment B raw42532 raw42532Labels = mixedMoment B raw42532step0 raw42532step0Labels := by
      have ha : raw42532step0 = (fun i j => raw42532 (permutation520 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42532step0 raw42532; decide +kernel
      have hl : raw42532step0Labels = raw42532Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42532 raw42532Labels permutation520 permutation4
    mixedMoment B raw42532step0 raw42532step0Labels = mixedMoment B raw42532step1 raw42532step1Labels := by
      have ha : raw42532step1 = raw42532step0 := by apply Matrix.ext; unfold raw42532step1 raw42532step0; decide +kernel
      have hl : raw42532step0Labels = labelEmbedding1 ∘ raw42532step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42532step0 raw42532step0Labels raw42532step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2655 node2655Labels := by rfl

def raw42533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw42533Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw42533step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42533step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw42533step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42533 raw42533Labels = mixedMoment B node5116 node5116Labels := by
  calc
    mixedMoment B raw42533 raw42533Labels = mixedMoment B raw42533step0 raw42533step0Labels := by
      have ha : raw42533step0 = (fun i j => raw42533 (permutation638 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42533step0 raw42533; decide +kernel
      have hl : raw42533step0Labels = raw42533Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42533 raw42533Labels permutation638 permutation7
    mixedMoment B raw42533step0 raw42533step0Labels = mixedMoment B raw42533step1 raw42533step1Labels := by
      have ha : raw42533step1 = raw42533step0 := by apply Matrix.ext; unfold raw42533step1 raw42533step0; decide +kernel
      have hl : raw42533step0Labels = labelEmbedding6 ∘ raw42533step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42533step0 raw42533step0Labels raw42533step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5116 node5116Labels := by rfl

def raw42534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw42534Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw42534step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42534step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw42534step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42534step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw42534step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42534 raw42534Labels = mixedMoment B node3024 node3024Labels := by
  calc
    mixedMoment B raw42534 raw42534Labels = mixedMoment B raw42534step0 raw42534step0Labels := by
      have hz : ∀ j, raw42534 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42534step0 = (fun i j => raw42534 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42534step0 raw42534; decide +kernel
      have hl : raw42534step0Labels = raw42534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42534 raw42534Labels permutation434 hz
    mixedMoment B raw42534step0 raw42534step0Labels = mixedMoment B raw42534step1 raw42534step1Labels := by
      have ha : raw42534step1 = (fun i j => raw42534step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42534step1 raw42534step0; decide +kernel
      have hl : raw42534step1Labels = raw42534step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42534step0 raw42534step0Labels permutation128 permutation4
    mixedMoment B raw42534step1 raw42534step1Labels = mixedMoment B raw42534step2 raw42534step2Labels := by
      have ha : raw42534step2 = raw42534step1 := by apply Matrix.ext; unfold raw42534step2 raw42534step1; decide +kernel
      have hl : raw42534step1Labels = labelEmbedding1 ∘ raw42534step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42534step1 raw42534step1Labels raw42534step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3024 node3024Labels := by rfl

def raw42535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw42535Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw42535step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42535step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw42535step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42535 raw42535Labels = mixedMoment B node5103 node5103Labels := by
  calc
    mixedMoment B raw42535 raw42535Labels = mixedMoment B raw42535step0 raw42535step0Labels := by
      have hz : ∀ j, raw42535 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42535step0 = (fun i j => raw42535 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42535step0 raw42535; decide +kernel
      have hl : raw42535step0Labels = raw42535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42535 raw42535Labels permutation434 hz
    mixedMoment B raw42535step0 raw42535step0Labels = mixedMoment B raw42535step1 raw42535step1Labels := by
      have ha : raw42535step1 = (fun i j => raw42535step0 (permutation119 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42535step1 raw42535step0; decide +kernel
      have hl : raw42535step1Labels = raw42535step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42535step0 raw42535step0Labels permutation119 permutation6
    _ = mixedMoment B node5103 node5103Labels := by rfl

def raw42536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw42536Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw42536step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42536step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw42536step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42536step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw42536step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42536 raw42536Labels = mixedMoment B node2657 node2657Labels := by
  calc
    mixedMoment B raw42536 raw42536Labels = mixedMoment B raw42536step0 raw42536step0Labels := by
      have hz : ∀ j, raw42536 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42536step0 = (fun i j => raw42536 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42536step0 raw42536; decide +kernel
      have hl : raw42536step0Labels = raw42536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42536 raw42536Labels permutation434 hz
    mixedMoment B raw42536step0 raw42536step0Labels = mixedMoment B raw42536step1 raw42536step1Labels := by
      have ha : raw42536step1 = (fun i j => raw42536step0 (permutation104 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42536step1 raw42536step0; decide +kernel
      have hl : raw42536step1Labels = raw42536step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42536step0 raw42536step0Labels permutation104 permutation4
    mixedMoment B raw42536step1 raw42536step1Labels = mixedMoment B raw42536step2 raw42536step2Labels := by
      have ha : raw42536step2 = raw42536step1 := by apply Matrix.ext; unfold raw42536step2 raw42536step1; decide +kernel
      have hl : raw42536step1Labels = labelEmbedding1 ∘ raw42536step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42536step1 raw42536step1Labels raw42536step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2657 node2657Labels := by rfl

def raw42537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw42537Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw42537step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42537step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw42537step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42537 raw42537Labels = mixedMoment B node4548 node4548Labels := by
  calc
    mixedMoment B raw42537 raw42537Labels = mixedMoment B raw42537step0 raw42537step0Labels := by
      have hz : ∀ j, raw42537 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42537step0 = (fun i j => raw42537 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42537step0 raw42537; decide +kernel
      have hl : raw42537step0Labels = raw42537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42537 raw42537Labels permutation434 hz
    mixedMoment B raw42537step0 raw42537step0Labels = mixedMoment B raw42537step1 raw42537step1Labels := by
      have ha : raw42537step1 = (fun i j => raw42537step0 (permutation142 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42537step1 raw42537step0; decide +kernel
      have hl : raw42537step1Labels = raw42537step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42537step0 raw42537step0Labels permutation142 permutation6
    _ = mixedMoment B node4548 node4548Labels := by rfl

def raw42538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42538Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42538step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw42538step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42538step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42538step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42538step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42538step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42538 raw42538Labels = mixedMoment B node3464 node3464Labels := by
  calc
    mixedMoment B raw42538 raw42538Labels = mixedMoment B raw42538step0 raw42538step0Labels := by
      have ha : raw42538step0 = (fun i j => raw42538 (permutation543 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42538step0 raw42538; decide +kernel
      have hl : raw42538step0Labels = raw42538Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42538 raw42538Labels permutation543 permutation4
    mixedMoment B raw42538step0 raw42538step0Labels = mixedMoment B raw42538step1 raw42538step1Labels := by
      have ha : raw42538step1 = -raw42538step0 := by apply Matrix.ext; change ∀ i j, raw42538step1 i j = -(raw42538step0 i j); unfold raw42538step1 raw42538step0; decide +kernel
      have hl : raw42538step1Labels = raw42538step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42538step1 raw42538step1Labels = mixedMoment B raw42538step2 raw42538step2Labels := by
      have ha : raw42538step2 = raw42538step1 := by apply Matrix.ext; unfold raw42538step2 raw42538step1; decide +kernel
      have hl : raw42538step1Labels = labelEmbedding1 ∘ raw42538step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42538step1 raw42538step1Labels raw42538step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3464 node3464Labels := by rfl

def raw42539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42539Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42539step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42539 raw42539Labels = mixedMoment B node5086 node5086Labels := by
  calc
    mixedMoment B raw42539 raw42539Labels = mixedMoment B raw42539step0 raw42539step0Labels := by
      have ha : raw42539step0 = (fun i j => raw42539 (permutation550 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42539step0 raw42539; decide +kernel
      have hl : raw42539step0Labels = raw42539Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42539 raw42539Labels permutation550 permutation6
    _ = mixedMoment B node5086 node5086Labels := by rfl

def raw42540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw42540Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw42540step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42540step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42540step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42540step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42540step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42540 raw42540Labels = mixedMoment B node3259 node3259Labels := by
  calc
    mixedMoment B raw42540 raw42540Labels = mixedMoment B raw42540step0 raw42540step0Labels := by
      have ha : raw42540step0 = (fun i j => raw42540 (permutation629 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42540step0 raw42540; decide +kernel
      have hl : raw42540step0Labels = raw42540Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42540 raw42540Labels permutation629 permutation4
    mixedMoment B raw42540step0 raw42540step0Labels = mixedMoment B raw42540step1 raw42540step1Labels := by
      have ha : raw42540step1 = -raw42540step0 := by apply Matrix.ext; change ∀ i j, raw42540step1 i j = -(raw42540step0 i j); unfold raw42540step1 raw42540step0; decide +kernel
      have hl : raw42540step1Labels = raw42540step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42540step1 raw42540step1Labels = mixedMoment B raw42540step2 raw42540step2Labels := by
      have ha : raw42540step2 = raw42540step1 := by apply Matrix.ext; unfold raw42540step2 raw42540step1; decide +kernel
      have hl : raw42540step1Labels = labelEmbedding1 ∘ raw42540step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42540step1 raw42540step1Labels raw42540step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3259 node3259Labels := by rfl

def raw42541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw42541Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42541step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42541step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42541 raw42541Labels = mixedMoment B node4545 node4545Labels := by
  calc
    mixedMoment B raw42541 raw42541Labels = mixedMoment B raw42541step0 raw42541step0Labels := by
      have ha : raw42541step0 = (fun i j => raw42541 (permutation632 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42541step0 raw42541; decide +kernel
      have hl : raw42541step0Labels = raw42541Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42541 raw42541Labels permutation632 permutation6
    _ = mixedMoment B node4545 node4545Labels := by rfl

def raw42542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw42542Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42542step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw42542step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42542step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42542step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42542step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42542step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42542 raw42542Labels = mixedMoment B node3258 node3258Labels := by
  calc
    mixedMoment B raw42542 raw42542Labels = mixedMoment B raw42542step0 raw42542step0Labels := by
      have ha : raw42542step0 = (fun i j => raw42542 (permutation630 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42542step0 raw42542; decide +kernel
      have hl : raw42542step0Labels = raw42542Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42542 raw42542Labels permutation630 permutation4
    mixedMoment B raw42542step0 raw42542step0Labels = mixedMoment B raw42542step1 raw42542step1Labels := by
      have ha : raw42542step1 = -raw42542step0 := by apply Matrix.ext; change ∀ i j, raw42542step1 i j = -(raw42542step0 i j); unfold raw42542step1 raw42542step0; decide +kernel
      have hl : raw42542step1Labels = raw42542step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42542step1 raw42542step1Labels = mixedMoment B raw42542step2 raw42542step2Labels := by
      have ha : raw42542step2 = raw42542step1 := by apply Matrix.ext; unfold raw42542step2 raw42542step1; decide +kernel
      have hl : raw42542step1Labels = labelEmbedding1 ∘ raw42542step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42542step1 raw42542step1Labels raw42542step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3258 node3258Labels := by rfl

def raw42543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw42543Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42543step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw42543step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42543 raw42543Labels = mixedMoment B node4529 node4529Labels := by
  calc
    mixedMoment B raw42543 raw42543Labels = mixedMoment B raw42543step0 raw42543step0Labels := by
      have ha : raw42543step0 = (fun i j => raw42543 (permutation643 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42543step0 raw42543; decide +kernel
      have hl : raw42543step0Labels = raw42543Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42543 raw42543Labels permutation643 permutation6
    _ = mixedMoment B node4529 node4529Labels := by rfl

def raw42544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw42544Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw42544step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42544step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw42544step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42544 raw42544Labels = mixedMoment B node2652 node2652Labels := by
  calc
    mixedMoment B raw42544 raw42544Labels = mixedMoment B raw42544step0 raw42544step0Labels := by
      have ha : raw42544step0 = (fun i j => raw42544 (permutation593 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42544step0 raw42544; decide +kernel
      have hl : raw42544step0Labels = raw42544Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42544 raw42544Labels permutation593 permutation4
    mixedMoment B raw42544step0 raw42544step0Labels = mixedMoment B raw42544step1 raw42544step1Labels := by
      have ha : raw42544step1 = raw42544step0 := by apply Matrix.ext; unfold raw42544step1 raw42544step0; decide +kernel
      have hl : raw42544step0Labels = labelEmbedding1 ∘ raw42544step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42544step0 raw42544step0Labels raw42544step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2652 node2652Labels := by rfl

def raw42545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw42545Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw42545step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42545 raw42545Labels = mixedMoment B node5035 node5035Labels := by
  calc
    mixedMoment B raw42545 raw42545Labels = mixedMoment B raw42545step0 raw42545step0Labels := by
      have ha : raw42545step0 = (fun i j => raw42545 (permutation477 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42545step0 raw42545; decide +kernel
      have hl : raw42545step0Labels = raw42545Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42545 raw42545Labels permutation477 permutation6
    _ = mixedMoment B node5035 node5035Labels := by rfl

def raw42546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw42546Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42546step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw42546step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42546step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42546step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42546step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42546step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42546 raw42546Labels = mixedMoment B node3463 node3463Labels := by
  calc
    mixedMoment B raw42546 raw42546Labels = mixedMoment B raw42546step0 raw42546step0Labels := by
      have ha : raw42546step0 = (fun i j => raw42546 (permutation470 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42546step0 raw42546; decide +kernel
      have hl : raw42546step0Labels = raw42546Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42546 raw42546Labels permutation470 permutation4
    mixedMoment B raw42546step0 raw42546step0Labels = mixedMoment B raw42546step1 raw42546step1Labels := by
      have ha : raw42546step1 = -raw42546step0 := by apply Matrix.ext; change ∀ i j, raw42546step1 i j = -(raw42546step0 i j); unfold raw42546step1 raw42546step0; decide +kernel
      have hl : raw42546step1Labels = raw42546step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42546step1 raw42546step1Labels = mixedMoment B raw42546step2 raw42546step2Labels := by
      have ha : raw42546step2 = raw42546step1 := by apply Matrix.ext; unfold raw42546step2 raw42546step1; decide +kernel
      have hl : raw42546step1Labels = labelEmbedding1 ∘ raw42546step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42546step1 raw42546step1Labels raw42546step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3463 node3463Labels := by rfl

def raw42547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw42547Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42547step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42547 raw42547Labels = mixedMoment B node5074 node5074Labels := by
  calc
    mixedMoment B raw42547 raw42547Labels = mixedMoment B raw42547step0 raw42547step0Labels := by
      have ha : raw42547step0 = (fun i j => raw42547 (permutation478 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42547step0 raw42547; decide +kernel
      have hl : raw42547step0Labels = raw42547Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42547 raw42547Labels permutation478 permutation6
    _ = mixedMoment B node5074 node5074Labels := by rfl

def raw42548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw42548Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw42548step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42548step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw42548step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42548 raw42548Labels = mixedMoment B node2656 node2656Labels := by
  calc
    mixedMoment B raw42548 raw42548Labels = mixedMoment B raw42548step0 raw42548step0Labels := by
      have ha : raw42548step0 = (fun i j => raw42548 (permutation590 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42548step0 raw42548; decide +kernel
      have hl : raw42548step0Labels = raw42548Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42548 raw42548Labels permutation590 permutation4
    mixedMoment B raw42548step0 raw42548step0Labels = mixedMoment B raw42548step1 raw42548step1Labels := by
      have ha : raw42548step1 = raw42548step0 := by apply Matrix.ext; unfold raw42548step1 raw42548step0; decide +kernel
      have hl : raw42548step0Labels = labelEmbedding1 ∘ raw42548step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42548step0 raw42548step0Labels raw42548step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2656 node2656Labels := by rfl

def raw42549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw42549Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42549step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw42549step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42549step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw42549step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42549 raw42549Labels = mixedMoment B node5217 node5217Labels := by
  calc
    mixedMoment B raw42549 raw42549Labels = mixedMoment B raw42549step0 raw42549step0Labels := by
      have ha : raw42549step0 = (fun i j => raw42549 (permutation590 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42549step0 raw42549; decide +kernel
      have hl : raw42549step0Labels = raw42549Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42549 raw42549Labels permutation590 permutation4
    mixedMoment B raw42549step0 raw42549step0Labels = mixedMoment B raw42549step1 raw42549step1Labels := by
      have ha : raw42549step1 = raw42549step0 := by apply Matrix.ext; unfold raw42549step1 raw42549step0; decide +kernel
      have hl : raw42549step0Labels = labelEmbedding10 ∘ raw42549step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42549step0 raw42549step0Labels raw42549step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5217 node5217Labels := by rfl

def raw42550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -3, 1]]
def raw42550Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 3, -4], ![2, -3, 1]]
def raw42550step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42550step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 3, -4], ![2, -3, 1]]
def raw42550step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42550step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw42550step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42550step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw42550step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42550step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw42550step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42550 raw42550Labels = mixedMoment B node1716 node1716Labels := by
  calc
    mixedMoment B raw42550 raw42550Labels = mixedMoment B raw42550step0 raw42550step0Labels := by
      have hz : ∀ j, raw42550 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42550step0 = (fun i j => raw42550 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42550step0 raw42550; decide +kernel
      have hl : raw42550step0Labels = raw42550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42550 raw42550Labels permutation434 hz
    mixedMoment B raw42550step0 raw42550step0Labels = mixedMoment B raw42550step1 raw42550step1Labels := by
      have hz : ∀ j, raw42550step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42550step1 = (fun i j => raw42550step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42550step1 raw42550step0; decide +kernel
      have hl : raw42550step1Labels = raw42550step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42550step0 raw42550step0Labels permutation80 hz
    mixedMoment B raw42550step1 raw42550step1Labels = mixedMoment B raw42550step2 raw42550step2Labels := by
      have ha : raw42550step2 = (fun i j => raw42550step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42550step2 raw42550step1; decide +kernel
      have hl : raw42550step2Labels = raw42550step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42550step1 raw42550step1Labels permutation22 permutation4
    mixedMoment B raw42550step2 raw42550step2Labels = mixedMoment B raw42550step3 raw42550step3Labels := by
      have ha : raw42550step3 = -raw42550step2 := by apply Matrix.ext; change ∀ i j, raw42550step3 i j = -(raw42550step2 i j); unfold raw42550step3 raw42550step2; decide +kernel
      have hl : raw42550step3Labels = raw42550step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42550step3 raw42550step3Labels = mixedMoment B raw42550step4 raw42550step4Labels := by
      have ha : raw42550step4 = raw42550step3 := by apply Matrix.ext; unfold raw42550step4 raw42550step3; decide +kernel
      have hl : raw42550step3Labels = labelEmbedding1 ∘ raw42550step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42550step3 raw42550step3Labels raw42550step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1716 node1716Labels := by rfl

def raw42551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -3, 1]]
def raw42551Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 3, -4], ![2, -3, 1]]
def raw42551step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42551step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 3, -4], ![2, -3, 1]]
def raw42551step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42551step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw42551step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42551 raw42551Labels = mixedMoment B node4500 node4500Labels := by
  calc
    mixedMoment B raw42551 raw42551Labels = mixedMoment B raw42551step0 raw42551step0Labels := by
      have hz : ∀ j, raw42551 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42551step0 = (fun i j => raw42551 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42551step0 raw42551; decide +kernel
      have hl : raw42551step0Labels = raw42551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42551 raw42551Labels permutation434 hz
    mixedMoment B raw42551step0 raw42551step0Labels = mixedMoment B raw42551step1 raw42551step1Labels := by
      have hz : ∀ j, raw42551step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42551step1 = (fun i j => raw42551step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42551step1 raw42551step0; decide +kernel
      have hl : raw42551step1Labels = raw42551step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42551step0 raw42551step0Labels permutation80 hz
    mixedMoment B raw42551step1 raw42551step1Labels = mixedMoment B raw42551step2 raw42551step2Labels := by
      have ha : raw42551step2 = (fun i j => raw42551step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42551step2 raw42551step1; decide +kernel
      have hl : raw42551step2Labels = raw42551step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42551step1 raw42551step1Labels permutation23 permutation6
    _ = mixedMoment B node4500 node4500Labels := by rfl

def raw42552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw42552Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw42552step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42552step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -3, 2], ![2, 3, -5]]
def raw42552step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42552step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw42552step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42552step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw42552step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42552step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw42552step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42552 raw42552Labels = mixedMoment B node1513 node1513Labels := by
  calc
    mixedMoment B raw42552 raw42552Labels = mixedMoment B raw42552step0 raw42552step0Labels := by
      have hz : ∀ j, raw42552 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42552step0 = (fun i j => raw42552 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42552step0 raw42552; decide +kernel
      have hl : raw42552step0Labels = raw42552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42552 raw42552Labels permutation434 hz
    mixedMoment B raw42552step0 raw42552step0Labels = mixedMoment B raw42552step1 raw42552step1Labels := by
      have hz : ∀ j, raw42552step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42552step1 = (fun i j => raw42552step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42552step1 raw42552step0; decide +kernel
      have hl : raw42552step1Labels = raw42552step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42552step0 raw42552step0Labels permutation80 hz
    mixedMoment B raw42552step1 raw42552step1Labels = mixedMoment B raw42552step2 raw42552step2Labels := by
      have ha : raw42552step2 = (fun i j => raw42552step1 (permutation28 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42552step2 raw42552step1; decide +kernel
      have hl : raw42552step2Labels = raw42552step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42552step1 raw42552step1Labels permutation28 permutation4
    mixedMoment B raw42552step2 raw42552step2Labels = mixedMoment B raw42552step3 raw42552step3Labels := by
      have ha : raw42552step3 = -raw42552step2 := by apply Matrix.ext; change ∀ i j, raw42552step3 i j = -(raw42552step2 i j); unfold raw42552step3 raw42552step2; decide +kernel
      have hl : raw42552step3Labels = raw42552step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42552step3 raw42552step3Labels = mixedMoment B raw42552step4 raw42552step4Labels := by
      have ha : raw42552step4 = raw42552step3 := by apply Matrix.ext; unfold raw42552step4 raw42552step3; decide +kernel
      have hl : raw42552step3Labels = labelEmbedding1 ∘ raw42552step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42552step3 raw42552step3Labels raw42552step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1513 node1513Labels := by rfl

def raw42553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw42553Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw42553step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42553step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -3, 2], ![2, 3, -5]]
def raw42553step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42553step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw42553step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42553 raw42553Labels = mixedMoment B node4179 node4179Labels := by
  calc
    mixedMoment B raw42553 raw42553Labels = mixedMoment B raw42553step0 raw42553step0Labels := by
      have hz : ∀ j, raw42553 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42553step0 = (fun i j => raw42553 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42553step0 raw42553; decide +kernel
      have hl : raw42553step0Labels = raw42553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42553 raw42553Labels permutation434 hz
    mixedMoment B raw42553step0 raw42553step0Labels = mixedMoment B raw42553step1 raw42553step1Labels := by
      have hz : ∀ j, raw42553step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42553step1 = (fun i j => raw42553step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42553step1 raw42553step0; decide +kernel
      have hl : raw42553step1Labels = raw42553step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42553step0 raw42553step0Labels permutation80 hz
    mixedMoment B raw42553step1 raw42553step1Labels = mixedMoment B raw42553step2 raw42553step2Labels := by
      have ha : raw42553step2 = (fun i j => raw42553step1 (permutation28 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42553step2 raw42553step1; decide +kernel
      have hl : raw42553step2Labels = raw42553step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42553step1 raw42553step1Labels permutation28 permutation6
    _ = mixedMoment B node4179 node4179Labels := by rfl

def raw42554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw42554Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw42554step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42554step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw42554step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42554step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42554step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42554step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42554step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42554 raw42554Labels = mixedMoment B node1715 node1715Labels := by
  calc
    mixedMoment B raw42554 raw42554Labels = mixedMoment B raw42554step0 raw42554step0Labels := by
      have hz : ∀ j, raw42554 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42554step0 = (fun i j => raw42554 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42554step0 raw42554; decide +kernel
      have hl : raw42554step0Labels = raw42554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42554 raw42554Labels permutation346 hz
    mixedMoment B raw42554step0 raw42554step0Labels = mixedMoment B raw42554step1 raw42554step1Labels := by
      have ha : raw42554step1 = (fun i j => raw42554step0 (permutation110 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42554step1 raw42554step0; decide +kernel
      have hl : raw42554step1Labels = raw42554step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42554step0 raw42554step0Labels permutation110 permutation4
    mixedMoment B raw42554step1 raw42554step1Labels = mixedMoment B raw42554step2 raw42554step2Labels := by
      have ha : raw42554step2 = -raw42554step1 := by apply Matrix.ext; change ∀ i j, raw42554step2 i j = -(raw42554step1 i j); unfold raw42554step2 raw42554step1; decide +kernel
      have hl : raw42554step2Labels = raw42554step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42554step2 raw42554step2Labels = mixedMoment B raw42554step3 raw42554step3Labels := by
      have ha : raw42554step3 = raw42554step2 := by apply Matrix.ext; unfold raw42554step3 raw42554step2; decide +kernel
      have hl : raw42554step2Labels = labelEmbedding1 ∘ raw42554step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42554step2 raw42554step2Labels raw42554step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1715 node1715Labels := by rfl

def raw42555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw42555Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw42555step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42555step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42555step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42555 raw42555Labels = mixedMoment B node4475 node4475Labels := by
  calc
    mixedMoment B raw42555 raw42555Labels = mixedMoment B raw42555step0 raw42555step0Labels := by
      have hz : ∀ j, raw42555 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42555step0 = (fun i j => raw42555 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42555step0 raw42555; decide +kernel
      have hl : raw42555step0Labels = raw42555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42555 raw42555Labels permutation346 hz
    mixedMoment B raw42555step0 raw42555step0Labels = mixedMoment B raw42555step1 raw42555step1Labels := by
      have ha : raw42555step1 = (fun i j => raw42555step0 (permutation125 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42555step1 raw42555step0; decide +kernel
      have hl : raw42555step1Labels = raw42555step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42555step0 raw42555step0Labels permutation125 permutation6
    _ = mixedMoment B node4475 node4475Labels := by rfl

def raw42556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw42556Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw42556step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42556step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw42556step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42556step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42556step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42556step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42556step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42556 raw42556Labels = mixedMoment B node1512 node1512Labels := by
  calc
    mixedMoment B raw42556 raw42556Labels = mixedMoment B raw42556step0 raw42556step0Labels := by
      have hz : ∀ j, raw42556 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42556step0 = (fun i j => raw42556 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42556step0 raw42556; decide +kernel
      have hl : raw42556step0Labels = raw42556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42556 raw42556Labels permutation346 hz
    mixedMoment B raw42556step0 raw42556step0Labels = mixedMoment B raw42556step1 raw42556step1Labels := by
      have ha : raw42556step1 = (fun i j => raw42556step0 (permutation134 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42556step1 raw42556step0; decide +kernel
      have hl : raw42556step1Labels = raw42556step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42556step0 raw42556step0Labels permutation134 permutation4
    mixedMoment B raw42556step1 raw42556step1Labels = mixedMoment B raw42556step2 raw42556step2Labels := by
      have ha : raw42556step2 = -raw42556step1 := by apply Matrix.ext; change ∀ i j, raw42556step2 i j = -(raw42556step1 i j); unfold raw42556step2 raw42556step1; decide +kernel
      have hl : raw42556step2Labels = raw42556step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42556step2 raw42556step2Labels = mixedMoment B raw42556step3 raw42556step3Labels := by
      have ha : raw42556step3 = raw42556step2 := by apply Matrix.ext; unfold raw42556step3 raw42556step2; decide +kernel
      have hl : raw42556step2Labels = labelEmbedding1 ∘ raw42556step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42556step2 raw42556step2Labels raw42556step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1512 node1512Labels := by rfl

def raw42557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw42557Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw42557step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42557step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42557step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42557 raw42557Labels = mixedMoment B node4176 node4176Labels := by
  calc
    mixedMoment B raw42557 raw42557Labels = mixedMoment B raw42557step0 raw42557step0Labels := by
      have hz : ∀ j, raw42557 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42557step0 = (fun i j => raw42557 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42557step0 raw42557; decide +kernel
      have hl : raw42557step0Labels = raw42557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42557 raw42557Labels permutation346 hz
    mixedMoment B raw42557step0 raw42557step0Labels = mixedMoment B raw42557step1 raw42557step1Labels := by
      have ha : raw42557step1 = (fun i j => raw42557step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42557step1 raw42557step0; decide +kernel
      have hl : raw42557step1Labels = raw42557step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42557step0 raw42557step0Labels permutation137 permutation6
    _ = mixedMoment B node4176 node4176Labels := by rfl

def raw42558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw42558Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw42558step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42558step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw42558step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42558step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42558step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42558step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42558step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42558 raw42558Labels = mixedMoment B node1511 node1511Labels := by
  calc
    mixedMoment B raw42558 raw42558Labels = mixedMoment B raw42558step0 raw42558step0Labels := by
      have hz : ∀ j, raw42558 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42558step0 = (fun i j => raw42558 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42558step0 raw42558; decide +kernel
      have hl : raw42558step0Labels = raw42558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42558 raw42558Labels permutation346 hz
    mixedMoment B raw42558step0 raw42558step0Labels = mixedMoment B raw42558step1 raw42558step1Labels := by
      have ha : raw42558step1 = (fun i j => raw42558step0 (permutation135 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42558step1 raw42558step0; decide +kernel
      have hl : raw42558step1Labels = raw42558step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42558step0 raw42558step0Labels permutation135 permutation4
    mixedMoment B raw42558step1 raw42558step1Labels = mixedMoment B raw42558step2 raw42558step2Labels := by
      have ha : raw42558step2 = -raw42558step1 := by apply Matrix.ext; change ∀ i j, raw42558step2 i j = -(raw42558step1 i j); unfold raw42558step2 raw42558step1; decide +kernel
      have hl : raw42558step2Labels = raw42558step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42558step2 raw42558step2Labels = mixedMoment B raw42558step3 raw42558step3Labels := by
      have ha : raw42558step3 = raw42558step2 := by apply Matrix.ext; unfold raw42558step3 raw42558step2; decide +kernel
      have hl : raw42558step2Labels = labelEmbedding1 ∘ raw42558step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42558step2 raw42558step2Labels raw42558step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1511 node1511Labels := by rfl

def raw42559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw42559Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw42559step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw42559step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42559 raw42559Labels = mixedMoment B node4154 node4154Labels := by
  calc
    mixedMoment B raw42559 raw42559Labels = mixedMoment B raw42559step0 raw42559step0Labels := by
      have hz : ∀ j, raw42559 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42559step0 = (fun i j => raw42559 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42559step0 raw42559; decide +kernel
      have hl : raw42559step0Labels = raw42559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42559 raw42559Labels permutation346 hz
    mixedMoment B raw42559step0 raw42559step0Labels = mixedMoment B raw42559step1 raw42559step1Labels := by
      have ha : raw42559step1 = (fun i j => raw42559step0 (permutation148 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42559step1 raw42559step0; decide +kernel
      have hl : raw42559step1Labels = raw42559step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42559step0 raw42559step0Labels permutation148 permutation6
    _ = mixedMoment B node4154 node4154Labels := by rfl

def raw42560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -2, 1]]
def raw42560Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 3, -4], ![1, -1, 0], ![1, -2, 1]]
def raw42560step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42560step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw42560step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42560step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42560step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42560step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42560step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42560 raw42560Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw42560 raw42560Labels = mixedMoment B raw42560step0 raw42560step0Labels := by
      have hz : ∀ j, raw42560 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42560step0 = (fun i j => raw42560 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42560step0 raw42560; decide +kernel
      have hl : raw42560step0Labels = raw42560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42560 raw42560Labels permutation346 hz
    mixedMoment B raw42560step0 raw42560step0Labels = mixedMoment B raw42560step1 raw42560step1Labels := by
      have ha : raw42560step1 = (fun i j => raw42560step0 (permutation86 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42560step1 raw42560step0; decide +kernel
      have hl : raw42560step1Labels = raw42560step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42560step0 raw42560step0Labels permutation86 permutation4
    mixedMoment B raw42560step1 raw42560step1Labels = mixedMoment B raw42560step2 raw42560step2Labels := by
      have ha : raw42560step2 = -raw42560step1 := by apply Matrix.ext; change ∀ i j, raw42560step2 i j = -(raw42560step1 i j); unfold raw42560step2 raw42560step1; decide +kernel
      have hl : raw42560step2Labels = raw42560step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42560step2 raw42560step2Labels = mixedMoment B raw42560step3 raw42560step3Labels := by
      have ha : raw42560step3 = raw42560step2 := by apply Matrix.ext; unfold raw42560step3 raw42560step2; decide +kernel
      have hl : raw42560step2Labels = labelEmbedding1 ∘ raw42560step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42560step2 raw42560step2Labels raw42560step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1714 node1714Labels := by rfl

def raw42561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0], ![1, -2, 1]]
def raw42561Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 3, -4], ![1, -1, 0], ![1, -2, 1]]
def raw42561step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42561step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42561step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42561 raw42561Labels = mixedMoment B node4459 node4459Labels := by
  calc
    mixedMoment B raw42561 raw42561Labels = mixedMoment B raw42561step0 raw42561step0Labels := by
      have hz : ∀ j, raw42561 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42561step0 = (fun i j => raw42561 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42561step0 raw42561; decide +kernel
      have hl : raw42561step0Labels = raw42561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42561 raw42561Labels permutation346 hz
    mixedMoment B raw42561step0 raw42561step0Labels = mixedMoment B raw42561step1 raw42561step1Labels := by
      have ha : raw42561step1 = (fun i j => raw42561step0 (permutation95 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42561step1 raw42561step0; decide +kernel
      have hl : raw42561step1Labels = raw42561step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42561step0 raw42561step0Labels permutation95 permutation6
    _ = mixedMoment B node4459 node4459Labels := by rfl

def raw42562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -3, 2]]
def raw42562Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 2, -3], ![1, 1, -2], ![1, -3, 2]]
def raw42562step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42562step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw42562step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42562step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw42562step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42562 raw42562Labels = mixedMoment B node2658 node2658Labels := by
  calc
    mixedMoment B raw42562 raw42562Labels = mixedMoment B raw42562step0 raw42562step0Labels := by
      have hz : ∀ j, raw42562 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42562step0 = (fun i j => raw42562 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42562step0 raw42562; decide +kernel
      have hl : raw42562step0Labels = raw42562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42562 raw42562Labels permutation346 hz
    mixedMoment B raw42562step0 raw42562step0Labels = mixedMoment B raw42562step1 raw42562step1Labels := by
      have ha : raw42562step1 = (fun i j => raw42562step0 (permutation129 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42562step1 raw42562step0; decide +kernel
      have hl : raw42562step1Labels = raw42562step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42562step0 raw42562step0Labels permutation129 permutation4
    mixedMoment B raw42562step1 raw42562step1Labels = mixedMoment B raw42562step2 raw42562step2Labels := by
      have ha : raw42562step2 = raw42562step1 := by apply Matrix.ext; unfold raw42562step2 raw42562step1; decide +kernel
      have hl : raw42562step1Labels = labelEmbedding1 ∘ raw42562step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42562step1 raw42562step1Labels raw42562step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2658 node2658Labels := by rfl

def raw42563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2], ![1, -3, 2]]
def raw42563Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 2, -3], ![1, 1, -2], ![1, -3, 2]]
def raw42563step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42563step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw42563step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42563 raw42563Labels = mixedMoment B node4945 node4945Labels := by
  calc
    mixedMoment B raw42563 raw42563Labels = mixedMoment B raw42563step0 raw42563step0Labels := by
      have hz : ∀ j, raw42563 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42563step0 = (fun i j => raw42563 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42563step0 raw42563; decide +kernel
      have hl : raw42563step0Labels = raw42563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42563 raw42563Labels permutation346 hz
    mixedMoment B raw42563step0 raw42563step0Labels = mixedMoment B raw42563step1 raw42563step1Labels := by
      have ha : raw42563step1 = (fun i j => raw42563step0 (permutation94 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42563step1 raw42563step0; decide +kernel
      have hl : raw42563step1Labels = raw42563step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42563step0 raw42563step0Labels permutation94 permutation6
    _ = mixedMoment B node4945 node4945Labels := by rfl

def raw42564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw42564Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42564step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw42564step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42564step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42564step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42564step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42564step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42564 raw42564Labels = mixedMoment B node1510 node1510Labels := by
  calc
    mixedMoment B raw42564 raw42564Labels = mixedMoment B raw42564step0 raw42564step0Labels := by
      have ha : raw42564step0 = (fun i j => raw42564 (permutation606 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42564step0 raw42564; decide +kernel
      have hl : raw42564step0Labels = raw42564Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42564 raw42564Labels permutation606 permutation4
    mixedMoment B raw42564step0 raw42564step0Labels = mixedMoment B raw42564step1 raw42564step1Labels := by
      have ha : raw42564step1 = -raw42564step0 := by apply Matrix.ext; change ∀ i j, raw42564step1 i j = -(raw42564step0 i j); unfold raw42564step1 raw42564step0; decide +kernel
      have hl : raw42564step1Labels = raw42564step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42564step1 raw42564step1Labels = mixedMoment B raw42564step2 raw42564step2Labels := by
      have ha : raw42564step2 = raw42564step1 := by apply Matrix.ext; unfold raw42564step2 raw42564step1; decide +kernel
      have hl : raw42564step1Labels = labelEmbedding1 ∘ raw42564step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42564step1 raw42564step1Labels raw42564step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1510 node1510Labels := by rfl

def raw42565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw42565Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42565step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42565step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42565 raw42565Labels = mixedMoment B node4152 node4152Labels := by
  calc
    mixedMoment B raw42565 raw42565Labels = mixedMoment B raw42565step0 raw42565step0Labels := by
      have ha : raw42565step0 = (fun i j => raw42565 (permutation674 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42565step0 raw42565; decide +kernel
      have hl : raw42565step0Labels = raw42565Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42565 raw42565Labels permutation674 permutation6
    _ = mixedMoment B node4152 node4152Labels := by rfl

def raw42566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw42566Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42566step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw42566step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42566step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42566step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42566step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42566step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42566 raw42566Labels = mixedMoment B node1668 node1668Labels := by
  calc
    mixedMoment B raw42566 raw42566Labels = mixedMoment B raw42566step0 raw42566step0Labels := by
      have ha : raw42566step0 = (fun i j => raw42566 (permutation489 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42566step0 raw42566; decide +kernel
      have hl : raw42566step0Labels = raw42566Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42566 raw42566Labels permutation489 permutation4
    mixedMoment B raw42566step0 raw42566step0Labels = mixedMoment B raw42566step1 raw42566step1Labels := by
      have ha : raw42566step1 = -raw42566step0 := by apply Matrix.ext; change ∀ i j, raw42566step1 i j = -(raw42566step0 i j); unfold raw42566step1 raw42566step0; decide +kernel
      have hl : raw42566step1Labels = raw42566step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42566step1 raw42566step1Labels = mixedMoment B raw42566step2 raw42566step2Labels := by
      have ha : raw42566step2 = raw42566step1 := by apply Matrix.ext; unfold raw42566step2 raw42566step1; decide +kernel
      have hl : raw42566step1Labels = labelEmbedding1 ∘ raw42566step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42566step1 raw42566step1Labels raw42566step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1668 node1668Labels := by rfl

def raw42567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1], ![1, -2, 1]]
def raw42567Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42567step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42567 raw42567Labels = mixedMoment B node4345 node4345Labels := by
  calc
    mixedMoment B raw42567 raw42567Labels = mixedMoment B raw42567step0 raw42567step0Labels := by
      have ha : raw42567step0 = (fun i j => raw42567 (permutation492 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42567step0 raw42567; decide +kernel
      have hl : raw42567step0Labels = raw42567Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42567 raw42567Labels permutation492 permutation6
    _ = mixedMoment B node4345 node4345Labels := by rfl

def raw42568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw42568Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42568step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw42568step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42568step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42568step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42568step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42568step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42568 raw42568Labels = mixedMoment B node1713 node1713Labels := by
  calc
    mixedMoment B raw42568 raw42568Labels = mixedMoment B raw42568step0 raw42568step0Labels := by
      have ha : raw42568step0 = (fun i j => raw42568 (permutation454 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42568step0 raw42568; decide +kernel
      have hl : raw42568step0Labels = raw42568Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42568 raw42568Labels permutation454 permutation4
    mixedMoment B raw42568step0 raw42568step0Labels = mixedMoment B raw42568step1 raw42568step1Labels := by
      have ha : raw42568step1 = -raw42568step0 := by apply Matrix.ext; change ∀ i j, raw42568step1 i j = -(raw42568step0 i j); unfold raw42568step1 raw42568step0; decide +kernel
      have hl : raw42568step1Labels = raw42568step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42568step1 raw42568step1Labels = mixedMoment B raw42568step2 raw42568step2Labels := by
      have ha : raw42568step2 = raw42568step1 := by apply Matrix.ext; unfold raw42568step2 raw42568step1; decide +kernel
      have hl : raw42568step1Labels = labelEmbedding1 ∘ raw42568step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42568step1 raw42568step1Labels raw42568step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1713 node1713Labels := by rfl

def raw42569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0], ![1, -1, 0]]
def raw42569Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42569step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42569step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42569 raw42569Labels = mixedMoment B node4439 node4439Labels := by
  calc
    mixedMoment B raw42569 raw42569Labels = mixedMoment B raw42569step0 raw42569step0Labels := by
      have ha : raw42569step0 = (fun i j => raw42569 (permutation502 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42569step0 raw42569; decide +kernel
      have hl : raw42569step0Labels = raw42569Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42569 raw42569Labels permutation502 permutation6
    _ = mixedMoment B node4439 node4439Labels := by rfl

def raw42570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw42570Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw42570step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42570step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42570step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42570step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42570step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42570 raw42570Labels = mixedMoment B node3407 node3407Labels := by
  calc
    mixedMoment B raw42570 raw42570Labels = mixedMoment B raw42570step0 raw42570step0Labels := by
      have ha : raw42570step0 = (fun i j => raw42570 (permutation489 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42570step0 raw42570; decide +kernel
      have hl : raw42570step0Labels = raw42570Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42570 raw42570Labels permutation489 permutation4
    mixedMoment B raw42570step0 raw42570step0Labels = mixedMoment B raw42570step1 raw42570step1Labels := by
      have ha : raw42570step1 = -raw42570step0 := by apply Matrix.ext; change ∀ i j, raw42570step1 i j = -(raw42570step0 i j); unfold raw42570step1 raw42570step0; decide +kernel
      have hl : raw42570step1Labels = raw42570step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42570step1 raw42570step1Labels = mixedMoment B raw42570step2 raw42570step2Labels := by
      have ha : raw42570step2 = raw42570step1 := by apply Matrix.ext; unfold raw42570step2 raw42570step1; decide +kernel
      have hl : raw42570step1Labels = labelEmbedding1 ∘ raw42570step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42570step1 raw42570step1Labels raw42570step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3407 node3407Labels := by rfl

def raw42571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2], ![1, -2, 1]]
def raw42571Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42571step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42571step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42571 raw42571Labels = mixedMoment B node4942 node4942Labels := by
  calc
    mixedMoment B raw42571 raw42571Labels = mixedMoment B raw42571step0 raw42571step0Labels := by
      have ha : raw42571step0 = (fun i j => raw42571 (permutation492 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42571step0 raw42571; decide +kernel
      have hl : raw42571step0Labels = raw42571Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42571 raw42571Labels permutation492 permutation6
    _ = mixedMoment B node4942 node4942Labels := by rfl

def raw42572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42572Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw42572step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42572step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42572step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42572step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42572step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42572 raw42572Labels = mixedMoment B node1667 node1667Labels := by
  calc
    mixedMoment B raw42572 raw42572Labels = mixedMoment B raw42572step0 raw42572step0Labels := by
      have ha : raw42572step0 = (fun i j => raw42572 (permutation490 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42572step0 raw42572; decide +kernel
      have hl : raw42572step0Labels = raw42572Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42572 raw42572Labels permutation490 permutation4
    mixedMoment B raw42572step0 raw42572step0Labels = mixedMoment B raw42572step1 raw42572step1Labels := by
      have ha : raw42572step1 = -raw42572step0 := by apply Matrix.ext; change ∀ i j, raw42572step1 i j = -(raw42572step0 i j); unfold raw42572step1 raw42572step0; decide +kernel
      have hl : raw42572step1Labels = raw42572step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42572step1 raw42572step1Labels = mixedMoment B raw42572step2 raw42572step2Labels := by
      have ha : raw42572step2 = raw42572step1 := by apply Matrix.ext; unfold raw42572step2 raw42572step1; decide +kernel
      have hl : raw42572step1Labels = labelEmbedding1 ∘ raw42572step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42572step1 raw42572step1Labels raw42572step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1667 node1667Labels := by rfl

def raw42573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1], ![1, -1, 0]]
def raw42573Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42573step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw42573step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42573 raw42573Labels = mixedMoment B node4328 node4328Labels := by
  calc
    mixedMoment B raw42573 raw42573Labels = mixedMoment B raw42573step0 raw42573step0Labels := by
      have ha : raw42573step0 = (fun i j => raw42573 (permutation501 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42573step0 raw42573; decide +kernel
      have hl : raw42573step0Labels = raw42573Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42573 raw42573Labels permutation501 permutation6
    _ = mixedMoment B node4328 node4328Labels := by rfl

def raw42574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42574Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42574step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw42574step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42574step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42574step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42574step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42574step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42574 raw42574Labels = mixedMoment B node3406 node3406Labels := by
  calc
    mixedMoment B raw42574 raw42574Labels = mixedMoment B raw42574step0 raw42574step0Labels := by
      have ha : raw42574step0 = (fun i j => raw42574 (permutation490 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42574step0 raw42574; decide +kernel
      have hl : raw42574step0Labels = raw42574Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42574 raw42574Labels permutation490 permutation4
    mixedMoment B raw42574step0 raw42574step0Labels = mixedMoment B raw42574step1 raw42574step1Labels := by
      have ha : raw42574step1 = -raw42574step0 := by apply Matrix.ext; change ∀ i j, raw42574step1 i j = -(raw42574step0 i j); unfold raw42574step1 raw42574step0; decide +kernel
      have hl : raw42574step1Labels = raw42574step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42574step1 raw42574step1Labels = mixedMoment B raw42574step2 raw42574step2Labels := by
      have ha : raw42574step2 = raw42574step1 := by apply Matrix.ext; unfold raw42574step2 raw42574step1; decide +kernel
      have hl : raw42574step1Labels = labelEmbedding1 ∘ raw42574step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42574step1 raw42574step1Labels raw42574step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3406 node3406Labels := by rfl

def raw42575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2], ![1, -1, 0]]
def raw42575Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw42575step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42575 raw42575Labels = mixedMoment B node4931 node4931Labels := by
  calc
    mixedMoment B raw42575 raw42575Labels = mixedMoment B raw42575step0 raw42575step0Labels := by
      have ha : raw42575step0 = (fun i j => raw42575 (permutation501 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42575step0 raw42575; decide +kernel
      have hl : raw42575step0Labels = raw42575Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42575 raw42575Labels permutation501 permutation6
    _ = mixedMoment B node4931 node4931Labels := by rfl

def raw42576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42576Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw42576step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw42576step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42576step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw42576step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42576step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw42576step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42576 raw42576Labels = mixedMoment B node2217 node2217Labels := by
  calc
    mixedMoment B raw42576 raw42576Labels = mixedMoment B raw42576step0 raw42576step0Labels := by
      have hz : ∀ j, raw42576 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42576step0 = (fun i j => raw42576 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42576step0 raw42576; decide +kernel
      have hl : raw42576step0Labels = raw42576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42576 raw42576Labels permutation434 hz
    mixedMoment B raw42576step0 raw42576step0Labels = mixedMoment B raw42576step1 raw42576step1Labels := by
      have ha : raw42576step1 = (fun i j => raw42576step0 (permutation92 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42576step1 raw42576step0; decide +kernel
      have hl : raw42576step1Labels = raw42576step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42576step0 raw42576step0Labels permutation92 permutation4
    mixedMoment B raw42576step1 raw42576step1Labels = mixedMoment B raw42576step2 raw42576step2Labels := by
      have ha : raw42576step2 = -raw42576step1 := by apply Matrix.ext; change ∀ i j, raw42576step2 i j = -(raw42576step1 i j); unfold raw42576step2 raw42576step1; decide +kernel
      have hl : raw42576step2Labels = raw42576step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42576step2 raw42576step2Labels = mixedMoment B raw42576step3 raw42576step3Labels := by
      have ha : raw42576step3 = raw42576step2 := by apply Matrix.ext; unfold raw42576step3 raw42576step2; decide +kernel
      have hl : raw42576step2Labels = labelEmbedding1 ∘ raw42576step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42576step2 raw42576step2Labels raw42576step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2217 node2217Labels := by rfl

def raw42577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42577Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw42577step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw42577step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42577 raw42577Labels = mixedMoment B node4821 node4821Labels := by
  calc
    mixedMoment B raw42577 raw42577Labels = mixedMoment B raw42577step0 raw42577step0Labels := by
      have hz : ∀ j, raw42577 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42577step0 = (fun i j => raw42577 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42577step0 raw42577; decide +kernel
      have hl : raw42577step0Labels = raw42577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42577 raw42577Labels permutation434 hz
    mixedMoment B raw42577step0 raw42577step0Labels = mixedMoment B raw42577step1 raw42577step1Labels := by
      have ha : raw42577step1 = (fun i j => raw42577step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42577step1 raw42577step0; decide +kernel
      have hl : raw42577step1Labels = raw42577step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42577step0 raw42577step0Labels permutation96 permutation6
    _ = mixedMoment B node4821 node4821Labels := by rfl

def raw42578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42578Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw42578step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42578step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw42578step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42578step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42578step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42578step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42578step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42578 raw42578Labels = mixedMoment B node2274 node2274Labels := by
  calc
    mixedMoment B raw42578 raw42578Labels = mixedMoment B raw42578step0 raw42578step0Labels := by
      have hz : ∀ j, raw42578 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42578step0 = (fun i j => raw42578 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42578step0 raw42578; decide +kernel
      have hl : raw42578step0Labels = raw42578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42578 raw42578Labels permutation434 hz
    mixedMoment B raw42578step0 raw42578step0Labels = mixedMoment B raw42578step1 raw42578step1Labels := by
      have ha : raw42578step1 = (fun i j => raw42578step0 (permutation85 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42578step1 raw42578step0; decide +kernel
      have hl : raw42578step1Labels = raw42578step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42578step0 raw42578step0Labels permutation85 permutation4
    mixedMoment B raw42578step1 raw42578step1Labels = mixedMoment B raw42578step2 raw42578step2Labels := by
      have ha : raw42578step2 = -raw42578step1 := by apply Matrix.ext; change ∀ i j, raw42578step2 i j = -(raw42578step1 i j); unfold raw42578step2 raw42578step1; decide +kernel
      have hl : raw42578step2Labels = raw42578step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42578step2 raw42578step2Labels = mixedMoment B raw42578step3 raw42578step3Labels := by
      have ha : raw42578step3 = raw42578step2 := by apply Matrix.ext; unfold raw42578step3 raw42578step2; decide +kernel
      have hl : raw42578step2Labels = labelEmbedding1 ∘ raw42578step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42578step2 raw42578step2Labels raw42578step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2274 node2274Labels := by rfl

def raw42579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42579Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw42579step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42579step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw42579step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42579 raw42579Labels = mixedMoment B node4856 node4856Labels := by
  calc
    mixedMoment B raw42579 raw42579Labels = mixedMoment B raw42579step0 raw42579step0Labels := by
      have hz : ∀ j, raw42579 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42579step0 = (fun i j => raw42579 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42579step0 raw42579; decide +kernel
      have hl : raw42579step0Labels = raw42579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42579 raw42579Labels permutation434 hz
    mixedMoment B raw42579step0 raw42579step0Labels = mixedMoment B raw42579step1 raw42579step1Labels := by
      have ha : raw42579step1 = (fun i j => raw42579step0 (permutation102 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42579step1 raw42579step0; decide +kernel
      have hl : raw42579step1Labels = raw42579step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42579step0 raw42579step0Labels permutation102 permutation6
    _ = mixedMoment B node4856 node4856Labels := by rfl

def raw42580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42580Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw42580step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw42580step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42580step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw42580step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42580step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw42580step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42580 raw42580Labels = mixedMoment B node2158 node2158Labels := by
  calc
    mixedMoment B raw42580 raw42580Labels = mixedMoment B raw42580step0 raw42580step0Labels := by
      have hz : ∀ j, raw42580 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42580step0 = (fun i j => raw42580 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42580step0 raw42580; decide +kernel
      have hl : raw42580step0Labels = raw42580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42580 raw42580Labels permutation434 hz
    mixedMoment B raw42580step0 raw42580step0Labels = mixedMoment B raw42580step1 raw42580step1Labels := by
      have ha : raw42580step1 = (fun i j => raw42580step0 (permutation98 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42580step1 raw42580step0; decide +kernel
      have hl : raw42580step1Labels = raw42580step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42580step0 raw42580step0Labels permutation98 permutation4
    mixedMoment B raw42580step1 raw42580step1Labels = mixedMoment B raw42580step2 raw42580step2Labels := by
      have ha : raw42580step2 = -raw42580step1 := by apply Matrix.ext; change ∀ i j, raw42580step2 i j = -(raw42580step1 i j); unfold raw42580step2 raw42580step1; decide +kernel
      have hl : raw42580step2Labels = raw42580step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42580step2 raw42580step2Labels = mixedMoment B raw42580step3 raw42580step3Labels := by
      have ha : raw42580step3 = raw42580step2 := by apply Matrix.ext; unfold raw42580step3 raw42580step2; decide +kernel
      have hl : raw42580step2Labels = labelEmbedding1 ∘ raw42580step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42580step2 raw42580step2Labels raw42580step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2158 node2158Labels := by rfl

def raw42581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42581Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw42581step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42581step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw42581step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42581 raw42581Labels = mixedMoment B node4690 node4690Labels := by
  calc
    mixedMoment B raw42581 raw42581Labels = mixedMoment B raw42581step0 raw42581step0Labels := by
      have hz : ∀ j, raw42581 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42581step0 = (fun i j => raw42581 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42581step0 raw42581; decide +kernel
      have hl : raw42581step0Labels = raw42581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42581 raw42581Labels permutation434 hz
    mixedMoment B raw42581step0 raw42581step0Labels = mixedMoment B raw42581step1 raw42581step1Labels := by
      have ha : raw42581step1 = (fun i j => raw42581step0 (permutation102 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42581step1 raw42581step0; decide +kernel
      have hl : raw42581step1Labels = raw42581step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42581step0 raw42581step0Labels permutation102 permutation6
    _ = mixedMoment B node4690 node4690Labels := by rfl

def raw42582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42582Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42582step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw42582step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42582step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42582step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42582step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42582step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42582 raw42582Labels = mixedMoment B node2154 node2154Labels := by
  calc
    mixedMoment B raw42582 raw42582Labels = mixedMoment B raw42582step0 raw42582step0Labels := by
      have ha : raw42582step0 = (fun i j => raw42582 (permutation418 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42582step0 raw42582; decide +kernel
      have hl : raw42582step0Labels = raw42582Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42582 raw42582Labels permutation418 permutation4
    mixedMoment B raw42582step0 raw42582step0Labels = mixedMoment B raw42582step1 raw42582step1Labels := by
      have ha : raw42582step1 = -raw42582step0 := by apply Matrix.ext; change ∀ i j, raw42582step1 i j = -(raw42582step0 i j); unfold raw42582step1 raw42582step0; decide +kernel
      have hl : raw42582step1Labels = raw42582step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42582step1 raw42582step1Labels = mixedMoment B raw42582step2 raw42582step2Labels := by
      have ha : raw42582step2 = raw42582step1 := by apply Matrix.ext; unfold raw42582step2 raw42582step1; decide +kernel
      have hl : raw42582step1Labels = labelEmbedding1 ∘ raw42582step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42582step1 raw42582step1Labels raw42582step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2154 node2154Labels := by rfl

def raw42583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42583Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42583step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw42583step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42583 raw42583Labels = mixedMoment B node4668 node4668Labels := by
  calc
    mixedMoment B raw42583 raw42583Labels = mixedMoment B raw42583step0 raw42583step0Labels := by
      have ha : raw42583step0 = (fun i j => raw42583 (permutation432 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42583step0 raw42583; decide +kernel
      have hl : raw42583step0Labels = raw42583Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42583 raw42583Labels permutation432 permutation6
    _ = mixedMoment B node4668 node4668Labels := by rfl

def raw42584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42584Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw42584step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42584step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw42584step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42584step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw42584step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42584 raw42584Labels = mixedMoment B node2178 node2178Labels := by
  calc
    mixedMoment B raw42584 raw42584Labels = mixedMoment B raw42584step0 raw42584step0Labels := by
      have ha : raw42584step0 = (fun i j => raw42584 (permutation389 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42584step0 raw42584; decide +kernel
      have hl : raw42584step0Labels = raw42584Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42584 raw42584Labels permutation389 permutation4
    mixedMoment B raw42584step0 raw42584step0Labels = mixedMoment B raw42584step1 raw42584step1Labels := by
      have ha : raw42584step1 = -raw42584step0 := by apply Matrix.ext; change ∀ i j, raw42584step1 i j = -(raw42584step0 i j); unfold raw42584step1 raw42584step0; decide +kernel
      have hl : raw42584step1Labels = raw42584step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42584step1 raw42584step1Labels = mixedMoment B raw42584step2 raw42584step2Labels := by
      have ha : raw42584step2 = raw42584step1 := by apply Matrix.ext; unfold raw42584step2 raw42584step1; decide +kernel
      have hl : raw42584step1Labels = labelEmbedding1 ∘ raw42584step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42584step1 raw42584step1Labels raw42584step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2178 node2178Labels := by rfl

def raw42585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42585Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw42585step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42585 raw42585Labels = mixedMoment B node4768 node4768Labels := by
  calc
    mixedMoment B raw42585 raw42585Labels = mixedMoment B raw42585step0 raw42585step0Labels := by
      have ha : raw42585step0 = (fun i j => raw42585 (permutation393 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42585step0 raw42585; decide +kernel
      have hl : raw42585step0Labels = raw42585Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42585 raw42585Labels permutation393 permutation6
    _ = mixedMoment B node4768 node4768Labels := by rfl

def raw42586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42586Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42586step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw42586step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42586step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42586step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42586step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42586step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42586 raw42586Labels = mixedMoment B node2213 node2213Labels := by
  calc
    mixedMoment B raw42586 raw42586Labels = mixedMoment B raw42586step0 raw42586step0Labels := by
      have ha : raw42586step0 = (fun i j => raw42586 (permutation383 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42586step0 raw42586; decide +kernel
      have hl : raw42586step0Labels = raw42586Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42586 raw42586Labels permutation383 permutation4
    mixedMoment B raw42586step0 raw42586step0Labels = mixedMoment B raw42586step1 raw42586step1Labels := by
      have ha : raw42586step1 = -raw42586step0 := by apply Matrix.ext; change ∀ i j, raw42586step1 i j = -(raw42586step0 i j); unfold raw42586step1 raw42586step0; decide +kernel
      have hl : raw42586step1Labels = raw42586step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42586step1 raw42586step1Labels = mixedMoment B raw42586step2 raw42586step2Labels := by
      have ha : raw42586step2 = raw42586step1 := by apply Matrix.ext; unfold raw42586step2 raw42586step1; decide +kernel
      have hl : raw42586step1Labels = labelEmbedding1 ∘ raw42586step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42586step1 raw42586step1Labels raw42586step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2213 node2213Labels := by rfl

def raw42587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42587Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42587step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw42587step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42587 raw42587Labels = mixedMoment B node4795 node4795Labels := by
  calc
    mixedMoment B raw42587 raw42587Labels = mixedMoment B raw42587step0 raw42587step0Labels := by
      have ha : raw42587step0 = (fun i j => raw42587 (permutation393 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42587step0 raw42587; decide +kernel
      have hl : raw42587step0Labels = raw42587Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42587 raw42587Labels permutation393 permutation6
    _ = mixedMoment B node4795 node4795Labels := by rfl

def raw42588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42588Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42588step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42588step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42588step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42588step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42588 raw42588Labels = mixedMoment B node3762 node3762Labels := by
  calc
    mixedMoment B raw42588 raw42588Labels = mixedMoment B raw42588step0 raw42588step0Labels := by
      have ha : raw42588step0 = (fun i j => raw42588 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42588step0 raw42588; decide +kernel
      have hl : raw42588step0Labels = raw42588Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42588 raw42588Labels permutation158 permutation2
    mixedMoment B raw42588step0 raw42588step0Labels = mixedMoment B raw42588step1 raw42588step1Labels := by
      have ha : raw42588step1 = raw42588step0 := by apply Matrix.ext; unfold raw42588step1 raw42588step0; decide +kernel
      have hl : raw42588step0Labels = labelEmbedding1 ∘ raw42588step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42588step0 raw42588step0Labels raw42588step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3762 node3762Labels := by rfl

def raw42589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42589Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw42589step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42589step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42589step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42589step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42589step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42589 raw42589Labels = mixedMoment B node5360 node5360Labels := by
  calc
    mixedMoment B raw42589 raw42589Labels = mixedMoment B raw42589step0 raw42589step0Labels := by
      have ha : raw42589step0 = (fun i j => raw42589 (permutation173 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42589step0 raw42589; decide +kernel
      have hl : raw42589step0Labels = raw42589Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42589 raw42589Labels permutation173 permutation7
    mixedMoment B raw42589step0 raw42589step0Labels = mixedMoment B raw42589step1 raw42589step1Labels := by
      have ha : raw42589step1 = -raw42589step0 := by apply Matrix.ext; change ∀ i j, raw42589step1 i j = -(raw42589step0 i j); unfold raw42589step1 raw42589step0; decide +kernel
      have hl : raw42589step1Labels = raw42589step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42589step1 raw42589step1Labels = mixedMoment B raw42589step2 raw42589step2Labels := by
      have ha : raw42589step2 = raw42589step1 := by apply Matrix.ext; unfold raw42589step2 raw42589step1; decide +kernel
      have hl : raw42589step1Labels = labelEmbedding6 ∘ raw42589step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42589step1 raw42589step1Labels raw42589step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5360 node5360Labels := by rfl

def raw42590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42590Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42590step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42590step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42590step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42590step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42590 raw42590Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw42590 raw42590Labels = mixedMoment B raw42590step0 raw42590step0Labels := by
      have ha : raw42590step0 = (fun i j => raw42590 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42590step0 raw42590; decide +kernel
      have hl : raw42590step0Labels = raw42590Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42590 raw42590Labels permutation158 permutation2
    mixedMoment B raw42590step0 raw42590step0Labels = mixedMoment B raw42590step1 raw42590step1Labels := by
      have ha : raw42590step1 = raw42590step0 := by apply Matrix.ext; unfold raw42590step1 raw42590step0; decide +kernel
      have hl : raw42590step0Labels = labelEmbedding1 ∘ raw42590step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42590step0 raw42590step0Labels raw42590step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3761 node3761Labels := by rfl

def raw42591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42591Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42591step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw42591step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42591step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42591step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42591step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42591step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42591 raw42591Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw42591 raw42591Labels = mixedMoment B raw42591step0 raw42591step0Labels := by
      have ha : raw42591step0 = (fun i j => raw42591 (permutation167 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42591step0 raw42591; decide +kernel
      have hl : raw42591step0Labels = raw42591Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42591 raw42591Labels permutation167 permutation7
    mixedMoment B raw42591step0 raw42591step0Labels = mixedMoment B raw42591step1 raw42591step1Labels := by
      have ha : raw42591step1 = -raw42591step0 := by apply Matrix.ext; change ∀ i j, raw42591step1 i j = -(raw42591step0 i j); unfold raw42591step1 raw42591step0; decide +kernel
      have hl : raw42591step1Labels = raw42591step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42591step1 raw42591step1Labels = mixedMoment B raw42591step2 raw42591step2Labels := by
      have ha : raw42591step2 = raw42591step1 := by apply Matrix.ext; unfold raw42591step2 raw42591step1; decide +kernel
      have hl : raw42591step1Labels = labelEmbedding6 ∘ raw42591step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42591step1 raw42591step1Labels raw42591step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5353 node5353Labels := by rfl

def raw42592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42592Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42592step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw42592step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42592step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw42592step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42592 raw42592Labels = mixedMoment B node3760 node3760Labels := by
  calc
    mixedMoment B raw42592 raw42592Labels = mixedMoment B raw42592step0 raw42592step0Labels := by
      have ha : raw42592step0 = (fun i j => raw42592 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42592step0 raw42592; decide +kernel
      have hl : raw42592step0Labels = raw42592Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42592 raw42592Labels permutation158 permutation2
    mixedMoment B raw42592step0 raw42592step0Labels = mixedMoment B raw42592step1 raw42592step1Labels := by
      have ha : raw42592step1 = raw42592step0 := by apply Matrix.ext; unfold raw42592step1 raw42592step0; decide +kernel
      have hl : raw42592step0Labels = labelEmbedding1 ∘ raw42592step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42592step0 raw42592step0Labels raw42592step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3760 node3760Labels := by rfl

def raw42593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42593Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw42593step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42593step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw42593step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42593step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw42593step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42593 raw42593Labels = mixedMoment B node5339 node5339Labels := by
  calc
    mixedMoment B raw42593 raw42593Labels = mixedMoment B raw42593step0 raw42593step0Labels := by
      have ha : raw42593step0 = (fun i j => raw42593 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42593step0 raw42593; decide +kernel
      have hl : raw42593step0Labels = raw42593Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42593 raw42593Labels permutation166 permutation7
    mixedMoment B raw42593step0 raw42593step0Labels = mixedMoment B raw42593step1 raw42593step1Labels := by
      have ha : raw42593step1 = -raw42593step0 := by apply Matrix.ext; change ∀ i j, raw42593step1 i j = -(raw42593step0 i j); unfold raw42593step1 raw42593step0; decide +kernel
      have hl : raw42593step1Labels = raw42593step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42593step1 raw42593step1Labels = mixedMoment B raw42593step2 raw42593step2Labels := by
      have ha : raw42593step2 = raw42593step1 := by apply Matrix.ext; unfold raw42593step2 raw42593step1; decide +kernel
      have hl : raw42593step1Labels = labelEmbedding6 ∘ raw42593step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42593step1 raw42593step1Labels raw42593step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5339 node5339Labels := by rfl

def raw42594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42594Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw42594step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw42594step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42594 raw42594Labels = mixedMoment B node3772 node3772Labels := by
  calc
    mixedMoment B raw42594 raw42594Labels = mixedMoment B raw42594step0 raw42594step0Labels := by
      have hz : ∀ j, raw42594 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42594step0 = (fun i j => raw42594 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42594step0 raw42594; decide +kernel
      have hl : raw42594step0Labels = raw42594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42594 raw42594Labels permutation434 hz
    mixedMoment B raw42594step0 raw42594step0Labels = mixedMoment B raw42594step1 raw42594step1Labels := by
      have ha : raw42594step1 = raw42594step0 := by apply Matrix.ext; unfold raw42594step1 raw42594step0; decide +kernel
      have hl : raw42594step0Labels = labelEmbedding1 ∘ raw42594step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42594step0 raw42594step0Labels raw42594step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3772 node3772Labels := by rfl

def raw42595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42595Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw42595step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42595step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw42595step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42595 raw42595Labels = mixedMoment B node5361 node5361Labels := by
  calc
    mixedMoment B raw42595 raw42595Labels = mixedMoment B raw42595step0 raw42595step0Labels := by
      have hz : ∀ j, raw42595 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42595step0 = (fun i j => raw42595 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42595step0 raw42595; decide +kernel
      have hl : raw42595step0Labels = raw42595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42595 raw42595Labels permutation434 hz
    mixedMoment B raw42595step0 raw42595step0Labels = mixedMoment B raw42595step1 raw42595step1Labels := by
      have ha : raw42595step1 = (fun i j => raw42595step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42595step1 raw42595step0; decide +kernel
      have hl : raw42595step1Labels = raw42595step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42595step0 raw42595step0Labels permutation96 permutation6
    _ = mixedMoment B node5361 node5361Labels := by rfl

def raw42596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw42596Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw42596step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw42596step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42596step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw42596step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42596step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw42596step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42596 raw42596Labels = mixedMoment B node3555 node3555Labels := by
  calc
    mixedMoment B raw42596 raw42596Labels = mixedMoment B raw42596step0 raw42596step0Labels := by
      have hz : ∀ j, raw42596 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42596step0 = (fun i j => raw42596 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42596step0 raw42596; decide +kernel
      have hl : raw42596step0Labels = raw42596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42596 raw42596Labels permutation434 hz
    mixedMoment B raw42596step0 raw42596step0Labels = mixedMoment B raw42596step1 raw42596step1Labels := by
      have ha : raw42596step1 = (fun i j => raw42596step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42596step1 raw42596step0; decide +kernel
      have hl : raw42596step1Labels = raw42596step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42596step0 raw42596step0Labels permutation151 permutation2
    mixedMoment B raw42596step1 raw42596step1Labels = mixedMoment B raw42596step2 raw42596step2Labels := by
      have ha : raw42596step2 = -raw42596step1 := by apply Matrix.ext; change ∀ i j, raw42596step2 i j = -(raw42596step1 i j); unfold raw42596step2 raw42596step1; decide +kernel
      have hl : raw42596step2Labels = raw42596step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42596step2 raw42596step2Labels = mixedMoment B raw42596step3 raw42596step3Labels := by
      have ha : raw42596step3 = raw42596step2 := by apply Matrix.ext; unfold raw42596step3 raw42596step2; decide +kernel
      have hl : raw42596step2Labels = labelEmbedding1 ∘ raw42596step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42596step2 raw42596step2Labels raw42596step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3555 node3555Labels := by rfl

def raw42597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw42597Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw42597step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42597step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw42597step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42597step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw42597step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42597 raw42597Labels = mixedMoment B node4966 node4966Labels := by
  calc
    mixedMoment B raw42597 raw42597Labels = mixedMoment B raw42597step0 raw42597step0Labels := by
      have hz : ∀ j, raw42597 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42597step0 = (fun i j => raw42597 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42597step0 raw42597; decide +kernel
      have hl : raw42597step0Labels = raw42597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42597 raw42597Labels permutation434 hz
    mixedMoment B raw42597step0 raw42597step0Labels = mixedMoment B raw42597step1 raw42597step1Labels := by
      have ha : raw42597step1 = (fun i j => raw42597step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42597step1 raw42597step0; decide +kernel
      have hl : raw42597step1Labels = raw42597step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42597step0 raw42597step0Labels permutation145 permutation7
    mixedMoment B raw42597step1 raw42597step1Labels = mixedMoment B raw42597step2 raw42597step2Labels := by
      have ha : raw42597step2 = raw42597step1 := by apply Matrix.ext; unfold raw42597step2 raw42597step1; decide +kernel
      have hl : raw42597step1Labels = labelEmbedding6 ∘ raw42597step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42597step1 raw42597step1Labels raw42597step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4966 node4966Labels := by rfl

def raw42598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42598Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw42598step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42598step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw42598step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42598step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw42598step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42598 raw42598Labels = mixedMoment B node3508 node3508Labels := by
  calc
    mixedMoment B raw42598 raw42598Labels = mixedMoment B raw42598step0 raw42598step0Labels := by
      have ha : raw42598step0 = (fun i j => raw42598 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42598step0 raw42598; decide +kernel
      have hl : raw42598step0Labels = raw42598Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42598 raw42598Labels permutation682 permutation2
    mixedMoment B raw42598step0 raw42598step0Labels = mixedMoment B raw42598step1 raw42598step1Labels := by
      have ha : raw42598step1 = -raw42598step0 := by apply Matrix.ext; change ∀ i j, raw42598step1 i j = -(raw42598step0 i j); unfold raw42598step1 raw42598step0; decide +kernel
      have hl : raw42598step1Labels = raw42598step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42598step1 raw42598step1Labels = mixedMoment B raw42598step2 raw42598step2Labels := by
      have ha : raw42598step2 = raw42598step1 := by apply Matrix.ext; unfold raw42598step2 raw42598step1; decide +kernel
      have hl : raw42598step1Labels = labelEmbedding1 ∘ raw42598step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42598step1 raw42598step1Labels raw42598step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3508 node3508Labels := by rfl

def raw42599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42599Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42599step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw42599step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42599step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw42599step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42599 raw42599Labels = mixedMoment B node4955 node4955Labels := by
  calc
    mixedMoment B raw42599 raw42599Labels = mixedMoment B raw42599step0 raw42599step0Labels := by
      have ha : raw42599step0 = (fun i j => raw42599 (permutation646 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42599step0 raw42599; decide +kernel
      have hl : raw42599step0Labels = raw42599Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42599 raw42599Labels permutation646 permutation7
    mixedMoment B raw42599step0 raw42599step0Labels = mixedMoment B raw42599step1 raw42599step1Labels := by
      have ha : raw42599step1 = raw42599step0 := by apply Matrix.ext; unfold raw42599step1 raw42599step0; decide +kernel
      have hl : raw42599step0Labels = labelEmbedding6 ∘ raw42599step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42599step0 raw42599step0Labels raw42599step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4955 node4955Labels := by rfl

def raw42600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42600Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw42600step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42600step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw42600step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42600step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw42600step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42600 raw42600Labels = mixedMoment B node3755 node3755Labels := by
  calc
    mixedMoment B raw42600 raw42600Labels = mixedMoment B raw42600step0 raw42600step0Labels := by
      have ha : raw42600step0 = (fun i j => raw42600 (permutation389 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42600step0 raw42600; decide +kernel
      have hl : raw42600step0Labels = raw42600Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42600 raw42600Labels permutation389 permutation4
    mixedMoment B raw42600step0 raw42600step0Labels = mixedMoment B raw42600step1 raw42600step1Labels := by
      have ha : raw42600step1 = -raw42600step0 := by apply Matrix.ext; change ∀ i j, raw42600step1 i j = -(raw42600step0 i j); unfold raw42600step1 raw42600step0; decide +kernel
      have hl : raw42600step1Labels = raw42600step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42600step1 raw42600step1Labels = mixedMoment B raw42600step2 raw42600step2Labels := by
      have ha : raw42600step2 = raw42600step1 := by apply Matrix.ext; unfold raw42600step2 raw42600step1; decide +kernel
      have hl : raw42600step1Labels = labelEmbedding1 ∘ raw42600step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42600step1 raw42600step1Labels raw42600step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3755 node3755Labels := by rfl

def raw42601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42601Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42601step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw42601step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42601 raw42601Labels = mixedMoment B node5338 node5338Labels := by
  calc
    mixedMoment B raw42601 raw42601Labels = mixedMoment B raw42601step0 raw42601step0Labels := by
      have ha : raw42601step0 = (fun i j => raw42601 (permutation393 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42601step0 raw42601; decide +kernel
      have hl : raw42601step0Labels = raw42601Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42601 raw42601Labels permutation393 permutation6
    _ = mixedMoment B node5338 node5338Labels := by rfl

def raw42602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw42602Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42602step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42602step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42602step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42602step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42602 raw42602Labels = mixedMoment B node3768 node3768Labels := by
  calc
    mixedMoment B raw42602 raw42602Labels = mixedMoment B raw42602step0 raw42602step0Labels := by
      have ha : raw42602step0 = (fun i j => raw42602 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42602step0 raw42602; decide +kernel
      have hl : raw42602step0Labels = raw42602Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42602 raw42602Labels permutation155 permutation2
    mixedMoment B raw42602step0 raw42602step0Labels = mixedMoment B raw42602step1 raw42602step1Labels := by
      have ha : raw42602step1 = raw42602step0 := by apply Matrix.ext; unfold raw42602step1 raw42602step0; decide +kernel
      have hl : raw42602step0Labels = labelEmbedding1 ∘ raw42602step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42602step0 raw42602step0Labels raw42602step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3768 node3768Labels := by rfl

def raw42603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw42603Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw42603step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42603 raw42603Labels = mixedMoment B node5348 node5348Labels := by
  calc
    mixedMoment B raw42603 raw42603Labels = mixedMoment B raw42603step0 raw42603step0Labels := by
      have ha : raw42603step0 = (fun i j => raw42603 (permutation393 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42603step0 raw42603; decide +kernel
      have hl : raw42603step0Labels = raw42603Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42603 raw42603Labels permutation393 permutation6
    _ = mixedMoment B node5348 node5348Labels := by rfl

def raw42604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42604Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42604step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42604 raw42604Labels = mixedMoment B node3759 node3759Labels := by
  calc
    mixedMoment B raw42604 raw42604Labels = mixedMoment B raw42604step0 raw42604step0Labels := by
      have ha : raw42604step0 = raw42604 := by apply Matrix.ext; unfold raw42604step0 raw42604; decide +kernel
      have hl : raw42604Labels = labelEmbedding1 ∘ raw42604step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42604 raw42604Labels raw42604step0Labels labelEmbedding1 hl
    _ = mixedMoment B node3759 node3759Labels := by rfl

def raw42605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42605Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42605step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw42605step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42605step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42605step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42605step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42605step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42605 raw42605Labels = mixedMoment B node5359 node5359Labels := by
  calc
    mixedMoment B raw42605 raw42605Labels = mixedMoment B raw42605step0 raw42605step0Labels := by
      have ha : raw42605step0 = (fun i j => raw42605 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42605step0 raw42605; decide +kernel
      have hl : raw42605step0Labels = raw42605Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42605 raw42605Labels permutation170 permutation7
    mixedMoment B raw42605step0 raw42605step0Labels = mixedMoment B raw42605step1 raw42605step1Labels := by
      have ha : raw42605step1 = -raw42605step0 := by apply Matrix.ext; change ∀ i j, raw42605step1 i j = -(raw42605step0 i j); unfold raw42605step1 raw42605step0; decide +kernel
      have hl : raw42605step1Labels = raw42605step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42605step1 raw42605step1Labels = mixedMoment B raw42605step2 raw42605step2Labels := by
      have ha : raw42605step2 = raw42605step1 := by apply Matrix.ext; unfold raw42605step2 raw42605step1; decide +kernel
      have hl : raw42605step1Labels = labelEmbedding6 ∘ raw42605step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42605step1 raw42605step1Labels raw42605step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5359 node5359Labels := by rfl

def raw42606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw42606Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42606step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw42606step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42606step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw42606step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42606step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw42606step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42606 raw42606Labels = mixedMoment B node3556 node3556Labels := by
  calc
    mixedMoment B raw42606 raw42606Labels = mixedMoment B raw42606step0 raw42606step0Labels := by
      have ha : raw42606step0 = (fun i j => raw42606 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42606step0 raw42606; decide +kernel
      have hl : raw42606step0Labels = raw42606Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42606 raw42606Labels permutation682 permutation2
    mixedMoment B raw42606step0 raw42606step0Labels = mixedMoment B raw42606step1 raw42606step1Labels := by
      have ha : raw42606step1 = -raw42606step0 := by apply Matrix.ext; change ∀ i j, raw42606step1 i j = -(raw42606step0 i j); unfold raw42606step1 raw42606step0; decide +kernel
      have hl : raw42606step1Labels = raw42606step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42606step1 raw42606step1Labels = mixedMoment B raw42606step2 raw42606step2Labels := by
      have ha : raw42606step2 = raw42606step1 := by apply Matrix.ext; unfold raw42606step2 raw42606step1; decide +kernel
      have hl : raw42606step1Labels = labelEmbedding1 ∘ raw42606step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42606step1 raw42606step1Labels raw42606step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3556 node3556Labels := by rfl

def raw42607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw42607Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42607step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw42607step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42607step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw42607step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42607 raw42607Labels = mixedMoment B node5112 node5112Labels := by
  calc
    mixedMoment B raw42607 raw42607Labels = mixedMoment B raw42607step0 raw42607step0Labels := by
      have ha : raw42607step0 = (fun i j => raw42607 (permutation640 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42607step0 raw42607; decide +kernel
      have hl : raw42607step0Labels = raw42607Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42607 raw42607Labels permutation640 permutation7
    mixedMoment B raw42607step0 raw42607step0Labels = mixedMoment B raw42607step1 raw42607step1Labels := by
      have ha : raw42607step1 = raw42607step0 := by apply Matrix.ext; unfold raw42607step1 raw42607step0; decide +kernel
      have hl : raw42607step0Labels = labelEmbedding6 ∘ raw42607step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42607step0 raw42607step0Labels raw42607step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5112 node5112Labels := by rfl

def raw42608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw42608Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw42608step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw42608step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42608step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw42608step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42608step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw42608step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42608 raw42608Labels = mixedMoment B node3480 node3480Labels := by
  calc
    mixedMoment B raw42608 raw42608Labels = mixedMoment B raw42608step0 raw42608step0Labels := by
      have hz : ∀ j, raw42608 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42608step0 = (fun i j => raw42608 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42608step0 raw42608; decide +kernel
      have hl : raw42608step0Labels = raw42608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42608 raw42608Labels permutation434 hz
    mixedMoment B raw42608step0 raw42608step0Labels = mixedMoment B raw42608step1 raw42608step1Labels := by
      have ha : raw42608step1 = (fun i j => raw42608step0 (permutation116 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42608step1 raw42608step0; decide +kernel
      have hl : raw42608step1Labels = raw42608step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42608step0 raw42608step0Labels permutation116 permutation4
    mixedMoment B raw42608step1 raw42608step1Labels = mixedMoment B raw42608step2 raw42608step2Labels := by
      have ha : raw42608step2 = -raw42608step1 := by apply Matrix.ext; change ∀ i j, raw42608step2 i j = -(raw42608step1 i j); unfold raw42608step2 raw42608step1; decide +kernel
      have hl : raw42608step2Labels = raw42608step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42608step2 raw42608step2Labels = mixedMoment B raw42608step3 raw42608step3Labels := by
      have ha : raw42608step3 = raw42608step2 := by apply Matrix.ext; unfold raw42608step3 raw42608step2; decide +kernel
      have hl : raw42608step2Labels = labelEmbedding1 ∘ raw42608step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42608step2 raw42608step2Labels raw42608step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3480 node3480Labels := by rfl

def raw42609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw42609Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw42609step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42609step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw42609step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42609 raw42609Labels = mixedMoment B node5090 node5090Labels := by
  calc
    mixedMoment B raw42609 raw42609Labels = mixedMoment B raw42609step0 raw42609step0Labels := by
      have hz : ∀ j, raw42609 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42609step0 = (fun i j => raw42609 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42609step0 raw42609; decide +kernel
      have hl : raw42609step0Labels = raw42609Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42609 raw42609Labels permutation434 hz
    mixedMoment B raw42609step0 raw42609step0Labels = mixedMoment B raw42609step1 raw42609step1Labels := by
      have ha : raw42609step1 = (fun i j => raw42609step0 (permutation120 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42609step1 raw42609step0; decide +kernel
      have hl : raw42609step1Labels = raw42609step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42609step0 raw42609step0Labels permutation120 permutation6
    _ = mixedMoment B node5090 node5090Labels := by rfl

def raw42610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw42610Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw42610step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw42610step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42610step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw42610step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42610step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw42610step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42610 raw42610Labels = mixedMoment B node3271 node3271Labels := by
  calc
    mixedMoment B raw42610 raw42610Labels = mixedMoment B raw42610step0 raw42610step0Labels := by
      have hz : ∀ j, raw42610 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42610step0 = (fun i j => raw42610 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42610step0 raw42610; decide +kernel
      have hl : raw42610step0Labels = raw42610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42610 raw42610Labels permutation434 hz
    mixedMoment B raw42610step0 raw42610step0Labels = mixedMoment B raw42610step1 raw42610step1Labels := by
      have ha : raw42610step1 = (fun i j => raw42610step0 (permutation140 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42610step1 raw42610step0; decide +kernel
      have hl : raw42610step1Labels = raw42610step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42610step0 raw42610step0Labels permutation140 permutation4
    mixedMoment B raw42610step1 raw42610step1Labels = mixedMoment B raw42610step2 raw42610step2Labels := by
      have ha : raw42610step2 = -raw42610step1 := by apply Matrix.ext; change ∀ i j, raw42610step2 i j = -(raw42610step1 i j); unfold raw42610step2 raw42610step1; decide +kernel
      have hl : raw42610step2Labels = raw42610step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42610step2 raw42610step2Labels = mixedMoment B raw42610step3 raw42610step3Labels := by
      have ha : raw42610step3 = raw42610step2 := by apply Matrix.ext; unfold raw42610step3 raw42610step2; decide +kernel
      have hl : raw42610step2Labels = labelEmbedding1 ∘ raw42610step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42610step2 raw42610step2Labels raw42610step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3271 node3271Labels := by rfl

def raw42611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw42611Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw42611step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw42611step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42611 raw42611Labels = mixedMoment B node4556 node4556Labels := by
  calc
    mixedMoment B raw42611 raw42611Labels = mixedMoment B raw42611step0 raw42611step0Labels := by
      have hz : ∀ j, raw42611 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42611step0 = (fun i j => raw42611 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42611step0 raw42611; decide +kernel
      have hl : raw42611step0Labels = raw42611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42611 raw42611Labels permutation434 hz
    mixedMoment B raw42611step0 raw42611step0Labels = mixedMoment B raw42611step1 raw42611step1Labels := by
      have ha : raw42611step1 = (fun i j => raw42611step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42611step1 raw42611step0; decide +kernel
      have hl : raw42611step1Labels = raw42611step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42611step0 raw42611step0Labels permutation144 permutation6
    _ = mixedMoment B node4556 node4556Labels := by rfl

def raw42612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42612Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42612step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw42612step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42612step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42612step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42612step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42612step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42612 raw42612Labels = mixedMoment B node3267 node3267Labels := by
  calc
    mixedMoment B raw42612 raw42612Labels = mixedMoment B raw42612step0 raw42612step0Labels := by
      have ha : raw42612step0 = (fun i j => raw42612 (permutation628 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42612step0 raw42612; decide +kernel
      have hl : raw42612step0Labels = raw42612Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42612 raw42612Labels permutation628 permutation4
    mixedMoment B raw42612step0 raw42612step0Labels = mixedMoment B raw42612step1 raw42612step1Labels := by
      have ha : raw42612step1 = -raw42612step0 := by apply Matrix.ext; change ∀ i j, raw42612step1 i j = -(raw42612step0 i j); unfold raw42612step1 raw42612step0; decide +kernel
      have hl : raw42612step1Labels = raw42612step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42612step1 raw42612step1Labels = mixedMoment B raw42612step2 raw42612step2Labels := by
      have ha : raw42612step2 = raw42612step1 := by apply Matrix.ext; unfold raw42612step2 raw42612step1; decide +kernel
      have hl : raw42612step1Labels = labelEmbedding1 ∘ raw42612step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42612step1 raw42612step1Labels raw42612step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3267 node3267Labels := by rfl

def raw42613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42613Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42613step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw42613step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42613 raw42613Labels = mixedMoment B node4533 node4533Labels := by
  calc
    mixedMoment B raw42613 raw42613Labels = mixedMoment B raw42613step0 raw42613step0Labels := by
      have ha : raw42613step0 = (fun i j => raw42613 (permutation645 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42613step0 raw42613; decide +kernel
      have hl : raw42613step0Labels = raw42613Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42613 raw42613Labels permutation645 permutation6
    _ = mixedMoment B node4533 node4533Labels := by rfl

def raw42614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw42614Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42614step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw42614step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42614step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw42614step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42614step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw42614step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42614 raw42614Labels = mixedMoment B node3454 node3454Labels := by
  calc
    mixedMoment B raw42614 raw42614Labels = mixedMoment B raw42614step0 raw42614step0Labels := by
      have ha : raw42614step0 = (fun i j => raw42614 (permutation475 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42614step0 raw42614; decide +kernel
      have hl : raw42614step0Labels = raw42614Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42614 raw42614Labels permutation475 permutation4
    mixedMoment B raw42614step0 raw42614step0Labels = mixedMoment B raw42614step1 raw42614step1Labels := by
      have ha : raw42614step1 = -raw42614step0 := by apply Matrix.ext; change ∀ i j, raw42614step1 i j = -(raw42614step0 i j); unfold raw42614step1 raw42614step0; decide +kernel
      have hl : raw42614step1Labels = raw42614step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42614step1 raw42614step1Labels = mixedMoment B raw42614step2 raw42614step2Labels := by
      have ha : raw42614step2 = raw42614step1 := by apply Matrix.ext; unfold raw42614step2 raw42614step1; decide +kernel
      have hl : raw42614step1Labels = labelEmbedding1 ∘ raw42614step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42614step1 raw42614step1Labels raw42614step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3454 node3454Labels := by rfl

def raw42615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw42615Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42615step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw42615step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42615 raw42615Labels = mixedMoment B node5040 node5040Labels := by
  calc
    mixedMoment B raw42615 raw42615Labels = mixedMoment B raw42615step0 raw42615step0Labels := by
      have ha : raw42615step0 = (fun i j => raw42615 (permutation479 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42615step0 raw42615; decide +kernel
      have hl : raw42615step0Labels = raw42615Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42615 raw42615Labels permutation479 permutation6
    _ = mixedMoment B node5040 node5040Labels := by rfl

def raw42616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw42616Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42616step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw42616step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42616step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42616step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42616step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42616step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42616 raw42616Labels = mixedMoment B node3476 node3476Labels := by
  calc
    mixedMoment B raw42616 raw42616Labels = mixedMoment B raw42616step0 raw42616step0Labels := by
      have ha : raw42616step0 = (fun i j => raw42616 (permutation468 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42616step0 raw42616; decide +kernel
      have hl : raw42616step0Labels = raw42616Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42616 raw42616Labels permutation468 permutation4
    mixedMoment B raw42616step0 raw42616step0Labels = mixedMoment B raw42616step1 raw42616step1Labels := by
      have ha : raw42616step1 = -raw42616step0 := by apply Matrix.ext; change ∀ i j, raw42616step1 i j = -(raw42616step0 i j); unfold raw42616step1 raw42616step0; decide +kernel
      have hl : raw42616step1Labels = raw42616step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42616step1 raw42616step1Labels = mixedMoment B raw42616step2 raw42616step2Labels := by
      have ha : raw42616step2 = raw42616step1 := by apply Matrix.ext; unfold raw42616step2 raw42616step1; decide +kernel
      have hl : raw42616step1Labels = labelEmbedding1 ∘ raw42616step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42616step1 raw42616step1Labels raw42616step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3476 node3476Labels := by rfl

def raw42617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw42617Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42617step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw42617step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42617 raw42617Labels = mixedMoment B node5067 node5067Labels := by
  calc
    mixedMoment B raw42617 raw42617Labels = mixedMoment B raw42617step0 raw42617step0Labels := by
      have ha : raw42617step0 = (fun i j => raw42617 (permutation479 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42617step0 raw42617; decide +kernel
      have hl : raw42617step0Labels = raw42617Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42617 raw42617Labels permutation479 permutation6
    _ = mixedMoment B node5067 node5067Labels := by rfl

def raw42618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw42618Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42618step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42618step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42618step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42618 raw42618Labels = mixedMoment B node3763 node3763Labels := by
  calc
    mixedMoment B raw42618 raw42618Labels = mixedMoment B raw42618step0 raw42618step0Labels := by
      have ha : raw42618step0 = (fun i j => raw42618 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42618step0 raw42618; decide +kernel
      have hl : raw42618step0Labels = raw42618Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42618 raw42618Labels permutation156 permutation2
    mixedMoment B raw42618step0 raw42618step0Labels = mixedMoment B raw42618step1 raw42618step1Labels := by
      have ha : raw42618step1 = raw42618step0 := by apply Matrix.ext; unfold raw42618step1 raw42618step0; decide +kernel
      have hl : raw42618step0Labels = labelEmbedding1 ∘ raw42618step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42618step0 raw42618step0Labels raw42618step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3763 node3763Labels := by rfl

def raw42619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw42619Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42619step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw42619step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42619step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw42619step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42619step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw42619step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42619 raw42619Labels = mixedMoment B node5340 node5340Labels := by
  calc
    mixedMoment B raw42619 raw42619Labels = mixedMoment B raw42619step0 raw42619step0Labels := by
      have ha : raw42619step0 = (fun i j => raw42619 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42619step0 raw42619; decide +kernel
      have hl : raw42619step0Labels = raw42619Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42619 raw42619Labels permutation170 permutation7
    mixedMoment B raw42619step0 raw42619step0Labels = mixedMoment B raw42619step1 raw42619step1Labels := by
      have ha : raw42619step1 = -raw42619step0 := by apply Matrix.ext; change ∀ i j, raw42619step1 i j = -(raw42619step0 i j); unfold raw42619step1 raw42619step0; decide +kernel
      have hl : raw42619step1Labels = raw42619step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42619step1 raw42619step1Labels = mixedMoment B raw42619step2 raw42619step2Labels := by
      have ha : raw42619step2 = raw42619step1 := by apply Matrix.ext; unfold raw42619step2 raw42619step1; decide +kernel
      have hl : raw42619step1Labels = labelEmbedding6 ∘ raw42619step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42619step1 raw42619step1Labels raw42619step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5340 node5340Labels := by rfl

def raw42620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw42620Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw42620step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42620step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 3, -4], ![2, -2, 0]]
def raw42620step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42620step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw42620step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42620step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw42620step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42620step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw42620step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42620 raw42620Labels = mixedMoment B node1740 node1740Labels := by
  calc
    mixedMoment B raw42620 raw42620Labels = mixedMoment B raw42620step0 raw42620step0Labels := by
      have hz : ∀ j, raw42620 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42620step0 = (fun i j => raw42620 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42620step0 raw42620; decide +kernel
      have hl : raw42620step0Labels = raw42620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42620 raw42620Labels permutation434 hz
    mixedMoment B raw42620step0 raw42620step0Labels = mixedMoment B raw42620step1 raw42620step1Labels := by
      have hz : ∀ j, raw42620step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42620step1 = (fun i j => raw42620step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42620step1 raw42620step0; decide +kernel
      have hl : raw42620step1Labels = raw42620step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42620step0 raw42620step0Labels permutation80 hz
    mixedMoment B raw42620step1 raw42620step1Labels = mixedMoment B raw42620step2 raw42620step2Labels := by
      have ha : raw42620step2 = (fun i j => raw42620step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42620step2 raw42620step1; decide +kernel
      have hl : raw42620step2Labels = raw42620step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42620step1 raw42620step1Labels permutation20 permutation4
    mixedMoment B raw42620step2 raw42620step2Labels = mixedMoment B raw42620step3 raw42620step3Labels := by
      have ha : raw42620step3 = -raw42620step2 := by apply Matrix.ext; change ∀ i j, raw42620step3 i j = -(raw42620step2 i j); unfold raw42620step3 raw42620step2; decide +kernel
      have hl : raw42620step3Labels = raw42620step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42620step3 raw42620step3Labels = mixedMoment B raw42620step4 raw42620step4Labels := by
      have ha : raw42620step4 = raw42620step3 := by apply Matrix.ext; unfold raw42620step4 raw42620step3; decide +kernel
      have hl : raw42620step3Labels = labelEmbedding1 ∘ raw42620step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42620step3 raw42620step3Labels raw42620step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1740 node1740Labels := by rfl

def raw42621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw42621Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw42621step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42621step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 3, -4], ![2, -2, 0]]
def raw42621step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42621step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw42621step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42621 raw42621Labels = mixedMoment B node4480 node4480Labels := by
  calc
    mixedMoment B raw42621 raw42621Labels = mixedMoment B raw42621step0 raw42621step0Labels := by
      have hz : ∀ j, raw42621 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42621step0 = (fun i j => raw42621 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42621step0 raw42621; decide +kernel
      have hl : raw42621step0Labels = raw42621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42621 raw42621Labels permutation434 hz
    mixedMoment B raw42621step0 raw42621step0Labels = mixedMoment B raw42621step1 raw42621step1Labels := by
      have hz : ∀ j, raw42621step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42621step1 = (fun i j => raw42621step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42621step1 raw42621step0; decide +kernel
      have hl : raw42621step1Labels = raw42621step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42621step0 raw42621step0Labels permutation80 hz
    mixedMoment B raw42621step1 raw42621step1Labels = mixedMoment B raw42621step2 raw42621step2Labels := by
      have ha : raw42621step2 = (fun i j => raw42621step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42621step2 raw42621step1; decide +kernel
      have hl : raw42621step2Labels = raw42621step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42621step1 raw42621step1Labels permutation24 permutation6
    _ = mixedMoment B node4480 node4480Labels := by rfl

def raw42622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw42622Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw42622step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42622step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -2, 1], ![2, 3, -5]]
def raw42622step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42622step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw42622step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42622step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw42622step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42622step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw42622step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42622 raw42622Labels = mixedMoment B node1526 node1526Labels := by
  calc
    mixedMoment B raw42622 raw42622Labels = mixedMoment B raw42622step0 raw42622step0Labels := by
      have hz : ∀ j, raw42622 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42622step0 = (fun i j => raw42622 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42622step0 raw42622; decide +kernel
      have hl : raw42622step0Labels = raw42622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42622 raw42622Labels permutation434 hz
    mixedMoment B raw42622step0 raw42622step0Labels = mixedMoment B raw42622step1 raw42622step1Labels := by
      have hz : ∀ j, raw42622step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42622step1 = (fun i j => raw42622step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42622step1 raw42622step0; decide +kernel
      have hl : raw42622step1Labels = raw42622step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42622step0 raw42622step0Labels permutation80 hz
    mixedMoment B raw42622step1 raw42622step1Labels = mixedMoment B raw42622step2 raw42622step2Labels := by
      have ha : raw42622step2 = (fun i j => raw42622step1 (permutation26 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42622step2 raw42622step1; decide +kernel
      have hl : raw42622step2Labels = raw42622step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42622step1 raw42622step1Labels permutation26 permutation4
    mixedMoment B raw42622step2 raw42622step2Labels = mixedMoment B raw42622step3 raw42622step3Labels := by
      have ha : raw42622step3 = -raw42622step2 := by apply Matrix.ext; change ∀ i j, raw42622step3 i j = -(raw42622step2 i j); unfold raw42622step3 raw42622step2; decide +kernel
      have hl : raw42622step3Labels = raw42622step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42622step3 raw42622step3Labels = mixedMoment B raw42622step4 raw42622step4Labels := by
      have ha : raw42622step4 = raw42622step3 := by apply Matrix.ext; unfold raw42622step4 raw42622step3; decide +kernel
      have hl : raw42622step3Labels = labelEmbedding1 ∘ raw42622step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42622step3 raw42622step3Labels raw42622step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1526 node1526Labels := by rfl

def raw42623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw42623Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw42623step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42623step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -2, 1], ![2, 3, -5]]
def raw42623step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42623step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw42623step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42623 raw42623Labels = mixedMoment B node4188 node4188Labels := by
  calc
    mixedMoment B raw42623 raw42623Labels = mixedMoment B raw42623step0 raw42623step0Labels := by
      have hz : ∀ j, raw42623 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42623step0 = (fun i j => raw42623 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42623step0 raw42623; decide +kernel
      have hl : raw42623step0Labels = raw42623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42623 raw42623Labels permutation434 hz
    mixedMoment B raw42623step0 raw42623step0Labels = mixedMoment B raw42623step1 raw42623step1Labels := by
      have hz : ∀ j, raw42623step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42623step1 = (fun i j => raw42623step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42623step1 raw42623step0; decide +kernel
      have hl : raw42623step1Labels = raw42623step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42623step0 raw42623step0Labels permutation80 hz
    mixedMoment B raw42623step1 raw42623step1Labels = mixedMoment B raw42623step2 raw42623step2Labels := by
      have ha : raw42623step2 = (fun i j => raw42623step1 (permutation30 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42623step2 raw42623step1; decide +kernel
      have hl : raw42623step2Labels = raw42623step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42623step1 raw42623step1Labels permutation30 permutation6
    _ = mixedMoment B node4188 node4188Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
