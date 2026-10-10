import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw42368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42368Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw42368step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42368step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42368step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42368step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42368 raw42368Labels = mixedMoment B node2678 node2678Labels := by
  calc
    mixedMoment B raw42368 raw42368Labels = mixedMoment B raw42368step0 raw42368step0Labels := by
      have hz : ∀ j, raw42368 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42368step0 = (fun i j => raw42368 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42368step0 raw42368; decide +kernel
      have hl : raw42368step0Labels = raw42368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42368 raw42368Labels permutation434 hz
    mixedMoment B raw42368step0 raw42368step0Labels = mixedMoment B raw42368step1 raw42368step1Labels := by
      have ha : raw42368step1 = (fun i j => raw42368step0 (permutation109 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42368step1 raw42368step0; decide +kernel
      have hl : raw42368step1Labels = raw42368step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42368step0 raw42368step0Labels permutation109 permutation4
    mixedMoment B raw42368step1 raw42368step1Labels = mixedMoment B raw42368step2 raw42368step2Labels := by
      have ha : raw42368step2 = raw42368step1 := by apply Matrix.ext; unfold raw42368step2 raw42368step1; decide +kernel
      have hl : raw42368step1Labels = labelEmbedding1 ∘ raw42368step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42368step1 raw42368step1Labels raw42368step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2678 node2678Labels := by rfl

def raw42369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42369Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw42369step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42369step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42369step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42369step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42369 raw42369Labels = mixedMoment B node5233 node5233Labels := by
  calc
    mixedMoment B raw42369 raw42369Labels = mixedMoment B raw42369step0 raw42369step0Labels := by
      have hz : ∀ j, raw42369 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42369step0 = (fun i j => raw42369 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42369step0 raw42369; decide +kernel
      have hl : raw42369step0Labels = raw42369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42369 raw42369Labels permutation434 hz
    mixedMoment B raw42369step0 raw42369step0Labels = mixedMoment B raw42369step1 raw42369step1Labels := by
      have ha : raw42369step1 = (fun i j => raw42369step0 (permutation109 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42369step1 raw42369step0; decide +kernel
      have hl : raw42369step1Labels = raw42369step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42369step0 raw42369step0Labels permutation109 permutation4
    mixedMoment B raw42369step1 raw42369step1Labels = mixedMoment B raw42369step2 raw42369step2Labels := by
      have ha : raw42369step2 = raw42369step1 := by apply Matrix.ext; unfold raw42369step2 raw42369step1; decide +kernel
      have hl : raw42369step1Labels = labelEmbedding10 ∘ raw42369step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42369step1 raw42369step1Labels raw42369step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5233 node5233Labels := by rfl

def raw42370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42370Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42370step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42370step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42370step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42370 raw42370Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw42370 raw42370Labels = mixedMoment B raw42370step0 raw42370step0Labels := by
      have ha : raw42370step0 = (fun i j => raw42370 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42370step0 raw42370; decide +kernel
      have hl : raw42370step0Labels = raw42370Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42370 raw42370Labels permutation158 permutation2
    mixedMoment B raw42370step0 raw42370step0Labels = mixedMoment B raw42370step1 raw42370step1Labels := by
      have ha : raw42370step1 = raw42370step0 := by apply Matrix.ext; unfold raw42370step1 raw42370step0; decide +kernel
      have hl : raw42370step0Labels = labelEmbedding1 ∘ raw42370step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42370step0 raw42370step0Labels raw42370step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3872 node3872Labels := by rfl

def raw42371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42371Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42371step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42371step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42371step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42371step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42371step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42371 raw42371Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw42371 raw42371Labels = mixedMoment B raw42371step0 raw42371step0Labels := by
      have ha : raw42371step0 = (fun i j => raw42371 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42371step0 raw42371; decide +kernel
      have hl : raw42371step0Labels = raw42371Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42371 raw42371Labels permutation688 permutation3
    mixedMoment B raw42371step0 raw42371step0Labels = mixedMoment B raw42371step1 raw42371step1Labels := by
      have ha : raw42371step1 = -raw42371step0 := by apply Matrix.ext; change ∀ i j, raw42371step1 i j = -(raw42371step0 i j); unfold raw42371step1 raw42371step0; decide +kernel
      have hl : raw42371step1Labels = raw42371step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42371step1 raw42371step1Labels = mixedMoment B raw42371step2 raw42371step2Labels := by
      have ha : raw42371step2 = raw42371step1 := by apply Matrix.ext; unfold raw42371step2 raw42371step1; decide +kernel
      have hl : raw42371step1Labels = labelEmbedding7 ∘ raw42371step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42371step1 raw42371step1Labels raw42371step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw42372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42372Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42372step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42372step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42372step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42372 raw42372Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw42372 raw42372Labels = mixedMoment B raw42372step0 raw42372step0Labels := by
      have ha : raw42372step0 = (fun i j => raw42372 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42372step0 raw42372; decide +kernel
      have hl : raw42372step0Labels = raw42372Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42372 raw42372Labels permutation158 permutation2
    mixedMoment B raw42372step0 raw42372step0Labels = mixedMoment B raw42372step1 raw42372step1Labels := by
      have ha : raw42372step1 = raw42372step0 := by apply Matrix.ext; unfold raw42372step1 raw42372step0; decide +kernel
      have hl : raw42372step0Labels = labelEmbedding1 ∘ raw42372step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42372step0 raw42372step0Labels raw42372step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3871 node3871Labels := by rfl

def raw42373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42373Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw42373step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42373step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42373step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42373step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42373step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42373 raw42373Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw42373 raw42373Labels = mixedMoment B raw42373step0 raw42373step0Labels := by
      have ha : raw42373step0 = (fun i j => raw42373 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42373step0 raw42373; decide +kernel
      have hl : raw42373step0Labels = raw42373Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42373 raw42373Labels permutation212 permutation7
    mixedMoment B raw42373step0 raw42373step0Labels = mixedMoment B raw42373step1 raw42373step1Labels := by
      have ha : raw42373step1 = -raw42373step0 := by apply Matrix.ext; change ∀ i j, raw42373step1 i j = -(raw42373step0 i j); unfold raw42373step1 raw42373step0; decide +kernel
      have hl : raw42373step1Labels = raw42373step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42373step1 raw42373step1Labels = mixedMoment B raw42373step2 raw42373step2Labels := by
      have ha : raw42373step2 = raw42373step1 := by apply Matrix.ext; unfold raw42373step2 raw42373step1; decide +kernel
      have hl : raw42373step1Labels = labelEmbedding6 ∘ raw42373step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42373step1 raw42373step1Labels raw42373step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw42374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42374Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42374step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42374step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42374step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42374step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42374 raw42374Labels = mixedMoment B node3870 node3870Labels := by
  calc
    mixedMoment B raw42374 raw42374Labels = mixedMoment B raw42374step0 raw42374step0Labels := by
      have ha : raw42374step0 = (fun i j => raw42374 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42374step0 raw42374; decide +kernel
      have hl : raw42374step0Labels = raw42374Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42374 raw42374Labels permutation158 permutation2
    mixedMoment B raw42374step0 raw42374step0Labels = mixedMoment B raw42374step1 raw42374step1Labels := by
      have ha : raw42374step1 = raw42374step0 := by apply Matrix.ext; unfold raw42374step1 raw42374step0; decide +kernel
      have hl : raw42374step0Labels = labelEmbedding1 ∘ raw42374step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42374step0 raw42374step0Labels raw42374step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3870 node3870Labels := by rfl

def raw42375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42375Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42375step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42375step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42375step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42375step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42375 raw42375Labels = mixedMoment B node5420 node5420Labels := by
  calc
    mixedMoment B raw42375 raw42375Labels = mixedMoment B raw42375step0 raw42375step0Labels := by
      have ha : raw42375step0 = (fun i j => raw42375 (permutation634 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42375step0 raw42375; decide +kernel
      have hl : raw42375step0Labels = raw42375Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42375 raw42375Labels permutation634 permutation7
    mixedMoment B raw42375step0 raw42375step0Labels = mixedMoment B raw42375step1 raw42375step1Labels := by
      have ha : raw42375step1 = raw42375step0 := by apply Matrix.ext; unfold raw42375step1 raw42375step0; decide +kernel
      have hl : raw42375step0Labels = labelEmbedding6 ∘ raw42375step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42375step0 raw42375step0Labels raw42375step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5420 node5420Labels := by rfl

def raw42376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42376Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42376step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42376step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42376step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42376 raw42376Labels = mixedMoment B node3834 node3834Labels := by
  calc
    mixedMoment B raw42376 raw42376Labels = mixedMoment B raw42376step0 raw42376step0Labels := by
      have ha : raw42376step0 = (fun i j => raw42376 (permutation488 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42376step0 raw42376; decide +kernel
      have hl : raw42376step0Labels = raw42376Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42376 raw42376Labels permutation488 permutation4
    mixedMoment B raw42376step0 raw42376step0Labels = mixedMoment B raw42376step1 raw42376step1Labels := by
      have ha : raw42376step1 = raw42376step0 := by apply Matrix.ext; unfold raw42376step1 raw42376step0; decide +kernel
      have hl : raw42376step0Labels = labelEmbedding1 ∘ raw42376step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42376step0 raw42376step0Labels raw42376step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3834 node3834Labels := by rfl

def raw42377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42377Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42377step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42377step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42377step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42377 raw42377Labels = mixedMoment B node5381 node5381Labels := by
  calc
    mixedMoment B raw42377 raw42377Labels = mixedMoment B raw42377step0 raw42377step0Labels := by
      have ha : raw42377step0 = (fun i j => raw42377 (permutation445 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42377step0 raw42377; decide +kernel
      have hl : raw42377step0Labels = raw42377Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42377 raw42377Labels permutation445 permutation6
    mixedMoment B raw42377step0 raw42377step0Labels = mixedMoment B raw42377step1 raw42377step1Labels := by
      have ha : raw42377step1 = -raw42377step0 := by apply Matrix.ext; change ∀ i j, raw42377step1 i j = -(raw42377step0 i j); unfold raw42377step1 raw42377step0; decide +kernel
      have hl : raw42377step1Labels = raw42377step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5381 node5381Labels := by rfl

def raw42378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42378Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42378step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42378step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42378step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42378 raw42378Labels = mixedMoment B node2662 node2662Labels := by
  calc
    mixedMoment B raw42378 raw42378Labels = mixedMoment B raw42378step0 raw42378step0Labels := by
      have ha : raw42378step0 = (fun i j => raw42378 (permutation598 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42378step0 raw42378; decide +kernel
      have hl : raw42378step0Labels = raw42378Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42378 raw42378Labels permutation598 permutation4
    mixedMoment B raw42378step0 raw42378step0Labels = mixedMoment B raw42378step1 raw42378step1Labels := by
      have ha : raw42378step1 = raw42378step0 := by apply Matrix.ext; unfold raw42378step1 raw42378step0; decide +kernel
      have hl : raw42378step0Labels = labelEmbedding1 ∘ raw42378step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42378step0 raw42378step0Labels raw42378step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2662 node2662Labels := by rfl

def raw42379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42379Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42379step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42379step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42379step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42379step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42379 raw42379Labels = mixedMoment B node5220 node5220Labels := by
  calc
    mixedMoment B raw42379 raw42379Labels = mixedMoment B raw42379step0 raw42379step0Labels := by
      have ha : raw42379step0 = (fun i j => raw42379 (permutation598 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42379step0 raw42379; decide +kernel
      have hl : raw42379step0Labels = raw42379Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42379 raw42379Labels permutation598 permutation4
    mixedMoment B raw42379step0 raw42379step0Labels = mixedMoment B raw42379step1 raw42379step1Labels := by
      have ha : raw42379step1 = raw42379step0 := by apply Matrix.ext; unfold raw42379step1 raw42379step0; decide +kernel
      have hl : raw42379step0Labels = labelEmbedding10 ∘ raw42379step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42379step0 raw42379step0Labels raw42379step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5220 node5220Labels := by rfl

def raw42380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42380Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42380step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42380step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42380step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42380 raw42380Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw42380 raw42380Labels = mixedMoment B raw42380step0 raw42380step0Labels := by
      have ha : raw42380step0 = (fun i j => raw42380 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42380step0 raw42380; decide +kernel
      have hl : raw42380step0Labels = raw42380Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42380 raw42380Labels permutation157 permutation2
    mixedMoment B raw42380step0 raw42380step0Labels = mixedMoment B raw42380step1 raw42380step1Labels := by
      have ha : raw42380step1 = raw42380step0 := by apply Matrix.ext; unfold raw42380step1 raw42380step0; decide +kernel
      have hl : raw42380step0Labels = labelEmbedding1 ∘ raw42380step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42380step0 raw42380step0Labels raw42380step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3880 node3880Labels := by rfl

def raw42381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42381Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42381step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42381step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42381step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42381step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42381 raw42381Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw42381 raw42381Labels = mixedMoment B raw42381step0 raw42381step0Labels := by
      have ha : raw42381step0 = (fun i j => raw42381 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42381step0 raw42381; decide +kernel
      have hl : raw42381step0Labels = raw42381Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42381 raw42381Labels permutation157 permutation2
    mixedMoment B raw42381step0 raw42381step0Labels = mixedMoment B raw42381step1 raw42381step1Labels := by
      have ha : raw42381step1 = raw42381step0 := by apply Matrix.ext; unfold raw42381step1 raw42381step0; decide +kernel
      have hl : raw42381step0Labels = labelEmbedding8 ∘ raw42381step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42381step0 raw42381step0Labels raw42381step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

def raw42382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42382Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42382step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42382step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42382 raw42382Labels = mixedMoment B node3882 node3882Labels := by
  calc
    mixedMoment B raw42382 raw42382Labels = mixedMoment B raw42382step0 raw42382step0Labels := by
      have ha : raw42382step0 = raw42382 := by apply Matrix.ext; unfold raw42382step0 raw42382; decide +kernel
      have hl : raw42382Labels = labelEmbedding1 ∘ raw42382step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42382 raw42382Labels raw42382step0Labels labelEmbedding1 hl
    _ = mixedMoment B node3882 node3882Labels := by rfl

def raw42383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42383Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42383step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42383 raw42383Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw42383 raw42383Labels = mixedMoment B raw42383step0 raw42383step0Labels := by
      have ha : raw42383step0 = raw42383 := by apply Matrix.ext; unfold raw42383step0 raw42383; decide +kernel
      have hl : raw42383Labels = labelEmbedding8 ∘ raw42383step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42383 raw42383Labels raw42383step0Labels labelEmbedding8 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

def raw42384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42384Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42384step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42384step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42384step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42384step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw42384step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42384step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw42384step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42384 raw42384Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw42384 raw42384Labels = mixedMoment B raw42384step0 raw42384step0Labels := by
      have hz : ∀ j, raw42384 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42384step0 = (fun i j => raw42384 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42384step0 raw42384; decide +kernel
      have hl : raw42384step0Labels = raw42384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42384 raw42384Labels permutation434 hz
    mixedMoment B raw42384step0 raw42384step0Labels = mixedMoment B raw42384step1 raw42384step1Labels := by
      have hz : ∀ j, raw42384step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42384step1 = (fun i j => raw42384step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42384step1 raw42384step0; decide +kernel
      have hl : raw42384step1Labels = raw42384step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42384step0 raw42384step0Labels permutation80 hz
    mixedMoment B raw42384step1 raw42384step1Labels = mixedMoment B raw42384step2 raw42384step2Labels := by
      have ha : raw42384step2 = (fun i j => raw42384step1 (permutation27 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42384step2 raw42384step1; decide +kernel
      have hl : raw42384step2Labels = raw42384step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42384step1 raw42384step1Labels permutation27 permutation4
    mixedMoment B raw42384step2 raw42384step2Labels = mixedMoment B raw42384step3 raw42384step3Labels := by
      have ha : raw42384step3 = raw42384step2 := by apply Matrix.ext; unfold raw42384step3 raw42384step2; decide +kernel
      have hl : raw42384step2Labels = labelEmbedding1 ∘ raw42384step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42384step2 raw42384step2Labels raw42384step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3055 node3055Labels := by rfl

def raw42385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42385Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42385step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42385step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42385step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42385step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42385step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42385step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42385step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42385 raw42385Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw42385 raw42385Labels = mixedMoment B raw42385step0 raw42385step0Labels := by
      have hz : ∀ j, raw42385 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42385step0 = (fun i j => raw42385 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42385step0 raw42385; decide +kernel
      have hl : raw42385step0Labels = raw42385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42385 raw42385Labels permutation434 hz
    mixedMoment B raw42385step0 raw42385step0Labels = mixedMoment B raw42385step1 raw42385step1Labels := by
      have hz : ∀ j, raw42385step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42385step1 = (fun i j => raw42385step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42385step1 raw42385step0; decide +kernel
      have hl : raw42385step1Labels = raw42385step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42385step0 raw42385step0Labels permutation80 hz
    mixedMoment B raw42385step1 raw42385step1Labels = mixedMoment B raw42385step2 raw42385step2Labels := by
      have ha : raw42385step2 = (fun i j => raw42385step1 (permutation27 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42385step2 raw42385step1; decide +kernel
      have hl : raw42385step2Labels = raw42385step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42385step1 raw42385step1Labels permutation27 permutation5
    mixedMoment B raw42385step2 raw42385step2Labels = mixedMoment B raw42385step3 raw42385step3Labels := by
      have ha : raw42385step3 = raw42385step2 := by apply Matrix.ext; unfold raw42385step3 raw42385step2; decide +kernel
      have hl : raw42385step2Labels = labelEmbedding9 ∘ raw42385step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42385step2 raw42385step2Labels raw42385step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5300 node5300Labels := by rfl

def raw42386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42386Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42386step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42386step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -3, 2], ![2, 1, -3]]
def raw42386step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42386step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw42386step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42386step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw42386step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42386 raw42386Labels = mixedMoment B node2687 node2687Labels := by
  calc
    mixedMoment B raw42386 raw42386Labels = mixedMoment B raw42386step0 raw42386step0Labels := by
      have hz : ∀ j, raw42386 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42386step0 = (fun i j => raw42386 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42386step0 raw42386; decide +kernel
      have hl : raw42386step0Labels = raw42386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42386 raw42386Labels permutation434 hz
    mixedMoment B raw42386step0 raw42386step0Labels = mixedMoment B raw42386step1 raw42386step1Labels := by
      have hz : ∀ j, raw42386step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42386step1 = (fun i j => raw42386step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42386step1 raw42386step0; decide +kernel
      have hl : raw42386step1Labels = raw42386step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42386step0 raw42386step0Labels permutation80 hz
    mixedMoment B raw42386step1 raw42386step1Labels = mixedMoment B raw42386step2 raw42386step2Labels := by
      have ha : raw42386step2 = (fun i j => raw42386step1 (permutation21 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42386step2 raw42386step1; decide +kernel
      have hl : raw42386step2Labels = raw42386step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42386step1 raw42386step1Labels permutation21 permutation4
    mixedMoment B raw42386step2 raw42386step2Labels = mixedMoment B raw42386step3 raw42386step3Labels := by
      have ha : raw42386step3 = raw42386step2 := by apply Matrix.ext; unfold raw42386step3 raw42386step2; decide +kernel
      have hl : raw42386step2Labels = labelEmbedding1 ∘ raw42386step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42386step2 raw42386step2Labels raw42386step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2687 node2687Labels := by rfl

def raw42387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42387Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42387step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42387step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -3, 2], ![2, 1, -3]]
def raw42387step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42387step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw42387step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42387step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw42387step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42387 raw42387Labels = mixedMoment B node5206 node5206Labels := by
  calc
    mixedMoment B raw42387 raw42387Labels = mixedMoment B raw42387step0 raw42387step0Labels := by
      have hz : ∀ j, raw42387 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42387step0 = (fun i j => raw42387 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42387step0 raw42387; decide +kernel
      have hl : raw42387step0Labels = raw42387Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42387 raw42387Labels permutation434 hz
    mixedMoment B raw42387step0 raw42387step0Labels = mixedMoment B raw42387step1 raw42387step1Labels := by
      have hz : ∀ j, raw42387step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42387step1 = (fun i j => raw42387step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42387step1 raw42387step0; decide +kernel
      have hl : raw42387step1Labels = raw42387step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42387step0 raw42387step0Labels permutation80 hz
    mixedMoment B raw42387step1 raw42387step1Labels = mixedMoment B raw42387step2 raw42387step2Labels := by
      have ha : raw42387step2 = (fun i j => raw42387step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42387step2 raw42387step1; decide +kernel
      have hl : raw42387step2Labels = raw42387step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42387step1 raw42387step1Labels permutation29 permutation7
    mixedMoment B raw42387step2 raw42387step2Labels = mixedMoment B raw42387step3 raw42387step3Labels := by
      have ha : raw42387step3 = raw42387step2 := by apply Matrix.ext; unfold raw42387step3 raw42387step2; decide +kernel
      have hl : raw42387step2Labels = labelEmbedding6 ∘ raw42387step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42387step2 raw42387step2Labels raw42387step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5206 node5206Labels := by rfl

def raw42388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42388Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42388step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42388step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42388 raw42388Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw42388 raw42388Labels = mixedMoment B raw42388step0 raw42388step0Labels := by
      have hz : ∀ j, raw42388 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42388step0 = (fun i j => raw42388 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42388step0 raw42388; decide +kernel
      have hl : raw42388step0Labels = raw42388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42388 raw42388Labels permutation346 hz
    mixedMoment B raw42388step0 raw42388step0Labels = mixedMoment B raw42388step1 raw42388step1Labels := by
      have ha : raw42388step1 = raw42388step0 := by apply Matrix.ext; unfold raw42388step1 raw42388step0; decide +kernel
      have hl : raw42388step0Labels = labelEmbedding1 ∘ raw42388step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42388step0 raw42388step0Labels raw42388step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3877 node3877Labels := by rfl

def raw42389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42389Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42389step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42389step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42389step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42389step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42389step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42389 raw42389Labels = mixedMoment B node5436 node5436Labels := by
  calc
    mixedMoment B raw42389 raw42389Labels = mixedMoment B raw42389step0 raw42389step0Labels := by
      have hz : ∀ j, raw42389 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42389step0 = (fun i j => raw42389 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42389step0 raw42389; decide +kernel
      have hl : raw42389step0Labels = raw42389Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42389 raw42389Labels permutation346 hz
    mixedMoment B raw42389step0 raw42389step0Labels = mixedMoment B raw42389step1 raw42389step1Labels := by
      have ha : raw42389step1 = (fun i j => raw42389step0 (permutation141 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42389step1 raw42389step0; decide +kernel
      have hl : raw42389step1Labels = raw42389step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42389step0 raw42389step0Labels permutation141 permutation5
    mixedMoment B raw42389step1 raw42389step1Labels = mixedMoment B raw42389step2 raw42389step2Labels := by
      have ha : raw42389step2 = raw42389step1 := by apply Matrix.ext; unfold raw42389step2 raw42389step1; decide +kernel
      have hl : raw42389step1Labels = labelEmbedding9 ∘ raw42389step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42389step1 raw42389step1Labels raw42389step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5436 node5436Labels := by rfl

def raw42390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42390Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42390step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42390step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw42390step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42390step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42390step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42390step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42390step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42390 raw42390Labels = mixedMoment B node3570 node3570Labels := by
  calc
    mixedMoment B raw42390 raw42390Labels = mixedMoment B raw42390step0 raw42390step0Labels := by
      have hz : ∀ j, raw42390 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42390step0 = (fun i j => raw42390 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42390step0 raw42390; decide +kernel
      have hl : raw42390step0Labels = raw42390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42390 raw42390Labels permutation346 hz
    mixedMoment B raw42390step0 raw42390step0Labels = mixedMoment B raw42390step1 raw42390step1Labels := by
      have ha : raw42390step1 = (fun i j => raw42390step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42390step1 raw42390step0; decide +kernel
      have hl : raw42390step1Labels = raw42390step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42390step0 raw42390step0Labels permutation151 permutation2
    mixedMoment B raw42390step1 raw42390step1Labels = mixedMoment B raw42390step2 raw42390step2Labels := by
      have ha : raw42390step2 = -raw42390step1 := by apply Matrix.ext; change ∀ i j, raw42390step2 i j = -(raw42390step1 i j); unfold raw42390step2 raw42390step1; decide +kernel
      have hl : raw42390step2Labels = raw42390step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42390step2 raw42390step2Labels = mixedMoment B raw42390step3 raw42390step3Labels := by
      have ha : raw42390step3 = raw42390step2 := by apply Matrix.ext; unfold raw42390step3 raw42390step2; decide +kernel
      have hl : raw42390step2Labels = labelEmbedding1 ∘ raw42390step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42390step2 raw42390step2Labels raw42390step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3570 node3570Labels := by rfl

def raw42391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42391Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42391step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42391step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42391step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42391step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42391step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42391 raw42391Labels = mixedMoment B node5198 node5198Labels := by
  calc
    mixedMoment B raw42391 raw42391Labels = mixedMoment B raw42391step0 raw42391step0Labels := by
      have hz : ∀ j, raw42391 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42391step0 = (fun i j => raw42391 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42391step0 raw42391; decide +kernel
      have hl : raw42391step0Labels = raw42391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42391 raw42391Labels permutation346 hz
    mixedMoment B raw42391step0 raw42391step0Labels = mixedMoment B raw42391step1 raw42391step1Labels := by
      have ha : raw42391step1 = (fun i j => raw42391step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42391step1 raw42391step0; decide +kernel
      have hl : raw42391step1Labels = raw42391step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42391step0 raw42391step0Labels permutation139 permutation7
    mixedMoment B raw42391step1 raw42391step1Labels = mixedMoment B raw42391step2 raw42391step2Labels := by
      have ha : raw42391step2 = raw42391step1 := by apply Matrix.ext; unfold raw42391step2 raw42391step1; decide +kernel
      have hl : raw42391step1Labels = labelEmbedding6 ∘ raw42391step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42391step1 raw42391step1Labels raw42391step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5198 node5198Labels := by rfl

def raw42392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42392Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42392step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42392step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw42392step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42392step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw42392step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42392step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw42392step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42392 raw42392Labels = mixedMoment B node3538 node3538Labels := by
  calc
    mixedMoment B raw42392 raw42392Labels = mixedMoment B raw42392step0 raw42392step0Labels := by
      have hz : ∀ j, raw42392 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42392step0 = (fun i j => raw42392 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42392step0 raw42392; decide +kernel
      have hl : raw42392step0Labels = raw42392Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42392 raw42392Labels permutation346 hz
    mixedMoment B raw42392step0 raw42392step0Labels = mixedMoment B raw42392step1 raw42392step1Labels := by
      have ha : raw42392step1 = (fun i j => raw42392step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42392step1 raw42392step0; decide +kernel
      have hl : raw42392step1Labels = raw42392step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42392step0 raw42392step0Labels permutation151 permutation2
    mixedMoment B raw42392step1 raw42392step1Labels = mixedMoment B raw42392step2 raw42392step2Labels := by
      have ha : raw42392step2 = -raw42392step1 := by apply Matrix.ext; change ∀ i j, raw42392step2 i j = -(raw42392step1 i j); unfold raw42392step2 raw42392step1; decide +kernel
      have hl : raw42392step2Labels = raw42392step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42392step2 raw42392step2Labels = mixedMoment B raw42392step3 raw42392step3Labels := by
      have ha : raw42392step3 = raw42392step2 := by apply Matrix.ext; unfold raw42392step3 raw42392step2; decide +kernel
      have hl : raw42392step2Labels = labelEmbedding1 ∘ raw42392step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42392step2 raw42392step2Labels raw42392step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3538 node3538Labels := by rfl

def raw42393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42393Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42393step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42393step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw42393step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42393step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw42393step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42393 raw42393Labels = mixedMoment B node5188 node5188Labels := by
  calc
    mixedMoment B raw42393 raw42393Labels = mixedMoment B raw42393step0 raw42393step0Labels := by
      have hz : ∀ j, raw42393 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42393step0 = (fun i j => raw42393 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42393step0 raw42393; decide +kernel
      have hl : raw42393step0Labels = raw42393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42393 raw42393Labels permutation346 hz
    mixedMoment B raw42393step0 raw42393step0Labels = mixedMoment B raw42393step1 raw42393step1Labels := by
      have ha : raw42393step1 = (fun i j => raw42393step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42393step1 raw42393step0; decide +kernel
      have hl : raw42393step1Labels = raw42393step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42393step0 raw42393step0Labels permutation139 permutation7
    mixedMoment B raw42393step1 raw42393step1Labels = mixedMoment B raw42393step2 raw42393step2Labels := by
      have ha : raw42393step2 = raw42393step1 := by apply Matrix.ext; unfold raw42393step2 raw42393step1; decide +kernel
      have hl : raw42393step1Labels = labelEmbedding6 ∘ raw42393step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42393step1 raw42393step1Labels raw42393step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5188 node5188Labels := by rfl

def raw42394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw42394Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw42394step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42394step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw42394step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42394step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw42394step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42394 raw42394Labels = mixedMoment B node2673 node2673Labels := by
  calc
    mixedMoment B raw42394 raw42394Labels = mixedMoment B raw42394step0 raw42394step0Labels := by
      have hz : ∀ j, raw42394 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42394step0 = (fun i j => raw42394 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42394step0 raw42394; decide +kernel
      have hl : raw42394step0Labels = raw42394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42394 raw42394Labels permutation346 hz
    mixedMoment B raw42394step0 raw42394step0Labels = mixedMoment B raw42394step1 raw42394step1Labels := by
      have ha : raw42394step1 = (fun i j => raw42394step0 (permutation133 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42394step1 raw42394step0; decide +kernel
      have hl : raw42394step1Labels = raw42394step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42394step0 raw42394step0Labels permutation133 permutation4
    mixedMoment B raw42394step1 raw42394step1Labels = mixedMoment B raw42394step2 raw42394step2Labels := by
      have ha : raw42394step2 = raw42394step1 := by apply Matrix.ext; unfold raw42394step2 raw42394step1; decide +kernel
      have hl : raw42394step1Labels = labelEmbedding1 ∘ raw42394step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42394step1 raw42394step1Labels raw42394step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2673 node2673Labels := by rfl

def raw42395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw42395Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw42395step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw42395step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42395step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw42395step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42395 raw42395Labels = mixedMoment B node5229 node5229Labels := by
  calc
    mixedMoment B raw42395 raw42395Labels = mixedMoment B raw42395step0 raw42395step0Labels := by
      have hz : ∀ j, raw42395 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42395step0 = (fun i j => raw42395 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42395step0 raw42395; decide +kernel
      have hl : raw42395step0Labels = raw42395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42395 raw42395Labels permutation346 hz
    mixedMoment B raw42395step0 raw42395step0Labels = mixedMoment B raw42395step1 raw42395step1Labels := by
      have ha : raw42395step1 = (fun i j => raw42395step0 (permutation133 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42395step1 raw42395step0; decide +kernel
      have hl : raw42395step1Labels = raw42395step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42395step0 raw42395step0Labels permutation133 permutation4
    mixedMoment B raw42395step1 raw42395step1Labels = mixedMoment B raw42395step2 raw42395step2Labels := by
      have ha : raw42395step2 = raw42395step1 := by apply Matrix.ext; unfold raw42395step2 raw42395step1; decide +kernel
      have hl : raw42395step1Labels = labelEmbedding10 ∘ raw42395step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42395step1 raw42395step1Labels raw42395step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5229 node5229Labels := by rfl

def raw42396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42396Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42396step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42396step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42396step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42396step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42396step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42396 raw42396Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw42396 raw42396Labels = mixedMoment B raw42396step0 raw42396step0Labels := by
      have hz : ∀ j, raw42396 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42396step0 = (fun i j => raw42396 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42396step0 raw42396; decide +kernel
      have hl : raw42396step0Labels = raw42396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42396 raw42396Labels permutation346 hz
    mixedMoment B raw42396step0 raw42396step0Labels = mixedMoment B raw42396step1 raw42396step1Labels := by
      have ha : raw42396step1 = (fun i j => raw42396step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42396step1 raw42396step0; decide +kernel
      have hl : raw42396step1Labels = raw42396step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42396step0 raw42396step0Labels permutation37 permutation2
    mixedMoment B raw42396step1 raw42396step1Labels = mixedMoment B raw42396step2 raw42396step2Labels := by
      have ha : raw42396step2 = raw42396step1 := by apply Matrix.ext; unfold raw42396step2 raw42396step1; decide +kernel
      have hl : raw42396step1Labels = labelEmbedding1 ∘ raw42396step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42396step1 raw42396step1Labels raw42396step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3884 node3884Labels := by rfl

def raw42397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42397Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42397step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42397step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42397step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42397step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42397step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42397step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42397 raw42397Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw42397 raw42397Labels = mixedMoment B raw42397step0 raw42397step0Labels := by
      have hz : ∀ j, raw42397 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42397step0 = (fun i j => raw42397 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42397step0 raw42397; decide +kernel
      have hl : raw42397step0Labels = raw42397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42397 raw42397Labels permutation346 hz
    mixedMoment B raw42397step0 raw42397step0Labels = mixedMoment B raw42397step1 raw42397step1Labels := by
      have ha : raw42397step1 = (fun i j => raw42397step0 (permutation54 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42397step1 raw42397step0; decide +kernel
      have hl : raw42397step1Labels = raw42397step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42397step0 raw42397step0Labels permutation54 permutation7
    mixedMoment B raw42397step1 raw42397step1Labels = mixedMoment B raw42397step2 raw42397step2Labels := by
      have ha : raw42397step2 = -raw42397step1 := by apply Matrix.ext; change ∀ i j, raw42397step2 i j = -(raw42397step1 i j); unfold raw42397step2 raw42397step1; decide +kernel
      have hl : raw42397step2Labels = raw42397step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42397step2 raw42397step2Labels = mixedMoment B raw42397step3 raw42397step3Labels := by
      have ha : raw42397step3 = raw42397step2 := by apply Matrix.ext; unfold raw42397step3 raw42397step2; decide +kernel
      have hl : raw42397step2Labels = labelEmbedding6 ∘ raw42397step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42397step2 raw42397step2Labels raw42397step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw42398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42398Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw42398step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42398step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42398step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42398step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42398step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42398 raw42398Labels = mixedMoment B node3524 node3524Labels := by
  calc
    mixedMoment B raw42398 raw42398Labels = mixedMoment B raw42398step0 raw42398step0Labels := by
      have ha : raw42398step0 = (fun i j => raw42398 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42398step0 raw42398; decide +kernel
      have hl : raw42398step0Labels = raw42398Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42398 raw42398Labels permutation682 permutation2
    mixedMoment B raw42398step0 raw42398step0Labels = mixedMoment B raw42398step1 raw42398step1Labels := by
      have ha : raw42398step1 = -raw42398step0 := by apply Matrix.ext; change ∀ i j, raw42398step1 i j = -(raw42398step0 i j); unfold raw42398step1 raw42398step0; decide +kernel
      have hl : raw42398step1Labels = raw42398step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42398step1 raw42398step1Labels = mixedMoment B raw42398step2 raw42398step2Labels := by
      have ha : raw42398step2 = raw42398step1 := by apply Matrix.ext; unfold raw42398step2 raw42398step1; decide +kernel
      have hl : raw42398step1Labels = labelEmbedding1 ∘ raw42398step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42398step1 raw42398step1Labels raw42398step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3524 node3524Labels := by rfl

def raw42399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42399Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42399step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42399step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42399step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42399step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42399 raw42399Labels = mixedMoment B node5184 node5184Labels := by
  calc
    mixedMoment B raw42399 raw42399Labels = mixedMoment B raw42399step0 raw42399step0Labels := by
      have ha : raw42399step0 = (fun i j => raw42399 (permutation620 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42399step0 raw42399; decide +kernel
      have hl : raw42399step0Labels = raw42399Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42399 raw42399Labels permutation620 permutation7
    mixedMoment B raw42399step0 raw42399step0Labels = mixedMoment B raw42399step1 raw42399step1Labels := by
      have ha : raw42399step1 = raw42399step0 := by apply Matrix.ext; unfold raw42399step1 raw42399step0; decide +kernel
      have hl : raw42399step0Labels = labelEmbedding6 ∘ raw42399step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42399step0 raw42399step0Labels raw42399step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5184 node5184Labels := by rfl

def raw42400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42400Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42400step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42400step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42400step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42400step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42400 raw42400Labels = mixedMoment B node3873 node3873Labels := by
  calc
    mixedMoment B raw42400 raw42400Labels = mixedMoment B raw42400step0 raw42400step0Labels := by
      have ha : raw42400step0 = (fun i j => raw42400 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42400step0 raw42400; decide +kernel
      have hl : raw42400step0Labels = raw42400Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42400 raw42400Labels permutation157 permutation2
    mixedMoment B raw42400step0 raw42400step0Labels = mixedMoment B raw42400step1 raw42400step1Labels := by
      have ha : raw42400step1 = raw42400step0 := by apply Matrix.ext; unfold raw42400step1 raw42400step0; decide +kernel
      have hl : raw42400step0Labels = labelEmbedding1 ∘ raw42400step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42400step0 raw42400step0Labels raw42400step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3873 node3873Labels := by rfl

def raw42401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42401Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42401step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42401step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42401step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw42401step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42401step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw42401step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42401 raw42401Labels = mixedMoment B node5421 node5421Labels := by
  calc
    mixedMoment B raw42401 raw42401Labels = mixedMoment B raw42401step0 raw42401step0Labels := by
      have ha : raw42401step0 = (fun i j => raw42401 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42401step0 raw42401; decide +kernel
      have hl : raw42401step0Labels = raw42401Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42401 raw42401Labels permutation195 permutation7
    mixedMoment B raw42401step0 raw42401step0Labels = mixedMoment B raw42401step1 raw42401step1Labels := by
      have ha : raw42401step1 = -raw42401step0 := by apply Matrix.ext; change ∀ i j, raw42401step1 i j = -(raw42401step0 i j); unfold raw42401step1 raw42401step0; decide +kernel
      have hl : raw42401step1Labels = raw42401step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42401step1 raw42401step1Labels = mixedMoment B raw42401step2 raw42401step2Labels := by
      have ha : raw42401step2 = raw42401step1 := by apply Matrix.ext; unfold raw42401step2 raw42401step1; decide +kernel
      have hl : raw42401step1Labels = labelEmbedding6 ∘ raw42401step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42401step1 raw42401step1Labels raw42401step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5421 node5421Labels := by rfl

def raw42402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw42402Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42402step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42402step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42402step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42402step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42402 raw42402Labels = mixedMoment B node3874 node3874Labels := by
  calc
    mixedMoment B raw42402 raw42402Labels = mixedMoment B raw42402step0 raw42402step0Labels := by
      have ha : raw42402step0 = (fun i j => raw42402 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42402step0 raw42402; decide +kernel
      have hl : raw42402step0Labels = raw42402Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42402 raw42402Labels permutation155 permutation2
    mixedMoment B raw42402step0 raw42402step0Labels = mixedMoment B raw42402step1 raw42402step1Labels := by
      have ha : raw42402step1 = raw42402step0 := by apply Matrix.ext; unfold raw42402step1 raw42402step0; decide +kernel
      have hl : raw42402step0Labels = labelEmbedding1 ∘ raw42402step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42402step0 raw42402step0Labels raw42402step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3874 node3874Labels := by rfl

def raw42403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw42403Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42403step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42403step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42403step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42403step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42403step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42403step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42403 raw42403Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw42403 raw42403Labels = mixedMoment B raw42403step0 raw42403step0Labels := by
      have ha : raw42403step0 = (fun i j => raw42403 (permutation192 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42403step0 raw42403; decide +kernel
      have hl : raw42403step0Labels = raw42403Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42403 raw42403Labels permutation192 permutation7
    mixedMoment B raw42403step0 raw42403step0Labels = mixedMoment B raw42403step1 raw42403step1Labels := by
      have ha : raw42403step1 = -raw42403step0 := by apply Matrix.ext; change ∀ i j, raw42403step1 i j = -(raw42403step0 i j); unfold raw42403step1 raw42403step0; decide +kernel
      have hl : raw42403step1Labels = raw42403step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42403step1 raw42403step1Labels = mixedMoment B raw42403step2 raw42403step2Labels := by
      have ha : raw42403step2 = raw42403step1 := by apply Matrix.ext; unfold raw42403step2 raw42403step1; decide +kernel
      have hl : raw42403step1Labels = labelEmbedding6 ∘ raw42403step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42403step1 raw42403step1Labels raw42403step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw42404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42404Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42404step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw42404step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42404step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw42404step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42404 raw42404Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw42404 raw42404Labels = mixedMoment B raw42404step0 raw42404step0Labels := by
      have ha : raw42404step0 = (fun i j => raw42404 (permutation418 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42404step0 raw42404; decide +kernel
      have hl : raw42404step0Labels = raw42404Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42404 raw42404Labels permutation418 permutation4
    mixedMoment B raw42404step0 raw42404step0Labels = mixedMoment B raw42404step1 raw42404step1Labels := by
      have ha : raw42404step1 = raw42404step0 := by apply Matrix.ext; unfold raw42404step1 raw42404step0; decide +kernel
      have hl : raw42404step0Labels = labelEmbedding1 ∘ raw42404step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42404step0 raw42404step0Labels raw42404step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3832 node3832Labels := by rfl

def raw42405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42405Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw42405step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42405step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw42405step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42405 raw42405Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw42405 raw42405Labels = mixedMoment B raw42405step0 raw42405step0Labels := by
      have ha : raw42405step0 = (fun i j => raw42405 (permutation365 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42405step0 raw42405; decide +kernel
      have hl : raw42405step0Labels = raw42405Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42405 raw42405Labels permutation365 permutation6
    mixedMoment B raw42405step0 raw42405step0Labels = mixedMoment B raw42405step1 raw42405step1Labels := by
      have ha : raw42405step1 = -raw42405step0 := by apply Matrix.ext; change ∀ i j, raw42405step1 i j = -(raw42405step0 i j); unfold raw42405step1 raw42405step0; decide +kernel
      have hl : raw42405step1Labels = raw42405step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5379 node5379Labels := by rfl

def raw42406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42406Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw42406step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42406step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw42406step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42406step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 1, 0], ![-2, 0, 2]]
def raw42406step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42406step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42406step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42406step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42406step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42406 raw42406Labels = mixedMoment B node3224 node3224Labels := by
  calc
    mixedMoment B raw42406 raw42406Labels = mixedMoment B raw42406step0 raw42406step0Labels := by
      have hz : ∀ j, raw42406 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42406step0 = (fun i j => raw42406 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42406step0 raw42406; decide +kernel
      have hl : raw42406step0Labels = raw42406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42406 raw42406Labels permutation520 hz
    mixedMoment B raw42406step0 raw42406step0Labels = mixedMoment B raw42406step1 raw42406step1Labels := by
      have hz : ∀ j, raw42406step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42406step1 = (fun i j => raw42406step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42406step1 raw42406step0; decide +kernel
      have hl : raw42406step1Labels = raw42406step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42406step0 raw42406step0Labels permutation104 hz
    mixedMoment B raw42406step1 raw42406step1Labels = mixedMoment B raw42406step2 raw42406step2Labels := by
      have ha : raw42406step2 = (fun i j => raw42406step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42406step2 raw42406step1; decide +kernel
      have hl : raw42406step2Labels = raw42406step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42406step1 raw42406step1Labels permutation31 permutation2
    mixedMoment B raw42406step2 raw42406step2Labels = mixedMoment B raw42406step3 raw42406step3Labels := by
      have ha : raw42406step3 = -raw42406step2 := by apply Matrix.ext; change ∀ i j, raw42406step3 i j = -(raw42406step2 i j); unfold raw42406step3 raw42406step2; decide +kernel
      have hl : raw42406step3Labels = raw42406step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42406step3 raw42406step3Labels = mixedMoment B raw42406step4 raw42406step4Labels := by
      have ha : raw42406step4 = raw42406step3 := by apply Matrix.ext; unfold raw42406step4 raw42406step3; decide +kernel
      have hl : raw42406step3Labels = labelEmbedding1 ∘ raw42406step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42406step3 raw42406step3Labels raw42406step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3224 node3224Labels := by rfl

def raw42407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42407Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw42407step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42407step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw42407step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42407step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw42407step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42407step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42407step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42407step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42407step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42407 raw42407Labels = mixedMoment B node4898 node4898Labels := by
  calc
    mixedMoment B raw42407 raw42407Labels = mixedMoment B raw42407step0 raw42407step0Labels := by
      have hz : ∀ j, raw42407 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42407step0 = (fun i j => raw42407 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42407step0 raw42407; decide +kernel
      have hl : raw42407step0Labels = raw42407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42407 raw42407Labels permutation520 hz
    mixedMoment B raw42407step0 raw42407step0Labels = mixedMoment B raw42407step1 raw42407step1Labels := by
      have hz : ∀ j, raw42407step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42407step1 = (fun i j => raw42407step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42407step1 raw42407step0; decide +kernel
      have hl : raw42407step1Labels = raw42407step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42407step0 raw42407step0Labels permutation104 hz
    mixedMoment B raw42407step1 raw42407step1Labels = mixedMoment B raw42407step2 raw42407step2Labels := by
      have ha : raw42407step2 = (fun i j => raw42407step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42407step2 raw42407step1; decide +kernel
      have hl : raw42407step2Labels = raw42407step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42407step1 raw42407step1Labels permutation31 permutation3
    mixedMoment B raw42407step2 raw42407step2Labels = mixedMoment B raw42407step3 raw42407step3Labels := by
      have ha : raw42407step3 = -raw42407step2 := by apply Matrix.ext; change ∀ i j, raw42407step3 i j = -(raw42407step2 i j); unfold raw42407step3 raw42407step2; decide +kernel
      have hl : raw42407step3Labels = raw42407step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42407step3 raw42407step3Labels = mixedMoment B raw42407step4 raw42407step4Labels := by
      have ha : raw42407step4 = raw42407step3 := by apply Matrix.ext; unfold raw42407step4 raw42407step3; decide +kernel
      have hl : raw42407step3Labels = labelEmbedding7 ∘ raw42407step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42407step3 raw42407step3Labels raw42407step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4898 node4898Labels := by rfl

def raw42408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42408Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw42408step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42408step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42408step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42408step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42408 raw42408Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw42408 raw42408Labels = mixedMoment B raw42408step0 raw42408step0Labels := by
      have hz : ∀ j, raw42408 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42408step0 = (fun i j => raw42408 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42408step0 raw42408; decide +kernel
      have hl : raw42408step0Labels = raw42408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42408 raw42408Labels permutation434 hz
    mixedMoment B raw42408step0 raw42408step0Labels = mixedMoment B raw42408step1 raw42408step1Labels := by
      have ha : raw42408step1 = (fun i j => raw42408step0 (permutation132 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42408step1 raw42408step0; decide +kernel
      have hl : raw42408step1Labels = raw42408step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42408step0 raw42408step0Labels permutation132 permutation4
    mixedMoment B raw42408step1 raw42408step1Labels = mixedMoment B raw42408step2 raw42408step2Labels := by
      have ha : raw42408step2 = raw42408step1 := by apply Matrix.ext; unfold raw42408step2 raw42408step1; decide +kernel
      have hl : raw42408step1Labels = labelEmbedding1 ∘ raw42408step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42408step1 raw42408step1Labels raw42408step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3038 node3038Labels := by rfl

def raw42409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42409Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw42409step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42409step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42409step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42409step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42409step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42409 raw42409Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw42409 raw42409Labels = mixedMoment B raw42409step0 raw42409step0Labels := by
      have hz : ∀ j, raw42409 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42409step0 = (fun i j => raw42409 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42409step0 raw42409; decide +kernel
      have hl : raw42409step0Labels = raw42409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42409 raw42409Labels permutation434 hz
    mixedMoment B raw42409step0 raw42409step0Labels = mixedMoment B raw42409step1 raw42409step1Labels := by
      have ha : raw42409step1 = (fun i j => raw42409step0 (permutation146 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42409step1 raw42409step0; decide +kernel
      have hl : raw42409step1Labels = raw42409step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42409step0 raw42409step0Labels permutation146 permutation5
    mixedMoment B raw42409step1 raw42409step1Labels = mixedMoment B raw42409step2 raw42409step2Labels := by
      have ha : raw42409step2 = raw42409step1 := by apply Matrix.ext; unfold raw42409step2 raw42409step1; decide +kernel
      have hl : raw42409step1Labels = labelEmbedding9 ∘ raw42409step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42409step1 raw42409step1Labels raw42409step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw42410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42410Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42410step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42410step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42410step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42410 raw42410Labels = mixedMoment B node3856 node3856Labels := by
  calc
    mixedMoment B raw42410 raw42410Labels = mixedMoment B raw42410step0 raw42410step0Labels := by
      have hz : ∀ j, raw42410 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42410step0 = (fun i j => raw42410 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42410step0 raw42410; decide +kernel
      have hl : raw42410step0Labels = raw42410Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42410 raw42410Labels permutation434 hz
    mixedMoment B raw42410step0 raw42410step0Labels = mixedMoment B raw42410step1 raw42410step1Labels := by
      have ha : raw42410step1 = raw42410step0 := by apply Matrix.ext; unfold raw42410step1 raw42410step0; decide +kernel
      have hl : raw42410step0Labels = labelEmbedding1 ∘ raw42410step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42410step0 raw42410step0Labels raw42410step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3856 node3856Labels := by rfl

def raw42411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42411Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42411step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42411step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw42411step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42411step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42411step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42411step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42411step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42411 raw42411Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw42411 raw42411Labels = mixedMoment B raw42411step0 raw42411step0Labels := by
      have hz : ∀ j, raw42411 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42411step0 = (fun i j => raw42411 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42411step0 raw42411; decide +kernel
      have hl : raw42411step0Labels = raw42411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42411 raw42411Labels permutation434 hz
    mixedMoment B raw42411step0 raw42411step0Labels = mixedMoment B raw42411step1 raw42411step1Labels := by
      have ha : raw42411step1 = (fun i j => raw42411step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42411step1 raw42411step0; decide +kernel
      have hl : raw42411step1Labels = raw42411step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42411step0 raw42411step0Labels permutation151 permutation3
    mixedMoment B raw42411step1 raw42411step1Labels = mixedMoment B raw42411step2 raw42411step2Labels := by
      have ha : raw42411step2 = -raw42411step1 := by apply Matrix.ext; change ∀ i j, raw42411step2 i j = -(raw42411step1 i j); unfold raw42411step2 raw42411step1; decide +kernel
      have hl : raw42411step2Labels = raw42411step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42411step2 raw42411step2Labels = mixedMoment B raw42411step3 raw42411step3Labels := by
      have ha : raw42411step3 = raw42411step2 := by apply Matrix.ext; unfold raw42411step3 raw42411step2; decide +kernel
      have hl : raw42411step2Labels = labelEmbedding7 ∘ raw42411step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42411step2 raw42411step2Labels raw42411step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw42412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42412Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42412step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42412step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42412step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42412 raw42412Labels = mixedMoment B node3854 node3854Labels := by
  calc
    mixedMoment B raw42412 raw42412Labels = mixedMoment B raw42412step0 raw42412step0Labels := by
      have hz : ∀ j, raw42412 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42412step0 = (fun i j => raw42412 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42412step0 raw42412; decide +kernel
      have hl : raw42412step0Labels = raw42412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42412 raw42412Labels permutation434 hz
    mixedMoment B raw42412step0 raw42412step0Labels = mixedMoment B raw42412step1 raw42412step1Labels := by
      have ha : raw42412step1 = raw42412step0 := by apply Matrix.ext; unfold raw42412step1 raw42412step0; decide +kernel
      have hl : raw42412step0Labels = labelEmbedding1 ∘ raw42412step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42412step0 raw42412step0Labels raw42412step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3854 node3854Labels := by rfl

def raw42413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42413Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42413step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42413step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42413step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42413 raw42413Labels = mixedMoment B node5436 node5436Labels := by
  calc
    mixedMoment B raw42413 raw42413Labels = mixedMoment B raw42413step0 raw42413step0Labels := by
      have hz : ∀ j, raw42413 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42413step0 = (fun i j => raw42413 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42413step0 raw42413; decide +kernel
      have hl : raw42413step0Labels = raw42413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42413 raw42413Labels permutation434 hz
    mixedMoment B raw42413step0 raw42413step0Labels = mixedMoment B raw42413step1 raw42413step1Labels := by
      have ha : raw42413step1 = raw42413step0 := by apply Matrix.ext; unfold raw42413step1 raw42413step0; decide +kernel
      have hl : raw42413step0Labels = labelEmbedding8 ∘ raw42413step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42413step0 raw42413step0Labels raw42413step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5436 node5436Labels := by rfl

def raw42414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42414Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw42414step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42414step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42414step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42414step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42414step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42414 raw42414Labels = mixedMoment B node2677 node2677Labels := by
  calc
    mixedMoment B raw42414 raw42414Labels = mixedMoment B raw42414step0 raw42414step0Labels := by
      have hz : ∀ j, raw42414 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42414step0 = (fun i j => raw42414 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42414step0 raw42414; decide +kernel
      have hl : raw42414step0Labels = raw42414Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42414 raw42414Labels permutation434 hz
    mixedMoment B raw42414step0 raw42414step0Labels = mixedMoment B raw42414step1 raw42414step1Labels := by
      have ha : raw42414step1 = (fun i j => raw42414step0 (permutation108 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42414step1 raw42414step0; decide +kernel
      have hl : raw42414step1Labels = raw42414step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42414step0 raw42414step0Labels permutation108 permutation4
    mixedMoment B raw42414step1 raw42414step1Labels = mixedMoment B raw42414step2 raw42414step2Labels := by
      have ha : raw42414step2 = raw42414step1 := by apply Matrix.ext; unfold raw42414step2 raw42414step1; decide +kernel
      have hl : raw42414step1Labels = labelEmbedding1 ∘ raw42414step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42414step1 raw42414step1Labels raw42414step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2677 node2677Labels := by rfl

def raw42415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42415Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw42415step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42415step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42415step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42415step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42415step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42415 raw42415Labels = mixedMoment B node5232 node5232Labels := by
  calc
    mixedMoment B raw42415 raw42415Labels = mixedMoment B raw42415step0 raw42415step0Labels := by
      have hz : ∀ j, raw42415 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42415step0 = (fun i j => raw42415 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42415step0 raw42415; decide +kernel
      have hl : raw42415step0Labels = raw42415Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42415 raw42415Labels permutation434 hz
    mixedMoment B raw42415step0 raw42415step0Labels = mixedMoment B raw42415step1 raw42415step1Labels := by
      have ha : raw42415step1 = (fun i j => raw42415step0 (permutation108 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42415step1 raw42415step0; decide +kernel
      have hl : raw42415step1Labels = raw42415step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42415step0 raw42415step0Labels permutation108 permutation4
    mixedMoment B raw42415step1 raw42415step1Labels = mixedMoment B raw42415step2 raw42415step2Labels := by
      have ha : raw42415step2 = raw42415step1 := by apply Matrix.ext; unfold raw42415step2 raw42415step1; decide +kernel
      have hl : raw42415step1Labels = labelEmbedding10 ∘ raw42415step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42415step1 raw42415step1Labels raw42415step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5232 node5232Labels := by rfl

def raw42416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42416Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42416step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42416step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42416step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42416step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42416 raw42416Labels = mixedMoment B node3841 node3841Labels := by
  calc
    mixedMoment B raw42416 raw42416Labels = mixedMoment B raw42416step0 raw42416step0Labels := by
      have ha : raw42416step0 = (fun i j => raw42416 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42416step0 raw42416; decide +kernel
      have hl : raw42416step0Labels = raw42416Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42416 raw42416Labels permutation158 permutation2
    mixedMoment B raw42416step0 raw42416step0Labels = mixedMoment B raw42416step1 raw42416step1Labels := by
      have ha : raw42416step1 = raw42416step0 := by apply Matrix.ext; unfold raw42416step1 raw42416step0; decide +kernel
      have hl : raw42416step0Labels = labelEmbedding1 ∘ raw42416step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42416step0 raw42416step0Labels raw42416step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3841 node3841Labels := by rfl

def raw42417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42417Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42417step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42417step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42417step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42417 raw42417Labels = mixedMoment B node5426 node5426Labels := by
  calc
    mixedMoment B raw42417 raw42417Labels = mixedMoment B raw42417step0 raw42417step0Labels := by
      have ha : raw42417step0 = (fun i j => raw42417 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42417step0 raw42417; decide +kernel
      have hl : raw42417step0Labels = raw42417Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42417 raw42417Labels permutation158 permutation2
    mixedMoment B raw42417step0 raw42417step0Labels = mixedMoment B raw42417step1 raw42417step1Labels := by
      have ha : raw42417step1 = raw42417step0 := by apply Matrix.ext; unfold raw42417step1 raw42417step0; decide +kernel
      have hl : raw42417step0Labels = labelEmbedding8 ∘ raw42417step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42417step0 raw42417step0Labels raw42417step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5426 node5426Labels := by rfl

def raw42418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42418Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42418step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42418step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42418 raw42418Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw42418 raw42418Labels = mixedMoment B raw42418step0 raw42418step0Labels := by
      have ha : raw42418step0 = (fun i j => raw42418 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42418step0 raw42418; decide +kernel
      have hl : raw42418step0Labels = raw42418Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42418 raw42418Labels permutation158 permutation2
    mixedMoment B raw42418step0 raw42418step0Labels = mixedMoment B raw42418step1 raw42418step1Labels := by
      have ha : raw42418step1 = raw42418step0 := by apply Matrix.ext; unfold raw42418step1 raw42418step0; decide +kernel
      have hl : raw42418step0Labels = labelEmbedding1 ∘ raw42418step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42418step0 raw42418step0Labels raw42418step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3840 node3840Labels := by rfl

def raw42419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42419Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42419step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42419step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42419step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42419step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42419step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42419step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42419 raw42419Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw42419 raw42419Labels = mixedMoment B raw42419step0 raw42419step0Labels := by
      have ha : raw42419step0 = (fun i j => raw42419 (permutation203 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42419step0 raw42419; decide +kernel
      have hl : raw42419step0Labels = raw42419Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42419 raw42419Labels permutation203 permutation7
    mixedMoment B raw42419step0 raw42419step0Labels = mixedMoment B raw42419step1 raw42419step1Labels := by
      have ha : raw42419step1 = -raw42419step0 := by apply Matrix.ext; change ∀ i j, raw42419step1 i j = -(raw42419step0 i j); unfold raw42419step1 raw42419step0; decide +kernel
      have hl : raw42419step1Labels = raw42419step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42419step1 raw42419step1Labels = mixedMoment B raw42419step2 raw42419step2Labels := by
      have ha : raw42419step2 = raw42419step1 := by apply Matrix.ext; unfold raw42419step2 raw42419step1; decide +kernel
      have hl : raw42419step1Labels = labelEmbedding6 ∘ raw42419step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42419step1 raw42419step1Labels raw42419step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw42420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42420Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42420step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw42420step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42420step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42420step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42420step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42420step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42420 raw42420Labels = mixedMoment B node3834 node3834Labels := by
  calc
    mixedMoment B raw42420 raw42420Labels = mixedMoment B raw42420step0 raw42420step0Labels := by
      have ha : raw42420step0 = (fun i j => raw42420 (permutation379 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42420step0 raw42420; decide +kernel
      have hl : raw42420step0Labels = raw42420Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42420 raw42420Labels permutation379 permutation4
    mixedMoment B raw42420step0 raw42420step0Labels = mixedMoment B raw42420step1 raw42420step1Labels := by
      have ha : raw42420step1 = -raw42420step0 := by apply Matrix.ext; change ∀ i j, raw42420step1 i j = -(raw42420step0 i j); unfold raw42420step1 raw42420step0; decide +kernel
      have hl : raw42420step1Labels = raw42420step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42420step1 raw42420step1Labels = mixedMoment B raw42420step2 raw42420step2Labels := by
      have ha : raw42420step2 = raw42420step1 := by apply Matrix.ext; unfold raw42420step2 raw42420step1; decide +kernel
      have hl : raw42420step1Labels = labelEmbedding1 ∘ raw42420step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42420step1 raw42420step1Labels raw42420step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3834 node3834Labels := by rfl

def raw42421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42421Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42421step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42421 raw42421Labels = mixedMoment B node5381 node5381Labels := by
  calc
    mixedMoment B raw42421 raw42421Labels = mixedMoment B raw42421step0 raw42421step0Labels := by
      have ha : raw42421step0 = (fun i j => raw42421 (permutation421 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42421step0 raw42421; decide +kernel
      have hl : raw42421step0Labels = raw42421Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42421 raw42421Labels permutation421 permutation6
    _ = mixedMoment B node5381 node5381Labels := by rfl

def raw42422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42422Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42422step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42422step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42422step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42422 raw42422Labels = mixedMoment B node3833 node3833Labels := by
  calc
    mixedMoment B raw42422 raw42422Labels = mixedMoment B raw42422step0 raw42422step0Labels := by
      have ha : raw42422step0 = (fun i j => raw42422 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42422step0 raw42422; decide +kernel
      have hl : raw42422step0Labels = raw42422Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42422 raw42422Labels permutation158 permutation2
    mixedMoment B raw42422step0 raw42422step0Labels = mixedMoment B raw42422step1 raw42422step1Labels := by
      have ha : raw42422step1 = raw42422step0 := by apply Matrix.ext; unfold raw42422step1 raw42422step0; decide +kernel
      have hl : raw42422step0Labels = labelEmbedding1 ∘ raw42422step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42422step0 raw42422step0Labels raw42422step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3833 node3833Labels := by rfl

def raw42423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42423Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw42423step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42423 raw42423Labels = mixedMoment B node5376 node5376Labels := by
  calc
    mixedMoment B raw42423 raw42423Labels = mixedMoment B raw42423step0 raw42423step0Labels := by
      have ha : raw42423step0 = (fun i j => raw42423 (permutation422 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42423step0 raw42423; decide +kernel
      have hl : raw42423step0Labels = raw42423Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42423 raw42423Labels permutation422 permutation6
    _ = mixedMoment B node5376 node5376Labels := by rfl

def raw42424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42424Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42424step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42424step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42424step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42424 raw42424Labels = mixedMoment B node2661 node2661Labels := by
  calc
    mixedMoment B raw42424 raw42424Labels = mixedMoment B raw42424step0 raw42424step0Labels := by
      have ha : raw42424step0 = (fun i j => raw42424 (permutation597 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42424step0 raw42424; decide +kernel
      have hl : raw42424step0Labels = raw42424Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42424 raw42424Labels permutation597 permutation4
    mixedMoment B raw42424step0 raw42424step0Labels = mixedMoment B raw42424step1 raw42424step1Labels := by
      have ha : raw42424step1 = raw42424step0 := by apply Matrix.ext; unfold raw42424step1 raw42424step0; decide +kernel
      have hl : raw42424step0Labels = labelEmbedding1 ∘ raw42424step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42424step0 raw42424step0Labels raw42424step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2661 node2661Labels := by rfl

def raw42425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42425Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42425step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42425step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42425step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42425step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42425 raw42425Labels = mixedMoment B node5219 node5219Labels := by
  calc
    mixedMoment B raw42425 raw42425Labels = mixedMoment B raw42425step0 raw42425step0Labels := by
      have ha : raw42425step0 = (fun i j => raw42425 (permutation597 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42425step0 raw42425; decide +kernel
      have hl : raw42425step0Labels = raw42425Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42425 raw42425Labels permutation597 permutation4
    mixedMoment B raw42425step0 raw42425step0Labels = mixedMoment B raw42425step1 raw42425step1Labels := by
      have ha : raw42425step1 = raw42425step0 := by apply Matrix.ext; unfold raw42425step1 raw42425step0; decide +kernel
      have hl : raw42425step0Labels = labelEmbedding10 ∘ raw42425step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42425step0 raw42425step0Labels raw42425step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5219 node5219Labels := by rfl

def raw42426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42426Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw42426step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42426step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42426step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42426step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42426step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42426 raw42426Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw42426 raw42426Labels = mixedMoment B raw42426step0 raw42426step0Labels := by
      have ha : raw42426step0 = (fun i j => raw42426 (permutation372 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42426step0 raw42426; decide +kernel
      have hl : raw42426step0Labels = raw42426Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42426 raw42426Labels permutation372 permutation4
    mixedMoment B raw42426step0 raw42426step0Labels = mixedMoment B raw42426step1 raw42426step1Labels := by
      have ha : raw42426step1 = -raw42426step0 := by apply Matrix.ext; change ∀ i j, raw42426step1 i j = -(raw42426step0 i j); unfold raw42426step1 raw42426step0; decide +kernel
      have hl : raw42426step1Labels = raw42426step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42426step1 raw42426step1Labels = mixedMoment B raw42426step2 raw42426step2Labels := by
      have ha : raw42426step2 = raw42426step1 := by apply Matrix.ext; unfold raw42426step2 raw42426step1; decide +kernel
      have hl : raw42426step1Labels = labelEmbedding1 ∘ raw42426step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42426step1 raw42426step1Labels raw42426step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3840 node3840Labels := by rfl

def raw42427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42427Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42427step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42427 raw42427Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw42427 raw42427Labels = mixedMoment B raw42427step0 raw42427step0Labels := by
      have ha : raw42427step0 = (fun i j => raw42427 (permutation387 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42427step0 raw42427; decide +kernel
      have hl : raw42427step0Labels = raw42427Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42427 raw42427Labels permutation387 permutation6
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw42428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42428Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42428step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42428 raw42428Labels = mixedMoment B node3855 node3855Labels := by
  calc
    mixedMoment B raw42428 raw42428Labels = mixedMoment B raw42428step0 raw42428step0Labels := by
      have ha : raw42428step0 = raw42428 := by apply Matrix.ext; unfold raw42428step0 raw42428; decide +kernel
      have hl : raw42428Labels = labelEmbedding1 ∘ raw42428step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42428 raw42428Labels raw42428step0Labels labelEmbedding1 hl
    _ = mixedMoment B node3855 node3855Labels := by rfl

def raw42429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42429Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42429step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42429 raw42429Labels = mixedMoment B node5437 node5437Labels := by
  calc
    mixedMoment B raw42429 raw42429Labels = mixedMoment B raw42429step0 raw42429step0Labels := by
      have ha : raw42429step0 = raw42429 := by apply Matrix.ext; unfold raw42429step0 raw42429; decide +kernel
      have hl : raw42429Labels = labelEmbedding8 ∘ raw42429step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42429 raw42429Labels raw42429step0Labels labelEmbedding8 hl
    _ = mixedMoment B node5437 node5437Labels := by rfl

def raw42430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42430Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw42430step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42430step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42430step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42430step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42430 raw42430Labels = mixedMoment B node3223 node3223Labels := by
  calc
    mixedMoment B raw42430 raw42430Labels = mixedMoment B raw42430step0 raw42430step0Labels := by
      have hz : ∀ j, raw42430 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42430step0 = (fun i j => raw42430 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42430step0 raw42430; decide +kernel
      have hl : raw42430step0Labels = raw42430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42430 raw42430Labels permutation520 hz
    mixedMoment B raw42430step0 raw42430step0Labels = mixedMoment B raw42430step1 raw42430step1Labels := by
      have ha : raw42430step1 = (fun i j => raw42430step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42430step1 raw42430step0; decide +kernel
      have hl : raw42430step1Labels = raw42430step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42430step0 raw42430step0Labels permutation128 permutation4
    mixedMoment B raw42430step1 raw42430step1Labels = mixedMoment B raw42430step2 raw42430step2Labels := by
      have ha : raw42430step2 = raw42430step1 := by apply Matrix.ext; unfold raw42430step2 raw42430step1; decide +kernel
      have hl : raw42430step1Labels = labelEmbedding1 ∘ raw42430step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42430step1 raw42430step1Labels raw42430step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3223 node3223Labels := by rfl

def raw42431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42431Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw42431step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42431step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42431step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42431step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42431step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42431step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42431 raw42431Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw42431 raw42431Labels = mixedMoment B raw42431step0 raw42431step0Labels := by
      have hz : ∀ j, raw42431 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42431step0 = (fun i j => raw42431 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42431step0 raw42431; decide +kernel
      have hl : raw42431step0Labels = raw42431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42431 raw42431Labels permutation520 hz
    mixedMoment B raw42431step0 raw42431step0Labels = mixedMoment B raw42431step1 raw42431step1Labels := by
      have ha : raw42431step1 = (fun i j => raw42431step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42431step1 raw42431step0; decide +kernel
      have hl : raw42431step1Labels = raw42431step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42431step0 raw42431step0Labels permutation145 permutation3
    mixedMoment B raw42431step1 raw42431step1Labels = mixedMoment B raw42431step2 raw42431step2Labels := by
      have ha : raw42431step2 = -raw42431step1 := by apply Matrix.ext; change ∀ i j, raw42431step2 i j = -(raw42431step1 i j); unfold raw42431step2 raw42431step1; decide +kernel
      have hl : raw42431step2Labels = raw42431step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42431step2 raw42431step2Labels = mixedMoment B raw42431step3 raw42431step3Labels := by
      have ha : raw42431step3 = raw42431step2 := by apply Matrix.ext; unfold raw42431step3 raw42431step2; decide +kernel
      have hl : raw42431step2Labels = labelEmbedding7 ∘ raw42431step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42431step2 raw42431step2Labels raw42431step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw42432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42432Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42432step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42432step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42432step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42432 raw42432Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw42432 raw42432Labels = mixedMoment B raw42432step0 raw42432step0Labels := by
      have ha : raw42432step0 = (fun i j => raw42432 (permutation599 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42432step0 raw42432; decide +kernel
      have hl : raw42432step0Labels = raw42432Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42432 raw42432Labels permutation599 permutation4
    mixedMoment B raw42432step0 raw42432step0Labels = mixedMoment B raw42432step1 raw42432step1Labels := by
      have ha : raw42432step1 = raw42432step0 := by apply Matrix.ext; unfold raw42432step1 raw42432step0; decide +kernel
      have hl : raw42432step0Labels = labelEmbedding1 ∘ raw42432step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42432step0 raw42432step0Labels raw42432step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3037 node3037Labels := by rfl

def raw42433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42433Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42433step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42433step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42433step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42433 raw42433Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw42433 raw42433Labels = mixedMoment B raw42433step0 raw42433step0Labels := by
      have ha : raw42433step0 = (fun i j => raw42433 (permutation668 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42433step0 raw42433; decide +kernel
      have hl : raw42433step0Labels = raw42433Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42433 raw42433Labels permutation668 permutation5
    mixedMoment B raw42433step0 raw42433step0Labels = mixedMoment B raw42433step1 raw42433step1Labels := by
      have ha : raw42433step1 = raw42433step0 := by apply Matrix.ext; unfold raw42433step1 raw42433step0; decide +kernel
      have hl : raw42433step0Labels = labelEmbedding9 ∘ raw42433step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42433step0 raw42433step0Labels raw42433step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw42434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42434Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42434step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42434 raw42434Labels = mixedMoment B node3847 node3847Labels := by
  calc
    mixedMoment B raw42434 raw42434Labels = mixedMoment B raw42434step0 raw42434step0Labels := by
      have ha : raw42434step0 = raw42434 := by apply Matrix.ext; unfold raw42434step0 raw42434; decide +kernel
      have hl : raw42434Labels = labelEmbedding1 ∘ raw42434step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42434 raw42434Labels raw42434step0Labels labelEmbedding1 hl
    _ = mixedMoment B node3847 node3847Labels := by rfl

def raw42435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42435Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42435step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42435step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42435step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42435step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42435step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42435step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42435 raw42435Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw42435 raw42435Labels = mixedMoment B raw42435step0 raw42435step0Labels := by
      have ha : raw42435step0 = (fun i j => raw42435 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42435step0 raw42435; decide +kernel
      have hl : raw42435step0Labels = raw42435Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42435 raw42435Labels permutation682 permutation3
    mixedMoment B raw42435step0 raw42435step0Labels = mixedMoment B raw42435step1 raw42435step1Labels := by
      have ha : raw42435step1 = -raw42435step0 := by apply Matrix.ext; change ∀ i j, raw42435step1 i j = -(raw42435step0 i j); unfold raw42435step1 raw42435step0; decide +kernel
      have hl : raw42435step1Labels = raw42435step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42435step1 raw42435step1Labels = mixedMoment B raw42435step2 raw42435step2Labels := by
      have ha : raw42435step2 = raw42435step1 := by apply Matrix.ext; unfold raw42435step2 raw42435step1; decide +kernel
      have hl : raw42435step1Labels = labelEmbedding7 ∘ raw42435step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42435step1 raw42435step1Labels raw42435step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw42436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42436Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42436step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42436step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42436 raw42436Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw42436 raw42436Labels = mixedMoment B raw42436step0 raw42436step0Labels := by
      have ha : raw42436step0 = raw42436 := by apply Matrix.ext; unfold raw42436step0 raw42436; decide +kernel
      have hl : raw42436Labels = labelEmbedding1 ∘ raw42436step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42436 raw42436Labels raw42436step0Labels labelEmbedding1 hl
    _ = mixedMoment B node3846 node3846Labels := by rfl

def raw42437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42437Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42437step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42437 raw42437Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw42437 raw42437Labels = mixedMoment B raw42437step0 raw42437step0Labels := by
      have ha : raw42437step0 = raw42437 := by apply Matrix.ext; unfold raw42437step0 raw42437; decide +kernel
      have hl : raw42437Labels = labelEmbedding8 ∘ raw42437step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42437 raw42437Labels raw42437step0Labels labelEmbedding8 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw42438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw42438Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42438step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42438step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42438step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42438step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42438 raw42438Labels = mixedMoment B node2676 node2676Labels := by
  calc
    mixedMoment B raw42438 raw42438Labels = mixedMoment B raw42438step0 raw42438step0Labels := by
      have ha : raw42438step0 = (fun i j => raw42438 (permutation526 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42438step0 raw42438; decide +kernel
      have hl : raw42438step0Labels = raw42438Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42438 raw42438Labels permutation526 permutation4
    mixedMoment B raw42438step0 raw42438step0Labels = mixedMoment B raw42438step1 raw42438step1Labels := by
      have ha : raw42438step1 = raw42438step0 := by apply Matrix.ext; unfold raw42438step1 raw42438step0; decide +kernel
      have hl : raw42438step0Labels = labelEmbedding1 ∘ raw42438step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42438step0 raw42438step0Labels raw42438step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2676 node2676Labels := by rfl

def raw42439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw42439Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42439step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42439step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42439step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42439step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42439 raw42439Labels = mixedMoment B node5231 node5231Labels := by
  calc
    mixedMoment B raw42439 raw42439Labels = mixedMoment B raw42439step0 raw42439step0Labels := by
      have ha : raw42439step0 = (fun i j => raw42439 (permutation526 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42439step0 raw42439; decide +kernel
      have hl : raw42439step0Labels = raw42439Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42439 raw42439Labels permutation526 permutation4
    mixedMoment B raw42439step0 raw42439step0Labels = mixedMoment B raw42439step1 raw42439step1Labels := by
      have ha : raw42439step1 = raw42439step0 := by apply Matrix.ext; unfold raw42439step1 raw42439step0; decide +kernel
      have hl : raw42439step0Labels = labelEmbedding10 ∘ raw42439step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42439step0 raw42439step0Labels raw42439step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5231 node5231Labels := by rfl

def raw42440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42440Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42440step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42440step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42440step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42440step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42440 raw42440Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw42440 raw42440Labels = mixedMoment B raw42440step0 raw42440step0Labels := by
      have hz : ∀ j, raw42440 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42440step0 = (fun i j => raw42440 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42440step0 raw42440; decide +kernel
      have hl : raw42440step0Labels = raw42440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42440 raw42440Labels permutation434 hz
    mixedMoment B raw42440step0 raw42440step0Labels = mixedMoment B raw42440step1 raw42440step1Labels := by
      have ha : raw42440step1 = (fun i j => raw42440step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42440step1 raw42440step0; decide +kernel
      have hl : raw42440step1Labels = raw42440step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42440step0 raw42440step0Labels permutation128 permutation4
    mixedMoment B raw42440step1 raw42440step1Labels = mixedMoment B raw42440step2 raw42440step2Labels := by
      have ha : raw42440step2 = raw42440step1 := by apply Matrix.ext; unfold raw42440step2 raw42440step1; decide +kernel
      have hl : raw42440step1Labels = labelEmbedding1 ∘ raw42440step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42440step1 raw42440step1Labels raw42440step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw42441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42441Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42441step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42441step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42441step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42441step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42441 raw42441Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw42441 raw42441Labels = mixedMoment B raw42441step0 raw42441step0Labels := by
      have hz : ∀ j, raw42441 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42441step0 = (fun i j => raw42441 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42441step0 raw42441; decide +kernel
      have hl : raw42441step0Labels = raw42441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42441 raw42441Labels permutation434 hz
    mixedMoment B raw42441step0 raw42441step0Labels = mixedMoment B raw42441step1 raw42441step1Labels := by
      have ha : raw42441step1 = (fun i j => raw42441step0 (permutation133 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42441step1 raw42441step0; decide +kernel
      have hl : raw42441step1Labels = raw42441step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42441step0 raw42441step0Labels permutation133 permutation5
    mixedMoment B raw42441step1 raw42441step1Labels = mixedMoment B raw42441step2 raw42441step2Labels := by
      have ha : raw42441step2 = raw42441step1 := by apply Matrix.ext; unfold raw42441step2 raw42441step1; decide +kernel
      have hl : raw42441step1Labels = labelEmbedding9 ∘ raw42441step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42441step1 raw42441step1Labels raw42441step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw42442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42442Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw42442step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42442step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42442step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw42442step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42442 raw42442Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw42442 raw42442Labels = mixedMoment B raw42442step0 raw42442step0Labels := by
      have hz : ∀ j, raw42442 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42442step0 = (fun i j => raw42442 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42442step0 raw42442; decide +kernel
      have hl : raw42442step0Labels = raw42442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42442 raw42442Labels permutation434 hz
    mixedMoment B raw42442step0 raw42442step0Labels = mixedMoment B raw42442step1 raw42442step1Labels := by
      have ha : raw42442step1 = (fun i j => raw42442step0 (permutation104 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42442step1 raw42442step0; decide +kernel
      have hl : raw42442step1Labels = raw42442step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42442step0 raw42442step0Labels permutation104 permutation4
    mixedMoment B raw42442step1 raw42442step1Labels = mixedMoment B raw42442step2 raw42442step2Labels := by
      have ha : raw42442step2 = raw42442step1 := by apply Matrix.ext; unfold raw42442step2 raw42442step1; decide +kernel
      have hl : raw42442step1Labels = labelEmbedding1 ∘ raw42442step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42442step1 raw42442step1Labels raw42442step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2681 node2681Labels := by rfl

def raw42443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42443Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw42443step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw42443step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42443step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw42443step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42443 raw42443Labels = mixedMoment B node5151 node5151Labels := by
  calc
    mixedMoment B raw42443 raw42443Labels = mixedMoment B raw42443step0 raw42443step0Labels := by
      have hz : ∀ j, raw42443 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42443step0 = (fun i j => raw42443 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42443step0 raw42443; decide +kernel
      have hl : raw42443step0Labels = raw42443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42443 raw42443Labels permutation434 hz
    mixedMoment B raw42443step0 raw42443step0Labels = mixedMoment B raw42443step1 raw42443step1Labels := by
      have ha : raw42443step1 = (fun i j => raw42443step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42443step1 raw42443step0; decide +kernel
      have hl : raw42443step1Labels = raw42443step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42443step0 raw42443step0Labels permutation143 permutation7
    mixedMoment B raw42443step1 raw42443step1Labels = mixedMoment B raw42443step2 raw42443step2Labels := by
      have ha : raw42443step2 = raw42443step1 := by apply Matrix.ext; unfold raw42443step2 raw42443step1; decide +kernel
      have hl : raw42443step1Labels = labelEmbedding6 ∘ raw42443step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42443step1 raw42443step1Labels raw42443step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5151 node5151Labels := by rfl

def raw42444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42444Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42444step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42444step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42444step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42444step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42444 raw42444Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw42444 raw42444Labels = mixedMoment B raw42444step0 raw42444step0Labels := by
      have ha : raw42444step0 = (fun i j => raw42444 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42444step0 raw42444; decide +kernel
      have hl : raw42444step0Labels = raw42444Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42444 raw42444Labels permutation158 permutation2
    mixedMoment B raw42444step0 raw42444step0Labels = mixedMoment B raw42444step1 raw42444step1Labels := by
      have ha : raw42444step1 = raw42444step0 := by apply Matrix.ext; unfold raw42444step1 raw42444step0; decide +kernel
      have hl : raw42444step0Labels = labelEmbedding1 ∘ raw42444step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42444step0 raw42444step0Labels raw42444step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3839 node3839Labels := by rfl

def raw42445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42445Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42445step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42445step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42445step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42445step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42445 raw42445Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw42445 raw42445Labels = mixedMoment B raw42445step0 raw42445step0Labels := by
      have ha : raw42445step0 = (fun i j => raw42445 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42445step0 raw42445; decide +kernel
      have hl : raw42445step0Labels = raw42445Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42445 raw42445Labels permutation158 permutation2
    mixedMoment B raw42445step0 raw42445step0Labels = mixedMoment B raw42445step1 raw42445step1Labels := by
      have ha : raw42445step1 = raw42445step0 := by apply Matrix.ext; unfold raw42445step1 raw42445step0; decide +kernel
      have hl : raw42445step0Labels = labelEmbedding8 ∘ raw42445step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42445step0 raw42445step0Labels raw42445step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw42446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42446Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42446step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw42446step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42446step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42446step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42446step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42446step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42446 raw42446Labels = mixedMoment B node3557 node3557Labels := by
  calc
    mixedMoment B raw42446 raw42446Labels = mixedMoment B raw42446step0 raw42446step0Labels := by
      have ha : raw42446step0 = (fun i j => raw42446 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42446step0 raw42446; decide +kernel
      have hl : raw42446step0Labels = raw42446Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42446 raw42446Labels permutation682 permutation2
    mixedMoment B raw42446step0 raw42446step0Labels = mixedMoment B raw42446step1 raw42446step1Labels := by
      have ha : raw42446step1 = -raw42446step0 := by apply Matrix.ext; change ∀ i j, raw42446step1 i j = -(raw42446step0 i j); unfold raw42446step1 raw42446step0; decide +kernel
      have hl : raw42446step1Labels = raw42446step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42446step1 raw42446step1Labels = mixedMoment B raw42446step2 raw42446step2Labels := by
      have ha : raw42446step2 = raw42446step1 := by apply Matrix.ext; unfold raw42446step2 raw42446step1; decide +kernel
      have hl : raw42446step1Labels = labelEmbedding1 ∘ raw42446step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42446step1 raw42446step1Labels raw42446step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3557 node3557Labels := by rfl

def raw42447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42447Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42447step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42447step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42447step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42447 raw42447Labels = mixedMoment B node5144 node5144Labels := by
  calc
    mixedMoment B raw42447 raw42447Labels = mixedMoment B raw42447step0 raw42447step0Labels := by
      have ha : raw42447step0 = (fun i j => raw42447 (permutation634 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42447step0 raw42447; decide +kernel
      have hl : raw42447step0Labels = raw42447Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42447 raw42447Labels permutation634 permutation7
    mixedMoment B raw42447step0 raw42447step0Labels = mixedMoment B raw42447step1 raw42447step1Labels := by
      have ha : raw42447step1 = raw42447step0 := by apply Matrix.ext; unfold raw42447step1 raw42447step0; decide +kernel
      have hl : raw42447step0Labels = labelEmbedding6 ∘ raw42447step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42447step0 raw42447step0Labels raw42447step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5144 node5144Labels := by rfl

def raw42448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42448Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw42448step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42448step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42448step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42448step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42448step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42448 raw42448Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw42448 raw42448Labels = mixedMoment B raw42448step0 raw42448step0Labels := by
      have ha : raw42448step0 = (fun i j => raw42448 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42448step0 raw42448; decide +kernel
      have hl : raw42448step0Labels = raw42448Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42448 raw42448Labels permutation682 permutation2
    mixedMoment B raw42448step0 raw42448step0Labels = mixedMoment B raw42448step1 raw42448step1Labels := by
      have ha : raw42448step1 = -raw42448step0 := by apply Matrix.ext; change ∀ i j, raw42448step1 i j = -(raw42448step0 i j); unfold raw42448step1 raw42448step0; decide +kernel
      have hl : raw42448step1Labels = raw42448step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42448step1 raw42448step1Labels = mixedMoment B raw42448step2 raw42448step2Labels := by
      have ha : raw42448step2 = raw42448step1 := by apply Matrix.ext; unfold raw42448step2 raw42448step1; decide +kernel
      have hl : raw42448step1Labels = labelEmbedding1 ∘ raw42448step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42448step1 raw42448step1Labels raw42448step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

def raw42449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42449Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42449step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw42449step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42449step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw42449step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42449 raw42449Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw42449 raw42449Labels = mixedMoment B raw42449step0 raw42449step0Labels := by
      have ha : raw42449step0 = (fun i j => raw42449 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42449step0 raw42449; decide +kernel
      have hl : raw42449step0Labels = raw42449Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42449 raw42449Labels permutation644 permutation7
    mixedMoment B raw42449step0 raw42449step0Labels = mixedMoment B raw42449step1 raw42449step1Labels := by
      have ha : raw42449step1 = raw42449step0 := by apply Matrix.ext; unfold raw42449step1 raw42449step0; decide +kernel
      have hl : raw42449step0Labels = labelEmbedding6 ∘ raw42449step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42449step0 raw42449step0Labels raw42449step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5129 node5129Labels := by rfl

def raw42450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42450Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42450step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42450step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42450step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42450step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42450 raw42450Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw42450 raw42450Labels = mixedMoment B raw42450step0 raw42450step0Labels := by
      have ha : raw42450step0 = (fun i j => raw42450 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42450step0 raw42450; decide +kernel
      have hl : raw42450step0Labels = raw42450Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42450 raw42450Labels permutation157 permutation2
    mixedMoment B raw42450step0 raw42450step0Labels = mixedMoment B raw42450step1 raw42450step1Labels := by
      have ha : raw42450step1 = raw42450step0 := by apply Matrix.ext; unfold raw42450step1 raw42450step0; decide +kernel
      have hl : raw42450step0Labels = labelEmbedding1 ∘ raw42450step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42450step0 raw42450step0Labels raw42450step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw42451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42451Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42451step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42451step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42451step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42451 raw42451Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw42451 raw42451Labels = mixedMoment B raw42451step0 raw42451step0Labels := by
      have ha : raw42451step0 = (fun i j => raw42451 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42451step0 raw42451; decide +kernel
      have hl : raw42451step0Labels = raw42451Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42451 raw42451Labels permutation157 permutation2
    mixedMoment B raw42451step0 raw42451step0Labels = mixedMoment B raw42451step1 raw42451step1Labels := by
      have ha : raw42451step1 = raw42451step0 := by apply Matrix.ext; unfold raw42451step1 raw42451step0; decide +kernel
      have hl : raw42451step0Labels = labelEmbedding8 ∘ raw42451step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42451step0 raw42451step0Labels raw42451step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw42452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw42452Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw42452step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42452step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw42452step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42452step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42452step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42452step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42452step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42452 raw42452Labels = mixedMoment B node3052 node3052Labels := by
  calc
    mixedMoment B raw42452 raw42452Labels = mixedMoment B raw42452step0 raw42452step0Labels := by
      have hz : ∀ j, raw42452 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42452step0 = (fun i j => raw42452 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42452step0 raw42452; decide +kernel
      have hl : raw42452step0Labels = raw42452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42452 raw42452Labels permutation434 hz
    mixedMoment B raw42452step0 raw42452step0Labels = mixedMoment B raw42452step1 raw42452step1Labels := by
      have hz : ∀ j, raw42452step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42452step1 = (fun i j => raw42452step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42452step1 raw42452step0; decide +kernel
      have hl : raw42452step1Labels = raw42452step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42452step0 raw42452step0Labels permutation80 hz
    mixedMoment B raw42452step1 raw42452step1Labels = mixedMoment B raw42452step2 raw42452step2Labels := by
      have ha : raw42452step2 = (fun i j => raw42452step1 (permutation26 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42452step2 raw42452step1; decide +kernel
      have hl : raw42452step2Labels = raw42452step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42452step1 raw42452step1Labels permutation26 permutation4
    mixedMoment B raw42452step2 raw42452step2Labels = mixedMoment B raw42452step3 raw42452step3Labels := by
      have ha : raw42452step3 = raw42452step2 := by apply Matrix.ext; unfold raw42452step3 raw42452step2; decide +kernel
      have hl : raw42452step2Labels = labelEmbedding1 ∘ raw42452step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42452step2 raw42452step2Labels raw42452step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3052 node3052Labels := by rfl

def raw42453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw42453Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw42453step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42453step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw42453step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42453step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42453step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42453 raw42453Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw42453 raw42453Labels = mixedMoment B raw42453step0 raw42453step0Labels := by
      have hz : ∀ j, raw42453 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42453step0 = (fun i j => raw42453 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42453step0 raw42453; decide +kernel
      have hl : raw42453step0Labels = raw42453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42453 raw42453Labels permutation434 hz
    mixedMoment B raw42453step0 raw42453step0Labels = mixedMoment B raw42453step1 raw42453step1Labels := by
      have hz : ∀ j, raw42453step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42453step1 = (fun i j => raw42453step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42453step1 raw42453step0; decide +kernel
      have hl : raw42453step1Labels = raw42453step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42453step0 raw42453step0Labels permutation80 hz
    mixedMoment B raw42453step1 raw42453step1Labels = mixedMoment B raw42453step2 raw42453step2Labels := by
      have ha : raw42453step2 = (fun i j => raw42453step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42453step2 raw42453step1; decide +kernel
      have hl : raw42453step2Labels = raw42453step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42453step1 raw42453step1Labels permutation23 permutation6
    _ = mixedMoment B node5276 node5276Labels := by rfl

def raw42454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw42454Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw42454step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42454step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -3, 2], ![2, 2, -4]]
def raw42454step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42454step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw42454step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42454step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw42454step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42454 raw42454Labels = mixedMoment B node2683 node2683Labels := by
  calc
    mixedMoment B raw42454 raw42454Labels = mixedMoment B raw42454step0 raw42454step0Labels := by
      have hz : ∀ j, raw42454 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42454step0 = (fun i j => raw42454 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42454step0 raw42454; decide +kernel
      have hl : raw42454step0Labels = raw42454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42454 raw42454Labels permutation434 hz
    mixedMoment B raw42454step0 raw42454step0Labels = mixedMoment B raw42454step1 raw42454step1Labels := by
      have hz : ∀ j, raw42454step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42454step1 = (fun i j => raw42454step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42454step1 raw42454step0; decide +kernel
      have hl : raw42454step1Labels = raw42454step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42454step0 raw42454step0Labels permutation80 hz
    mixedMoment B raw42454step1 raw42454step1Labels = mixedMoment B raw42454step2 raw42454step2Labels := by
      have ha : raw42454step2 = (fun i j => raw42454step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42454step2 raw42454step1; decide +kernel
      have hl : raw42454step2Labels = raw42454step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42454step1 raw42454step1Labels permutation20 permutation4
    mixedMoment B raw42454step2 raw42454step2Labels = mixedMoment B raw42454step3 raw42454step3Labels := by
      have ha : raw42454step3 = raw42454step2 := by apply Matrix.ext; unfold raw42454step3 raw42454step2; decide +kernel
      have hl : raw42454step2Labels = labelEmbedding1 ∘ raw42454step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42454step2 raw42454step2Labels raw42454step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2683 node2683Labels := by rfl

def raw42455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw42455Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw42455step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42455step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -3, 2], ![2, 2, -4]]
def raw42455step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42455step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw42455step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42455 raw42455Labels = mixedMoment B node4611 node4611Labels := by
  calc
    mixedMoment B raw42455 raw42455Labels = mixedMoment B raw42455step0 raw42455step0Labels := by
      have hz : ∀ j, raw42455 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42455step0 = (fun i j => raw42455 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42455step0 raw42455; decide +kernel
      have hl : raw42455step0Labels = raw42455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42455 raw42455Labels permutation434 hz
    mixedMoment B raw42455step0 raw42455step0Labels = mixedMoment B raw42455step1 raw42455step1Labels := by
      have hz : ∀ j, raw42455step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42455step1 = (fun i j => raw42455step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42455step1 raw42455step0; decide +kernel
      have hl : raw42455step1Labels = raw42455step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42455step0 raw42455step0Labels permutation80 hz
    mixedMoment B raw42455step1 raw42455step1Labels = mixedMoment B raw42455step2 raw42455step2Labels := by
      have ha : raw42455step2 = (fun i j => raw42455step1 (permutation28 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42455step2 raw42455step1; decide +kernel
      have hl : raw42455step2Labels = raw42455step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42455step1 raw42455step1Labels permutation28 permutation6
    _ = mixedMoment B node4611 node4611Labels := by rfl

def raw42456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42456Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42456step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42456step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw42456step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42456step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42456step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42456step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42456step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42456 raw42456Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw42456 raw42456Labels = mixedMoment B raw42456step0 raw42456step0Labels := by
      have hz : ∀ j, raw42456 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42456step0 = (fun i j => raw42456 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42456step0 raw42456; decide +kernel
      have hl : raw42456step0Labels = raw42456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42456 raw42456Labels permutation346 hz
    mixedMoment B raw42456step0 raw42456step0Labels = mixedMoment B raw42456step1 raw42456step1Labels := by
      have ha : raw42456step1 = (fun i j => raw42456step0 (permutation110 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42456step1 raw42456step0; decide +kernel
      have hl : raw42456step1Labels = raw42456step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42456step0 raw42456step0Labels permutation110 permutation4
    mixedMoment B raw42456step1 raw42456step1Labels = mixedMoment B raw42456step2 raw42456step2Labels := by
      have ha : raw42456step2 = -raw42456step1 := by apply Matrix.ext; change ∀ i j, raw42456step2 i j = -(raw42456step1 i j); unfold raw42456step2 raw42456step1; decide +kernel
      have hl : raw42456step2Labels = raw42456step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42456step2 raw42456step2Labels = mixedMoment B raw42456step3 raw42456step3Labels := by
      have ha : raw42456step3 = raw42456step2 := by apply Matrix.ext; unfold raw42456step3 raw42456step2; decide +kernel
      have hl : raw42456step2Labels = labelEmbedding1 ∘ raw42456step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42456step2 raw42456step2Labels raw42456step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3541 node3541Labels := by rfl

def raw42457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42457Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42457step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42457step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42457step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42457 raw42457Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw42457 raw42457Labels = mixedMoment B raw42457step0 raw42457step0Labels := by
      have hz : ∀ j, raw42457 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42457step0 = (fun i j => raw42457 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42457step0 raw42457; decide +kernel
      have hl : raw42457step0Labels = raw42457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42457 raw42457Labels permutation346 hz
    mixedMoment B raw42457step0 raw42457step0Labels = mixedMoment B raw42457step1 raw42457step1Labels := by
      have ha : raw42457step1 = (fun i j => raw42457step0 (permutation115 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42457step1 raw42457step0; decide +kernel
      have hl : raw42457step1Labels = raw42457step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42457step0 raw42457step0Labels permutation115 permutation6
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw42458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw42458Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw42458step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42458step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw42458step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42458step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42458step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42458step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42458step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42458 raw42458Labels = mixedMoment B node3296 node3296Labels := by
  calc
    mixedMoment B raw42458 raw42458Labels = mixedMoment B raw42458step0 raw42458step0Labels := by
      have hz : ∀ j, raw42458 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42458step0 = (fun i j => raw42458 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42458step0 raw42458; decide +kernel
      have hl : raw42458step0Labels = raw42458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42458 raw42458Labels permutation346 hz
    mixedMoment B raw42458step0 raw42458step0Labels = mixedMoment B raw42458step1 raw42458step1Labels := by
      have ha : raw42458step1 = (fun i j => raw42458step0 (permutation134 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42458step1 raw42458step0; decide +kernel
      have hl : raw42458step1Labels = raw42458step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42458step0 raw42458step0Labels permutation134 permutation4
    mixedMoment B raw42458step1 raw42458step1Labels = mixedMoment B raw42458step2 raw42458step2Labels := by
      have ha : raw42458step2 = -raw42458step1 := by apply Matrix.ext; change ∀ i j, raw42458step2 i j = -(raw42458step1 i j); unfold raw42458step2 raw42458step1; decide +kernel
      have hl : raw42458step2Labels = raw42458step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42458step2 raw42458step2Labels = mixedMoment B raw42458step3 raw42458step3Labels := by
      have ha : raw42458step3 = raw42458step2 := by apply Matrix.ext; unfold raw42458step3 raw42458step2; decide +kernel
      have hl : raw42458step2Labels = labelEmbedding1 ∘ raw42458step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42458step2 raw42458step2Labels raw42458step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3296 node3296Labels := by rfl

def raw42459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw42459Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw42459step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42459step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42459step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42459 raw42459Labels = mixedMoment B node4607 node4607Labels := by
  calc
    mixedMoment B raw42459 raw42459Labels = mixedMoment B raw42459step0 raw42459step0Labels := by
      have hz : ∀ j, raw42459 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42459step0 = (fun i j => raw42459 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42459step0 raw42459; decide +kernel
      have hl : raw42459step0Labels = raw42459Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42459 raw42459Labels permutation346 hz
    mixedMoment B raw42459step0 raw42459step0Labels = mixedMoment B raw42459step1 raw42459step1Labels := by
      have ha : raw42459step1 = (fun i j => raw42459step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42459step1 raw42459step0; decide +kernel
      have hl : raw42459step1Labels = raw42459step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42459step0 raw42459step0Labels permutation137 permutation6
    _ = mixedMoment B node4607 node4607Labels := by rfl

def raw42460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw42460Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw42460step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42460step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw42460step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42460step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42460step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42460step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42460step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42460 raw42460Labels = mixedMoment B node3295 node3295Labels := by
  calc
    mixedMoment B raw42460 raw42460Labels = mixedMoment B raw42460step0 raw42460step0Labels := by
      have hz : ∀ j, raw42460 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42460step0 = (fun i j => raw42460 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42460step0 raw42460; decide +kernel
      have hl : raw42460step0Labels = raw42460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42460 raw42460Labels permutation346 hz
    mixedMoment B raw42460step0 raw42460step0Labels = mixedMoment B raw42460step1 raw42460step1Labels := by
      have ha : raw42460step1 = (fun i j => raw42460step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42460step1 raw42460step0; decide +kernel
      have hl : raw42460step1Labels = raw42460step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42460step0 raw42460step0Labels permutation151 permutation2
    mixedMoment B raw42460step1 raw42460step1Labels = mixedMoment B raw42460step2 raw42460step2Labels := by
      have ha : raw42460step2 = -raw42460step1 := by apply Matrix.ext; change ∀ i j, raw42460step2 i j = -(raw42460step1 i j); unfold raw42460step2 raw42460step1; decide +kernel
      have hl : raw42460step2Labels = raw42460step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42460step2 raw42460step2Labels = mixedMoment B raw42460step3 raw42460step3Labels := by
      have ha : raw42460step3 = raw42460step2 := by apply Matrix.ext; unfold raw42460step3 raw42460step2; decide +kernel
      have hl : raw42460step2Labels = labelEmbedding1 ∘ raw42460step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42460step2 raw42460step2Labels raw42460step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3295 node3295Labels := by rfl

def raw42461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw42461Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw42461step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42461step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw42461step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42461 raw42461Labels = mixedMoment B node4592 node4592Labels := by
  calc
    mixedMoment B raw42461 raw42461Labels = mixedMoment B raw42461step0 raw42461step0Labels := by
      have hz : ∀ j, raw42461 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42461step0 = (fun i j => raw42461 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42461step0 raw42461; decide +kernel
      have hl : raw42461step0Labels = raw42461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42461 raw42461Labels permutation346 hz
    mixedMoment B raw42461step0 raw42461step0Labels = mixedMoment B raw42461step1 raw42461step1Labels := by
      have ha : raw42461step1 = (fun i j => raw42461step0 (permutation138 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42461step1 raw42461step0; decide +kernel
      have hl : raw42461step1Labels = raw42461step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42461step0 raw42461step0Labels permutation138 permutation6
    _ = mixedMoment B node4592 node4592Labels := by rfl

def raw42462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw42462Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw42462step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42462step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42462step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42462step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42462 raw42462Labels = mixedMoment B node2670 node2670Labels := by
  calc
    mixedMoment B raw42462 raw42462Labels = mixedMoment B raw42462step0 raw42462step0Labels := by
      have hz : ∀ j, raw42462 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42462step0 = (fun i j => raw42462 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42462step0 raw42462; decide +kernel
      have hl : raw42462step0Labels = raw42462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42462 raw42462Labels permutation346 hz
    mixedMoment B raw42462step0 raw42462step0Labels = mixedMoment B raw42462step1 raw42462step1Labels := by
      have ha : raw42462step1 = (fun i j => raw42462step0 (permutation132 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42462step1 raw42462step0; decide +kernel
      have hl : raw42462step1Labels = raw42462step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42462step0 raw42462step0Labels permutation132 permutation4
    mixedMoment B raw42462step1 raw42462step1Labels = mixedMoment B raw42462step2 raw42462step2Labels := by
      have ha : raw42462step2 = raw42462step1 := by apply Matrix.ext; unfold raw42462step2 raw42462step1; decide +kernel
      have hl : raw42462step1Labels = labelEmbedding1 ∘ raw42462step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42462step1 raw42462step1Labels raw42462step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2670 node2670Labels := by rfl

def raw42463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw42463Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw42463step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42463step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw42463step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42463 raw42463Labels = mixedMoment B node5140 node5140Labels := by
  calc
    mixedMoment B raw42463 raw42463Labels = mixedMoment B raw42463step0 raw42463step0Labels := by
      have hz : ∀ j, raw42463 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42463step0 = (fun i j => raw42463 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42463step0 raw42463; decide +kernel
      have hl : raw42463step0Labels = raw42463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42463 raw42463Labels permutation346 hz
    mixedMoment B raw42463step0 raw42463step0Labels = mixedMoment B raw42463step1 raw42463step1Labels := by
      have ha : raw42463step1 = (fun i j => raw42463step0 (permutation94 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42463step1 raw42463step0; decide +kernel
      have hl : raw42463step1Labels = raw42463step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42463step0 raw42463step0Labels permutation94 permutation6
    _ = mixedMoment B node5140 node5140Labels := by rfl

def raw42464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw42464Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw42464step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42464step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw42464step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42464step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42464step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42464step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42464step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42464 raw42464Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw42464 raw42464Labels = mixedMoment B raw42464step0 raw42464step0Labels := by
      have hz : ∀ j, raw42464 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42464step0 = (fun i j => raw42464 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42464step0 raw42464; decide +kernel
      have hl : raw42464step0Labels = raw42464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42464 raw42464Labels permutation346 hz
    mixedMoment B raw42464step0 raw42464step0Labels = mixedMoment B raw42464step1 raw42464step1Labels := by
      have ha : raw42464step1 = (fun i j => raw42464step0 (permutation86 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42464step1 raw42464step0; decide +kernel
      have hl : raw42464step1Labels = raw42464step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42464step0 raw42464step0Labels permutation86 permutation4
    mixedMoment B raw42464step1 raw42464step1Labels = mixedMoment B raw42464step2 raw42464step2Labels := by
      have ha : raw42464step2 = -raw42464step1 := by apply Matrix.ext; change ∀ i j, raw42464step2 i j = -(raw42464step1 i j); unfold raw42464step2 raw42464step1; decide +kernel
      have hl : raw42464step2Labels = raw42464step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42464step2 raw42464step2Labels = mixedMoment B raw42464step3 raw42464step3Labels := by
      have ha : raw42464step3 = raw42464step2 := by apply Matrix.ext; unfold raw42464step3 raw42464step2; decide +kernel
      have hl : raw42464step2Labels = labelEmbedding1 ∘ raw42464step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42464step2 raw42464step2Labels raw42464step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

def raw42465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw42465Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw42465step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42465step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42465step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42465 raw42465Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw42465 raw42465Labels = mixedMoment B raw42465step0 raw42465step0Labels := by
      have hz : ∀ j, raw42465 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42465step0 = (fun i j => raw42465 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42465step0 raw42465; decide +kernel
      have hl : raw42465step0Labels = raw42465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42465 raw42465Labels permutation346 hz
    mixedMoment B raw42465step0 raw42465step0Labels = mixedMoment B raw42465step1 raw42465step1Labels := by
      have ha : raw42465step1 = (fun i j => raw42465step0 (permutation89 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42465step1 raw42465step0; decide +kernel
      have hl : raw42465step1Labels = raw42465step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42465step0 raw42465step0Labels permutation89 permutation6
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw42466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw42466Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw42466step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42466step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw42466step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42466step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw42466step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42466 raw42466Labels = mixedMoment B node2682 node2682Labels := by
  calc
    mixedMoment B raw42466 raw42466Labels = mixedMoment B raw42466step0 raw42466step0Labels := by
      have hz : ∀ j, raw42466 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42466step0 = (fun i j => raw42466 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42466step0 raw42466; decide +kernel
      have hl : raw42466step0Labels = raw42466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42466 raw42466Labels permutation346 hz
    mixedMoment B raw42466step0 raw42466step0Labels = mixedMoment B raw42466step1 raw42466step1Labels := by
      have ha : raw42466step1 = (fun i j => raw42466step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42466step1 raw42466step0; decide +kernel
      have hl : raw42466step1Labels = raw42466step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42466step0 raw42466step0Labels permutation128 permutation4
    mixedMoment B raw42466step1 raw42466step1Labels = mixedMoment B raw42466step2 raw42466step2Labels := by
      have ha : raw42466step2 = raw42466step1 := by apply Matrix.ext; unfold raw42466step2 raw42466step1; decide +kernel
      have hl : raw42466step1Labels = labelEmbedding1 ∘ raw42466step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42466step1 raw42466step1Labels raw42466step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2682 node2682Labels := by rfl

def raw42467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw42467Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw42467step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42467step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw42467step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42467step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw42467step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42467 raw42467Labels = mixedMoment B node5236 node5236Labels := by
  calc
    mixedMoment B raw42467 raw42467Labels = mixedMoment B raw42467step0 raw42467step0Labels := by
      have hz : ∀ j, raw42467 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42467step0 = (fun i j => raw42467 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42467step0 raw42467; decide +kernel
      have hl : raw42467step0Labels = raw42467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42467 raw42467Labels permutation346 hz
    mixedMoment B raw42467step0 raw42467step0Labels = mixedMoment B raw42467step1 raw42467step1Labels := by
      have ha : raw42467step1 = (fun i j => raw42467step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42467step1 raw42467step0; decide +kernel
      have hl : raw42467step1Labels = raw42467step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42467step0 raw42467step0Labels permutation128 permutation4
    mixedMoment B raw42467step1 raw42467step1Labels = mixedMoment B raw42467step2 raw42467step2Labels := by
      have ha : raw42467step2 = raw42467step1 := by apply Matrix.ext; unfold raw42467step2 raw42467step1; decide +kernel
      have hl : raw42467step1Labels = labelEmbedding10 ∘ raw42467step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42467step1 raw42467step1Labels raw42467step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5236 node5236Labels := by rfl

def raw42468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42468Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42468step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw42468step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42468step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42468step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42468step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42468step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42468 raw42468Labels = mixedMoment B node3288 node3288Labels := by
  calc
    mixedMoment B raw42468 raw42468Labels = mixedMoment B raw42468step0 raw42468step0Labels := by
      have ha : raw42468step0 = (fun i j => raw42468 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42468step0 raw42468; decide +kernel
      have hl : raw42468step0Labels = raw42468Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42468 raw42468Labels permutation682 permutation2
    mixedMoment B raw42468step0 raw42468step0Labels = mixedMoment B raw42468step1 raw42468step1Labels := by
      have ha : raw42468step1 = -raw42468step0 := by apply Matrix.ext; change ∀ i j, raw42468step1 i j = -(raw42468step0 i j); unfold raw42468step1 raw42468step0; decide +kernel
      have hl : raw42468step1Labels = raw42468step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42468step1 raw42468step1Labels = mixedMoment B raw42468step2 raw42468step2Labels := by
      have ha : raw42468step2 = raw42468step1 := by apply Matrix.ext; unfold raw42468step2 raw42468step1; decide +kernel
      have hl : raw42468step1Labels = labelEmbedding1 ∘ raw42468step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42468step1 raw42468step1Labels raw42468step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3288 node3288Labels := by rfl

def raw42469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42469Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42469step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42469step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42469step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42469 raw42469Labels = mixedMoment B node4589 node4589Labels := by
  calc
    mixedMoment B raw42469 raw42469Labels = mixedMoment B raw42469step0 raw42469step0Labels := by
      have ha : raw42469step0 = (fun i j => raw42469 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42469step0 raw42469; decide +kernel
      have hl : raw42469step0Labels = raw42469Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42469 raw42469Labels permutation674 permutation7
    mixedMoment B raw42469step0 raw42469step0Labels = mixedMoment B raw42469step1 raw42469step1Labels := by
      have ha : raw42469step1 = raw42469step0 := by apply Matrix.ext; unfold raw42469step1 raw42469step0; decide +kernel
      have hl : raw42469step0Labels = labelEmbedding6 ∘ raw42469step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42469step0 raw42469step0Labels raw42469step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4589 node4589Labels := by rfl

def raw42470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw42470Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42470step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw42470step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42470step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42470step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42470step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42470step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42470 raw42470Labels = mixedMoment B node3517 node3517Labels := by
  calc
    mixedMoment B raw42470 raw42470Labels = mixedMoment B raw42470step0 raw42470step0Labels := by
      have ha : raw42470step0 = (fun i j => raw42470 (permutation459 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42470step0 raw42470; decide +kernel
      have hl : raw42470step0Labels = raw42470Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42470 raw42470Labels permutation459 permutation4
    mixedMoment B raw42470step0 raw42470step0Labels = mixedMoment B raw42470step1 raw42470step1Labels := by
      have ha : raw42470step1 = -raw42470step0 := by apply Matrix.ext; change ∀ i j, raw42470step1 i j = -(raw42470step0 i j); unfold raw42470step1 raw42470step0; decide +kernel
      have hl : raw42470step1Labels = raw42470step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42470step1 raw42470step1Labels = mixedMoment B raw42470step2 raw42470step2Labels := by
      have ha : raw42470step2 = raw42470step1 := by apply Matrix.ext; unfold raw42470step2 raw42470step1; decide +kernel
      have hl : raw42470step1Labels = labelEmbedding1 ∘ raw42470step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42470step1 raw42470step1Labels raw42470step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3517 node3517Labels := by rfl

def raw42471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw42471Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42471step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42471 raw42471Labels = mixedMoment B node5138 node5138Labels := by
  calc
    mixedMoment B raw42471 raw42471Labels = mixedMoment B raw42471step0 raw42471step0Labels := by
      have ha : raw42471step0 = (fun i j => raw42471 (permutation492 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42471step0 raw42471; decide +kernel
      have hl : raw42471step0Labels = raw42471Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42471 raw42471Labels permutation492 permutation6
    _ = mixedMoment B node5138 node5138Labels := by rfl

def raw42472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw42472Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42472step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw42472step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42472step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42472step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42472step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42472step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42472 raw42472Labels = mixedMoment B node3539 node3539Labels := by
  calc
    mixedMoment B raw42472 raw42472Labels = mixedMoment B raw42472step0 raw42472step0Labels := by
      have ha : raw42472step0 = (fun i j => raw42472 (permutation454 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42472step0 raw42472; decide +kernel
      have hl : raw42472step0Labels = raw42472Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42472 raw42472Labels permutation454 permutation4
    mixedMoment B raw42472step0 raw42472step0Labels = mixedMoment B raw42472step1 raw42472step1Labels := by
      have ha : raw42472step1 = -raw42472step0 := by apply Matrix.ext; change ∀ i j, raw42472step1 i j = -(raw42472step0 i j); unfold raw42472step1 raw42472step0; decide +kernel
      have hl : raw42472step1Labels = raw42472step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42472step1 raw42472step1Labels = mixedMoment B raw42472step2 raw42472step2Labels := by
      have ha : raw42472step2 = raw42472step1 := by apply Matrix.ext; unfold raw42472step2 raw42472step1; decide +kernel
      have hl : raw42472step1Labels = labelEmbedding1 ∘ raw42472step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42472step1 raw42472step1Labels raw42472step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3539 node3539Labels := by rfl

def raw42473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw42473Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42473step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42473 raw42473Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw42473 raw42473Labels = mixedMoment B raw42473step0 raw42473step0Labels := by
      have ha : raw42473step0 = (fun i j => raw42473 (permutation463 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42473step0 raw42473; decide +kernel
      have hl : raw42473step0Labels = raw42473Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42473 raw42473Labels permutation463 permutation6
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw42474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw42474Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42474step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42474step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42474step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42474 raw42474Labels = mixedMoment B node3842 node3842Labels := by
  calc
    mixedMoment B raw42474 raw42474Labels = mixedMoment B raw42474step0 raw42474step0Labels := by
      have ha : raw42474step0 = (fun i j => raw42474 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42474step0 raw42474; decide +kernel
      have hl : raw42474step0Labels = raw42474Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42474 raw42474Labels permutation156 permutation2
    mixedMoment B raw42474step0 raw42474step0Labels = mixedMoment B raw42474step1 raw42474step1Labels := by
      have ha : raw42474step1 = raw42474step0 := by apply Matrix.ext; unfold raw42474step1 raw42474step0; decide +kernel
      have hl : raw42474step0Labels = labelEmbedding1 ∘ raw42474step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42474step0 raw42474step0Labels raw42474step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3842 node3842Labels := by rfl

def raw42475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw42475Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42475step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw42475step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42475step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw42475step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42475step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw42475step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42475 raw42475Labels = mixedMoment B node5419 node5419Labels := by
  calc
    mixedMoment B raw42475 raw42475Labels = mixedMoment B raw42475step0 raw42475step0Labels := by
      have ha : raw42475step0 = (fun i j => raw42475 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42475step0 raw42475; decide +kernel
      have hl : raw42475step0Labels = raw42475Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42475 raw42475Labels permutation194 permutation7
    mixedMoment B raw42475step0 raw42475step0Labels = mixedMoment B raw42475step1 raw42475step1Labels := by
      have ha : raw42475step1 = -raw42475step0 := by apply Matrix.ext; change ∀ i j, raw42475step1 i j = -(raw42475step0 i j); unfold raw42475step1 raw42475step0; decide +kernel
      have hl : raw42475step1Labels = raw42475step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42475step1 raw42475step1Labels = mixedMoment B raw42475step2 raw42475step2Labels := by
      have ha : raw42475step2 = raw42475step1 := by apply Matrix.ext; unfold raw42475step2 raw42475step1; decide +kernel
      have hl : raw42475step1Labels = labelEmbedding6 ∘ raw42475step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42475step1 raw42475step1Labels raw42475step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5419 node5419Labels := by rfl

def raw42476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42476Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw42476step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42476step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42476step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42476step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42476step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42476 raw42476Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw42476 raw42476Labels = mixedMoment B raw42476step0 raw42476step0Labels := by
      have ha : raw42476step0 = (fun i j => raw42476 (permutation460 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42476step0 raw42476; decide +kernel
      have hl : raw42476step0Labels = raw42476Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42476 raw42476Labels permutation460 permutation4
    mixedMoment B raw42476step0 raw42476step0Labels = mixedMoment B raw42476step1 raw42476step1Labels := by
      have ha : raw42476step1 = -raw42476step0 := by apply Matrix.ext; change ∀ i j, raw42476step1 i j = -(raw42476step0 i j); unfold raw42476step1 raw42476step0; decide +kernel
      have hl : raw42476step1Labels = raw42476step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42476step1 raw42476step1Labels = mixedMoment B raw42476step2 raw42476step2Labels := by
      have ha : raw42476step2 = raw42476step1 := by apply Matrix.ext; unfold raw42476step2 raw42476step1; decide +kernel
      have hl : raw42476step1Labels = labelEmbedding1 ∘ raw42476step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42476step1 raw42476step1Labels raw42476step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

def raw42477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42477Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw42477step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42477 raw42477Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw42477 raw42477Labels = mixedMoment B raw42477step0 raw42477step0Labels := by
      have ha : raw42477step0 = (fun i j => raw42477 (permutation493 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42477step0 raw42477; decide +kernel
      have hl : raw42477step0Labels = raw42477Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42477 raw42477Labels permutation493 permutation6
    _ = mixedMoment B node5129 node5129Labels := by rfl

def raw42478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw42478Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42478step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw42478step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42478step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw42478step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42478 raw42478Labels = mixedMoment B node3835 node3835Labels := by
  calc
    mixedMoment B raw42478 raw42478Labels = mixedMoment B raw42478step0 raw42478step0Labels := by
      have ha : raw42478step0 = (fun i j => raw42478 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42478step0 raw42478; decide +kernel
      have hl : raw42478step0Labels = raw42478Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42478 raw42478Labels permutation156 permutation2
    mixedMoment B raw42478step0 raw42478step0Labels = mixedMoment B raw42478step1 raw42478step1Labels := by
      have ha : raw42478step1 = raw42478step0 := by apply Matrix.ext; unfold raw42478step1 raw42478step0; decide +kernel
      have hl : raw42478step0Labels = labelEmbedding1 ∘ raw42478step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42478step0 raw42478step0Labels raw42478step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3835 node3835Labels := by rfl

def raw42479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw42479Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw42479step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42479step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw42479step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42479 raw42479Labels = mixedMoment B node5377 node5377Labels := by
  calc
    mixedMoment B raw42479 raw42479Labels = mixedMoment B raw42479step0 raw42479step0Labels := by
      have ha : raw42479step0 = (fun i j => raw42479 (permutation361 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42479step0 raw42479; decide +kernel
      have hl : raw42479step0Labels = raw42479Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42479 raw42479Labels permutation361 permutation6
    mixedMoment B raw42479step0 raw42479step0Labels = mixedMoment B raw42479step1 raw42479step1Labels := by
      have ha : raw42479step1 = -raw42479step0 := by apply Matrix.ext; change ∀ i j, raw42479step1 i j = -(raw42479step0 i j); unfold raw42479step1 raw42479step0; decide +kernel
      have hl : raw42479step1Labels = raw42479step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5377 node5377Labels := by rfl

def raw42480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42480Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![3, -3, 0]]
def raw42480step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42480step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![3, -3, 0]]
def raw42480step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42480step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw42480step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42480step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw42480step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42480step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw42480step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42480 raw42480Labels = mixedMoment B node2255 node2255Labels := by
  calc
    mixedMoment B raw42480 raw42480Labels = mixedMoment B raw42480step0 raw42480step0Labels := by
      have hz : ∀ j, raw42480 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42480step0 = (fun i j => raw42480 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42480step0 raw42480; decide +kernel
      have hl : raw42480step0Labels = raw42480Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42480 raw42480Labels permutation520 hz
    mixedMoment B raw42480step0 raw42480step0Labels = mixedMoment B raw42480step1 raw42480step1Labels := by
      have hz : ∀ j, raw42480step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42480step1 = (fun i j => raw42480step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42480step1 raw42480step0; decide +kernel
      have hl : raw42480step1Labels = raw42480step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42480step0 raw42480step0Labels permutation104 hz
    mixedMoment B raw42480step1 raw42480step1Labels = mixedMoment B raw42480step2 raw42480step2Labels := by
      have ha : raw42480step2 = (fun i j => raw42480step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42480step2 raw42480step1; decide +kernel
      have hl : raw42480step2Labels = raw42480step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42480step1 raw42480step1Labels permutation22 permutation4
    mixedMoment B raw42480step2 raw42480step2Labels = mixedMoment B raw42480step3 raw42480step3Labels := by
      have ha : raw42480step3 = -raw42480step2 := by apply Matrix.ext; change ∀ i j, raw42480step3 i j = -(raw42480step2 i j); unfold raw42480step3 raw42480step2; decide +kernel
      have hl : raw42480step3Labels = raw42480step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42480step3 raw42480step3Labels = mixedMoment B raw42480step4 raw42480step4Labels := by
      have ha : raw42480step4 = raw42480step3 := by apply Matrix.ext; unfold raw42480step4 raw42480step3; decide +kernel
      have hl : raw42480step3Labels = labelEmbedding1 ∘ raw42480step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42480step3 raw42480step3Labels raw42480step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2255 node2255Labels := by rfl

def raw42481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42481Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![3, -3, 0]]
def raw42481step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42481step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![3, -3, 0]]
def raw42481step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42481step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw42481step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42481step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw42481step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42481step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw42481step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42481 raw42481Labels = mixedMoment B node4892 node4892Labels := by
  calc
    mixedMoment B raw42481 raw42481Labels = mixedMoment B raw42481step0 raw42481step0Labels := by
      have hz : ∀ j, raw42481 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42481step0 = (fun i j => raw42481 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42481step0 raw42481; decide +kernel
      have hl : raw42481step0Labels = raw42481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42481 raw42481Labels permutation520 hz
    mixedMoment B raw42481step0 raw42481step0Labels = mixedMoment B raw42481step1 raw42481step1Labels := by
      have hz : ∀ j, raw42481step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42481step1 = (fun i j => raw42481step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42481step1 raw42481step0; decide +kernel
      have hl : raw42481step1Labels = raw42481step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42481step0 raw42481step0Labels permutation104 hz
    mixedMoment B raw42481step1 raw42481step1Labels = mixedMoment B raw42481step2 raw42481step2Labels := by
      have ha : raw42481step2 = (fun i j => raw42481step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42481step2 raw42481step1; decide +kernel
      have hl : raw42481step2Labels = raw42481step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42481step1 raw42481step1Labels permutation22 permutation4
    mixedMoment B raw42481step2 raw42481step2Labels = mixedMoment B raw42481step3 raw42481step3Labels := by
      have ha : raw42481step3 = -raw42481step2 := by apply Matrix.ext; change ∀ i j, raw42481step3 i j = -(raw42481step2 i j); unfold raw42481step3 raw42481step2; decide +kernel
      have hl : raw42481step3Labels = raw42481step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42481step3 raw42481step3Labels = mixedMoment B raw42481step4 raw42481step4Labels := by
      have ha : raw42481step4 = raw42481step3 := by apply Matrix.ext; unfold raw42481step4 raw42481step3; decide +kernel
      have hl : raw42481step3Labels = labelEmbedding10 ∘ raw42481step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42481step3 raw42481step3Labels raw42481step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4892 node4892Labels := by rfl

def raw42482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42482Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![2, -3, 1]]
def raw42482step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42482step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw42482step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42482step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw42482step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42482step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw42482step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42482 raw42482Labels = mixedMoment B node2197 node2197Labels := by
  calc
    mixedMoment B raw42482 raw42482Labels = mixedMoment B raw42482step0 raw42482step0Labels := by
      have hz : ∀ j, raw42482 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42482step0 = (fun i j => raw42482 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42482step0 raw42482; decide +kernel
      have hl : raw42482step0Labels = raw42482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42482 raw42482Labels permutation434 hz
    mixedMoment B raw42482step0 raw42482step0Labels = mixedMoment B raw42482step1 raw42482step1Labels := by
      have ha : raw42482step1 = (fun i j => raw42482step0 (permutation94 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42482step1 raw42482step0; decide +kernel
      have hl : raw42482step1Labels = raw42482step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42482step0 raw42482step0Labels permutation94 permutation4
    mixedMoment B raw42482step1 raw42482step1Labels = mixedMoment B raw42482step2 raw42482step2Labels := by
      have ha : raw42482step2 = -raw42482step1 := by apply Matrix.ext; change ∀ i j, raw42482step2 i j = -(raw42482step1 i j); unfold raw42482step2 raw42482step1; decide +kernel
      have hl : raw42482step2Labels = raw42482step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42482step2 raw42482step2Labels = mixedMoment B raw42482step3 raw42482step3Labels := by
      have ha : raw42482step3 = raw42482step2 := by apply Matrix.ext; unfold raw42482step3 raw42482step2; decide +kernel
      have hl : raw42482step2Labels = labelEmbedding1 ∘ raw42482step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42482step2 raw42482step2Labels raw42482step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2197 node2197Labels := by rfl

def raw42483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42483Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![2, -3, 1]]
def raw42483step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42483step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw42483step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42483 raw42483Labels = mixedMoment B node4836 node4836Labels := by
  calc
    mixedMoment B raw42483 raw42483Labels = mixedMoment B raw42483step0 raw42483step0Labels := by
      have hz : ∀ j, raw42483 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42483step0 = (fun i j => raw42483 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42483step0 raw42483; decide +kernel
      have hl : raw42483step0Labels = raw42483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42483 raw42483Labels permutation434 hz
    mixedMoment B raw42483step0 raw42483step0Labels = mixedMoment B raw42483step1 raw42483step1Labels := by
      have ha : raw42483step1 = (fun i j => raw42483step0 (permutation95 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42483step1 raw42483step0; decide +kernel
      have hl : raw42483step1Labels = raw42483step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42483step0 raw42483step0Labels permutation95 permutation6
    _ = mixedMoment B node4836 node4836Labels := by rfl

def raw42484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42484Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw42484step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42484step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw42484step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42484step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42484step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42484step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42484step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42484 raw42484Labels = mixedMoment B node2253 node2253Labels := by
  calc
    mixedMoment B raw42484 raw42484Labels = mixedMoment B raw42484step0 raw42484step0Labels := by
      have hz : ∀ j, raw42484 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42484step0 = (fun i j => raw42484 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42484step0 raw42484; decide +kernel
      have hl : raw42484step0Labels = raw42484Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42484 raw42484Labels permutation434 hz
    mixedMoment B raw42484step0 raw42484step0Labels = mixedMoment B raw42484step1 raw42484step1Labels := by
      have ha : raw42484step1 = (fun i j => raw42484step0 (permutation86 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42484step1 raw42484step0; decide +kernel
      have hl : raw42484step1Labels = raw42484step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42484step0 raw42484step0Labels permutation86 permutation4
    mixedMoment B raw42484step1 raw42484step1Labels = mixedMoment B raw42484step2 raw42484step2Labels := by
      have ha : raw42484step2 = -raw42484step1 := by apply Matrix.ext; change ∀ i j, raw42484step2 i j = -(raw42484step1 i j); unfold raw42484step2 raw42484step1; decide +kernel
      have hl : raw42484step2Labels = raw42484step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42484step2 raw42484step2Labels = mixedMoment B raw42484step3 raw42484step3Labels := by
      have ha : raw42484step3 = raw42484step2 := by apply Matrix.ext; unfold raw42484step3 raw42484step2; decide +kernel
      have hl : raw42484step2Labels = labelEmbedding1 ∘ raw42484step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42484step2 raw42484step2Labels raw42484step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2253 node2253Labels := by rfl

def raw42485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42485Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw42485step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42485step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw42485step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42485step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42485step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42485step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42485step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42485 raw42485Labels = mixedMoment B node4891 node4891Labels := by
  calc
    mixedMoment B raw42485 raw42485Labels = mixedMoment B raw42485step0 raw42485step0Labels := by
      have hz : ∀ j, raw42485 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42485step0 = (fun i j => raw42485 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42485step0 raw42485; decide +kernel
      have hl : raw42485step0Labels = raw42485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42485 raw42485Labels permutation434 hz
    mixedMoment B raw42485step0 raw42485step0Labels = mixedMoment B raw42485step1 raw42485step1Labels := by
      have ha : raw42485step1 = (fun i j => raw42485step0 (permutation86 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42485step1 raw42485step0; decide +kernel
      have hl : raw42485step1Labels = raw42485step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42485step0 raw42485step0Labels permutation86 permutation4
    mixedMoment B raw42485step1 raw42485step1Labels = mixedMoment B raw42485step2 raw42485step2Labels := by
      have ha : raw42485step2 = -raw42485step1 := by apply Matrix.ext; change ∀ i j, raw42485step2 i j = -(raw42485step1 i j); unfold raw42485step2 raw42485step1; decide +kernel
      have hl : raw42485step2Labels = raw42485step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42485step2 raw42485step2Labels = mixedMoment B raw42485step3 raw42485step3Labels := by
      have ha : raw42485step3 = raw42485step2 := by apply Matrix.ext; unfold raw42485step3 raw42485step2; decide +kernel
      have hl : raw42485step2Labels = labelEmbedding10 ∘ raw42485step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42485step2 raw42485step2Labels raw42485step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4891 node4891Labels := by rfl

def raw42486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42486Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw42486step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42486step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw42486step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42486step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42486step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42486step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42486step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42486 raw42486Labels = mixedMoment B node2251 node2251Labels := by
  calc
    mixedMoment B raw42486 raw42486Labels = mixedMoment B raw42486step0 raw42486step0Labels := by
      have hz : ∀ j, raw42486 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42486step0 = (fun i j => raw42486 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42486step0 raw42486; decide +kernel
      have hl : raw42486step0Labels = raw42486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42486 raw42486Labels permutation434 hz
    mixedMoment B raw42486step0 raw42486step0Labels = mixedMoment B raw42486step1 raw42486step1Labels := by
      have ha : raw42486step1 = (fun i j => raw42486step0 (permutation87 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42486step1 raw42486step0; decide +kernel
      have hl : raw42486step1Labels = raw42486step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42486step0 raw42486step0Labels permutation87 permutation4
    mixedMoment B raw42486step1 raw42486step1Labels = mixedMoment B raw42486step2 raw42486step2Labels := by
      have ha : raw42486step2 = -raw42486step1 := by apply Matrix.ext; change ∀ i j, raw42486step2 i j = -(raw42486step1 i j); unfold raw42486step2 raw42486step1; decide +kernel
      have hl : raw42486step2Labels = raw42486step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42486step2 raw42486step2Labels = mixedMoment B raw42486step3 raw42486step3Labels := by
      have ha : raw42486step3 = raw42486step2 := by apply Matrix.ext; unfold raw42486step3 raw42486step2; decide +kernel
      have hl : raw42486step2Labels = labelEmbedding1 ∘ raw42486step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42486step2 raw42486step2Labels raw42486step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2251 node2251Labels := by rfl

def raw42487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42487Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw42487step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42487step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42487 raw42487Labels = mixedMoment B node4867 node4867Labels := by
  calc
    mixedMoment B raw42487 raw42487Labels = mixedMoment B raw42487step0 raw42487step0Labels := by
      have hz : ∀ j, raw42487 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42487step0 = (fun i j => raw42487 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42487step0 raw42487; decide +kernel
      have hl : raw42487step0Labels = raw42487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42487 raw42487Labels permutation434 hz
    mixedMoment B raw42487step0 raw42487step0Labels = mixedMoment B raw42487step1 raw42487step1Labels := by
      have ha : raw42487step1 = (fun i j => raw42487step0 (permutation101 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42487step1 raw42487step0; decide +kernel
      have hl : raw42487step1Labels = raw42487step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42487step0 raw42487step0Labels permutation101 permutation6
    _ = mixedMoment B node4867 node4867Labels := by rfl

def raw42488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42488Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![2, 0, -2]]
def raw42488step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw42488step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42488step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw42488step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42488step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw42488step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42488 raw42488Labels = mixedMoment B node2146 node2146Labels := by
  calc
    mixedMoment B raw42488 raw42488Labels = mixedMoment B raw42488step0 raw42488step0Labels := by
      have hz : ∀ j, raw42488 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42488step0 = (fun i j => raw42488 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42488step0 raw42488; decide +kernel
      have hl : raw42488step0Labels = raw42488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42488 raw42488Labels permutation434 hz
    mixedMoment B raw42488step0 raw42488step0Labels = mixedMoment B raw42488step1 raw42488step1Labels := by
      have ha : raw42488step1 = (fun i j => raw42488step0 (permutation100 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42488step1 raw42488step0; decide +kernel
      have hl : raw42488step1Labels = raw42488step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42488step0 raw42488step0Labels permutation100 permutation4
    mixedMoment B raw42488step1 raw42488step1Labels = mixedMoment B raw42488step2 raw42488step2Labels := by
      have ha : raw42488step2 = -raw42488step1 := by apply Matrix.ext; change ∀ i j, raw42488step2 i j = -(raw42488step1 i j); unfold raw42488step2 raw42488step1; decide +kernel
      have hl : raw42488step2Labels = raw42488step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42488step2 raw42488step2Labels = mixedMoment B raw42488step3 raw42488step3Labels := by
      have ha : raw42488step3 = raw42488step2 := by apply Matrix.ext; unfold raw42488step3 raw42488step2; decide +kernel
      have hl : raw42488step2Labels = labelEmbedding1 ∘ raw42488step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42488step2 raw42488step2Labels raw42488step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2146 node2146Labels := by rfl

def raw42489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42489Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![2, 0, -2]]
def raw42489step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42489step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw42489step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42489 raw42489Labels = mixedMoment B node4683 node4683Labels := by
  calc
    mixedMoment B raw42489 raw42489Labels = mixedMoment B raw42489step0 raw42489step0Labels := by
      have hz : ∀ j, raw42489 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42489step0 = (fun i j => raw42489 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42489step0 raw42489; decide +kernel
      have hl : raw42489step0Labels = raw42489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42489 raw42489Labels permutation434 hz
    mixedMoment B raw42489step0 raw42489step0Labels = mixedMoment B raw42489step1 raw42489step1Labels := by
      have ha : raw42489step1 = (fun i j => raw42489step0 (permutation100 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42489step1 raw42489step0; decide +kernel
      have hl : raw42489step1Labels = raw42489step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42489step0 raw42489step0Labels permutation100 permutation6
    _ = mixedMoment B node4683 node4683Labels := by rfl

def raw42490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42490Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw42490step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42490step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42490step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42490step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42490step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42490 raw42490Labels = mixedMoment B node2196 node2196Labels := by
  calc
    mixedMoment B raw42490 raw42490Labels = mixedMoment B raw42490step0 raw42490step0Labels := by
      have ha : raw42490step0 = (fun i j => raw42490 (permutation403 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42490step0 raw42490; decide +kernel
      have hl : raw42490step0Labels = raw42490Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42490 raw42490Labels permutation403 permutation4
    mixedMoment B raw42490step0 raw42490step0Labels = mixedMoment B raw42490step1 raw42490step1Labels := by
      have ha : raw42490step1 = -raw42490step0 := by apply Matrix.ext; change ∀ i j, raw42490step1 i j = -(raw42490step0 i j); unfold raw42490step1 raw42490step0; decide +kernel
      have hl : raw42490step1Labels = raw42490step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42490step1 raw42490step1Labels = mixedMoment B raw42490step2 raw42490step2Labels := by
      have ha : raw42490step2 = raw42490step1 := by apply Matrix.ext; unfold raw42490step2 raw42490step1; decide +kernel
      have hl : raw42490step1Labels = labelEmbedding1 ∘ raw42490step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42490step1 raw42490step1Labels raw42490step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2196 node2196Labels := by rfl

def raw42491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42491Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42491step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42491 raw42491Labels = mixedMoment B node4816 node4816Labels := by
  calc
    mixedMoment B raw42491 raw42491Labels = mixedMoment B raw42491step0 raw42491step0Labels := by
      have ha : raw42491step0 = (fun i j => raw42491 (permutation412 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42491step0 raw42491; decide +kernel
      have hl : raw42491step0Labels = raw42491Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42491 raw42491Labels permutation412 permutation6
    _ = mixedMoment B node4816 node4816Labels := by rfl

def raw42492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42492Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42492step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw42492step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42492step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42492step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42492step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42492step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42492 raw42492Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw42492 raw42492Labels = mixedMoment B raw42492step0 raw42492step0Labels := by
      have ha : raw42492step0 = (fun i j => raw42492 (permutation371 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42492step0 raw42492; decide +kernel
      have hl : raw42492step0Labels = raw42492Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42492 raw42492Labels permutation371 permutation4
    mixedMoment B raw42492step0 raw42492step0Labels = mixedMoment B raw42492step1 raw42492step1Labels := by
      have ha : raw42492step1 = -raw42492step0 := by apply Matrix.ext; change ∀ i j, raw42492step1 i j = -(raw42492step0 i j); unfold raw42492step1 raw42492step0; decide +kernel
      have hl : raw42492step1Labels = raw42492step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42492step1 raw42492step1Labels = mixedMoment B raw42492step2 raw42492step2Labels := by
      have ha : raw42492step2 = raw42492step1 := by apply Matrix.ext; unfold raw42492step2 raw42492step1; decide +kernel
      have hl : raw42492step1Labels = labelEmbedding1 ∘ raw42492step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42492step1 raw42492step1Labels raw42492step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2250 node2250Labels := by rfl

def raw42493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42493Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42493step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42493 raw42493Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw42493 raw42493Labels = mixedMoment B raw42493step0 raw42493step0Labels := by
      have ha : raw42493step0 = (fun i j => raw42493 (permutation431 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42493step0 raw42493; decide +kernel
      have hl : raw42493step0Labels = raw42493Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42493 raw42493Labels permutation431 permutation6
    _ = mixedMoment B node4852 node4852Labels := by rfl

def raw42494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42494Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42494step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw42494step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42494step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42494step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42494step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42494step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42494 raw42494Labels = mixedMoment B node2145 node2145Labels := by
  calc
    mixedMoment B raw42494 raw42494Labels = mixedMoment B raw42494step0 raw42494step0Labels := by
      have ha : raw42494step0 = (fun i j => raw42494 (permutation419 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42494step0 raw42494; decide +kernel
      have hl : raw42494step0Labels = raw42494Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42494 raw42494Labels permutation419 permutation4
    mixedMoment B raw42494step0 raw42494step0Labels = mixedMoment B raw42494step1 raw42494step1Labels := by
      have ha : raw42494step1 = -raw42494step0 := by apply Matrix.ext; change ∀ i j, raw42494step1 i j = -(raw42494step0 i j); unfold raw42494step1 raw42494step0; decide +kernel
      have hl : raw42494step1Labels = raw42494step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42494step1 raw42494step1Labels = mixedMoment B raw42494step2 raw42494step2Labels := by
      have ha : raw42494step2 = raw42494step1 := by apply Matrix.ext; unfold raw42494step2 raw42494step1; decide +kernel
      have hl : raw42494step1Labels = labelEmbedding1 ∘ raw42494step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42494step1 raw42494step1Labels raw42494step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2145 node2145Labels := by rfl

def raw42495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42495Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42495step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42495step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42495 raw42495Labels = mixedMoment B node4680 node4680Labels := by
  calc
    mixedMoment B raw42495 raw42495Labels = mixedMoment B raw42495step0 raw42495step0Labels := by
      have ha : raw42495step0 = (fun i j => raw42495 (permutation421 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42495step0 raw42495; decide +kernel
      have hl : raw42495step0Labels = raw42495Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42495 raw42495Labels permutation421 permutation6
    _ = mixedMoment B node4680 node4680Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
