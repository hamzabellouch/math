import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw768 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw768step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw768step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw768step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw768 raw768Labels = mixedMoment B node4143 node4143Labels := by
  calc
    mixedMoment B raw768 raw768Labels = mixedMoment B raw768step0 raw768step0Labels := by
      have ha : raw768step0 = (fun i j => raw768 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw768step0 raw768; decide +kernel
      have hl : raw768step0Labels = raw768Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw768 raw768Labels permutation152 permutation4
    mixedMoment B raw768step0 raw768step0Labels = mixedMoment B raw768step1 raw768step1Labels := by
      have ha : raw768step1 = raw768step0 := by apply Matrix.ext; unfold raw768step1 raw768step0; decide +kernel
      have hl : raw768step0Labels = labelEmbedding7 ∘ raw768step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw768step0 raw768step0Labels raw768step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4143 node4143Labels := by rfl

def raw769 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw769Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw769step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw769 raw769Labels = mixedMoment B node571 node571Labels := by
  calc
    mixedMoment B raw769 raw769Labels = mixedMoment B raw769step0 raw769step0Labels := by
      have ha : raw769step0 = (fun i j => raw769 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw769step0 raw769; decide +kernel
      have hl : raw769step0Labels = raw769Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw769 raw769Labels permutation152 permutation4
    _ = mixedMoment B node571 node571Labels := by rfl

def raw770 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw770Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw770step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw770step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw770step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw770step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw770step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw770 raw770Labels = mixedMoment B node1491 node1491Labels := by
  calc
    mixedMoment B raw770 raw770Labels = mixedMoment B raw770step0 raw770step0Labels := by
      have ha : raw770step0 = (fun i j => raw770 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw770step0 raw770; decide +kernel
      have hl : raw770step0Labels = raw770Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw770 raw770Labels permutation152 permutation6
    mixedMoment B raw770step0 raw770step0Labels = mixedMoment B raw770step1 raw770step1Labels := by
      have ha : raw770step1 = -raw770step0 := by apply Matrix.ext; change ∀ i j, raw770step1 i j = -(raw770step0 i j); unfold raw770step1 raw770step0; decide +kernel
      have hl : raw770step1Labels = raw770step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw770step1 raw770step1Labels = mixedMoment B raw770step2 raw770step2Labels := by
      have ha : raw770step2 = raw770step1 := by apply Matrix.ext; unfold raw770step2 raw770step1; decide +kernel
      have hl : raw770step1Labels = labelEmbedding1 ∘ raw770step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw770step1 raw770step1Labels raw770step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1491 node1491Labels := by rfl

def raw771 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw771step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw771step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw771step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw771 raw771Labels = mixedMoment B node4144 node4144Labels := by
  calc
    mixedMoment B raw771 raw771Labels = mixedMoment B raw771step0 raw771step0Labels := by
      have ha : raw771step0 = (fun i j => raw771 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw771step0 raw771; decide +kernel
      have hl : raw771step0Labels = raw771Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw771 raw771Labels permutation32 permutation4
    mixedMoment B raw771step0 raw771step0Labels = mixedMoment B raw771step1 raw771step1Labels := by
      have ha : raw771step1 = raw771step0 := by apply Matrix.ext; unfold raw771step1 raw771step0; decide +kernel
      have hl : raw771step0Labels = labelEmbedding7 ∘ raw771step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw771step0 raw771step0Labels raw771step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4144 node4144Labels := by rfl

def raw772 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw772Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw772step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw772 raw772Labels = mixedMoment B node572 node572Labels := by
  calc
    mixedMoment B raw772 raw772Labels = mixedMoment B raw772step0 raw772step0Labels := by
      have ha : raw772step0 = (fun i j => raw772 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw772step0 raw772; decide +kernel
      have hl : raw772step0Labels = raw772Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw772 raw772Labels permutation32 permutation4
    _ = mixedMoment B node572 node572Labels := by rfl

def raw773 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw773Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw773step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw773step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw773step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw773step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw773step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw773 raw773Labels = mixedMoment B node1492 node1492Labels := by
  calc
    mixedMoment B raw773 raw773Labels = mixedMoment B raw773step0 raw773step0Labels := by
      have ha : raw773step0 = (fun i j => raw773 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw773step0 raw773; decide +kernel
      have hl : raw773step0Labels = raw773Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw773 raw773Labels permutation32 permutation6
    mixedMoment B raw773step0 raw773step0Labels = mixedMoment B raw773step1 raw773step1Labels := by
      have ha : raw773step1 = -raw773step0 := by apply Matrix.ext; change ∀ i j, raw773step1 i j = -(raw773step0 i j); unfold raw773step1 raw773step0; decide +kernel
      have hl : raw773step1Labels = raw773step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw773step1 raw773step1Labels = mixedMoment B raw773step2 raw773step2Labels := by
      have ha : raw773step2 = raw773step1 := by apply Matrix.ext; unfold raw773step2 raw773step1; decide +kernel
      have hl : raw773step1Labels = labelEmbedding1 ∘ raw773step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw773step1 raw773step1Labels raw773step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1492 node1492Labels := by rfl

def raw774 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw774step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw774step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw774 raw774Labels = mixedMoment B node4145 node4145Labels := by
  calc
    mixedMoment B raw774 raw774Labels = mixedMoment B raw774step0 raw774step0Labels := by
      have ha : raw774step0 = (fun i j => raw774 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw774step0 raw774; decide +kernel
      have hl : raw774step0Labels = raw774Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw774 raw774Labels permutation32 permutation4
    mixedMoment B raw774step0 raw774step0Labels = mixedMoment B raw774step1 raw774step1Labels := by
      have ha : raw774step1 = raw774step0 := by apply Matrix.ext; unfold raw774step1 raw774step0; decide +kernel
      have hl : raw774step0Labels = labelEmbedding7 ∘ raw774step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw774step0 raw774step0Labels raw774step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4145 node4145Labels := by rfl

def raw775 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw775Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw775step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw775 raw775Labels = mixedMoment B node573 node573Labels := by
  calc
    mixedMoment B raw775 raw775Labels = mixedMoment B raw775step0 raw775step0Labels := by
      have ha : raw775step0 = (fun i j => raw775 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw775step0 raw775; decide +kernel
      have hl : raw775step0Labels = raw775Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw775 raw775Labels permutation32 permutation4
    _ = mixedMoment B node573 node573Labels := by rfl

def raw776 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw776Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw776step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw776step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw776step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw776step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw776step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw776 raw776Labels = mixedMoment B node1493 node1493Labels := by
  calc
    mixedMoment B raw776 raw776Labels = mixedMoment B raw776step0 raw776step0Labels := by
      have ha : raw776step0 = (fun i j => raw776 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw776step0 raw776; decide +kernel
      have hl : raw776step0Labels = raw776Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw776 raw776Labels permutation32 permutation6
    mixedMoment B raw776step0 raw776step0Labels = mixedMoment B raw776step1 raw776step1Labels := by
      have ha : raw776step1 = -raw776step0 := by apply Matrix.ext; change ∀ i j, raw776step1 i j = -(raw776step0 i j); unfold raw776step1 raw776step0; decide +kernel
      have hl : raw776step1Labels = raw776step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw776step1 raw776step1Labels = mixedMoment B raw776step2 raw776step2Labels := by
      have ha : raw776step2 = raw776step1 := by apply Matrix.ext; unfold raw776step2 raw776step1; decide +kernel
      have hl : raw776step1Labels = labelEmbedding1 ∘ raw776step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw776step1 raw776step1Labels raw776step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1493 node1493Labels := by rfl

def raw777 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![0, 1, -1], ![-1, 4, -3]]
def raw777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw777step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw777step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw777step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw777step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw777 raw777Labels = mixedMoment B node4146 node4146Labels := by
  calc
    mixedMoment B raw777 raw777Labels = mixedMoment B raw777step0 raw777step0Labels := by
      have ha : raw777step0 = (fun i j => raw777 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw777step0 raw777; decide +kernel
      have hl : raw777step0Labels = raw777Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw777 raw777Labels permutation8 permutation4
    mixedMoment B raw777step0 raw777step0Labels = mixedMoment B raw777step1 raw777step1Labels := by
      have ha : raw777step1 = raw777step0 := by apply Matrix.ext; unfold raw777step1 raw777step0; decide +kernel
      have hl : raw777step0Labels = labelEmbedding7 ∘ raw777step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw777step0 raw777step0Labels raw777step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4146 node4146Labels := by rfl

def raw778 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![0, 1, -1], ![-1, 4, -3]]
def raw778Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw778step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw778step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw778 raw778Labels = mixedMoment B node574 node574Labels := by
  calc
    mixedMoment B raw778 raw778Labels = mixedMoment B raw778step0 raw778step0Labels := by
      have ha : raw778step0 = (fun i j => raw778 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw778step0 raw778; decide +kernel
      have hl : raw778step0Labels = raw778Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw778 raw778Labels permutation8 permutation4
    _ = mixedMoment B node574 node574Labels := by rfl

def raw779 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![0, 1, -1], ![-1, 4, -3]]
def raw779Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw779step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, 0, 1], ![-3, -1, 4]]
def raw779step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw779step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![3, 1, -4]]
def raw779step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw779step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![3, 1, -4]]
def raw779step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw779 raw779Labels = mixedMoment B node1494 node1494Labels := by
  calc
    mixedMoment B raw779 raw779Labels = mixedMoment B raw779step0 raw779step0Labels := by
      have ha : raw779step0 = (fun i j => raw779 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw779step0 raw779; decide +kernel
      have hl : raw779step0Labels = raw779Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw779 raw779Labels permutation8 permutation6
    mixedMoment B raw779step0 raw779step0Labels = mixedMoment B raw779step1 raw779step1Labels := by
      have ha : raw779step1 = -raw779step0 := by apply Matrix.ext; change ∀ i j, raw779step1 i j = -(raw779step0 i j); unfold raw779step1 raw779step0; decide +kernel
      have hl : raw779step1Labels = raw779step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw779step1 raw779step1Labels = mixedMoment B raw779step2 raw779step2Labels := by
      have ha : raw779step2 = raw779step1 := by apply Matrix.ext; unfold raw779step2 raw779step1; decide +kernel
      have hl : raw779step1Labels = labelEmbedding1 ∘ raw779step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw779step1 raw779step1Labels raw779step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1494 node1494Labels := by rfl

def raw780 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, 3, -3]]
def raw780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw780step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw780step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw780step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw780step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw780 raw780Labels = mixedMoment B node4147 node4147Labels := by
  calc
    mixedMoment B raw780 raw780Labels = mixedMoment B raw780step0 raw780step0Labels := by
      have ha : raw780step0 = (fun i j => raw780 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw780step0 raw780; decide +kernel
      have hl : raw780step0Labels = raw780Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw780 raw780Labels permutation8 permutation4
    mixedMoment B raw780step0 raw780step0Labels = mixedMoment B raw780step1 raw780step1Labels := by
      have ha : raw780step1 = raw780step0 := by apply Matrix.ext; unfold raw780step1 raw780step0; decide +kernel
      have hl : raw780step0Labels = labelEmbedding7 ∘ raw780step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw780step0 raw780step0Labels raw780step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4147 node4147Labels := by rfl

def raw781 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, 3, -3]]
def raw781Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw781step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw781step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw781 raw781Labels = mixedMoment B node575 node575Labels := by
  calc
    mixedMoment B raw781 raw781Labels = mixedMoment B raw781step0 raw781step0Labels := by
      have ha : raw781step0 = (fun i j => raw781 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw781step0 raw781; decide +kernel
      have hl : raw781step0Labels = raw781Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw781 raw781Labels permutation8 permutation4
    _ = mixedMoment B node575 node575Labels := by rfl

def raw782 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, 3, -3]]
def raw782Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw782step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, -1, 2], ![-3, 0, 3]]
def raw782step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw782step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 1, -2], ![3, 0, -3]]
def raw782step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw782step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 1, -2], ![3, 0, -3]]
def raw782step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw782 raw782Labels = mixedMoment B node1495 node1495Labels := by
  calc
    mixedMoment B raw782 raw782Labels = mixedMoment B raw782step0 raw782step0Labels := by
      have ha : raw782step0 = (fun i j => raw782 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw782step0 raw782; decide +kernel
      have hl : raw782step0Labels = raw782Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw782 raw782Labels permutation8 permutation6
    mixedMoment B raw782step0 raw782step0Labels = mixedMoment B raw782step1 raw782step1Labels := by
      have ha : raw782step1 = -raw782step0 := by apply Matrix.ext; change ∀ i j, raw782step1 i j = -(raw782step0 i j); unfold raw782step1 raw782step0; decide +kernel
      have hl : raw782step1Labels = raw782step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw782step1 raw782step1Labels = mixedMoment B raw782step2 raw782step2Labels := by
      have ha : raw782step2 = raw782step1 := by apply Matrix.ext; unfold raw782step2 raw782step1; decide +kernel
      have hl : raw782step1Labels = labelEmbedding1 ∘ raw782step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw782step1 raw782step1Labels raw782step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1495 node1495Labels := by rfl

def raw783 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![0, 2, -2], ![-1, 3, -2]]
def raw783Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw783step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw783step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw783step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw783step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw783 raw783Labels = mixedMoment B node4148 node4148Labels := by
  calc
    mixedMoment B raw783 raw783Labels = mixedMoment B raw783step0 raw783step0Labels := by
      have ha : raw783step0 = (fun i j => raw783 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw783step0 raw783; decide +kernel
      have hl : raw783step0Labels = raw783Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw783 raw783Labels permutation8 permutation4
    mixedMoment B raw783step0 raw783step0Labels = mixedMoment B raw783step1 raw783step1Labels := by
      have ha : raw783step1 = raw783step0 := by apply Matrix.ext; unfold raw783step1 raw783step0; decide +kernel
      have hl : raw783step0Labels = labelEmbedding7 ∘ raw783step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw783step0 raw783step0Labels raw783step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4148 node4148Labels := by rfl

def raw784 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![0, 2, -2], ![-1, 3, -2]]
def raw784Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw784step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw784step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw784 raw784Labels = mixedMoment B node576 node576Labels := by
  calc
    mixedMoment B raw784 raw784Labels = mixedMoment B raw784step0 raw784step0Labels := by
      have ha : raw784step0 = (fun i j => raw784 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw784step0 raw784; decide +kernel
      have hl : raw784step0Labels = raw784Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw784 raw784Labels permutation8 permutation4
    _ = mixedMoment B node576 node576Labels := by rfl

def raw785 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 0, 1], ![0, 2, -2], ![-1, 3, -2]]
def raw785Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw785step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-2, 0, 2], ![-2, -1, 3]]
def raw785step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw785step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![2, 0, -2], ![2, 1, -3]]
def raw785step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw785step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![2, 0, -2], ![2, 1, -3]]
def raw785step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw785 raw785Labels = mixedMoment B node1496 node1496Labels := by
  calc
    mixedMoment B raw785 raw785Labels = mixedMoment B raw785step0 raw785step0Labels := by
      have ha : raw785step0 = (fun i j => raw785 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw785step0 raw785; decide +kernel
      have hl : raw785step0Labels = raw785Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw785 raw785Labels permutation8 permutation6
    mixedMoment B raw785step0 raw785step0Labels = mixedMoment B raw785step1 raw785step1Labels := by
      have ha : raw785step1 = -raw785step0 := by apply Matrix.ext; change ∀ i j, raw785step1 i j = -(raw785step0 i j); unfold raw785step1 raw785step0; decide +kernel
      have hl : raw785step1Labels = raw785step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw785step1 raw785step1Labels = mixedMoment B raw785step2 raw785step2Labels := by
      have ha : raw785step2 = raw785step1 := by apply Matrix.ext; unfold raw785step2 raw785step1; decide +kernel
      have hl : raw785step1Labels = labelEmbedding1 ∘ raw785step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw785step1 raw785step1Labels raw785step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1496 node1496Labels := by rfl

def raw786 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw786Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw786step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw786step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw786step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw786 raw786Labels = mixedMoment B node4164 node4164Labels := by
  calc
    mixedMoment B raw786 raw786Labels = mixedMoment B raw786step0 raw786step0Labels := by
      have ha : raw786step0 = (fun i j => raw786 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw786step0 raw786; decide +kernel
      have hl : raw786step0Labels = raw786Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw786 raw786Labels permutation152 permutation4
    mixedMoment B raw786step0 raw786step0Labels = mixedMoment B raw786step1 raw786step1Labels := by
      have ha : raw786step1 = raw786step0 := by apply Matrix.ext; unfold raw786step1 raw786step0; decide +kernel
      have hl : raw786step0Labels = labelEmbedding7 ∘ raw786step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw786step0 raw786step0Labels raw786step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4164 node4164Labels := by rfl

def raw787 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw787Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw787step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw787 raw787Labels = mixedMoment B node592 node592Labels := by
  calc
    mixedMoment B raw787 raw787Labels = mixedMoment B raw787step0 raw787step0Labels := by
      have ha : raw787step0 = (fun i j => raw787 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw787step0 raw787; decide +kernel
      have hl : raw787step0Labels = raw787Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw787 raw787Labels permutation152 permutation4
    _ = mixedMoment B node592 node592Labels := by rfl

def raw788 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw788Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw788step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw788step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw788step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw788step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw788step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw788 raw788Labels = mixedMoment B node1497 node1497Labels := by
  calc
    mixedMoment B raw788 raw788Labels = mixedMoment B raw788step0 raw788step0Labels := by
      have ha : raw788step0 = (fun i j => raw788 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw788step0 raw788; decide +kernel
      have hl : raw788step0Labels = raw788Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw788 raw788Labels permutation152 permutation6
    mixedMoment B raw788step0 raw788step0Labels = mixedMoment B raw788step1 raw788step1Labels := by
      have ha : raw788step1 = -raw788step0 := by apply Matrix.ext; change ∀ i j, raw788step1 i j = -(raw788step0 i j); unfold raw788step1 raw788step0; decide +kernel
      have hl : raw788step1Labels = raw788step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw788step1 raw788step1Labels = mixedMoment B raw788step2 raw788step2Labels := by
      have ha : raw788step2 = raw788step1 := by apply Matrix.ext; unfold raw788step2 raw788step1; decide +kernel
      have hl : raw788step1Labels = labelEmbedding1 ∘ raw788step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw788step1 raw788step1Labels raw788step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1497 node1497Labels := by rfl

def raw789 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw789Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw789step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw789step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw789 raw789Labels = mixedMoment B node4165 node4165Labels := by
  calc
    mixedMoment B raw789 raw789Labels = mixedMoment B raw789step0 raw789step0Labels := by
      have ha : raw789step0 = (fun i j => raw789 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw789step0 raw789; decide +kernel
      have hl : raw789step0Labels = raw789Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw789 raw789Labels permutation32 permutation4
    mixedMoment B raw789step0 raw789step0Labels = mixedMoment B raw789step1 raw789step1Labels := by
      have ha : raw789step1 = raw789step0 := by apply Matrix.ext; unfold raw789step1 raw789step0; decide +kernel
      have hl : raw789step0Labels = labelEmbedding7 ∘ raw789step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw789step0 raw789step0Labels raw789step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4165 node4165Labels := by rfl

def raw790 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw790Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw790step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw790 raw790Labels = mixedMoment B node593 node593Labels := by
  calc
    mixedMoment B raw790 raw790Labels = mixedMoment B raw790step0 raw790step0Labels := by
      have ha : raw790step0 = (fun i j => raw790 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw790step0 raw790; decide +kernel
      have hl : raw790step0Labels = raw790Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw790 raw790Labels permutation32 permutation4
    _ = mixedMoment B node593 node593Labels := by rfl

def raw791 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw791Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw791step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw791step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw791step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw791step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw791 raw791Labels = mixedMoment B node1498 node1498Labels := by
  calc
    mixedMoment B raw791 raw791Labels = mixedMoment B raw791step0 raw791step0Labels := by
      have ha : raw791step0 = (fun i j => raw791 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw791step0 raw791; decide +kernel
      have hl : raw791step0Labels = raw791Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw791 raw791Labels permutation32 permutation6
    mixedMoment B raw791step0 raw791step0Labels = mixedMoment B raw791step1 raw791step1Labels := by
      have ha : raw791step1 = -raw791step0 := by apply Matrix.ext; change ∀ i j, raw791step1 i j = -(raw791step0 i j); unfold raw791step1 raw791step0; decide +kernel
      have hl : raw791step1Labels = raw791step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw791step1 raw791step1Labels = mixedMoment B raw791step2 raw791step2Labels := by
      have ha : raw791step2 = raw791step1 := by apply Matrix.ext; unfold raw791step2 raw791step1; decide +kernel
      have hl : raw791step1Labels = labelEmbedding1 ∘ raw791step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw791step1 raw791step1Labels raw791step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1498 node1498Labels := by rfl

def raw792 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 3, -3]]
def raw792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw792step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw792step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw792step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw792step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw792 raw792Labels = mixedMoment B node4166 node4166Labels := by
  calc
    mixedMoment B raw792 raw792Labels = mixedMoment B raw792step0 raw792step0Labels := by
      have ha : raw792step0 = (fun i j => raw792 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw792step0 raw792; decide +kernel
      have hl : raw792step0Labels = raw792Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw792 raw792Labels permutation8 permutation4
    mixedMoment B raw792step0 raw792step0Labels = mixedMoment B raw792step1 raw792step1Labels := by
      have ha : raw792step1 = raw792step0 := by apply Matrix.ext; unfold raw792step1 raw792step0; decide +kernel
      have hl : raw792step0Labels = labelEmbedding7 ∘ raw792step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw792step0 raw792step0Labels raw792step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4166 node4166Labels := by rfl

def raw793 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 3, -3]]
def raw793Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw793step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw793step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw793 raw793Labels = mixedMoment B node594 node594Labels := by
  calc
    mixedMoment B raw793 raw793Labels = mixedMoment B raw793step0 raw793step0Labels := by
      have ha : raw793step0 = (fun i j => raw793 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw793step0 raw793; decide +kernel
      have hl : raw793step0Labels = raw793Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw793 raw793Labels permutation8 permutation4
    _ = mixedMoment B node594 node594Labels := by rfl

def raw794 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 3, -3]]
def raw794Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw794step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -2, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw794step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw794step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![3, 0, -3]]
def raw794step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw794step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![3, 0, -3]]
def raw794step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw794 raw794Labels = mixedMoment B node1499 node1499Labels := by
  calc
    mixedMoment B raw794 raw794Labels = mixedMoment B raw794step0 raw794step0Labels := by
      have ha : raw794step0 = (fun i j => raw794 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw794step0 raw794; decide +kernel
      have hl : raw794step0Labels = raw794Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw794 raw794Labels permutation8 permutation6
    mixedMoment B raw794step0 raw794step0Labels = mixedMoment B raw794step1 raw794step1Labels := by
      have ha : raw794step1 = -raw794step0 := by apply Matrix.ext; change ∀ i j, raw794step1 i j = -(raw794step0 i j); unfold raw794step1 raw794step0; decide +kernel
      have hl : raw794step1Labels = raw794step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw794step1 raw794step1Labels = mixedMoment B raw794step2 raw794step2Labels := by
      have ha : raw794step2 = raw794step1 := by apply Matrix.ext; unfold raw794step2 raw794step1; decide +kernel
      have hl : raw794step1Labels = labelEmbedding1 ∘ raw794step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw794step1 raw794step1Labels raw794step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1499 node1499Labels := by rfl

def raw795 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw795step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw795step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw795step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw795step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw795 raw795Labels = mixedMoment B node4167 node4167Labels := by
  calc
    mixedMoment B raw795 raw795Labels = mixedMoment B raw795step0 raw795step0Labels := by
      have ha : raw795step0 = (fun i j => raw795 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw795step0 raw795; decide +kernel
      have hl : raw795step0Labels = raw795Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw795 raw795Labels permutation8 permutation4
    mixedMoment B raw795step0 raw795step0Labels = mixedMoment B raw795step1 raw795step1Labels := by
      have ha : raw795step1 = raw795step0 := by apply Matrix.ext; unfold raw795step1 raw795step0; decide +kernel
      have hl : raw795step0Labels = labelEmbedding7 ∘ raw795step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw795step0 raw795step0Labels raw795step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4167 node4167Labels := by rfl

def raw796 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw796Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw796step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw796step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw796 raw796Labels = mixedMoment B node595 node595Labels := by
  calc
    mixedMoment B raw796 raw796Labels = mixedMoment B raw796step0 raw796step0Labels := by
      have ha : raw796step0 = (fun i j => raw796 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw796step0 raw796; decide +kernel
      have hl : raw796step0Labels = raw796Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw796 raw796Labels permutation8 permutation4
    _ = mixedMoment B node595 node595Labels := by rfl

def raw797 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw797Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw797step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -2, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw797step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw797step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![2, 0, -2], ![2, 0, -2]]
def raw797step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw797step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![2, 0, -2], ![2, 0, -2]]
def raw797step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw797 raw797Labels = mixedMoment B node1500 node1500Labels := by
  calc
    mixedMoment B raw797 raw797Labels = mixedMoment B raw797step0 raw797step0Labels := by
      have ha : raw797step0 = (fun i j => raw797 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw797step0 raw797; decide +kernel
      have hl : raw797step0Labels = raw797Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw797 raw797Labels permutation8 permutation6
    mixedMoment B raw797step0 raw797step0Labels = mixedMoment B raw797step1 raw797step1Labels := by
      have ha : raw797step1 = -raw797step0 := by apply Matrix.ext; change ∀ i j, raw797step1 i j = -(raw797step0 i j); unfold raw797step1 raw797step0; decide +kernel
      have hl : raw797step1Labels = raw797step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw797step1 raw797step1Labels = mixedMoment B raw797step2 raw797step2Labels := by
      have ha : raw797step2 = raw797step1 := by apply Matrix.ext; unfold raw797step2 raw797step1; decide +kernel
      have hl : raw797step1Labels = labelEmbedding1 ∘ raw797step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw797step1 raw797step1Labels raw797step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1500 node1500Labels := by rfl

def raw798 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 1, 1], ![0, 4, -4]]
def raw798Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw798step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![4, 0, -4]]
def raw798step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw798step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![4, 0, -4]]
def raw798step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw798 raw798Labels = mixedMoment B node4168 node4168Labels := by
  calc
    mixedMoment B raw798 raw798Labels = mixedMoment B raw798step0 raw798step0Labels := by
      have ha : raw798step0 = (fun i j => raw798 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw798step0 raw798; decide +kernel
      have hl : raw798step0Labels = raw798Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw798 raw798Labels permutation2 permutation4
    mixedMoment B raw798step0 raw798step0Labels = mixedMoment B raw798step1 raw798step1Labels := by
      have ha : raw798step1 = raw798step0 := by apply Matrix.ext; unfold raw798step1 raw798step0; decide +kernel
      have hl : raw798step0Labels = labelEmbedding7 ∘ raw798step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw798step0 raw798step0Labels raw798step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4168 node4168Labels := by rfl

def raw799 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 1, 1], ![0, 4, -4]]
def raw799Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw799step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![4, 0, -4]]
def raw799step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw799 raw799Labels = mixedMoment B node596 node596Labels := by
  calc
    mixedMoment B raw799 raw799Labels = mixedMoment B raw799step0 raw799step0Labels := by
      have ha : raw799step0 = (fun i j => raw799 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw799step0 raw799; decide +kernel
      have hl : raw799step0Labels = raw799Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw799 raw799Labels permutation2 permutation4
    _ = mixedMoment B node596 node596Labels := by rfl

def raw800 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 1, 1], ![0, 4, -4]]
def raw800Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw800step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![3, 2, -5]]
def raw800step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw800step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![3, 2, -5]]
def raw800step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw800 raw800Labels = mixedMoment B node845 node845Labels := by
  calc
    mixedMoment B raw800 raw800Labels = mixedMoment B raw800step0 raw800step0Labels := by
      have ha : raw800step0 = (fun i j => raw800 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw800step0 raw800; decide +kernel
      have hl : raw800step0Labels = raw800Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw800 raw800Labels permutation7 permutation6
    mixedMoment B raw800step0 raw800step0Labels = mixedMoment B raw800step1 raw800step1Labels := by
      have ha : raw800step1 = raw800step0 := by apply Matrix.ext; unfold raw800step1 raw800step0; decide +kernel
      have hl : raw800step0Labels = labelEmbedding1 ∘ raw800step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw800step0 raw800step0Labels raw800step1Labels labelEmbedding1 hl
    _ = mixedMoment B node845 node845Labels := by rfl

def raw801 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw801Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw801step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw801step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw801step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw801 raw801Labels = mixedMoment B node4171 node4171Labels := by
  calc
    mixedMoment B raw801 raw801Labels = mixedMoment B raw801step0 raw801step0Labels := by
      have ha : raw801step0 = (fun i j => raw801 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw801step0 raw801; decide +kernel
      have hl : raw801step0Labels = raw801Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw801 raw801Labels permutation152 permutation4
    mixedMoment B raw801step0 raw801step0Labels = mixedMoment B raw801step1 raw801step1Labels := by
      have ha : raw801step1 = raw801step0 := by apply Matrix.ext; unfold raw801step1 raw801step0; decide +kernel
      have hl : raw801step0Labels = labelEmbedding7 ∘ raw801step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw801step0 raw801step0Labels raw801step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4171 node4171Labels := by rfl

def raw802 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw802Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw802step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw802 raw802Labels = mixedMoment B node599 node599Labels := by
  calc
    mixedMoment B raw802 raw802Labels = mixedMoment B raw802step0 raw802step0Labels := by
      have ha : raw802step0 = (fun i j => raw802 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw802step0 raw802; decide +kernel
      have hl : raw802step0Labels = raw802Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw802 raw802Labels permutation152 permutation4
    _ = mixedMoment B node599 node599Labels := by rfl

def raw803 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw803Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw803step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw803step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw803step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw803step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw803step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw803 raw803Labels = mixedMoment B node1506 node1506Labels := by
  calc
    mixedMoment B raw803 raw803Labels = mixedMoment B raw803step0 raw803step0Labels := by
      have ha : raw803step0 = (fun i j => raw803 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw803step0 raw803; decide +kernel
      have hl : raw803step0Labels = raw803Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw803 raw803Labels permutation152 permutation6
    mixedMoment B raw803step0 raw803step0Labels = mixedMoment B raw803step1 raw803step1Labels := by
      have ha : raw803step1 = -raw803step0 := by apply Matrix.ext; change ∀ i j, raw803step1 i j = -(raw803step0 i j); unfold raw803step1 raw803step0; decide +kernel
      have hl : raw803step1Labels = raw803step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw803step1 raw803step1Labels = mixedMoment B raw803step2 raw803step2Labels := by
      have ha : raw803step2 = raw803step1 := by apply Matrix.ext; unfold raw803step2 raw803step1; decide +kernel
      have hl : raw803step1Labels = labelEmbedding1 ∘ raw803step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw803step1 raw803step1Labels raw803step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1506 node1506Labels := by rfl

def raw804 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw804Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw804step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw804step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw804 raw804Labels = mixedMoment B node4172 node4172Labels := by
  calc
    mixedMoment B raw804 raw804Labels = mixedMoment B raw804step0 raw804step0Labels := by
      have ha : raw804step0 = (fun i j => raw804 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw804step0 raw804; decide +kernel
      have hl : raw804step0Labels = raw804Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw804 raw804Labels permutation32 permutation4
    mixedMoment B raw804step0 raw804step0Labels = mixedMoment B raw804step1 raw804step1Labels := by
      have ha : raw804step1 = raw804step0 := by apply Matrix.ext; unfold raw804step1 raw804step0; decide +kernel
      have hl : raw804step0Labels = labelEmbedding7 ∘ raw804step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw804step0 raw804step0Labels raw804step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4172 node4172Labels := by rfl

def raw805 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw805Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw805step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw805 raw805Labels = mixedMoment B node600 node600Labels := by
  calc
    mixedMoment B raw805 raw805Labels = mixedMoment B raw805step0 raw805step0Labels := by
      have ha : raw805step0 = (fun i j => raw805 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw805step0 raw805; decide +kernel
      have hl : raw805step0Labels = raw805Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw805 raw805Labels permutation32 permutation4
    _ = mixedMoment B node600 node600Labels := by rfl

def raw806 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw806Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw806step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw806step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw806step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw806step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw806 raw806Labels = mixedMoment B node1507 node1507Labels := by
  calc
    mixedMoment B raw806 raw806Labels = mixedMoment B raw806step0 raw806step0Labels := by
      have ha : raw806step0 = (fun i j => raw806 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw806step0 raw806; decide +kernel
      have hl : raw806step0Labels = raw806Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw806 raw806Labels permutation32 permutation6
    mixedMoment B raw806step0 raw806step0Labels = mixedMoment B raw806step1 raw806step1Labels := by
      have ha : raw806step1 = -raw806step0 := by apply Matrix.ext; change ∀ i j, raw806step1 i j = -(raw806step0 i j); unfold raw806step1 raw806step0; decide +kernel
      have hl : raw806step1Labels = raw806step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw806step1 raw806step1Labels = mixedMoment B raw806step2 raw806step2Labels := by
      have ha : raw806step2 = raw806step1 := by apply Matrix.ext; unfold raw806step2 raw806step1; decide +kernel
      have hl : raw806step1Labels = labelEmbedding1 ∘ raw806step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw806step1 raw806step1Labels raw806step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1507 node1507Labels := by rfl

def raw807 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw807Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw807step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw807step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw807step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw807step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw807 raw807Labels = mixedMoment B node4174 node4174Labels := by
  calc
    mixedMoment B raw807 raw807Labels = mixedMoment B raw807step0 raw807step0Labels := by
      have ha : raw807step0 = (fun i j => raw807 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw807step0 raw807; decide +kernel
      have hl : raw807step0Labels = raw807Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw807 raw807Labels permutation8 permutation4
    mixedMoment B raw807step0 raw807step0Labels = mixedMoment B raw807step1 raw807step1Labels := by
      have ha : raw807step1 = raw807step0 := by apply Matrix.ext; unfold raw807step1 raw807step0; decide +kernel
      have hl : raw807step0Labels = labelEmbedding7 ∘ raw807step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw807step0 raw807step0Labels raw807step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4174 node4174Labels := by rfl

def raw808 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw808Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw808step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw808step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw808 raw808Labels = mixedMoment B node602 node602Labels := by
  calc
    mixedMoment B raw808 raw808Labels = mixedMoment B raw808step0 raw808step0Labels := by
      have ha : raw808step0 = (fun i j => raw808 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw808step0 raw808; decide +kernel
      have hl : raw808step0Labels = raw808Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw808 raw808Labels permutation8 permutation4
    _ = mixedMoment B node602 node602Labels := by rfl

def raw809 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw809Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw809step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw809step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw809step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw809step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw809step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw809step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw809 raw809Labels = mixedMoment B node1509 node1509Labels := by
  calc
    mixedMoment B raw809 raw809Labels = mixedMoment B raw809step0 raw809step0Labels := by
      have ha : raw809step0 = (fun i j => raw809 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw809step0 raw809; decide +kernel
      have hl : raw809step0Labels = raw809Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw809 raw809Labels permutation8 permutation6
    mixedMoment B raw809step0 raw809step0Labels = mixedMoment B raw809step1 raw809step1Labels := by
      have ha : raw809step1 = -raw809step0 := by apply Matrix.ext; change ∀ i j, raw809step1 i j = -(raw809step0 i j); unfold raw809step1 raw809step0; decide +kernel
      have hl : raw809step1Labels = raw809step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw809step1 raw809step1Labels = mixedMoment B raw809step2 raw809step2Labels := by
      have ha : raw809step2 = raw809step1 := by apply Matrix.ext; unfold raw809step2 raw809step1; decide +kernel
      have hl : raw809step1Labels = labelEmbedding1 ∘ raw809step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw809step1 raw809step1Labels raw809step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1509 node1509Labels := by rfl

def raw810 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw810Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw810step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw810step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw810step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw810 raw810Labels = mixedMoment B node4175 node4175Labels := by
  calc
    mixedMoment B raw810 raw810Labels = mixedMoment B raw810step0 raw810step0Labels := by
      have ha : raw810step0 = (fun i j => raw810 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw810step0 raw810; decide +kernel
      have hl : raw810step0Labels = raw810Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw810 raw810Labels permutation32 permutation4
    mixedMoment B raw810step0 raw810step0Labels = mixedMoment B raw810step1 raw810step1Labels := by
      have ha : raw810step1 = raw810step0 := by apply Matrix.ext; unfold raw810step1 raw810step0; decide +kernel
      have hl : raw810step0Labels = labelEmbedding7 ∘ raw810step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw810step0 raw810step0Labels raw810step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4175 node4175Labels := by rfl

def raw811 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw811Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw811step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw811 raw811Labels = mixedMoment B node603 node603Labels := by
  calc
    mixedMoment B raw811 raw811Labels = mixedMoment B raw811step0 raw811step0Labels := by
      have ha : raw811step0 = (fun i j => raw811 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw811step0 raw811; decide +kernel
      have hl : raw811step0Labels = raw811Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw811 raw811Labels permutation32 permutation4
    _ = mixedMoment B node603 node603Labels := by rfl

def raw812 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw812Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw812step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw812step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw812step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw812step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw812 raw812Labels = mixedMoment B node1517 node1517Labels := by
  calc
    mixedMoment B raw812 raw812Labels = mixedMoment B raw812step0 raw812step0Labels := by
      have ha : raw812step0 = (fun i j => raw812 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw812step0 raw812; decide +kernel
      have hl : raw812step0Labels = raw812Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw812 raw812Labels permutation32 permutation6
    mixedMoment B raw812step0 raw812step0Labels = mixedMoment B raw812step1 raw812step1Labels := by
      have ha : raw812step1 = -raw812step0 := by apply Matrix.ext; change ∀ i j, raw812step1 i j = -(raw812step0 i j); unfold raw812step1 raw812step0; decide +kernel
      have hl : raw812step1Labels = raw812step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw812step1 raw812step1Labels = mixedMoment B raw812step2 raw812step2Labels := by
      have ha : raw812step2 = raw812step1 := by apply Matrix.ext; unfold raw812step2 raw812step1; decide +kernel
      have hl : raw812step1Labels = labelEmbedding1 ∘ raw812step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw812step1 raw812step1Labels raw812step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1517 node1517Labels := by rfl

def raw813 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw813Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw813step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw813step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw813step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw813step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw813 raw813Labels = mixedMoment B node4177 node4177Labels := by
  calc
    mixedMoment B raw813 raw813Labels = mixedMoment B raw813step0 raw813step0Labels := by
      have ha : raw813step0 = (fun i j => raw813 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw813step0 raw813; decide +kernel
      have hl : raw813step0Labels = raw813Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw813 raw813Labels permutation8 permutation4
    mixedMoment B raw813step0 raw813step0Labels = mixedMoment B raw813step1 raw813step1Labels := by
      have ha : raw813step1 = raw813step0 := by apply Matrix.ext; unfold raw813step1 raw813step0; decide +kernel
      have hl : raw813step0Labels = labelEmbedding7 ∘ raw813step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw813step0 raw813step0Labels raw813step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4177 node4177Labels := by rfl

def raw814 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw814Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw814step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw814step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw814 raw814Labels = mixedMoment B node605 node605Labels := by
  calc
    mixedMoment B raw814 raw814Labels = mixedMoment B raw814step0 raw814step0Labels := by
      have ha : raw814step0 = (fun i j => raw814 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw814step0 raw814; decide +kernel
      have hl : raw814step0Labels = raw814Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw814 raw814Labels permutation8 permutation4
    _ = mixedMoment B node605 node605Labels := by rfl

def raw815 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw815Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw815step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw815step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw815step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw815step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw815step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw815step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw815 raw815Labels = mixedMoment B node1518 node1518Labels := by
  calc
    mixedMoment B raw815 raw815Labels = mixedMoment B raw815step0 raw815step0Labels := by
      have ha : raw815step0 = (fun i j => raw815 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw815step0 raw815; decide +kernel
      have hl : raw815step0Labels = raw815Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw815 raw815Labels permutation8 permutation6
    mixedMoment B raw815step0 raw815step0Labels = mixedMoment B raw815step1 raw815step1Labels := by
      have ha : raw815step1 = -raw815step0 := by apply Matrix.ext; change ∀ i j, raw815step1 i j = -(raw815step0 i j); unfold raw815step1 raw815step0; decide +kernel
      have hl : raw815step1Labels = raw815step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw815step1 raw815step1Labels = mixedMoment B raw815step2 raw815step2Labels := by
      have ha : raw815step2 = raw815step1 := by apply Matrix.ext; unfold raw815step2 raw815step1; decide +kernel
      have hl : raw815step1Labels = labelEmbedding1 ∘ raw815step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw815step1 raw815step1Labels raw815step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1518 node1518Labels := by rfl

def raw816 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw816Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw816step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw816step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw816step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw816step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw816 raw816Labels = mixedMoment B node4180 node4180Labels := by
  calc
    mixedMoment B raw816 raw816Labels = mixedMoment B raw816step0 raw816step0Labels := by
      have ha : raw816step0 = (fun i j => raw816 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw816step0 raw816; decide +kernel
      have hl : raw816step0Labels = raw816Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw816 raw816Labels permutation8 permutation4
    mixedMoment B raw816step0 raw816step0Labels = mixedMoment B raw816step1 raw816step1Labels := by
      have ha : raw816step1 = raw816step0 := by apply Matrix.ext; unfold raw816step1 raw816step0; decide +kernel
      have hl : raw816step0Labels = labelEmbedding7 ∘ raw816step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw816step0 raw816step0Labels raw816step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4180 node4180Labels := by rfl

def raw817 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw817Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw817step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw817step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw817 raw817Labels = mixedMoment B node608 node608Labels := by
  calc
    mixedMoment B raw817 raw817Labels = mixedMoment B raw817step0 raw817step0Labels := by
      have ha : raw817step0 = (fun i j => raw817 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw817step0 raw817; decide +kernel
      have hl : raw817step0Labels = raw817Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw817 raw817Labels permutation8 permutation4
    _ = mixedMoment B node608 node608Labels := by rfl

def raw818 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw818Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw818step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw818step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw818step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw818step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw818step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw818step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw818 raw818Labels = mixedMoment B node1519 node1519Labels := by
  calc
    mixedMoment B raw818 raw818Labels = mixedMoment B raw818step0 raw818step0Labels := by
      have ha : raw818step0 = (fun i j => raw818 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw818step0 raw818; decide +kernel
      have hl : raw818step0Labels = raw818Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw818 raw818Labels permutation8 permutation6
    mixedMoment B raw818step0 raw818step0Labels = mixedMoment B raw818step1 raw818step1Labels := by
      have ha : raw818step1 = -raw818step0 := by apply Matrix.ext; change ∀ i j, raw818step1 i j = -(raw818step0 i j); unfold raw818step1 raw818step0; decide +kernel
      have hl : raw818step1Labels = raw818step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw818step1 raw818step1Labels = mixedMoment B raw818step2 raw818step2Labels := by
      have ha : raw818step2 = raw818step1 := by apply Matrix.ext; unfold raw818step2 raw818step1; decide +kernel
      have hl : raw818step1Labels = labelEmbedding1 ∘ raw818step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw818step1 raw818step1Labels raw818step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1519 node1519Labels := by rfl

def raw819 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 4, -3]]
def raw819Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw819step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw819step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw819step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw819step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw819 raw819Labels = mixedMoment B node4181 node4181Labels := by
  calc
    mixedMoment B raw819 raw819Labels = mixedMoment B raw819step0 raw819step0Labels := by
      have ha : raw819step0 = (fun i j => raw819 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw819step0 raw819; decide +kernel
      have hl : raw819step0Labels = raw819Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw819 raw819Labels permutation2 permutation4
    mixedMoment B raw819step0 raw819step0Labels = mixedMoment B raw819step1 raw819step1Labels := by
      have ha : raw819step1 = raw819step0 := by apply Matrix.ext; unfold raw819step1 raw819step0; decide +kernel
      have hl : raw819step0Labels = labelEmbedding7 ∘ raw819step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw819step0 raw819step0Labels raw819step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4181 node4181Labels := by rfl

def raw820 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 4, -3]]
def raw820Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw820step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw820step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw820 raw820Labels = mixedMoment B node609 node609Labels := by
  calc
    mixedMoment B raw820 raw820Labels = mixedMoment B raw820step0 raw820step0Labels := by
      have ha : raw820step0 = (fun i j => raw820 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw820step0 raw820; decide +kernel
      have hl : raw820step0Labels = raw820Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw820 raw820Labels permutation2 permutation4
    _ = mixedMoment B node609 node609Labels := by rfl

def raw821 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 1, 0], ![-1, 4, -3]]
def raw821Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw821step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-3, -1, 4]]
def raw821step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw821step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw821step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw821step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw821step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw821 raw821Labels = mixedMoment B node1521 node1521Labels := by
  calc
    mixedMoment B raw821 raw821Labels = mixedMoment B raw821step0 raw821step0Labels := by
      have ha : raw821step0 = (fun i j => raw821 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw821step0 raw821; decide +kernel
      have hl : raw821step0Labels = raw821Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw821 raw821Labels permutation2 permutation6
    mixedMoment B raw821step0 raw821step0Labels = mixedMoment B raw821step1 raw821step1Labels := by
      have ha : raw821step1 = -raw821step0 := by apply Matrix.ext; change ∀ i j, raw821step1 i j = -(raw821step0 i j); unfold raw821step1 raw821step0; decide +kernel
      have hl : raw821step1Labels = raw821step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw821step1 raw821step1Labels = mixedMoment B raw821step2 raw821step2Labels := by
      have ha : raw821step2 = raw821step1 := by apply Matrix.ext; unfold raw821step2 raw821step1; decide +kernel
      have hl : raw821step1Labels = labelEmbedding1 ∘ raw821step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw821step1 raw821step1Labels raw821step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1521 node1521Labels := by rfl

def raw822 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw822Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw822step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw822step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw822step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw822 raw822Labels = mixedMoment B node4182 node4182Labels := by
  calc
    mixedMoment B raw822 raw822Labels = mixedMoment B raw822step0 raw822step0Labels := by
      have ha : raw822step0 = (fun i j => raw822 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw822step0 raw822; decide +kernel
      have hl : raw822step0Labels = raw822Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw822 raw822Labels permutation32 permutation4
    mixedMoment B raw822step0 raw822step0Labels = mixedMoment B raw822step1 raw822step1Labels := by
      have ha : raw822step1 = raw822step0 := by apply Matrix.ext; unfold raw822step1 raw822step0; decide +kernel
      have hl : raw822step0Labels = labelEmbedding7 ∘ raw822step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw822step0 raw822step0Labels raw822step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4182 node4182Labels := by rfl

def raw823 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw823Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw823step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw823 raw823Labels = mixedMoment B node610 node610Labels := by
  calc
    mixedMoment B raw823 raw823Labels = mixedMoment B raw823step0 raw823step0Labels := by
      have ha : raw823step0 = (fun i j => raw823 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw823step0 raw823; decide +kernel
      have hl : raw823step0Labels = raw823Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw823 raw823Labels permutation32 permutation4
    _ = mixedMoment B node610 node610Labels := by rfl

def raw824 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw824Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw824step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw824step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw824step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw824step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw824 raw824Labels = mixedMoment B node1524 node1524Labels := by
  calc
    mixedMoment B raw824 raw824Labels = mixedMoment B raw824step0 raw824step0Labels := by
      have ha : raw824step0 = (fun i j => raw824 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw824step0 raw824; decide +kernel
      have hl : raw824step0Labels = raw824Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw824 raw824Labels permutation50 permutation6
    mixedMoment B raw824step0 raw824step0Labels = mixedMoment B raw824step1 raw824step1Labels := by
      have ha : raw824step1 = -raw824step0 := by apply Matrix.ext; change ∀ i j, raw824step1 i j = -(raw824step0 i j); unfold raw824step1 raw824step0; decide +kernel
      have hl : raw824step1Labels = raw824step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw824step1 raw824step1Labels = mixedMoment B raw824step2 raw824step2Labels := by
      have ha : raw824step2 = raw824step1 := by apply Matrix.ext; unfold raw824step2 raw824step1; decide +kernel
      have hl : raw824step1Labels = labelEmbedding1 ∘ raw824step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw824step1 raw824step1Labels raw824step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1524 node1524Labels := by rfl

def raw825 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw825Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw825step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw825step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw825step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw825step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw825 raw825Labels = mixedMoment B node4183 node4183Labels := by
  calc
    mixedMoment B raw825 raw825Labels = mixedMoment B raw825step0 raw825step0Labels := by
      have ha : raw825step0 = (fun i j => raw825 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw825step0 raw825; decide +kernel
      have hl : raw825step0Labels = raw825Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw825 raw825Labels permutation8 permutation4
    mixedMoment B raw825step0 raw825step0Labels = mixedMoment B raw825step1 raw825step1Labels := by
      have ha : raw825step1 = raw825step0 := by apply Matrix.ext; unfold raw825step1 raw825step0; decide +kernel
      have hl : raw825step0Labels = labelEmbedding7 ∘ raw825step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw825step0 raw825step0Labels raw825step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4183 node4183Labels := by rfl

def raw826 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw826Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw826step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw826step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw826 raw826Labels = mixedMoment B node611 node611Labels := by
  calc
    mixedMoment B raw826 raw826Labels = mixedMoment B raw826step0 raw826step0Labels := by
      have ha : raw826step0 = (fun i j => raw826 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw826step0 raw826; decide +kernel
      have hl : raw826step0Labels = raw826Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw826 raw826Labels permutation8 permutation4
    _ = mixedMoment B node611 node611Labels := by rfl

def raw827 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw827Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw827step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw827step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw827step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw827step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw827step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw827step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw827 raw827Labels = mixedMoment B node1535 node1535Labels := by
  calc
    mixedMoment B raw827 raw827Labels = mixedMoment B raw827step0 raw827step0Labels := by
      have ha : raw827step0 = (fun i j => raw827 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw827step0 raw827; decide +kernel
      have hl : raw827step0Labels = raw827Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw827 raw827Labels permutation8 permutation6
    mixedMoment B raw827step0 raw827step0Labels = mixedMoment B raw827step1 raw827step1Labels := by
      have ha : raw827step1 = -raw827step0 := by apply Matrix.ext; change ∀ i j, raw827step1 i j = -(raw827step0 i j); unfold raw827step1 raw827step0; decide +kernel
      have hl : raw827step1Labels = raw827step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw827step1 raw827step1Labels = mixedMoment B raw827step2 raw827step2Labels := by
      have ha : raw827step2 = raw827step1 := by apply Matrix.ext; unfold raw827step2 raw827step1; decide +kernel
      have hl : raw827step1Labels = labelEmbedding1 ∘ raw827step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw827step1 raw827step1Labels raw827step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1535 node1535Labels := by rfl

def raw828 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw828Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw828step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw828step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw828step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw828step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw828 raw828Labels = mixedMoment B node4185 node4185Labels := by
  calc
    mixedMoment B raw828 raw828Labels = mixedMoment B raw828step0 raw828step0Labels := by
      have ha : raw828step0 = (fun i j => raw828 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw828step0 raw828; decide +kernel
      have hl : raw828step0Labels = raw828Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw828 raw828Labels permutation8 permutation4
    mixedMoment B raw828step0 raw828step0Labels = mixedMoment B raw828step1 raw828step1Labels := by
      have ha : raw828step1 = raw828step0 := by apply Matrix.ext; unfold raw828step1 raw828step0; decide +kernel
      have hl : raw828step0Labels = labelEmbedding7 ∘ raw828step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw828step0 raw828step0Labels raw828step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4185 node4185Labels := by rfl

def raw829 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw829Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw829step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw829step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw829 raw829Labels = mixedMoment B node613 node613Labels := by
  calc
    mixedMoment B raw829 raw829Labels = mixedMoment B raw829step0 raw829step0Labels := by
      have ha : raw829step0 = (fun i j => raw829 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw829step0 raw829; decide +kernel
      have hl : raw829step0Labels = raw829Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw829 raw829Labels permutation8 permutation4
    _ = mixedMoment B node613 node613Labels := by rfl

def raw830 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw830Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw830step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw830step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw830step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw830step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw830step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw830step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw830 raw830Labels = mixedMoment B node1525 node1525Labels := by
  calc
    mixedMoment B raw830 raw830Labels = mixedMoment B raw830step0 raw830step0Labels := by
      have ha : raw830step0 = (fun i j => raw830 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw830step0 raw830; decide +kernel
      have hl : raw830step0Labels = raw830Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw830 raw830Labels permutation10 permutation6
    mixedMoment B raw830step0 raw830step0Labels = mixedMoment B raw830step1 raw830step1Labels := by
      have ha : raw830step1 = -raw830step0 := by apply Matrix.ext; change ∀ i j, raw830step1 i j = -(raw830step0 i j); unfold raw830step1 raw830step0; decide +kernel
      have hl : raw830step1Labels = raw830step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw830step1 raw830step1Labels = mixedMoment B raw830step2 raw830step2Labels := by
      have ha : raw830step2 = raw830step1 := by apply Matrix.ext; unfold raw830step2 raw830step1; decide +kernel
      have hl : raw830step1Labels = labelEmbedding1 ∘ raw830step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw830step1 raw830step1Labels raw830step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1525 node1525Labels := by rfl

def raw831 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw831Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw831step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw831step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw831step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw831step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw831 raw831Labels = mixedMoment B node4186 node4186Labels := by
  calc
    mixedMoment B raw831 raw831Labels = mixedMoment B raw831step0 raw831step0Labels := by
      have ha : raw831step0 = (fun i j => raw831 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw831step0 raw831; decide +kernel
      have hl : raw831step0Labels = raw831Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw831 raw831Labels permutation8 permutation4
    mixedMoment B raw831step0 raw831step0Labels = mixedMoment B raw831step1 raw831step1Labels := by
      have ha : raw831step1 = raw831step0 := by apply Matrix.ext; unfold raw831step1 raw831step0; decide +kernel
      have hl : raw831step0Labels = labelEmbedding7 ∘ raw831step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw831step0 raw831step0Labels raw831step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4186 node4186Labels := by rfl

def raw832 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw832Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw832step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw832step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw832 raw832Labels = mixedMoment B node614 node614Labels := by
  calc
    mixedMoment B raw832 raw832Labels = mixedMoment B raw832step0 raw832step0Labels := by
      have ha : raw832step0 = (fun i j => raw832 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw832step0 raw832; decide +kernel
      have hl : raw832step0Labels = raw832Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw832 raw832Labels permutation8 permutation4
    _ = mixedMoment B node614 node614Labels := by rfl

def raw833 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw833Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw833step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw833step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw833step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw833step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw833step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw833step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw833 raw833Labels = mixedMoment B node1536 node1536Labels := by
  calc
    mixedMoment B raw833 raw833Labels = mixedMoment B raw833step0 raw833step0Labels := by
      have ha : raw833step0 = (fun i j => raw833 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw833step0 raw833; decide +kernel
      have hl : raw833step0Labels = raw833Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw833 raw833Labels permutation8 permutation6
    mixedMoment B raw833step0 raw833step0Labels = mixedMoment B raw833step1 raw833step1Labels := by
      have ha : raw833step1 = -raw833step0 := by apply Matrix.ext; change ∀ i j, raw833step1 i j = -(raw833step0 i j); unfold raw833step1 raw833step0; decide +kernel
      have hl : raw833step1Labels = raw833step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw833step1 raw833step1Labels = mixedMoment B raw833step2 raw833step2Labels := by
      have ha : raw833step2 = raw833step1 := by apply Matrix.ext; unfold raw833step2 raw833step1; decide +kernel
      have hl : raw833step1Labels = labelEmbedding1 ∘ raw833step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw833step1 raw833step1Labels raw833step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1536 node1536Labels := by rfl

def raw834 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-2, 4, -2]]
def raw834Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw834step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw834step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw834step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw834step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw834 raw834Labels = mixedMoment B node4187 node4187Labels := by
  calc
    mixedMoment B raw834 raw834Labels = mixedMoment B raw834step0 raw834step0Labels := by
      have ha : raw834step0 = (fun i j => raw834 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw834step0 raw834; decide +kernel
      have hl : raw834step0Labels = raw834Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw834 raw834Labels permutation2 permutation4
    mixedMoment B raw834step0 raw834step0Labels = mixedMoment B raw834step1 raw834step1Labels := by
      have ha : raw834step1 = raw834step0 := by apply Matrix.ext; unfold raw834step1 raw834step0; decide +kernel
      have hl : raw834step0Labels = labelEmbedding7 ∘ raw834step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw834step0 raw834step0Labels raw834step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4187 node4187Labels := by rfl

def raw835 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-2, 4, -2]]
def raw835Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw835step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw835step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw835 raw835Labels = mixedMoment B node615 node615Labels := by
  calc
    mixedMoment B raw835 raw835Labels = mixedMoment B raw835step0 raw835step0Labels := by
      have ha : raw835step0 = (fun i j => raw835 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw835step0 raw835; decide +kernel
      have hl : raw835step0Labels = raw835Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw835 raw835Labels permutation2 permutation4
    _ = mixedMoment B node615 node615Labels := by rfl

def raw836 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![0, 1, -1], ![-2, 4, -2]]
def raw836Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw836step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-2, -2, 4]]
def raw836step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw836step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![2, 2, -4]]
def raw836step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw836step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![2, 2, -4]]
def raw836step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw836 raw836Labels = mixedMoment B node1537 node1537Labels := by
  calc
    mixedMoment B raw836 raw836Labels = mixedMoment B raw836step0 raw836step0Labels := by
      have ha : raw836step0 = (fun i j => raw836 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw836step0 raw836; decide +kernel
      have hl : raw836step0Labels = raw836Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw836 raw836Labels permutation2 permutation6
    mixedMoment B raw836step0 raw836step0Labels = mixedMoment B raw836step1 raw836step1Labels := by
      have ha : raw836step1 = -raw836step0 := by apply Matrix.ext; change ∀ i j, raw836step1 i j = -(raw836step0 i j); unfold raw836step1 raw836step0; decide +kernel
      have hl : raw836step1Labels = raw836step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw836step1 raw836step1Labels = mixedMoment B raw836step2 raw836step2Labels := by
      have ha : raw836step2 = raw836step1 := by apply Matrix.ext; unfold raw836step2 raw836step1; decide +kernel
      have hl : raw836step1Labels = labelEmbedding1 ∘ raw836step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw836step1 raw836step1Labels raw836step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1537 node1537Labels := by rfl

def raw837 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 2, 0], ![0, 3, -3]]
def raw837Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw837step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw837step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw837step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw837step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw837 raw837Labels = mixedMoment B node4190 node4190Labels := by
  calc
    mixedMoment B raw837 raw837Labels = mixedMoment B raw837step0 raw837step0Labels := by
      have ha : raw837step0 = (fun i j => raw837 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw837step0 raw837; decide +kernel
      have hl : raw837step0Labels = raw837Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw837 raw837Labels permutation2 permutation4
    mixedMoment B raw837step0 raw837step0Labels = mixedMoment B raw837step1 raw837step1Labels := by
      have ha : raw837step1 = raw837step0 := by apply Matrix.ext; unfold raw837step1 raw837step0; decide +kernel
      have hl : raw837step0Labels = labelEmbedding7 ∘ raw837step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw837step0 raw837step0Labels raw837step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4190 node4190Labels := by rfl

def raw838 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 2, 0], ![0, 3, -3]]
def raw838Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw838step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw838step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw838 raw838Labels = mixedMoment B node618 node618Labels := by
  calc
    mixedMoment B raw838 raw838Labels = mixedMoment B raw838step0 raw838step0Labels := by
      have ha : raw838step0 = (fun i j => raw838 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw838step0 raw838; decide +kernel
      have hl : raw838step0Labels = raw838Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw838 raw838Labels permutation2 permutation4
    _ = mixedMoment B node618 node618Labels := by rfl

def raw839 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 2, 0], ![0, 3, -3]]
def raw839Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw839step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-3, 0, 3]]
def raw839step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw839step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![3, 0, -3]]
def raw839step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw839step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![3, 0, -3]]
def raw839step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw839 raw839Labels = mixedMoment B node1527 node1527Labels := by
  calc
    mixedMoment B raw839 raw839Labels = mixedMoment B raw839step0 raw839step0Labels := by
      have ha : raw839step0 = (fun i j => raw839 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw839step0 raw839; decide +kernel
      have hl : raw839step0Labels = raw839Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw839 raw839Labels permutation2 permutation6
    mixedMoment B raw839step0 raw839step0Labels = mixedMoment B raw839step1 raw839step1Labels := by
      have ha : raw839step1 = -raw839step0 := by apply Matrix.ext; change ∀ i j, raw839step1 i j = -(raw839step0 i j); unfold raw839step1 raw839step0; decide +kernel
      have hl : raw839step1Labels = raw839step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw839step1 raw839step1Labels = mixedMoment B raw839step2 raw839step2Labels := by
      have ha : raw839step2 = raw839step1 := by apply Matrix.ext; unfold raw839step2 raw839step1; decide +kernel
      have hl : raw839step1Labels = labelEmbedding1 ∘ raw839step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw839step1 raw839step1Labels raw839step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1527 node1527Labels := by rfl

def raw840 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 2, -1], ![-1, 3, -2]]
def raw840Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw840step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw840step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw840step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw840step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw840 raw840Labels = mixedMoment B node4191 node4191Labels := by
  calc
    mixedMoment B raw840 raw840Labels = mixedMoment B raw840step0 raw840step0Labels := by
      have ha : raw840step0 = (fun i j => raw840 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw840step0 raw840; decide +kernel
      have hl : raw840step0Labels = raw840Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw840 raw840Labels permutation2 permutation4
    mixedMoment B raw840step0 raw840step0Labels = mixedMoment B raw840step1 raw840step1Labels := by
      have ha : raw840step1 = raw840step0 := by apply Matrix.ext; unfold raw840step1 raw840step0; decide +kernel
      have hl : raw840step0Labels = labelEmbedding7 ∘ raw840step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw840step0 raw840step0Labels raw840step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4191 node4191Labels := by rfl

def raw841 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 2, -1], ![-1, 3, -2]]
def raw841Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw841step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw841step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw841 raw841Labels = mixedMoment B node619 node619Labels := by
  calc
    mixedMoment B raw841 raw841Labels = mixedMoment B raw841step0 raw841step0Labels := by
      have ha : raw841step0 = (fun i j => raw841 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw841step0 raw841; decide +kernel
      have hl : raw841step0Labels = raw841Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw841 raw841Labels permutation2 permutation4
    _ = mixedMoment B node619 node619Labels := by rfl

def raw842 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![-1, 2, -1], ![-1, 3, -2]]
def raw842Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw842step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, -1, 2], ![-2, -1, 3]]
def raw842step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw842step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 1, -2], ![2, 1, -3]]
def raw842step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw842step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 1, -2], ![2, 1, -3]]
def raw842step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw842 raw842Labels = mixedMoment B node1538 node1538Labels := by
  calc
    mixedMoment B raw842 raw842Labels = mixedMoment B raw842step0 raw842step0Labels := by
      have ha : raw842step0 = (fun i j => raw842 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw842step0 raw842; decide +kernel
      have hl : raw842step0Labels = raw842Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw842 raw842Labels permutation2 permutation6
    mixedMoment B raw842step0 raw842step0Labels = mixedMoment B raw842step1 raw842step1Labels := by
      have ha : raw842step1 = -raw842step0 := by apply Matrix.ext; change ∀ i j, raw842step1 i j = -(raw842step0 i j); unfold raw842step1 raw842step0; decide +kernel
      have hl : raw842step1Labels = raw842step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw842step1 raw842step1Labels = mixedMoment B raw842step2 raw842step2Labels := by
      have ha : raw842step2 = raw842step1 := by apply Matrix.ext; unfold raw842step2 raw842step1; decide +kernel
      have hl : raw842step1Labels = labelEmbedding1 ∘ raw842step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw842step1 raw842step1Labels raw842step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1538 node1538Labels := by rfl

def raw843 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![0, 2, -2], ![-2, 3, -1]]
def raw843Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw843step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def raw843step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw843step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def raw843step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw843 raw843Labels = mixedMoment B node4192 node4192Labels := by
  calc
    mixedMoment B raw843 raw843Labels = mixedMoment B raw843step0 raw843step0Labels := by
      have ha : raw843step0 = (fun i j => raw843 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw843step0 raw843; decide +kernel
      have hl : raw843step0Labels = raw843Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw843 raw843Labels permutation2 permutation4
    mixedMoment B raw843step0 raw843step0Labels = mixedMoment B raw843step1 raw843step1Labels := by
      have ha : raw843step1 = raw843step0 := by apply Matrix.ext; unfold raw843step1 raw843step0; decide +kernel
      have hl : raw843step0Labels = labelEmbedding7 ∘ raw843step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw843step0 raw843step0Labels raw843step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4192 node4192Labels := by rfl

def raw844 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![0, 2, -2], ![-2, 3, -1]]
def raw844Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw844step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def raw844step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw844 raw844Labels = mixedMoment B node620 node620Labels := by
  calc
    mixedMoment B raw844 raw844Labels = mixedMoment B raw844step0 raw844step0Labels := by
      have ha : raw844step0 = (fun i j => raw844 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw844step0 raw844; decide +kernel
      have hl : raw844step0Labels = raw844Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw844 raw844Labels permutation2 permutation4
    _ = mixedMoment B node620 node620Labels := by rfl

def raw845 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -5, 3], ![0, 2, -2], ![-2, 3, -1]]
def raw845Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw845step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, -2, 3], ![-2, 0, 2]]
def raw845step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw845step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 2, -3], ![2, 0, -2]]
def raw845step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw845step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 2, -3], ![2, 0, -2]]
def raw845step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw845 raw845Labels = mixedMoment B node1539 node1539Labels := by
  calc
    mixedMoment B raw845 raw845Labels = mixedMoment B raw845step0 raw845step0Labels := by
      have ha : raw845step0 = (fun i j => raw845 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw845step0 raw845; decide +kernel
      have hl : raw845step0Labels = raw845Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw845 raw845Labels permutation3 permutation6
    mixedMoment B raw845step0 raw845step0Labels = mixedMoment B raw845step1 raw845step1Labels := by
      have ha : raw845step1 = -raw845step0 := by apply Matrix.ext; change ∀ i j, raw845step1 i j = -(raw845step0 i j); unfold raw845step1 raw845step0; decide +kernel
      have hl : raw845step1Labels = raw845step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw845step1 raw845step1Labels = mixedMoment B raw845step2 raw845step2Labels := by
      have ha : raw845step2 = raw845step1 := by apply Matrix.ext; unfold raw845step2 raw845step1; decide +kernel
      have hl : raw845step1Labels = labelEmbedding1 ∘ raw845step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw845step1 raw845step1Labels raw845step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1539 node1539Labels := by rfl

def raw846 : Matrix (Fin 2) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 5, -3]]
def raw846Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw846step0 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 2, 3], ![5, -2, -3]]
def raw846step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw846step1 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 2, 3], ![5, -2, -3]]
def raw846step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw846 raw846Labels = mixedMoment B node4194 node4194Labels := by
  calc
    mixedMoment B raw846 raw846Labels = mixedMoment B raw846step0 raw846step0Labels := by
      have ha : raw846step0 = (fun i j => raw846 (permutation0 i) (permutation4 j)) := by apply Matrix.ext; unfold raw846step0 raw846; decide +kernel
      have hl : raw846step0Labels = raw846Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw846 raw846Labels permutation0 permutation4
    mixedMoment B raw846step0 raw846step0Labels = mixedMoment B raw846step1 raw846step1Labels := by
      have ha : raw846step1 = raw846step0 := by apply Matrix.ext; unfold raw846step1 raw846step0; decide +kernel
      have hl : raw846step0Labels = labelEmbedding7 ∘ raw846step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw846step0 raw846step0Labels raw846step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4194 node4194Labels := by rfl

def raw847 : Matrix (Fin 2) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 5, -3]]
def raw847Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw847step0 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 2, 3], ![5, -2, -3]]
def raw847step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw847 raw847Labels = mixedMoment B node622 node622Labels := by
  calc
    mixedMoment B raw847 raw847Labels = mixedMoment B raw847step0 raw847step0Labels := by
      have ha : raw847step0 = (fun i j => raw847 (permutation0 i) (permutation4 j)) := by apply Matrix.ext; unfold raw847step0 raw847; decide +kernel
      have hl : raw847step0Labels = raw847Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw847 raw847Labels permutation0 permutation4
    _ = mixedMoment B node622 node622Labels := by rfl

def raw848 : Matrix (Fin 2) (Fin 3) ℤ := ![![2, -5, 3], ![-2, 5, -3]]
def raw848Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw848step0 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, -2, 5], ![3, 2, -5]]
def raw848step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw848step1 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, -2, 5], ![3, 2, -5]]
def raw848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw848 raw848Labels = mixedMoment B node1541 node1541Labels := by
  calc
    mixedMoment B raw848 raw848Labels = mixedMoment B raw848step0 raw848step0Labels := by
      have ha : raw848step0 = (fun i j => raw848 (permutation1 i) (permutation6 j)) := by apply Matrix.ext; unfold raw848step0 raw848; decide +kernel
      have hl : raw848step0Labels = raw848Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw848 raw848Labels permutation1 permutation6
    mixedMoment B raw848step0 raw848step0Labels = mixedMoment B raw848step1 raw848step1Labels := by
      have ha : raw848step1 = raw848step0 := by apply Matrix.ext; unfold raw848step1 raw848step0; decide +kernel
      have hl : raw848step0Labels = labelEmbedding1 ∘ raw848step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw848step0 raw848step0Labels raw848step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1541 node1541Labels := by rfl

def raw849 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw849Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw849step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw849step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw849step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw849 raw849Labels = mixedMoment B node4195 node4195Labels := by
  calc
    mixedMoment B raw849 raw849Labels = mixedMoment B raw849step0 raw849step0Labels := by
      have ha : raw849step0 = (fun i j => raw849 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw849step0 raw849; decide +kernel
      have hl : raw849step0Labels = raw849Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw849 raw849Labels permutation152 permutation4
    mixedMoment B raw849step0 raw849step0Labels = mixedMoment B raw849step1 raw849step1Labels := by
      have ha : raw849step1 = raw849step0 := by apply Matrix.ext; unfold raw849step1 raw849step0; decide +kernel
      have hl : raw849step0Labels = labelEmbedding7 ∘ raw849step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw849step0 raw849step0Labels raw849step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4195 node4195Labels := by rfl

def raw850 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw850Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw850step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw850step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw850 raw850Labels = mixedMoment B node698 node698Labels := by
  calc
    mixedMoment B raw850 raw850Labels = mixedMoment B raw850step0 raw850step0Labels := by
      have ha : raw850step0 = (fun i j => raw850 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw850step0 raw850; decide +kernel
      have hl : raw850step0Labels = raw850Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw850 raw850Labels permutation152 permutation4
    _ = mixedMoment B node698 node698Labels := by rfl

def raw851 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw851Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw851step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw851step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw851step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw851step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw851step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw851step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw851 raw851Labels = mixedMoment B node744 node744Labels := by
  calc
    mixedMoment B raw851 raw851Labels = mixedMoment B raw851step0 raw851step0Labels := by
      have ha : raw851step0 = (fun i j => raw851 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw851step0 raw851; decide +kernel
      have hl : raw851step0Labels = raw851Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw851 raw851Labels permutation160 permutation6
    mixedMoment B raw851step0 raw851step0Labels = mixedMoment B raw851step1 raw851step1Labels := by
      have ha : raw851step1 = -raw851step0 := by apply Matrix.ext; change ∀ i j, raw851step1 i j = -(raw851step0 i j); unfold raw851step1 raw851step0; decide +kernel
      have hl : raw851step1Labels = raw851step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw851step1 raw851step1Labels = mixedMoment B raw851step2 raw851step2Labels := by
      have ha : raw851step2 = raw851step1 := by apply Matrix.ext; unfold raw851step2 raw851step1; decide +kernel
      have hl : raw851step1Labels = labelEmbedding1 ∘ raw851step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw851step1 raw851step1Labels raw851step2Labels labelEmbedding1 hl
    _ = mixedMoment B node744 node744Labels := by rfl

def raw852 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw852Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw852step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw852step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw852step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw852step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw852 raw852Labels = mixedMoment B node4196 node4196Labels := by
  calc
    mixedMoment B raw852 raw852Labels = mixedMoment B raw852step0 raw852step0Labels := by
      have ha : raw852step0 = (fun i j => raw852 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw852step0 raw852; decide +kernel
      have hl : raw852step0Labels = raw852Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw852 raw852Labels permutation152 permutation4
    mixedMoment B raw852step0 raw852step0Labels = mixedMoment B raw852step1 raw852step1Labels := by
      have ha : raw852step1 = raw852step0 := by apply Matrix.ext; unfold raw852step1 raw852step0; decide +kernel
      have hl : raw852step0Labels = labelEmbedding7 ∘ raw852step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw852step0 raw852step0Labels raw852step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4196 node4196Labels := by rfl

def raw853 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw853Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw853step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw853 raw853Labels = mixedMoment B node699 node699Labels := by
  calc
    mixedMoment B raw853 raw853Labels = mixedMoment B raw853step0 raw853step0Labels := by
      have ha : raw853step0 = (fun i j => raw853 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw853step0 raw853; decide +kernel
      have hl : raw853step0Labels = raw853Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw853 raw853Labels permutation152 permutation4
    _ = mixedMoment B node699 node699Labels := by rfl

def raw854 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw854Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw854step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw854step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw854step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw854step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw854step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw854step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw854 raw854Labels = mixedMoment B node748 node748Labels := by
  calc
    mixedMoment B raw854 raw854Labels = mixedMoment B raw854step0 raw854step0Labels := by
      have ha : raw854step0 = (fun i j => raw854 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw854step0 raw854; decide +kernel
      have hl : raw854step0Labels = raw854Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw854 raw854Labels permutation158 permutation6
    mixedMoment B raw854step0 raw854step0Labels = mixedMoment B raw854step1 raw854step1Labels := by
      have ha : raw854step1 = -raw854step0 := by apply Matrix.ext; change ∀ i j, raw854step1 i j = -(raw854step0 i j); unfold raw854step1 raw854step0; decide +kernel
      have hl : raw854step1Labels = raw854step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw854step1 raw854step1Labels = mixedMoment B raw854step2 raw854step2Labels := by
      have ha : raw854step2 = raw854step1 := by apply Matrix.ext; unfold raw854step2 raw854step1; decide +kernel
      have hl : raw854step1Labels = labelEmbedding1 ∘ raw854step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw854step1 raw854step1Labels raw854step2Labels labelEmbedding1 hl
    _ = mixedMoment B node748 node748Labels := by rfl

def raw855 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw855step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw855step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw855step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw855 raw855Labels = mixedMoment B node4197 node4197Labels := by
  calc
    mixedMoment B raw855 raw855Labels = mixedMoment B raw855step0 raw855step0Labels := by
      have ha : raw855step0 = (fun i j => raw855 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw855step0 raw855; decide +kernel
      have hl : raw855step0Labels = raw855Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw855 raw855Labels permutation152 permutation4
    mixedMoment B raw855step0 raw855step0Labels = mixedMoment B raw855step1 raw855step1Labels := by
      have ha : raw855step1 = raw855step0 := by apply Matrix.ext; unfold raw855step1 raw855step0; decide +kernel
      have hl : raw855step0Labels = labelEmbedding7 ∘ raw855step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw855step0 raw855step0Labels raw855step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4197 node4197Labels := by rfl

def raw856 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw856Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw856step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw856 raw856Labels = mixedMoment B node700 node700Labels := by
  calc
    mixedMoment B raw856 raw856Labels = mixedMoment B raw856step0 raw856step0Labels := by
      have ha : raw856step0 = (fun i j => raw856 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw856step0 raw856; decide +kernel
      have hl : raw856step0Labels = raw856Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw856 raw856Labels permutation152 permutation4
    _ = mixedMoment B node700 node700Labels := by rfl

def raw857 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw857Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw857step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw857step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw857step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw857step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw857step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw857 raw857Labels = mixedMoment B node749 node749Labels := by
  calc
    mixedMoment B raw857 raw857Labels = mixedMoment B raw857step0 raw857step0Labels := by
      have ha : raw857step0 = (fun i j => raw857 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw857step0 raw857; decide +kernel
      have hl : raw857step0Labels = raw857Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw857 raw857Labels permutation158 permutation6
    mixedMoment B raw857step0 raw857step0Labels = mixedMoment B raw857step1 raw857step1Labels := by
      have ha : raw857step1 = -raw857step0 := by apply Matrix.ext; change ∀ i j, raw857step1 i j = -(raw857step0 i j); unfold raw857step1 raw857step0; decide +kernel
      have hl : raw857step1Labels = raw857step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw857step1 raw857step1Labels = mixedMoment B raw857step2 raw857step2Labels := by
      have ha : raw857step2 = raw857step1 := by apply Matrix.ext; unfold raw857step2 raw857step1; decide +kernel
      have hl : raw857step1Labels = labelEmbedding1 ∘ raw857step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw857step1 raw857step1Labels raw857step2Labels labelEmbedding1 hl
    _ = mixedMoment B node749 node749Labels := by rfl

def raw858 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 4, -3]]
def raw858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw858step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw858step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw858 raw858Labels = mixedMoment B node4198 node4198Labels := by
  calc
    mixedMoment B raw858 raw858Labels = mixedMoment B raw858step0 raw858step0Labels := by
      have ha : raw858step0 = (fun i j => raw858 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw858step0 raw858; decide +kernel
      have hl : raw858step0Labels = raw858Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw858 raw858Labels permutation32 permutation4
    mixedMoment B raw858step0 raw858step0Labels = mixedMoment B raw858step1 raw858step1Labels := by
      have ha : raw858step1 = raw858step0 := by apply Matrix.ext; unfold raw858step1 raw858step0; decide +kernel
      have hl : raw858step0Labels = labelEmbedding7 ∘ raw858step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw858step0 raw858step0Labels raw858step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4198 node4198Labels := by rfl

def raw859 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 4, -3]]
def raw859Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw859step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw859 raw859Labels = mixedMoment B node701 node701Labels := by
  calc
    mixedMoment B raw859 raw859Labels = mixedMoment B raw859step0 raw859step0Labels := by
      have ha : raw859step0 = (fun i j => raw859 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw859step0 raw859; decide +kernel
      have hl : raw859step0Labels = raw859Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw859 raw859Labels permutation32 permutation4
    _ = mixedMoment B node701 node701Labels := by rfl

def raw860 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 4, -3]]
def raw860Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, -1, 4]]
def raw860step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw860step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw860step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw860step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw860 raw860Labels = mixedMoment B node750 node750Labels := by
  calc
    mixedMoment B raw860 raw860Labels = mixedMoment B raw860step0 raw860step0Labels := by
      have ha : raw860step0 = (fun i j => raw860 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw860step0 raw860; decide +kernel
      have hl : raw860step0Labels = raw860Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw860 raw860Labels permutation34 permutation6
    mixedMoment B raw860step0 raw860step0Labels = mixedMoment B raw860step1 raw860step1Labels := by
      have ha : raw860step1 = -raw860step0 := by apply Matrix.ext; change ∀ i j, raw860step1 i j = -(raw860step0 i j); unfold raw860step1 raw860step0; decide +kernel
      have hl : raw860step1Labels = raw860step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw860step1 raw860step1Labels = mixedMoment B raw860step2 raw860step2Labels := by
      have ha : raw860step2 = raw860step1 := by apply Matrix.ext; unfold raw860step2 raw860step1; decide +kernel
      have hl : raw860step1Labels = labelEmbedding1 ∘ raw860step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw860step1 raw860step1Labels raw860step2Labels labelEmbedding1 hl
    _ = mixedMoment B node750 node750Labels := by rfl

def raw861 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw861step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw861step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw861step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw861step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw861 raw861Labels = mixedMoment B node4199 node4199Labels := by
  calc
    mixedMoment B raw861 raw861Labels = mixedMoment B raw861step0 raw861step0Labels := by
      have ha : raw861step0 = (fun i j => raw861 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw861step0 raw861; decide +kernel
      have hl : raw861step0Labels = raw861Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw861 raw861Labels permutation152 permutation4
    mixedMoment B raw861step0 raw861step0Labels = mixedMoment B raw861step1 raw861step1Labels := by
      have ha : raw861step1 = raw861step0 := by apply Matrix.ext; unfold raw861step1 raw861step0; decide +kernel
      have hl : raw861step0Labels = labelEmbedding7 ∘ raw861step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw861step0 raw861step0Labels raw861step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4199 node4199Labels := by rfl

def raw862 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw862Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw862step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw862step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw862 raw862Labels = mixedMoment B node702 node702Labels := by
  calc
    mixedMoment B raw862 raw862Labels = mixedMoment B raw862step0 raw862step0Labels := by
      have ha : raw862step0 = (fun i j => raw862 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw862step0 raw862; decide +kernel
      have hl : raw862step0Labels = raw862Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw862 raw862Labels permutation152 permutation4
    _ = mixedMoment B node702 node702Labels := by rfl

def raw863 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw863Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw863step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw863step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw863step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw863step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw863step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw863 raw863Labels = mixedMoment B node760 node760Labels := by
  calc
    mixedMoment B raw863 raw863Labels = mixedMoment B raw863step0 raw863step0Labels := by
      have ha : raw863step0 = (fun i j => raw863 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw863step0 raw863; decide +kernel
      have hl : raw863step0Labels = raw863Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw863 raw863Labels permutation152 permutation6
    mixedMoment B raw863step0 raw863step0Labels = mixedMoment B raw863step1 raw863step1Labels := by
      have ha : raw863step1 = -raw863step0 := by apply Matrix.ext; change ∀ i j, raw863step1 i j = -(raw863step0 i j); unfold raw863step1 raw863step0; decide +kernel
      have hl : raw863step1Labels = raw863step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw863step1 raw863step1Labels = mixedMoment B raw863step2 raw863step2Labels := by
      have ha : raw863step2 = raw863step1 := by apply Matrix.ext; unfold raw863step2 raw863step1; decide +kernel
      have hl : raw863step1Labels = labelEmbedding1 ∘ raw863step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw863step1 raw863step1Labels raw863step2Labels labelEmbedding1 hl
    _ = mixedMoment B node760 node760Labels := by rfl

def raw864 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw864step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw864step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw864step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw864 raw864Labels = mixedMoment B node4200 node4200Labels := by
  calc
    mixedMoment B raw864 raw864Labels = mixedMoment B raw864step0 raw864step0Labels := by
      have ha : raw864step0 = (fun i j => raw864 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw864step0 raw864; decide +kernel
      have hl : raw864step0Labels = raw864Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw864 raw864Labels permutation152 permutation4
    mixedMoment B raw864step0 raw864step0Labels = mixedMoment B raw864step1 raw864step1Labels := by
      have ha : raw864step1 = raw864step0 := by apply Matrix.ext; unfold raw864step1 raw864step0; decide +kernel
      have hl : raw864step0Labels = labelEmbedding7 ∘ raw864step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw864step0 raw864step0Labels raw864step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4200 node4200Labels := by rfl

def raw865 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw865Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw865step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw865 raw865Labels = mixedMoment B node703 node703Labels := by
  calc
    mixedMoment B raw865 raw865Labels = mixedMoment B raw865step0 raw865step0Labels := by
      have ha : raw865step0 = (fun i j => raw865 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw865step0 raw865; decide +kernel
      have hl : raw865step0Labels = raw865Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw865 raw865Labels permutation152 permutation4
    _ = mixedMoment B node703 node703Labels := by rfl

def raw866 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw866Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw866step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw866step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw866step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw866step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw866step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw866step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw866 raw866Labels = mixedMoment B node754 node754Labels := by
  calc
    mixedMoment B raw866 raw866Labels = mixedMoment B raw866step0 raw866step0Labels := by
      have ha : raw866step0 = (fun i j => raw866 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw866step0 raw866; decide +kernel
      have hl : raw866step0Labels = raw866Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw866 raw866Labels permutation164 permutation6
    mixedMoment B raw866step0 raw866step0Labels = mixedMoment B raw866step1 raw866step1Labels := by
      have ha : raw866step1 = -raw866step0 := by apply Matrix.ext; change ∀ i j, raw866step1 i j = -(raw866step0 i j); unfold raw866step1 raw866step0; decide +kernel
      have hl : raw866step1Labels = raw866step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw866step1 raw866step1Labels = mixedMoment B raw866step2 raw866step2Labels := by
      have ha : raw866step2 = raw866step1 := by apply Matrix.ext; unfold raw866step2 raw866step1; decide +kernel
      have hl : raw866step1Labels = labelEmbedding1 ∘ raw866step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw866step1 raw866step1Labels raw866step2Labels labelEmbedding1 hl
    _ = mixedMoment B node754 node754Labels := by rfl

def raw867 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw867step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw867step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw867step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw867 raw867Labels = mixedMoment B node4201 node4201Labels := by
  calc
    mixedMoment B raw867 raw867Labels = mixedMoment B raw867step0 raw867step0Labels := by
      have ha : raw867step0 = (fun i j => raw867 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw867step0 raw867; decide +kernel
      have hl : raw867step0Labels = raw867Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw867 raw867Labels permutation152 permutation4
    mixedMoment B raw867step0 raw867step0Labels = mixedMoment B raw867step1 raw867step1Labels := by
      have ha : raw867step1 = raw867step0 := by apply Matrix.ext; unfold raw867step1 raw867step0; decide +kernel
      have hl : raw867step0Labels = labelEmbedding7 ∘ raw867step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw867step0 raw867step0Labels raw867step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4201 node4201Labels := by rfl

def raw868 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw868Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw868step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw868 raw868Labels = mixedMoment B node704 node704Labels := by
  calc
    mixedMoment B raw868 raw868Labels = mixedMoment B raw868step0 raw868step0Labels := by
      have ha : raw868step0 = (fun i j => raw868 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw868step0 raw868; decide +kernel
      have hl : raw868step0Labels = raw868Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw868 raw868Labels permutation152 permutation4
    _ = mixedMoment B node704 node704Labels := by rfl

def raw869 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw869Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw869step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw869step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw869step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw869step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw869step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw869 raw869Labels = mixedMoment B node761 node761Labels := by
  calc
    mixedMoment B raw869 raw869Labels = mixedMoment B raw869step0 raw869step0Labels := by
      have ha : raw869step0 = (fun i j => raw869 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw869step0 raw869; decide +kernel
      have hl : raw869step0Labels = raw869Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw869 raw869Labels permutation152 permutation6
    mixedMoment B raw869step0 raw869step0Labels = mixedMoment B raw869step1 raw869step1Labels := by
      have ha : raw869step1 = -raw869step0 := by apply Matrix.ext; change ∀ i j, raw869step1 i j = -(raw869step0 i j); unfold raw869step1 raw869step0; decide +kernel
      have hl : raw869step1Labels = raw869step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw869step1 raw869step1Labels = mixedMoment B raw869step2 raw869step2Labels := by
      have ha : raw869step2 = raw869step1 := by apply Matrix.ext; unfold raw869step2 raw869step1; decide +kernel
      have hl : raw869step1Labels = labelEmbedding1 ∘ raw869step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw869step1 raw869step1Labels raw869step2Labels labelEmbedding1 hl
    _ = mixedMoment B node761 node761Labels := by rfl

def raw870 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 4, -2]]
def raw870Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw870step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw870step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw870step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw870 raw870Labels = mixedMoment B node4202 node4202Labels := by
  calc
    mixedMoment B raw870 raw870Labels = mixedMoment B raw870step0 raw870step0Labels := by
      have ha : raw870step0 = (fun i j => raw870 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw870step0 raw870; decide +kernel
      have hl : raw870step0Labels = raw870Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw870 raw870Labels permutation32 permutation4
    mixedMoment B raw870step0 raw870step0Labels = mixedMoment B raw870step1 raw870step1Labels := by
      have ha : raw870step1 = raw870step0 := by apply Matrix.ext; unfold raw870step1 raw870step0; decide +kernel
      have hl : raw870step0Labels = labelEmbedding7 ∘ raw870step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw870step0 raw870step0Labels raw870step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4202 node4202Labels := by rfl

def raw871 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 4, -2]]
def raw871Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw871step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw871 raw871Labels = mixedMoment B node705 node705Labels := by
  calc
    mixedMoment B raw871 raw871Labels = mixedMoment B raw871step0 raw871step0Labels := by
      have ha : raw871step0 = (fun i j => raw871 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw871step0 raw871; decide +kernel
      have hl : raw871step0Labels = raw871Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw871 raw871Labels permutation32 permutation4
    _ = mixedMoment B node705 node705Labels := by rfl

def raw872 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 4, -2]]
def raw872Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw872step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw872step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw872step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw872step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw872step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw872 raw872Labels = mixedMoment B node762 node762Labels := by
  calc
    mixedMoment B raw872 raw872Labels = mixedMoment B raw872step0 raw872step0Labels := by
      have ha : raw872step0 = (fun i j => raw872 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw872step0 raw872; decide +kernel
      have hl : raw872step0Labels = raw872Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw872 raw872Labels permutation32 permutation6
    mixedMoment B raw872step0 raw872step0Labels = mixedMoment B raw872step1 raw872step1Labels := by
      have ha : raw872step1 = -raw872step0 := by apply Matrix.ext; change ∀ i j, raw872step1 i j = -(raw872step0 i j); unfold raw872step1 raw872step0; decide +kernel
      have hl : raw872step1Labels = raw872step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw872step1 raw872step1Labels = mixedMoment B raw872step2 raw872step2Labels := by
      have ha : raw872step2 = raw872step1 := by apply Matrix.ext; unfold raw872step2 raw872step1; decide +kernel
      have hl : raw872step1Labels = labelEmbedding1 ∘ raw872step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw872step1 raw872step1Labels raw872step2Labels labelEmbedding1 hl
    _ = mixedMoment B node762 node762Labels := by rfl

def raw873 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-2, 2, 0], ![0, 3, -3]]
def raw873Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw873step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw873step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw873 raw873Labels = mixedMoment B node4203 node4203Labels := by
  calc
    mixedMoment B raw873 raw873Labels = mixedMoment B raw873step0 raw873step0Labels := by
      have ha : raw873step0 = (fun i j => raw873 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw873step0 raw873; decide +kernel
      have hl : raw873step0Labels = raw873Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw873 raw873Labels permutation32 permutation4
    mixedMoment B raw873step0 raw873step0Labels = mixedMoment B raw873step1 raw873step1Labels := by
      have ha : raw873step1 = raw873step0 := by apply Matrix.ext; unfold raw873step1 raw873step0; decide +kernel
      have hl : raw873step0Labels = labelEmbedding7 ∘ raw873step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw873step0 raw873step0Labels raw873step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4203 node4203Labels := by rfl

def raw874 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-2, 2, 0], ![0, 3, -3]]
def raw874Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw874step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw874 raw874Labels = mixedMoment B node706 node706Labels := by
  calc
    mixedMoment B raw874 raw874Labels = mixedMoment B raw874step0 raw874step0Labels := by
      have ha : raw874step0 = (fun i j => raw874 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw874step0 raw874; decide +kernel
      have hl : raw874step0Labels = raw874Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw874 raw874Labels permutation32 permutation4
    _ = mixedMoment B node706 node706Labels := by rfl

def raw875 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-2, 2, 0], ![0, 3, -3]]
def raw875Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 0, 3]]
def raw875step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw875step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw875step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw875step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw875step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw875 raw875Labels = mixedMoment B node755 node755Labels := by
  calc
    mixedMoment B raw875 raw875Labels = mixedMoment B raw875step0 raw875step0Labels := by
      have ha : raw875step0 = (fun i j => raw875 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw875step0 raw875; decide +kernel
      have hl : raw875step0Labels = raw875Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw875 raw875Labels permutation34 permutation6
    mixedMoment B raw875step0 raw875step0Labels = mixedMoment B raw875step1 raw875step1Labels := by
      have ha : raw875step1 = -raw875step0 := by apply Matrix.ext; change ∀ i j, raw875step1 i j = -(raw875step0 i j); unfold raw875step1 raw875step0; decide +kernel
      have hl : raw875step1Labels = raw875step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw875step1 raw875step1Labels = mixedMoment B raw875step2 raw875step2Labels := by
      have ha : raw875step2 = raw875step1 := by apply Matrix.ext; unfold raw875step2 raw875step1; decide +kernel
      have hl : raw875step1Labels = labelEmbedding1 ∘ raw875step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw875step1 raw875step1Labels raw875step2Labels labelEmbedding1 hl
    _ = mixedMoment B node755 node755Labels := by rfl

def raw876 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw876Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw876step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw876step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw876step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw876 raw876Labels = mixedMoment B node4204 node4204Labels := by
  calc
    mixedMoment B raw876 raw876Labels = mixedMoment B raw876step0 raw876step0Labels := by
      have ha : raw876step0 = (fun i j => raw876 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw876step0 raw876; decide +kernel
      have hl : raw876step0Labels = raw876Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw876 raw876Labels permutation32 permutation4
    mixedMoment B raw876step0 raw876step0Labels = mixedMoment B raw876step1 raw876step1Labels := by
      have ha : raw876step1 = raw876step0 := by apply Matrix.ext; unfold raw876step1 raw876step0; decide +kernel
      have hl : raw876step0Labels = labelEmbedding7 ∘ raw876step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw876step0 raw876step0Labels raw876step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4204 node4204Labels := by rfl

def raw877 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw877Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw877step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw877 raw877Labels = mixedMoment B node707 node707Labels := by
  calc
    mixedMoment B raw877 raw877Labels = mixedMoment B raw877step0 raw877step0Labels := by
      have ha : raw877step0 = (fun i j => raw877 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw877step0 raw877; decide +kernel
      have hl : raw877step0Labels = raw877Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw877 raw877Labels permutation32 permutation4
    _ = mixedMoment B node707 node707Labels := by rfl

def raw878 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw878Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw878step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw878step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw878step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw878step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw878 raw878Labels = mixedMoment B node763 node763Labels := by
  calc
    mixedMoment B raw878 raw878Labels = mixedMoment B raw878step0 raw878step0Labels := by
      have ha : raw878step0 = (fun i j => raw878 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw878step0 raw878; decide +kernel
      have hl : raw878step0Labels = raw878Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw878 raw878Labels permutation32 permutation6
    mixedMoment B raw878step0 raw878step0Labels = mixedMoment B raw878step1 raw878step1Labels := by
      have ha : raw878step1 = -raw878step0 := by apply Matrix.ext; change ∀ i j, raw878step1 i j = -(raw878step0 i j); unfold raw878step1 raw878step0; decide +kernel
      have hl : raw878step1Labels = raw878step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw878step1 raw878step1Labels = mixedMoment B raw878step2 raw878step2Labels := by
      have ha : raw878step2 = raw878step1 := by apply Matrix.ext; unfold raw878step2 raw878step1; decide +kernel
      have hl : raw878step1Labels = labelEmbedding1 ∘ raw878step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw878step1 raw878step1Labels raw878step2Labels labelEmbedding1 hl
    _ = mixedMoment B node763 node763Labels := by rfl

def raw879 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw879Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw879step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw879step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw879step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw879 raw879Labels = mixedMoment B node4205 node4205Labels := by
  calc
    mixedMoment B raw879 raw879Labels = mixedMoment B raw879step0 raw879step0Labels := by
      have ha : raw879step0 = (fun i j => raw879 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw879step0 raw879; decide +kernel
      have hl : raw879step0Labels = raw879Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw879 raw879Labels permutation32 permutation4
    mixedMoment B raw879step0 raw879step0Labels = mixedMoment B raw879step1 raw879step1Labels := by
      have ha : raw879step1 = raw879step0 := by apply Matrix.ext; unfold raw879step1 raw879step0; decide +kernel
      have hl : raw879step0Labels = labelEmbedding7 ∘ raw879step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw879step0 raw879step0Labels raw879step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4205 node4205Labels := by rfl

def raw880 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw880 raw880Labels = mixedMoment B node708 node708Labels := by
  calc
    mixedMoment B raw880 raw880Labels = mixedMoment B raw880step0 raw880step0Labels := by
      have ha : raw880step0 = (fun i j => raw880 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw880step0 raw880; decide +kernel
      have hl : raw880step0Labels = raw880Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw880 raw880Labels permutation32 permutation4
    _ = mixedMoment B node708 node708Labels := by rfl

def raw881 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 0, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw881Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw881step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw881step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw881step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw881step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw881step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw881 raw881Labels = mixedMoment B node764 node764Labels := by
  calc
    mixedMoment B raw881 raw881Labels = mixedMoment B raw881step0 raw881step0Labels := by
      have ha : raw881step0 = (fun i j => raw881 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw881step0 raw881; decide +kernel
      have hl : raw881step0Labels = raw881Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw881 raw881Labels permutation33 permutation6
    mixedMoment B raw881step0 raw881step0Labels = mixedMoment B raw881step1 raw881step1Labels := by
      have ha : raw881step1 = -raw881step0 := by apply Matrix.ext; change ∀ i j, raw881step1 i j = -(raw881step0 i j); unfold raw881step1 raw881step0; decide +kernel
      have hl : raw881step1Labels = raw881step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw881step1 raw881step1Labels = mixedMoment B raw881step2 raw881step2Labels := by
      have ha : raw881step2 = raw881step1 := by apply Matrix.ext; unfold raw881step2 raw881step1; decide +kernel
      have hl : raw881step1Labels = labelEmbedding1 ∘ raw881step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw881step1 raw881step1Labels raw881step2Labels labelEmbedding1 hl
    _ = mixedMoment B node764 node764Labels := by rfl

def raw882 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw882Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw882step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw882step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw882step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw882step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw882 raw882Labels = mixedMoment B node4206 node4206Labels := by
  calc
    mixedMoment B raw882 raw882Labels = mixedMoment B raw882step0 raw882step0Labels := by
      have ha : raw882step0 = (fun i j => raw882 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw882step0 raw882; decide +kernel
      have hl : raw882step0Labels = raw882Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw882 raw882Labels permutation152 permutation4
    mixedMoment B raw882step0 raw882step0Labels = mixedMoment B raw882step1 raw882step1Labels := by
      have ha : raw882step1 = raw882step0 := by apply Matrix.ext; unfold raw882step1 raw882step0; decide +kernel
      have hl : raw882step0Labels = labelEmbedding7 ∘ raw882step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw882step0 raw882step0Labels raw882step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4206 node4206Labels := by rfl

def raw883 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw883Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw883step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw883step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw883 raw883Labels = mixedMoment B node709 node709Labels := by
  calc
    mixedMoment B raw883 raw883Labels = mixedMoment B raw883step0 raw883step0Labels := by
      have ha : raw883step0 = (fun i j => raw883 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw883step0 raw883; decide +kernel
      have hl : raw883step0Labels = raw883Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw883 raw883Labels permutation152 permutation4
    _ = mixedMoment B node709 node709Labels := by rfl

def raw884 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw884Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw884step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw884step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw884step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw884step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw884step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw884 raw884Labels = mixedMoment B node745 node745Labels := by
  calc
    mixedMoment B raw884 raw884Labels = mixedMoment B raw884step0 raw884step0Labels := by
      have ha : raw884step0 = (fun i j => raw884 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw884step0 raw884; decide +kernel
      have hl : raw884step0Labels = raw884Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw884 raw884Labels permutation152 permutation6
    mixedMoment B raw884step0 raw884step0Labels = mixedMoment B raw884step1 raw884step1Labels := by
      have ha : raw884step1 = -raw884step0 := by apply Matrix.ext; change ∀ i j, raw884step1 i j = -(raw884step0 i j); unfold raw884step1 raw884step0; decide +kernel
      have hl : raw884step1Labels = raw884step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw884step1 raw884step1Labels = mixedMoment B raw884step2 raw884step2Labels := by
      have ha : raw884step2 = raw884step1 := by apply Matrix.ext; unfold raw884step2 raw884step1; decide +kernel
      have hl : raw884step1Labels = labelEmbedding1 ∘ raw884step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw884step1 raw884step1Labels raw884step2Labels labelEmbedding1 hl
    _ = mixedMoment B node745 node745Labels := by rfl

def raw885 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw885step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw885step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw885step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw885 raw885Labels = mixedMoment B node4207 node4207Labels := by
  calc
    mixedMoment B raw885 raw885Labels = mixedMoment B raw885step0 raw885step0Labels := by
      have ha : raw885step0 = (fun i j => raw885 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw885step0 raw885; decide +kernel
      have hl : raw885step0Labels = raw885Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw885 raw885Labels permutation152 permutation4
    mixedMoment B raw885step0 raw885step0Labels = mixedMoment B raw885step1 raw885step1Labels := by
      have ha : raw885step1 = raw885step0 := by apply Matrix.ext; unfold raw885step1 raw885step0; decide +kernel
      have hl : raw885step0Labels = labelEmbedding7 ∘ raw885step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw885step0 raw885step0Labels raw885step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4207 node4207Labels := by rfl

def raw886 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw886Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw886step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw886 raw886Labels = mixedMoment B node710 node710Labels := by
  calc
    mixedMoment B raw886 raw886Labels = mixedMoment B raw886step0 raw886step0Labels := by
      have ha : raw886step0 = (fun i j => raw886 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw886step0 raw886; decide +kernel
      have hl : raw886step0Labels = raw886Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw886 raw886Labels permutation152 permutation4
    _ = mixedMoment B node710 node710Labels := by rfl

def raw887 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw887Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw887step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw887step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw887step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw887step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw887step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw887 raw887Labels = mixedMoment B node746 node746Labels := by
  calc
    mixedMoment B raw887 raw887Labels = mixedMoment B raw887step0 raw887step0Labels := by
      have ha : raw887step0 = (fun i j => raw887 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw887step0 raw887; decide +kernel
      have hl : raw887step0Labels = raw887Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw887 raw887Labels permutation152 permutation6
    mixedMoment B raw887step0 raw887step0Labels = mixedMoment B raw887step1 raw887step1Labels := by
      have ha : raw887step1 = -raw887step0 := by apply Matrix.ext; change ∀ i j, raw887step1 i j = -(raw887step0 i j); unfold raw887step1 raw887step0; decide +kernel
      have hl : raw887step1Labels = raw887step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw887step1 raw887step1Labels = mixedMoment B raw887step2 raw887step2Labels := by
      have ha : raw887step2 = raw887step1 := by apply Matrix.ext; unfold raw887step2 raw887step1; decide +kernel
      have hl : raw887step1Labels = labelEmbedding1 ∘ raw887step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw887step1 raw887step1Labels raw887step2Labels labelEmbedding1 hl
    _ = mixedMoment B node746 node746Labels := by rfl

def raw888 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, 3, -4]]
def raw888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw888step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw888step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw888 raw888Labels = mixedMoment B node4208 node4208Labels := by
  calc
    mixedMoment B raw888 raw888Labels = mixedMoment B raw888step0 raw888step0Labels := by
      have ha : raw888step0 = (fun i j => raw888 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw888step0 raw888; decide +kernel
      have hl : raw888step0Labels = raw888Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw888 raw888Labels permutation32 permutation4
    mixedMoment B raw888step0 raw888step0Labels = mixedMoment B raw888step1 raw888step1Labels := by
      have ha : raw888step1 = raw888step0 := by apply Matrix.ext; unfold raw888step1 raw888step0; decide +kernel
      have hl : raw888step0Labels = labelEmbedding7 ∘ raw888step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw888step0 raw888step0Labels raw888step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4208 node4208Labels := by rfl

def raw889 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, 3, -4]]
def raw889Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw889step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw889 raw889Labels = mixedMoment B node711 node711Labels := by
  calc
    mixedMoment B raw889 raw889Labels = mixedMoment B raw889step0 raw889step0Labels := by
      have ha : raw889step0 = (fun i j => raw889 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw889step0 raw889; decide +kernel
      have hl : raw889step0Labels = raw889Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw889 raw889Labels permutation32 permutation4
    _ = mixedMoment B node711 node711Labels := by rfl

def raw890 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, 3, -4]]
def raw890Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-4, 1, 3]]
def raw890step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw890step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -1, -3]]
def raw890step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw890step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -1, -3]]
def raw890step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw890 raw890Labels = mixedMoment B node747 node747Labels := by
  calc
    mixedMoment B raw890 raw890Labels = mixedMoment B raw890step0 raw890step0Labels := by
      have ha : raw890step0 = (fun i j => raw890 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw890step0 raw890; decide +kernel
      have hl : raw890step0Labels = raw890Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw890 raw890Labels permutation32 permutation6
    mixedMoment B raw890step0 raw890step0Labels = mixedMoment B raw890step1 raw890step1Labels := by
      have ha : raw890step1 = -raw890step0 := by apply Matrix.ext; change ∀ i j, raw890step1 i j = -(raw890step0 i j); unfold raw890step1 raw890step0; decide +kernel
      have hl : raw890step1Labels = raw890step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw890step1 raw890step1Labels = mixedMoment B raw890step2 raw890step2Labels := by
      have ha : raw890step2 = raw890step1 := by apply Matrix.ext; unfold raw890step2 raw890step1; decide +kernel
      have hl : raw890step1Labels = labelEmbedding1 ∘ raw890step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw890step1 raw890step1Labels raw890step2Labels labelEmbedding1 hl
    _ = mixedMoment B node747 node747Labels := by rfl

def raw891 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw891step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw891step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw891step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw891 raw891Labels = mixedMoment B node4210 node4210Labels := by
  calc
    mixedMoment B raw891 raw891Labels = mixedMoment B raw891step0 raw891step0Labels := by
      have ha : raw891step0 = (fun i j => raw891 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw891step0 raw891; decide +kernel
      have hl : raw891step0Labels = raw891Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw891 raw891Labels permutation152 permutation4
    mixedMoment B raw891step0 raw891step0Labels = mixedMoment B raw891step1 raw891step1Labels := by
      have ha : raw891step1 = raw891step0 := by apply Matrix.ext; unfold raw891step1 raw891step0; decide +kernel
      have hl : raw891step0Labels = labelEmbedding7 ∘ raw891step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw891step0 raw891step0Labels raw891step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4210 node4210Labels := by rfl

def raw892 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw892Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw892step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw892step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw892 raw892Labels = mixedMoment B node713 node713Labels := by
  calc
    mixedMoment B raw892 raw892Labels = mixedMoment B raw892step0 raw892step0Labels := by
      have ha : raw892step0 = (fun i j => raw892 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw892step0 raw892; decide +kernel
      have hl : raw892step0Labels = raw892Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw892 raw892Labels permutation152 permutation4
    _ = mixedMoment B node713 node713Labels := by rfl

def raw893 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw893Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw893step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw893step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw893step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw893step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw893step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw893step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw893 raw893Labels = mixedMoment B node751 node751Labels := by
  calc
    mixedMoment B raw893 raw893Labels = mixedMoment B raw893step0 raw893step0Labels := by
      have ha : raw893step0 = (fun i j => raw893 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw893step0 raw893; decide +kernel
      have hl : raw893step0Labels = raw893Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw893 raw893Labels permutation153 permutation6
    mixedMoment B raw893step0 raw893step0Labels = mixedMoment B raw893step1 raw893step1Labels := by
      have ha : raw893step1 = -raw893step0 := by apply Matrix.ext; change ∀ i j, raw893step1 i j = -(raw893step0 i j); unfold raw893step1 raw893step0; decide +kernel
      have hl : raw893step1Labels = raw893step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw893step1 raw893step1Labels = mixedMoment B raw893step2 raw893step2Labels := by
      have ha : raw893step2 = raw893step1 := by apply Matrix.ext; unfold raw893step2 raw893step1; decide +kernel
      have hl : raw893step1Labels = labelEmbedding1 ∘ raw893step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw893step1 raw893step1Labels raw893step2Labels labelEmbedding1 hl
    _ = mixedMoment B node751 node751Labels := by rfl

def raw894 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw894step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw894step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw894 raw894Labels = mixedMoment B node4212 node4212Labels := by
  calc
    mixedMoment B raw894 raw894Labels = mixedMoment B raw894step0 raw894step0Labels := by
      have ha : raw894step0 = (fun i j => raw894 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw894step0 raw894; decide +kernel
      have hl : raw894step0Labels = raw894Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw894 raw894Labels permutation32 permutation4
    mixedMoment B raw894step0 raw894step0Labels = mixedMoment B raw894step1 raw894step1Labels := by
      have ha : raw894step1 = raw894step0 := by apply Matrix.ext; unfold raw894step1 raw894step0; decide +kernel
      have hl : raw894step0Labels = labelEmbedding7 ∘ raw894step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw894step0 raw894step0Labels raw894step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4212 node4212Labels := by rfl

def raw895 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw895Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw895step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw895 raw895Labels = mixedMoment B node715 node715Labels := by
  calc
    mixedMoment B raw895 raw895Labels = mixedMoment B raw895step0 raw895step0Labels := by
      have ha : raw895step0 = (fun i j => raw895 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw895step0 raw895; decide +kernel
      have hl : raw895step0Labels = raw895Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw895 raw895Labels permutation32 permutation4
    _ = mixedMoment B node715 node715Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
