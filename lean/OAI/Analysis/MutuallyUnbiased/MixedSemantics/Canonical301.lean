import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw38528 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38528Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw38528step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38528step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38528step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38528step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38528 raw38528Labels = mixedMoment B node1618 node1618Labels := by
  calc
    mixedMoment B raw38528 raw38528Labels = mixedMoment B raw38528step0 raw38528step0Labels := by
      have ha : raw38528step0 = (fun i j => raw38528 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38528step0 raw38528; decide +kernel
      have hl : raw38528step0Labels = raw38528Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38528 raw38528Labels permutation32 permutation7
    mixedMoment B raw38528step0 raw38528step0Labels = mixedMoment B raw38528step1 raw38528step1Labels := by
      have ha : raw38528step1 = -raw38528step0 := by apply Matrix.ext; change ∀ i j, raw38528step1 i j = -(raw38528step0 i j); unfold raw38528step1 raw38528step0; decide +kernel
      have hl : raw38528step1Labels = raw38528step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38528step1 raw38528step1Labels = mixedMoment B raw38528step2 raw38528step2Labels := by
      have ha : raw38528step2 = raw38528step1 := by apply Matrix.ext; unfold raw38528step2 raw38528step1; decide +kernel
      have hl : raw38528step1Labels = labelEmbedding4 ∘ raw38528step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38528step1 raw38528step1Labels raw38528step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1618 node1618Labels := by rfl

def raw38529 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw38529Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38529step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw38529step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38529 raw38529Labels = mixedMoment B node986 node986Labels := by
  calc
    mixedMoment B raw38529 raw38529Labels = mixedMoment B raw38529step0 raw38529step0Labels := by
      have ha : raw38529step0 = raw38529 := by apply Matrix.ext; unfold raw38529step0 raw38529; decide +kernel
      have hl : raw38529Labels = labelEmbedding2 ∘ raw38529step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38529 raw38529Labels raw38529step0Labels labelEmbedding2 hl
    _ = mixedMoment B node986 node986Labels := by rfl

def raw38530 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw38530Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38530step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw38530step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw38530step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38530 raw38530Labels = mixedMoment B node1620 node1620Labels := by
  calc
    mixedMoment B raw38530 raw38530Labels = mixedMoment B raw38530step0 raw38530step0Labels := by
      have ha : raw38530step0 = (fun i j => raw38530 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38530step0 raw38530; decide +kernel
      have hl : raw38530step0Labels = raw38530Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38530 raw38530Labels permutation31 permutation7
    mixedMoment B raw38530step0 raw38530step0Labels = mixedMoment B raw38530step1 raw38530step1Labels := by
      have ha : raw38530step1 = raw38530step0 := by apply Matrix.ext; unfold raw38530step1 raw38530step0; decide +kernel
      have hl : raw38530step0Labels = labelEmbedding4 ∘ raw38530step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38530step0 raw38530step0Labels raw38530step1Labels labelEmbedding4 hl
    _ = mixedMoment B node1620 node1620Labels := by rfl

def raw38531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38531Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38531step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38531step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38531 raw38531Labels = mixedMoment B node998 node998Labels := by
  calc
    mixedMoment B raw38531 raw38531Labels = mixedMoment B raw38531step0 raw38531step0Labels := by
      have ha : raw38531step0 = raw38531 := by apply Matrix.ext; unfold raw38531step0 raw38531; decide +kernel
      have hl : raw38531Labels = labelEmbedding2 ∘ raw38531step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38531 raw38531Labels raw38531step0Labels labelEmbedding2 hl
    _ = mixedMoment B node998 node998Labels := by rfl

def raw38532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38532Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38532step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw38532step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38532step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38532step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38532step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38532step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38532 raw38532Labels = mixedMoment B node1600 node1600Labels := by
  calc
    mixedMoment B raw38532 raw38532Labels = mixedMoment B raw38532step0 raw38532step0Labels := by
      have ha : raw38532step0 = (fun i j => raw38532 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38532step0 raw38532; decide +kernel
      have hl : raw38532step0Labels = raw38532Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38532 raw38532Labels permutation152 permutation7
    mixedMoment B raw38532step0 raw38532step0Labels = mixedMoment B raw38532step1 raw38532step1Labels := by
      have ha : raw38532step1 = -raw38532step0 := by apply Matrix.ext; change ∀ i j, raw38532step1 i j = -(raw38532step0 i j); unfold raw38532step1 raw38532step0; decide +kernel
      have hl : raw38532step1Labels = raw38532step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38532step1 raw38532step1Labels = mixedMoment B raw38532step2 raw38532step2Labels := by
      have ha : raw38532step2 = raw38532step1 := by apply Matrix.ext; unfold raw38532step2 raw38532step1; decide +kernel
      have hl : raw38532step1Labels = labelEmbedding4 ∘ raw38532step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38532step1 raw38532step1Labels raw38532step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1600 node1600Labels := by rfl

def raw38533 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38533Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38533step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38533 raw38533Labels = mixedMoment B node999 node999Labels := by
  calc
    mixedMoment B raw38533 raw38533Labels = mixedMoment B raw38533step0 raw38533step0Labels := by
      have ha : raw38533step0 = raw38533 := by apply Matrix.ext; unfold raw38533step0 raw38533; decide +kernel
      have hl : raw38533Labels = labelEmbedding2 ∘ raw38533step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38533 raw38533Labels raw38533step0Labels labelEmbedding2 hl
    _ = mixedMoment B node999 node999Labels := by rfl

def raw38534 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38534Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw38534step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38534step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38534step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38534step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38534step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38534 raw38534Labels = mixedMoment B node1602 node1602Labels := by
  calc
    mixedMoment B raw38534 raw38534Labels = mixedMoment B raw38534step0 raw38534step0Labels := by
      have ha : raw38534step0 = (fun i j => raw38534 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38534step0 raw38534; decide +kernel
      have hl : raw38534step0Labels = raw38534Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38534 raw38534Labels permutation32 permutation7
    mixedMoment B raw38534step0 raw38534step0Labels = mixedMoment B raw38534step1 raw38534step1Labels := by
      have ha : raw38534step1 = -raw38534step0 := by apply Matrix.ext; change ∀ i j, raw38534step1 i j = -(raw38534step0 i j); unfold raw38534step1 raw38534step0; decide +kernel
      have hl : raw38534step1Labels = raw38534step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38534step1 raw38534step1Labels = mixedMoment B raw38534step2 raw38534step2Labels := by
      have ha : raw38534step2 = raw38534step1 := by apply Matrix.ext; unfold raw38534step2 raw38534step1; decide +kernel
      have hl : raw38534step1Labels = labelEmbedding4 ∘ raw38534step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38534step1 raw38534step1Labels raw38534step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1602 node1602Labels := by rfl

def raw38535 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38535Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38535step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38535 raw38535Labels = mixedMoment B node1000 node1000Labels := by
  calc
    mixedMoment B raw38535 raw38535Labels = mixedMoment B raw38535step0 raw38535step0Labels := by
      have ha : raw38535step0 = raw38535 := by apply Matrix.ext; unfold raw38535step0 raw38535; decide +kernel
      have hl : raw38535Labels = labelEmbedding2 ∘ raw38535step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38535 raw38535Labels raw38535step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1000 node1000Labels := by rfl

def raw38536 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38536Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw38536step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38536step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38536step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38536step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38536step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38536 raw38536Labels = mixedMoment B node1605 node1605Labels := by
  calc
    mixedMoment B raw38536 raw38536Labels = mixedMoment B raw38536step0 raw38536step0Labels := by
      have ha : raw38536step0 = (fun i j => raw38536 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38536step0 raw38536; decide +kernel
      have hl : raw38536step0Labels = raw38536Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38536 raw38536Labels permutation32 permutation7
    mixedMoment B raw38536step0 raw38536step0Labels = mixedMoment B raw38536step1 raw38536step1Labels := by
      have ha : raw38536step1 = -raw38536step0 := by apply Matrix.ext; change ∀ i j, raw38536step1 i j = -(raw38536step0 i j); unfold raw38536step1 raw38536step0; decide +kernel
      have hl : raw38536step1Labels = raw38536step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38536step1 raw38536step1Labels = mixedMoment B raw38536step2 raw38536step2Labels := by
      have ha : raw38536step2 = raw38536step1 := by apply Matrix.ext; unfold raw38536step2 raw38536step1; decide +kernel
      have hl : raw38536step1Labels = labelEmbedding4 ∘ raw38536step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38536step1 raw38536step1Labels raw38536step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1605 node1605Labels := by rfl

def raw38537 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw38537Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38537step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw38537step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38537 raw38537Labels = mixedMoment B node1002 node1002Labels := by
  calc
    mixedMoment B raw38537 raw38537Labels = mixedMoment B raw38537step0 raw38537step0Labels := by
      have ha : raw38537step0 = raw38537 := by apply Matrix.ext; unfold raw38537step0 raw38537; decide +kernel
      have hl : raw38537Labels = labelEmbedding2 ∘ raw38537step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38537 raw38537Labels raw38537step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1002 node1002Labels := by rfl

def raw38538 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw38538Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38538step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw38538step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38538step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw38538step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38538 raw38538Labels = mixedMoment B node1002 node1002Labels := by
  calc
    mixedMoment B raw38538 raw38538Labels = mixedMoment B raw38538step0 raw38538step0Labels := by
      have ha : raw38538step0 = (fun i j => raw38538 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38538step0 raw38538; decide +kernel
      have hl : raw38538step0Labels = raw38538Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38538 raw38538Labels permutation31 permutation7
    mixedMoment B raw38538step0 raw38538step0Labels = mixedMoment B raw38538step1 raw38538step1Labels := by
      have ha : raw38538step1 = raw38538step0 := by apply Matrix.ext; unfold raw38538step1 raw38538step0; decide +kernel
      have hl : raw38538step0Labels = labelEmbedding4 ∘ raw38538step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38538step0 raw38538step0Labels raw38538step1Labels labelEmbedding4 hl
    _ = mixedMoment B node1002 node1002Labels := by rfl

def raw38539 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38539Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38539step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38539 raw38539Labels = mixedMoment B node1005 node1005Labels := by
  calc
    mixedMoment B raw38539 raw38539Labels = mixedMoment B raw38539step0 raw38539step0Labels := by
      have ha : raw38539step0 = raw38539 := by apply Matrix.ext; unfold raw38539step0 raw38539; decide +kernel
      have hl : raw38539Labels = labelEmbedding2 ∘ raw38539step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38539 raw38539Labels raw38539step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1005 node1005Labels := by rfl

def raw38540 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38540Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw38540step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38540step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38540step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38540step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38540step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38540 raw38540Labels = mixedMoment B node1623 node1623Labels := by
  calc
    mixedMoment B raw38540 raw38540Labels = mixedMoment B raw38540step0 raw38540step0Labels := by
      have ha : raw38540step0 = (fun i j => raw38540 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38540step0 raw38540; decide +kernel
      have hl : raw38540step0Labels = raw38540Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38540 raw38540Labels permutation33 permutation7
    mixedMoment B raw38540step0 raw38540step0Labels = mixedMoment B raw38540step1 raw38540step1Labels := by
      have ha : raw38540step1 = -raw38540step0 := by apply Matrix.ext; change ∀ i j, raw38540step1 i j = -(raw38540step0 i j); unfold raw38540step1 raw38540step0; decide +kernel
      have hl : raw38540step1Labels = raw38540step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38540step1 raw38540step1Labels = mixedMoment B raw38540step2 raw38540step2Labels := by
      have ha : raw38540step2 = raw38540step1 := by apply Matrix.ext; unfold raw38540step2 raw38540step1; decide +kernel
      have hl : raw38540step1Labels = labelEmbedding4 ∘ raw38540step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38540step1 raw38540step1Labels raw38540step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1623 node1623Labels := by rfl

def raw38541 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw38541Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38541step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw38541step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38541 raw38541Labels = mixedMoment B node1009 node1009Labels := by
  calc
    mixedMoment B raw38541 raw38541Labels = mixedMoment B raw38541step0 raw38541step0Labels := by
      have ha : raw38541step0 = raw38541 := by apply Matrix.ext; unfold raw38541step0 raw38541; decide +kernel
      have hl : raw38541Labels = labelEmbedding2 ∘ raw38541step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38541 raw38541Labels raw38541step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1009 node1009Labels := by rfl

def raw38542 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw38542Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38542step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw38542step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38542step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw38542step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38542step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw38542step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38542 raw38542Labels = mixedMoment B node1630 node1630Labels := by
  calc
    mixedMoment B raw38542 raw38542Labels = mixedMoment B raw38542step0 raw38542step0Labels := by
      have ha : raw38542step0 = (fun i j => raw38542 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38542step0 raw38542; decide +kernel
      have hl : raw38542step0Labels = raw38542Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38542 raw38542Labels permutation8 permutation7
    mixedMoment B raw38542step0 raw38542step0Labels = mixedMoment B raw38542step1 raw38542step1Labels := by
      have ha : raw38542step1 = -raw38542step0 := by apply Matrix.ext; change ∀ i j, raw38542step1 i j = -(raw38542step0 i j); unfold raw38542step1 raw38542step0; decide +kernel
      have hl : raw38542step1Labels = raw38542step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38542step1 raw38542step1Labels = mixedMoment B raw38542step2 raw38542step2Labels := by
      have ha : raw38542step2 = raw38542step1 := by apply Matrix.ext; unfold raw38542step2 raw38542step1; decide +kernel
      have hl : raw38542step1Labels = labelEmbedding4 ∘ raw38542step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38542step1 raw38542step1Labels raw38542step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1630 node1630Labels := by rfl

def raw38543 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw38543Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38543step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw38543step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38543 raw38543Labels = mixedMoment B node1012 node1012Labels := by
  calc
    mixedMoment B raw38543 raw38543Labels = mixedMoment B raw38543step0 raw38543step0Labels := by
      have ha : raw38543step0 = raw38543 := by apply Matrix.ext; unfold raw38543step0 raw38543; decide +kernel
      have hl : raw38543Labels = labelEmbedding2 ∘ raw38543step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38543 raw38543Labels raw38543step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1012 node1012Labels := by rfl

def raw38544 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw38544Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38544step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw38544step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38544step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw38544step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38544step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw38544step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38544 raw38544Labels = mixedMoment B node1627 node1627Labels := by
  calc
    mixedMoment B raw38544 raw38544Labels = mixedMoment B raw38544step0 raw38544step0Labels := by
      have ha : raw38544step0 = (fun i j => raw38544 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38544step0 raw38544; decide +kernel
      have hl : raw38544step0Labels = raw38544Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38544 raw38544Labels permutation8 permutation7
    mixedMoment B raw38544step0 raw38544step0Labels = mixedMoment B raw38544step1 raw38544step1Labels := by
      have ha : raw38544step1 = -raw38544step0 := by apply Matrix.ext; change ∀ i j, raw38544step1 i j = -(raw38544step0 i j); unfold raw38544step1 raw38544step0; decide +kernel
      have hl : raw38544step1Labels = raw38544step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38544step1 raw38544step1Labels = mixedMoment B raw38544step2 raw38544step2Labels := by
      have ha : raw38544step2 = raw38544step1 := by apply Matrix.ext; unfold raw38544step2 raw38544step1; decide +kernel
      have hl : raw38544step1Labels = labelEmbedding4 ∘ raw38544step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38544step1 raw38544step1Labels raw38544step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1627 node1627Labels := by rfl

def raw38545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38545Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38545step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38545 raw38545Labels = mixedMoment B node1034 node1034Labels := by
  calc
    mixedMoment B raw38545 raw38545Labels = mixedMoment B raw38545step0 raw38545step0Labels := by
      have ha : raw38545step0 = raw38545 := by apply Matrix.ext; unfold raw38545step0 raw38545; decide +kernel
      have hl : raw38545Labels = labelEmbedding2 ∘ raw38545step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38545 raw38545Labels raw38545step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1034 node1034Labels := by rfl

def raw38546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38546Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38546step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw38546step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38546step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38546step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38546step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38546step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38546 raw38546Labels = mixedMoment B node1644 node1644Labels := by
  calc
    mixedMoment B raw38546 raw38546Labels = mixedMoment B raw38546step0 raw38546step0Labels := by
      have ha : raw38546step0 = (fun i j => raw38546 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38546step0 raw38546; decide +kernel
      have hl : raw38546step0Labels = raw38546Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38546 raw38546Labels permutation176 permutation7
    mixedMoment B raw38546step0 raw38546step0Labels = mixedMoment B raw38546step1 raw38546step1Labels := by
      have ha : raw38546step1 = -raw38546step0 := by apply Matrix.ext; change ∀ i j, raw38546step1 i j = -(raw38546step0 i j); unfold raw38546step1 raw38546step0; decide +kernel
      have hl : raw38546step1Labels = raw38546step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38546step1 raw38546step1Labels = mixedMoment B raw38546step2 raw38546step2Labels := by
      have ha : raw38546step2 = raw38546step1 := by apply Matrix.ext; unfold raw38546step2 raw38546step1; decide +kernel
      have hl : raw38546step1Labels = labelEmbedding4 ∘ raw38546step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38546step1 raw38546step1Labels raw38546step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1644 node1644Labels := by rfl

def raw38547 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw38547Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw38547step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38547 raw38547Labels = mixedMoment B node1035 node1035Labels := by
  calc
    mixedMoment B raw38547 raw38547Labels = mixedMoment B raw38547step0 raw38547step0Labels := by
      have ha : raw38547step0 = raw38547 := by apply Matrix.ext; unfold raw38547step0 raw38547; decide +kernel
      have hl : raw38547Labels = labelEmbedding2 ∘ raw38547step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38547 raw38547Labels raw38547step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1035 node1035Labels := by rfl

def raw38548 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw38548Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw38548step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38548step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38548step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38548step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38548step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38548 raw38548Labels = mixedMoment B node1645 node1645Labels := by
  calc
    mixedMoment B raw38548 raw38548Labels = mixedMoment B raw38548step0 raw38548step0Labels := by
      have ha : raw38548step0 = (fun i j => raw38548 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38548step0 raw38548; decide +kernel
      have hl : raw38548step0Labels = raw38548Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38548 raw38548Labels permutation38 permutation7
    mixedMoment B raw38548step0 raw38548step0Labels = mixedMoment B raw38548step1 raw38548step1Labels := by
      have ha : raw38548step1 = -raw38548step0 := by apply Matrix.ext; change ∀ i j, raw38548step1 i j = -(raw38548step0 i j); unfold raw38548step1 raw38548step0; decide +kernel
      have hl : raw38548step1Labels = raw38548step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38548step1 raw38548step1Labels = mixedMoment B raw38548step2 raw38548step2Labels := by
      have ha : raw38548step2 = raw38548step1 := by apply Matrix.ext; unfold raw38548step2 raw38548step1; decide +kernel
      have hl : raw38548step1Labels = labelEmbedding4 ∘ raw38548step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38548step1 raw38548step1Labels raw38548step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1645 node1645Labels := by rfl

def raw38549 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw38549Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38549step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw38549step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38549 raw38549Labels = mixedMoment B node1037 node1037Labels := by
  calc
    mixedMoment B raw38549 raw38549Labels = mixedMoment B raw38549step0 raw38549step0Labels := by
      have ha : raw38549step0 = raw38549 := by apply Matrix.ext; unfold raw38549step0 raw38549; decide +kernel
      have hl : raw38549Labels = labelEmbedding2 ∘ raw38549step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38549 raw38549Labels raw38549step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1037 node1037Labels := by rfl

def raw38550 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw38550Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38550step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw38550step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38550step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![3, 0, -3]]
def raw38550step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38550step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![3, 0, -3]]
def raw38550step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38550 raw38550Labels = mixedMoment B node1647 node1647Labels := by
  calc
    mixedMoment B raw38550 raw38550Labels = mixedMoment B raw38550step0 raw38550step0Labels := by
      have ha : raw38550step0 = (fun i j => raw38550 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38550step0 raw38550; decide +kernel
      have hl : raw38550step0Labels = raw38550Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38550 raw38550Labels permutation10 permutation7
    mixedMoment B raw38550step0 raw38550step0Labels = mixedMoment B raw38550step1 raw38550step1Labels := by
      have ha : raw38550step1 = -raw38550step0 := by apply Matrix.ext; change ∀ i j, raw38550step1 i j = -(raw38550step0 i j); unfold raw38550step1 raw38550step0; decide +kernel
      have hl : raw38550step1Labels = raw38550step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38550step1 raw38550step1Labels = mixedMoment B raw38550step2 raw38550step2Labels := by
      have ha : raw38550step2 = raw38550step1 := by apply Matrix.ext; unfold raw38550step2 raw38550step1; decide +kernel
      have hl : raw38550step1Labels = labelEmbedding4 ∘ raw38550step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38550step1 raw38550step1Labels raw38550step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1647 node1647Labels := by rfl

def raw38551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw38551Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw38551step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38551 raw38551Labels = mixedMoment B node1039 node1039Labels := by
  calc
    mixedMoment B raw38551 raw38551Labels = mixedMoment B raw38551step0 raw38551step0Labels := by
      have ha : raw38551step0 = raw38551 := by apply Matrix.ext; unfold raw38551step0 raw38551; decide +kernel
      have hl : raw38551Labels = labelEmbedding2 ∘ raw38551step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38551 raw38551Labels raw38551step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1039 node1039Labels := by rfl

def raw38552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw38552Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38552step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw38552step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38552step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw38552step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38552step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw38552step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38552 raw38552Labels = mixedMoment B node1706 node1706Labels := by
  calc
    mixedMoment B raw38552 raw38552Labels = mixedMoment B raw38552step0 raw38552step0Labels := by
      have ha : raw38552step0 = (fun i j => raw38552 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38552step0 raw38552; decide +kernel
      have hl : raw38552step0Labels = raw38552Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38552 raw38552Labels permutation182 permutation7
    mixedMoment B raw38552step0 raw38552step0Labels = mixedMoment B raw38552step1 raw38552step1Labels := by
      have ha : raw38552step1 = -raw38552step0 := by apply Matrix.ext; change ∀ i j, raw38552step1 i j = -(raw38552step0 i j); unfold raw38552step1 raw38552step0; decide +kernel
      have hl : raw38552step1Labels = raw38552step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38552step1 raw38552step1Labels = mixedMoment B raw38552step2 raw38552step2Labels := by
      have ha : raw38552step2 = raw38552step1 := by apply Matrix.ext; unfold raw38552step2 raw38552step1; decide +kernel
      have hl : raw38552step1Labels = labelEmbedding4 ∘ raw38552step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38552step1 raw38552step1Labels raw38552step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1706 node1706Labels := by rfl

def raw38553 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw38553Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw38553step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38553 raw38553Labels = mixedMoment B node1040 node1040Labels := by
  calc
    mixedMoment B raw38553 raw38553Labels = mixedMoment B raw38553step0 raw38553step0Labels := by
      have ha : raw38553step0 = raw38553 := by apply Matrix.ext; unfold raw38553step0 raw38553; decide +kernel
      have hl : raw38553Labels = labelEmbedding2 ∘ raw38553step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38553 raw38553Labels raw38553step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1040 node1040Labels := by rfl

def raw38554 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw38554Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw38554step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38554step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw38554step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38554step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw38554step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38554 raw38554Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw38554 raw38554Labels = mixedMoment B raw38554step0 raw38554step0Labels := by
      have ha : raw38554step0 = (fun i j => raw38554 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38554step0 raw38554; decide +kernel
      have hl : raw38554step0Labels = raw38554Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38554 raw38554Labels permutation40 permutation7
    mixedMoment B raw38554step0 raw38554step0Labels = mixedMoment B raw38554step1 raw38554step1Labels := by
      have ha : raw38554step1 = -raw38554step0 := by apply Matrix.ext; change ∀ i j, raw38554step1 i j = -(raw38554step0 i j); unfold raw38554step1 raw38554step0; decide +kernel
      have hl : raw38554step1Labels = raw38554step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38554step1 raw38554step1Labels = mixedMoment B raw38554step2 raw38554step2Labels := by
      have ha : raw38554step2 = raw38554step1 := by apply Matrix.ext; unfold raw38554step2 raw38554step1; decide +kernel
      have hl : raw38554step1Labels = labelEmbedding4 ∘ raw38554step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38554step1 raw38554step1Labels raw38554step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1707 node1707Labels := by rfl

def raw38555 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw38555Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw38555step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38555 raw38555Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw38555 raw38555Labels = mixedMoment B raw38555step0 raw38555step0Labels := by
      have ha : raw38555step0 = raw38555 := by apply Matrix.ext; unfold raw38555step0 raw38555; decide +kernel
      have hl : raw38555Labels = labelEmbedding2 ∘ raw38555step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38555 raw38555Labels raw38555step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1041 node1041Labels := by rfl

def raw38556 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw38556Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw38556step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38556step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw38556step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38556step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw38556step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38556 raw38556Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw38556 raw38556Labels = mixedMoment B raw38556step0 raw38556step0Labels := by
      have ha : raw38556step0 = (fun i j => raw38556 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38556step0 raw38556; decide +kernel
      have hl : raw38556step0Labels = raw38556Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38556 raw38556Labels permutation38 permutation7
    mixedMoment B raw38556step0 raw38556step0Labels = mixedMoment B raw38556step1 raw38556step1Labels := by
      have ha : raw38556step1 = -raw38556step0 := by apply Matrix.ext; change ∀ i j, raw38556step1 i j = -(raw38556step0 i j); unfold raw38556step1 raw38556step0; decide +kernel
      have hl : raw38556step1Labels = raw38556step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38556step1 raw38556step1Labels = mixedMoment B raw38556step2 raw38556step2Labels := by
      have ha : raw38556step2 = raw38556step1 := by apply Matrix.ext; unfold raw38556step2 raw38556step1; decide +kernel
      have hl : raw38556step1Labels = labelEmbedding4 ∘ raw38556step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38556step1 raw38556step1Labels raw38556step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

def raw38557 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw38557Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38557step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw38557step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38557 raw38557Labels = mixedMoment B node1043 node1043Labels := by
  calc
    mixedMoment B raw38557 raw38557Labels = mixedMoment B raw38557step0 raw38557step0Labels := by
      have ha : raw38557step0 = raw38557 := by apply Matrix.ext; unfold raw38557step0 raw38557; decide +kernel
      have hl : raw38557Labels = labelEmbedding2 ∘ raw38557step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38557 raw38557Labels raw38557step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1043 node1043Labels := by rfl

def raw38558 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw38558Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38558step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw38558step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38558step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw38558step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38558step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw38558step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38558 raw38558Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw38558 raw38558Labels = mixedMoment B raw38558step0 raw38558step0Labels := by
      have ha : raw38558step0 = (fun i j => raw38558 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38558step0 raw38558; decide +kernel
      have hl : raw38558step0Labels = raw38558Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38558 raw38558Labels permutation10 permutation7
    mixedMoment B raw38558step0 raw38558step0Labels = mixedMoment B raw38558step1 raw38558step1Labels := by
      have ha : raw38558step1 = -raw38558step0 := by apply Matrix.ext; change ∀ i j, raw38558step1 i j = -(raw38558step0 i j); unfold raw38558step1 raw38558step0; decide +kernel
      have hl : raw38558step1Labels = raw38558step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38558step1 raw38558step1Labels = mixedMoment B raw38558step2 raw38558step2Labels := by
      have ha : raw38558step2 = raw38558step1 := by apply Matrix.ext; unfold raw38558step2 raw38558step1; decide +kernel
      have hl : raw38558step1Labels = labelEmbedding4 ∘ raw38558step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38558step1 raw38558step1Labels raw38558step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1725 node1725Labels := by rfl

def raw38559 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38559Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38559step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38559 raw38559Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw38559 raw38559Labels = mixedMoment B raw38559step0 raw38559step0Labels := by
      have ha : raw38559step0 = raw38559 := by apply Matrix.ext; unfold raw38559step0 raw38559; decide +kernel
      have hl : raw38559Labels = labelEmbedding2 ∘ raw38559step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38559 raw38559Labels raw38559step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1044 node1044Labels := by rfl

def raw38560 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38560Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw38560step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38560step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw38560step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38560step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw38560step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38560 raw38560Labels = mixedMoment B node1737 node1737Labels := by
  calc
    mixedMoment B raw38560 raw38560Labels = mixedMoment B raw38560step0 raw38560step0Labels := by
      have ha : raw38560step0 = (fun i j => raw38560 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38560step0 raw38560; decide +kernel
      have hl : raw38560step0Labels = raw38560Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38560 raw38560Labels permutation50 permutation7
    mixedMoment B raw38560step0 raw38560step0Labels = mixedMoment B raw38560step1 raw38560step1Labels := by
      have ha : raw38560step1 = -raw38560step0 := by apply Matrix.ext; change ∀ i j, raw38560step1 i j = -(raw38560step0 i j); unfold raw38560step1 raw38560step0; decide +kernel
      have hl : raw38560step1Labels = raw38560step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38560step1 raw38560step1Labels = mixedMoment B raw38560step2 raw38560step2Labels := by
      have ha : raw38560step2 = raw38560step1 := by apply Matrix.ext; unfold raw38560step2 raw38560step1; decide +kernel
      have hl : raw38560step1Labels = labelEmbedding4 ∘ raw38560step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38560step1 raw38560step1Labels raw38560step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1737 node1737Labels := by rfl

def raw38561 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38561Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38561step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38561step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38561 raw38561Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw38561 raw38561Labels = mixedMoment B raw38561step0 raw38561step0Labels := by
      have ha : raw38561step0 = raw38561 := by apply Matrix.ext; unfold raw38561step0 raw38561; decide +kernel
      have hl : raw38561Labels = labelEmbedding2 ∘ raw38561step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38561 raw38561Labels raw38561step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1046 node1046Labels := by rfl

def raw38562 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38562Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38562step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw38562step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38562step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw38562step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38562step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw38562step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38562 raw38562Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw38562 raw38562Labels = mixedMoment B raw38562step0 raw38562step0Labels := by
      have ha : raw38562step0 = (fun i j => raw38562 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38562step0 raw38562; decide +kernel
      have hl : raw38562step0Labels = raw38562Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38562 raw38562Labels permutation8 permutation7
    mixedMoment B raw38562step0 raw38562step0Labels = mixedMoment B raw38562step1 raw38562step1Labels := by
      have ha : raw38562step1 = -raw38562step0 := by apply Matrix.ext; change ∀ i j, raw38562step1 i j = -(raw38562step0 i j); unfold raw38562step1 raw38562step0; decide +kernel
      have hl : raw38562step1Labels = raw38562step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38562step1 raw38562step1Labels = mixedMoment B raw38562step2 raw38562step2Labels := by
      have ha : raw38562step2 = raw38562step1 := by apply Matrix.ext; unfold raw38562step2 raw38562step1; decide +kernel
      have hl : raw38562step1Labels = labelEmbedding4 ∘ raw38562step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38562step1 raw38562step1Labels raw38562step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1750 node1750Labels := by rfl

def raw38563 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38563Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38563step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38563step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38563 raw38563Labels = mixedMoment B node1049 node1049Labels := by
  calc
    mixedMoment B raw38563 raw38563Labels = mixedMoment B raw38563step0 raw38563step0Labels := by
      have ha : raw38563step0 = raw38563 := by apply Matrix.ext; unfold raw38563step0 raw38563; decide +kernel
      have hl : raw38563Labels = labelEmbedding2 ∘ raw38563step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38563 raw38563Labels raw38563step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1049 node1049Labels := by rfl

def raw38564 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38564Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38564step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw38564step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38564step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw38564step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38564step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw38564step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38564 raw38564Labels = mixedMoment B node1738 node1738Labels := by
  calc
    mixedMoment B raw38564 raw38564Labels = mixedMoment B raw38564step0 raw38564step0Labels := by
      have ha : raw38564step0 = (fun i j => raw38564 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38564step0 raw38564; decide +kernel
      have hl : raw38564step0Labels = raw38564Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38564 raw38564Labels permutation10 permutation7
    mixedMoment B raw38564step0 raw38564step0Labels = mixedMoment B raw38564step1 raw38564step1Labels := by
      have ha : raw38564step1 = -raw38564step0 := by apply Matrix.ext; change ∀ i j, raw38564step1 i j = -(raw38564step0 i j); unfold raw38564step1 raw38564step0; decide +kernel
      have hl : raw38564step1Labels = raw38564step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38564step1 raw38564step1Labels = mixedMoment B raw38564step2 raw38564step2Labels := by
      have ha : raw38564step2 = raw38564step1 := by apply Matrix.ext; unfold raw38564step2 raw38564step1; decide +kernel
      have hl : raw38564step1Labels = labelEmbedding4 ∘ raw38564step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38564step1 raw38564step1Labels raw38564step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1738 node1738Labels := by rfl

def raw38565 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38565Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38565step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38565step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38565 raw38565Labels = mixedMoment B node1050 node1050Labels := by
  calc
    mixedMoment B raw38565 raw38565Labels = mixedMoment B raw38565step0 raw38565step0Labels := by
      have ha : raw38565step0 = raw38565 := by apply Matrix.ext; unfold raw38565step0 raw38565; decide +kernel
      have hl : raw38565Labels = labelEmbedding2 ∘ raw38565step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38565 raw38565Labels raw38565step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1050 node1050Labels := by rfl

def raw38566 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38566Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38566step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw38566step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38566step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw38566step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38566step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw38566step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38566 raw38566Labels = mixedMoment B node1751 node1751Labels := by
  calc
    mixedMoment B raw38566 raw38566Labels = mixedMoment B raw38566step0 raw38566step0Labels := by
      have ha : raw38566step0 = (fun i j => raw38566 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38566step0 raw38566; decide +kernel
      have hl : raw38566step0Labels = raw38566Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38566 raw38566Labels permutation8 permutation7
    mixedMoment B raw38566step0 raw38566step0Labels = mixedMoment B raw38566step1 raw38566step1Labels := by
      have ha : raw38566step1 = -raw38566step0 := by apply Matrix.ext; change ∀ i j, raw38566step1 i j = -(raw38566step0 i j); unfold raw38566step1 raw38566step0; decide +kernel
      have hl : raw38566step1Labels = raw38566step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38566step1 raw38566step1Labels = mixedMoment B raw38566step2 raw38566step2Labels := by
      have ha : raw38566step2 = raw38566step1 := by apply Matrix.ext; unfold raw38566step2 raw38566step1; decide +kernel
      have hl : raw38566step1Labels = labelEmbedding4 ∘ raw38566step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38566step1 raw38566step1Labels raw38566step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1751 node1751Labels := by rfl

def raw38567 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw38567Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38567step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw38567step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38567 raw38567Labels = mixedMoment B node1051 node1051Labels := by
  calc
    mixedMoment B raw38567 raw38567Labels = mixedMoment B raw38567step0 raw38567step0Labels := by
      have ha : raw38567step0 = raw38567 := by apply Matrix.ext; unfold raw38567step0 raw38567; decide +kernel
      have hl : raw38567Labels = labelEmbedding2 ∘ raw38567step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38567 raw38567Labels raw38567step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1051 node1051Labels := by rfl

def raw38568 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw38568Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38568step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw38568step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38568step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw38568step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38568step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw38568step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38568 raw38568Labels = mixedMoment B node1752 node1752Labels := by
  calc
    mixedMoment B raw38568 raw38568Labels = mixedMoment B raw38568step0 raw38568step0Labels := by
      have ha : raw38568step0 = (fun i j => raw38568 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38568step0 raw38568; decide +kernel
      have hl : raw38568step0Labels = raw38568Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38568 raw38568Labels permutation2 permutation7
    mixedMoment B raw38568step0 raw38568step0Labels = mixedMoment B raw38568step1 raw38568step1Labels := by
      have ha : raw38568step1 = -raw38568step0 := by apply Matrix.ext; change ∀ i j, raw38568step1 i j = -(raw38568step0 i j); unfold raw38568step1 raw38568step0; decide +kernel
      have hl : raw38568step1Labels = raw38568step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38568step1 raw38568step1Labels = mixedMoment B raw38568step2 raw38568step2Labels := by
      have ha : raw38568step2 = raw38568step1 := by apply Matrix.ext; unfold raw38568step2 raw38568step1; decide +kernel
      have hl : raw38568step1Labels = labelEmbedding4 ∘ raw38568step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38568step1 raw38568step1Labels raw38568step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1752 node1752Labels := by rfl

def raw38569 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38569Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38569step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38569 raw38569Labels = mixedMoment B node1073 node1073Labels := by
  calc
    mixedMoment B raw38569 raw38569Labels = mixedMoment B raw38569step0 raw38569step0Labels := by
      have ha : raw38569step0 = raw38569 := by apply Matrix.ext; unfold raw38569step0 raw38569; decide +kernel
      have hl : raw38569Labels = labelEmbedding2 ∘ raw38569step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38569 raw38569Labels raw38569step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1073 node1073Labels := by rfl

def raw38570 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38570Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw38570step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38570step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38570step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38570step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38570 raw38570Labels = mixedMoment B node1648 node1648Labels := by
  calc
    mixedMoment B raw38570 raw38570Labels = mixedMoment B raw38570step0 raw38570step0Labels := by
      have ha : raw38570step0 = (fun i j => raw38570 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38570step0 raw38570; decide +kernel
      have hl : raw38570step0Labels = raw38570Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38570 raw38570Labels permutation32 permutation7
    mixedMoment B raw38570step0 raw38570step0Labels = mixedMoment B raw38570step1 raw38570step1Labels := by
      have ha : raw38570step1 = -raw38570step0 := by apply Matrix.ext; change ∀ i j, raw38570step1 i j = -(raw38570step0 i j); unfold raw38570step1 raw38570step0; decide +kernel
      have hl : raw38570step1Labels = raw38570step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38570step1 raw38570step1Labels = mixedMoment B raw38570step2 raw38570step2Labels := by
      have ha : raw38570step2 = raw38570step1 := by apply Matrix.ext; unfold raw38570step2 raw38570step1; decide +kernel
      have hl : raw38570step1Labels = labelEmbedding4 ∘ raw38570step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38570step1 raw38570step1Labels raw38570step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1648 node1648Labels := by rfl

def raw38571 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw38571Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38571step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw38571step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38571 raw38571Labels = mixedMoment B node1074 node1074Labels := by
  calc
    mixedMoment B raw38571 raw38571Labels = mixedMoment B raw38571step0 raw38571step0Labels := by
      have ha : raw38571step0 = raw38571 := by apply Matrix.ext; unfold raw38571step0 raw38571; decide +kernel
      have hl : raw38571Labels = labelEmbedding2 ∘ raw38571step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38571 raw38571Labels raw38571step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1074 node1074Labels := by rfl

def raw38572 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw38572Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38572step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw38572step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38572step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38572step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38572step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38572step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38572 raw38572Labels = mixedMoment B node1650 node1650Labels := by
  calc
    mixedMoment B raw38572 raw38572Labels = mixedMoment B raw38572step0 raw38572step0Labels := by
      have ha : raw38572step0 = (fun i j => raw38572 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38572step0 raw38572; decide +kernel
      have hl : raw38572step0Labels = raw38572Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38572 raw38572Labels permutation8 permutation7
    mixedMoment B raw38572step0 raw38572step0Labels = mixedMoment B raw38572step1 raw38572step1Labels := by
      have ha : raw38572step1 = -raw38572step0 := by apply Matrix.ext; change ∀ i j, raw38572step1 i j = -(raw38572step0 i j); unfold raw38572step1 raw38572step0; decide +kernel
      have hl : raw38572step1Labels = raw38572step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38572step1 raw38572step1Labels = mixedMoment B raw38572step2 raw38572step2Labels := by
      have ha : raw38572step2 = raw38572step1 := by apply Matrix.ext; unfold raw38572step2 raw38572step1; decide +kernel
      have hl : raw38572step1Labels = labelEmbedding4 ∘ raw38572step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38572step1 raw38572step1Labels raw38572step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1650 node1650Labels := by rfl

def raw38573 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw38573Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38573step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw38573step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38573 raw38573Labels = mixedMoment B node1075 node1075Labels := by
  calc
    mixedMoment B raw38573 raw38573Labels = mixedMoment B raw38573step0 raw38573step0Labels := by
      have ha : raw38573step0 = raw38573 := by apply Matrix.ext; unfold raw38573step0 raw38573; decide +kernel
      have hl : raw38573Labels = labelEmbedding2 ∘ raw38573step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38573 raw38573Labels raw38573step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1075 node1075Labels := by rfl

def raw38574 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw38574Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38574step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw38574step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38574step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38574step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38574step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38574step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38574 raw38574Labels = mixedMoment B node1653 node1653Labels := by
  calc
    mixedMoment B raw38574 raw38574Labels = mixedMoment B raw38574step0 raw38574step0Labels := by
      have ha : raw38574step0 = (fun i j => raw38574 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38574step0 raw38574; decide +kernel
      have hl : raw38574step0Labels = raw38574Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38574 raw38574Labels permutation8 permutation7
    mixedMoment B raw38574step0 raw38574step0Labels = mixedMoment B raw38574step1 raw38574step1Labels := by
      have ha : raw38574step1 = -raw38574step0 := by apply Matrix.ext; change ∀ i j, raw38574step1 i j = -(raw38574step0 i j); unfold raw38574step1 raw38574step0; decide +kernel
      have hl : raw38574step1Labels = raw38574step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38574step1 raw38574step1Labels = mixedMoment B raw38574step2 raw38574step2Labels := by
      have ha : raw38574step2 = raw38574step1 := by apply Matrix.ext; unfold raw38574step2 raw38574step1; decide +kernel
      have hl : raw38574step1Labels = labelEmbedding4 ∘ raw38574step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38574step1 raw38574step1Labels raw38574step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1653 node1653Labels := by rfl

def raw38575 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw38575Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38575step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw38575step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38575 raw38575Labels = mixedMoment B node1077 node1077Labels := by
  calc
    mixedMoment B raw38575 raw38575Labels = mixedMoment B raw38575step0 raw38575step0Labels := by
      have ha : raw38575step0 = raw38575 := by apply Matrix.ext; unfold raw38575step0 raw38575; decide +kernel
      have hl : raw38575Labels = labelEmbedding2 ∘ raw38575step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38575 raw38575Labels raw38575step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1077 node1077Labels := by rfl

def raw38576 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw38576Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38576step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw38576step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38576step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw38576step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38576 raw38576Labels = mixedMoment B node1077 node1077Labels := by
  calc
    mixedMoment B raw38576 raw38576Labels = mixedMoment B raw38576step0 raw38576step0Labels := by
      have ha : raw38576step0 = (fun i j => raw38576 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38576step0 raw38576; decide +kernel
      have hl : raw38576step0Labels = raw38576Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38576 raw38576Labels permutation7 permutation7
    mixedMoment B raw38576step0 raw38576step0Labels = mixedMoment B raw38576step1 raw38576step1Labels := by
      have ha : raw38576step1 = raw38576step0 := by apply Matrix.ext; unfold raw38576step1 raw38576step0; decide +kernel
      have hl : raw38576step0Labels = labelEmbedding4 ∘ raw38576step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38576step0 raw38576step0Labels raw38576step1Labels labelEmbedding4 hl
    _ = mixedMoment B node1077 node1077Labels := by rfl

def raw38577 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw38577Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw38577step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38577 raw38577Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw38577 raw38577Labels = mixedMoment B raw38577step0 raw38577step0Labels := by
      have ha : raw38577step0 = raw38577 := by apply Matrix.ext; unfold raw38577step0 raw38577; decide +kernel
      have hl : raw38577Labels = labelEmbedding2 ∘ raw38577step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38577 raw38577Labels raw38577step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1079 node1079Labels := by rfl

def raw38578 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw38578Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw38578step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38578step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38578step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38578step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38578step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38578 raw38578Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw38578 raw38578Labels = mixedMoment B raw38578step0 raw38578step0Labels := by
      have ha : raw38578step0 = (fun i j => raw38578 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38578step0 raw38578; decide +kernel
      have hl : raw38578step0Labels = raw38578Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38578 raw38578Labels permutation32 permutation7
    mixedMoment B raw38578step0 raw38578step0Labels = mixedMoment B raw38578step1 raw38578step1Labels := by
      have ha : raw38578step1 = -raw38578step0 := by apply Matrix.ext; change ∀ i j, raw38578step1 i j = -(raw38578step0 i j); unfold raw38578step1 raw38578step0; decide +kernel
      have hl : raw38578step1Labels = raw38578step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38578step1 raw38578step1Labels = mixedMoment B raw38578step2 raw38578step2Labels := by
      have ha : raw38578step2 = raw38578step1 := by apply Matrix.ext; unfold raw38578step2 raw38578step1; decide +kernel
      have hl : raw38578step1Labels = labelEmbedding4 ∘ raw38578step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38578step1 raw38578step1Labels raw38578step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1708 node1708Labels := by rfl

def raw38579 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw38579Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38579step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw38579step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38579 raw38579Labels = mixedMoment B node1080 node1080Labels := by
  calc
    mixedMoment B raw38579 raw38579Labels = mixedMoment B raw38579step0 raw38579step0Labels := by
      have ha : raw38579step0 = raw38579 := by apply Matrix.ext; unfold raw38579step0 raw38579; decide +kernel
      have hl : raw38579Labels = labelEmbedding2 ∘ raw38579step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38579 raw38579Labels raw38579step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1080 node1080Labels := by rfl

def raw38580 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw38580Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38580step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw38580step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38580step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw38580step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38580step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw38580step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38580 raw38580Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw38580 raw38580Labels = mixedMoment B raw38580step0 raw38580step0Labels := by
      have ha : raw38580step0 = (fun i j => raw38580 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38580step0 raw38580; decide +kernel
      have hl : raw38580step0Labels = raw38580Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38580 raw38580Labels permutation8 permutation7
    mixedMoment B raw38580step0 raw38580step0Labels = mixedMoment B raw38580step1 raw38580step1Labels := by
      have ha : raw38580step1 = -raw38580step0 := by apply Matrix.ext; change ∀ i j, raw38580step1 i j = -(raw38580step0 i j); unfold raw38580step1 raw38580step0; decide +kernel
      have hl : raw38580step1Labels = raw38580step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38580step1 raw38580step1Labels = mixedMoment B raw38580step2 raw38580step2Labels := by
      have ha : raw38580step2 = raw38580step1 := by apply Matrix.ext; unfold raw38580step2 raw38580step1; decide +kernel
      have hl : raw38580step1Labels = labelEmbedding4 ∘ raw38580step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38580step1 raw38580step1Labels raw38580step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1710 node1710Labels := by rfl

def raw38581 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw38581Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38581step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw38581step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38581 raw38581Labels = mixedMoment B node1083 node1083Labels := by
  calc
    mixedMoment B raw38581 raw38581Labels = mixedMoment B raw38581step0 raw38581step0Labels := by
      have ha : raw38581step0 = raw38581 := by apply Matrix.ext; unfold raw38581step0 raw38581; decide +kernel
      have hl : raw38581Labels = labelEmbedding2 ∘ raw38581step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38581 raw38581Labels raw38581step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1083 node1083Labels := by rfl

def raw38582 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw38582Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38582step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw38582step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38582step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38582step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38582step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38582step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38582 raw38582Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw38582 raw38582Labels = mixedMoment B raw38582step0 raw38582step0Labels := by
      have ha : raw38582step0 = (fun i j => raw38582 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38582step0 raw38582; decide +kernel
      have hl : raw38582step0Labels = raw38582Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38582 raw38582Labels permutation9 permutation7
    mixedMoment B raw38582step0 raw38582step0Labels = mixedMoment B raw38582step1 raw38582step1Labels := by
      have ha : raw38582step1 = -raw38582step0 := by apply Matrix.ext; change ∀ i j, raw38582step1 i j = -(raw38582step0 i j); unfold raw38582step1 raw38582step0; decide +kernel
      have hl : raw38582step1Labels = raw38582step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38582step1 raw38582step1Labels = mixedMoment B raw38582step2 raw38582step2Labels := by
      have ha : raw38582step2 = raw38582step1 := by apply Matrix.ext; unfold raw38582step2 raw38582step1; decide +kernel
      have hl : raw38582step1Labels = labelEmbedding4 ∘ raw38582step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38582step1 raw38582step1Labels raw38582step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1728 node1728Labels := by rfl

def raw38583 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38583Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38583step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38583step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38583 raw38583Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw38583 raw38583Labels = mixedMoment B raw38583step0 raw38583step0Labels := by
      have ha : raw38583step0 = raw38583 := by apply Matrix.ext; unfold raw38583step0 raw38583; decide +kernel
      have hl : raw38583Labels = labelEmbedding2 ∘ raw38583step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38583 raw38583Labels raw38583step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1087 node1087Labels := by rfl

def raw38584 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38584Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38584step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw38584step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38584step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw38584step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38584step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw38584step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38584 raw38584Labels = mixedMoment B node1739 node1739Labels := by
  calc
    mixedMoment B raw38584 raw38584Labels = mixedMoment B raw38584step0 raw38584step0Labels := by
      have ha : raw38584step0 = (fun i j => raw38584 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38584step0 raw38584; decide +kernel
      have hl : raw38584step0Labels = raw38584Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38584 raw38584Labels permutation12 permutation7
    mixedMoment B raw38584step0 raw38584step0Labels = mixedMoment B raw38584step1 raw38584step1Labels := by
      have ha : raw38584step1 = -raw38584step0 := by apply Matrix.ext; change ∀ i j, raw38584step1 i j = -(raw38584step0 i j); unfold raw38584step1 raw38584step0; decide +kernel
      have hl : raw38584step1Labels = raw38584step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38584step1 raw38584step1Labels = mixedMoment B raw38584step2 raw38584step2Labels := by
      have ha : raw38584step2 = raw38584step1 := by apply Matrix.ext; unfold raw38584step2 raw38584step1; decide +kernel
      have hl : raw38584step1Labels = labelEmbedding4 ∘ raw38584step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38584step1 raw38584step1Labels raw38584step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1739 node1739Labels := by rfl

def raw38585 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw38585Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38585step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw38585step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38585 raw38585Labels = mixedMoment B node1091 node1091Labels := by
  calc
    mixedMoment B raw38585 raw38585Labels = mixedMoment B raw38585step0 raw38585step0Labels := by
      have ha : raw38585step0 = raw38585 := by apply Matrix.ext; unfold raw38585step0 raw38585; decide +kernel
      have hl : raw38585Labels = labelEmbedding2 ∘ raw38585step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38585 raw38585Labels raw38585step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1091 node1091Labels := by rfl

def raw38586 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw38586Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38586step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -2, 3], ![-2, 1, 1]]
def raw38586step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38586step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]
def raw38586step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38586step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]
def raw38586step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38586 raw38586Labels = mixedMoment B node1756 node1756Labels := by
  calc
    mixedMoment B raw38586 raw38586Labels = mixedMoment B raw38586step0 raw38586step0Labels := by
      have ha : raw38586step0 = (fun i j => raw38586 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38586step0 raw38586; decide +kernel
      have hl : raw38586step0Labels = raw38586Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38586 raw38586Labels permutation3 permutation7
    mixedMoment B raw38586step0 raw38586step0Labels = mixedMoment B raw38586step1 raw38586step1Labels := by
      have ha : raw38586step1 = -raw38586step0 := by apply Matrix.ext; change ∀ i j, raw38586step1 i j = -(raw38586step0 i j); unfold raw38586step1 raw38586step0; decide +kernel
      have hl : raw38586step1Labels = raw38586step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38586step1 raw38586step1Labels = mixedMoment B raw38586step2 raw38586step2Labels := by
      have ha : raw38586step2 = raw38586step1 := by apply Matrix.ext; unfold raw38586step2 raw38586step1; decide +kernel
      have hl : raw38586step1Labels = labelEmbedding4 ∘ raw38586step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38586step1 raw38586step1Labels raw38586step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1756 node1756Labels := by rfl

def raw38587 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw38587Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38587step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw38587step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38587 raw38587Labels = mixedMoment B node1094 node1094Labels := by
  calc
    mixedMoment B raw38587 raw38587Labels = mixedMoment B raw38587step0 raw38587step0Labels := by
      have ha : raw38587step0 = raw38587 := by apply Matrix.ext; unfold raw38587step0 raw38587; decide +kernel
      have hl : raw38587Labels = labelEmbedding2 ∘ raw38587step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38587 raw38587Labels raw38587step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1094 node1094Labels := by rfl

def raw38588 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw38588Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38588step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-3, 1, 2]]
def raw38588step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38588step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw38588step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38588step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw38588step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38588 raw38588Labels = mixedMoment B node1741 node1741Labels := by
  calc
    mixedMoment B raw38588 raw38588Labels = mixedMoment B raw38588step0 raw38588step0Labels := by
      have ha : raw38588step0 = (fun i j => raw38588 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38588step0 raw38588; decide +kernel
      have hl : raw38588step0Labels = raw38588Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38588 raw38588Labels permutation2 permutation7
    mixedMoment B raw38588step0 raw38588step0Labels = mixedMoment B raw38588step1 raw38588step1Labels := by
      have ha : raw38588step1 = -raw38588step0 := by apply Matrix.ext; change ∀ i j, raw38588step1 i j = -(raw38588step0 i j); unfold raw38588step1 raw38588step0; decide +kernel
      have hl : raw38588step1Labels = raw38588step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38588step1 raw38588step1Labels = mixedMoment B raw38588step2 raw38588step2Labels := by
      have ha : raw38588step2 = raw38588step1 := by apply Matrix.ext; unfold raw38588step2 raw38588step1; decide +kernel
      have hl : raw38588step1Labels = labelEmbedding4 ∘ raw38588step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38588step1 raw38588step1Labels raw38588step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1741 node1741Labels := by rfl

def raw38589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38589Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38589step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38589 raw38589Labels = mixedMoment B node1097 node1097Labels := by
  calc
    mixedMoment B raw38589 raw38589Labels = mixedMoment B raw38589step0 raw38589step0Labels := by
      have ha : raw38589step0 = raw38589 := by apply Matrix.ext; unfold raw38589step0 raw38589; decide +kernel
      have hl : raw38589Labels = labelEmbedding2 ∘ raw38589step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38589 raw38589Labels raw38589step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1097 node1097Labels := by rfl

def raw38590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38590Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38590step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw38590step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38590step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38590step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38590step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38590step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38590 raw38590Labels = mixedMoment B node3232 node3232Labels := by
  calc
    mixedMoment B raw38590 raw38590Labels = mixedMoment B raw38590step0 raw38590step0Labels := by
      have ha : raw38590step0 = (fun i j => raw38590 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38590step0 raw38590; decide +kernel
      have hl : raw38590step0Labels = raw38590Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38590 raw38590Labels permutation152 permutation7
    mixedMoment B raw38590step0 raw38590step0Labels = mixedMoment B raw38590step1 raw38590step1Labels := by
      have ha : raw38590step1 = -raw38590step0 := by apply Matrix.ext; change ∀ i j, raw38590step1 i j = -(raw38590step0 i j); unfold raw38590step1 raw38590step0; decide +kernel
      have hl : raw38590step1Labels = raw38590step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38590step1 raw38590step1Labels = mixedMoment B raw38590step2 raw38590step2Labels := by
      have ha : raw38590step2 = raw38590step1 := by apply Matrix.ext; unfold raw38590step2 raw38590step1; decide +kernel
      have hl : raw38590step1Labels = labelEmbedding4 ∘ raw38590step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38590step1 raw38590step1Labels raw38590step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3232 node3232Labels := by rfl

def raw38591 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw38591Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw38591step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38591 raw38591Labels = mixedMoment B node1098 node1098Labels := by
  calc
    mixedMoment B raw38591 raw38591Labels = mixedMoment B raw38591step0 raw38591step0Labels := by
      have ha : raw38591step0 = raw38591 := by apply Matrix.ext; unfold raw38591step0 raw38591; decide +kernel
      have hl : raw38591Labels = labelEmbedding2 ∘ raw38591step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38591 raw38591Labels raw38591step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1098 node1098Labels := by rfl

def raw38592 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw38592Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 2, -4]]
def raw38592step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 2, -4]]
def raw38592step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38592 raw38592Labels = mixedMoment B node1894 node1894Labels := by
  calc
    mixedMoment B raw38592 raw38592Labels = mixedMoment B raw38592step0 raw38592step0Labels := by
      have ha : raw38592step0 = (fun i j => raw38592 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38592step0 raw38592; decide +kernel
      have hl : raw38592step0Labels = raw38592Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38592 raw38592Labels permutation151 permutation7
    mixedMoment B raw38592step0 raw38592step0Labels = mixedMoment B raw38592step1 raw38592step1Labels := by
      have ha : raw38592step1 = raw38592step0 := by apply Matrix.ext; unfold raw38592step1 raw38592step0; decide +kernel
      have hl : raw38592step0Labels = labelEmbedding4 ∘ raw38592step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38592step0 raw38592step0Labels raw38592step1Labels labelEmbedding4 hl
    _ = mixedMoment B node1894 node1894Labels := by rfl

def raw38593 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw38593Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw38593step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38593 raw38593Labels = mixedMoment B node1099 node1099Labels := by
  calc
    mixedMoment B raw38593 raw38593Labels = mixedMoment B raw38593step0 raw38593step0Labels := by
      have ha : raw38593step0 = raw38593 := by apply Matrix.ext; unfold raw38593step0 raw38593; decide +kernel
      have hl : raw38593Labels = labelEmbedding2 ∘ raw38593step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38593 raw38593Labels raw38593step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1099 node1099Labels := by rfl

def raw38594 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw38594Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -1, -1], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw38594step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw38594step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38594step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw38594step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38594 raw38594Labels = mixedMoment B node3233 node3233Labels := by
  calc
    mixedMoment B raw38594 raw38594Labels = mixedMoment B raw38594step0 raw38594step0Labels := by
      have ha : raw38594step0 = (fun i j => raw38594 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38594step0 raw38594; decide +kernel
      have hl : raw38594step0Labels = raw38594Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38594 raw38594Labels permutation32 permutation7
    mixedMoment B raw38594step0 raw38594step0Labels = mixedMoment B raw38594step1 raw38594step1Labels := by
      have ha : raw38594step1 = -raw38594step0 := by apply Matrix.ext; change ∀ i j, raw38594step1 i j = -(raw38594step0 i j); unfold raw38594step1 raw38594step0; decide +kernel
      have hl : raw38594step1Labels = raw38594step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38594step1 raw38594step1Labels = mixedMoment B raw38594step2 raw38594step2Labels := by
      have ha : raw38594step2 = raw38594step1 := by apply Matrix.ext; unfold raw38594step2 raw38594step1; decide +kernel
      have hl : raw38594step1Labels = labelEmbedding4 ∘ raw38594step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38594step1 raw38594step1Labels raw38594step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3233 node3233Labels := by rfl

def raw38595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38595Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38595step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38595step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38595 raw38595Labels = mixedMoment B node1100 node1100Labels := by
  calc
    mixedMoment B raw38595 raw38595Labels = mixedMoment B raw38595step0 raw38595step0Labels := by
      have ha : raw38595step0 = raw38595 := by apply Matrix.ext; unfold raw38595step0 raw38595; decide +kernel
      have hl : raw38595Labels = labelEmbedding2 ∘ raw38595step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38595 raw38595Labels raw38595step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1100 node1100Labels := by rfl

def raw38596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38596Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38596step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw38596step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38596step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38596step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38596step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38596step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38596 raw38596Labels = mixedMoment B node3234 node3234Labels := by
  calc
    mixedMoment B raw38596 raw38596Labels = mixedMoment B raw38596step0 raw38596step0Labels := by
      have ha : raw38596step0 = (fun i j => raw38596 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38596step0 raw38596; decide +kernel
      have hl : raw38596step0Labels = raw38596Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38596 raw38596Labels permutation152 permutation7
    mixedMoment B raw38596step0 raw38596step0Labels = mixedMoment B raw38596step1 raw38596step1Labels := by
      have ha : raw38596step1 = -raw38596step0 := by apply Matrix.ext; change ∀ i j, raw38596step1 i j = -(raw38596step0 i j); unfold raw38596step1 raw38596step0; decide +kernel
      have hl : raw38596step1Labels = raw38596step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38596step1 raw38596step1Labels = mixedMoment B raw38596step2 raw38596step2Labels := by
      have ha : raw38596step2 = raw38596step1 := by apply Matrix.ext; unfold raw38596step2 raw38596step1; decide +kernel
      have hl : raw38596step1Labels = labelEmbedding4 ∘ raw38596step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38596step1 raw38596step1Labels raw38596step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3234 node3234Labels := by rfl

def raw38597 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38597Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38597step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38597 raw38597Labels = mixedMoment B node1101 node1101Labels := by
  calc
    mixedMoment B raw38597 raw38597Labels = mixedMoment B raw38597step0 raw38597step0Labels := by
      have ha : raw38597step0 = raw38597 := by apply Matrix.ext; unfold raw38597step0 raw38597; decide +kernel
      have hl : raw38597Labels = labelEmbedding2 ∘ raw38597step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38597 raw38597Labels raw38597step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1101 node1101Labels := by rfl

def raw38598 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38598Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw38598step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38598step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw38598step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38598step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw38598step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38598 raw38598Labels = mixedMoment B node3235 node3235Labels := by
  calc
    mixedMoment B raw38598 raw38598Labels = mixedMoment B raw38598step0 raw38598step0Labels := by
      have ha : raw38598step0 = (fun i j => raw38598 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38598step0 raw38598; decide +kernel
      have hl : raw38598step0Labels = raw38598Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38598 raw38598Labels permutation32 permutation7
    mixedMoment B raw38598step0 raw38598step0Labels = mixedMoment B raw38598step1 raw38598step1Labels := by
      have ha : raw38598step1 = -raw38598step0 := by apply Matrix.ext; change ∀ i j, raw38598step1 i j = -(raw38598step0 i j); unfold raw38598step1 raw38598step0; decide +kernel
      have hl : raw38598step1Labels = raw38598step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38598step1 raw38598step1Labels = mixedMoment B raw38598step2 raw38598step2Labels := by
      have ha : raw38598step2 = raw38598step1 := by apply Matrix.ext; unfold raw38598step2 raw38598step1; decide +kernel
      have hl : raw38598step1Labels = labelEmbedding4 ∘ raw38598step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38598step1 raw38598step1Labels raw38598step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3235 node3235Labels := by rfl

def raw38599 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38599Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38599step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38599 raw38599Labels = mixedMoment B node1102 node1102Labels := by
  calc
    mixedMoment B raw38599 raw38599Labels = mixedMoment B raw38599step0 raw38599step0Labels := by
      have ha : raw38599step0 = raw38599 := by apply Matrix.ext; unfold raw38599step0 raw38599; decide +kernel
      have hl : raw38599Labels = labelEmbedding2 ∘ raw38599step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38599 raw38599Labels raw38599step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1102 node1102Labels := by rfl

def raw38600 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38600Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw38600step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38600step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw38600step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38600step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw38600step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38600 raw38600Labels = mixedMoment B node3236 node3236Labels := by
  calc
    mixedMoment B raw38600 raw38600Labels = mixedMoment B raw38600step0 raw38600step0Labels := by
      have ha : raw38600step0 = (fun i j => raw38600 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38600step0 raw38600; decide +kernel
      have hl : raw38600step0Labels = raw38600Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38600 raw38600Labels permutation32 permutation7
    mixedMoment B raw38600step0 raw38600step0Labels = mixedMoment B raw38600step1 raw38600step1Labels := by
      have ha : raw38600step1 = -raw38600step0 := by apply Matrix.ext; change ∀ i j, raw38600step1 i j = -(raw38600step0 i j); unfold raw38600step1 raw38600step0; decide +kernel
      have hl : raw38600step1Labels = raw38600step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38600step1 raw38600step1Labels = mixedMoment B raw38600step2 raw38600step2Labels := by
      have ha : raw38600step2 = raw38600step1 := by apply Matrix.ext; unfold raw38600step2 raw38600step1; decide +kernel
      have hl : raw38600step1Labels = labelEmbedding4 ∘ raw38600step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38600step1 raw38600step1Labels raw38600step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3236 node3236Labels := by rfl

def raw38601 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw38601Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38601step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw38601step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38601 raw38601Labels = mixedMoment B node1103 node1103Labels := by
  calc
    mixedMoment B raw38601 raw38601Labels = mixedMoment B raw38601step0 raw38601step0Labels := by
      have ha : raw38601step0 = raw38601 := by apply Matrix.ext; unfold raw38601step0 raw38601; decide +kernel
      have hl : raw38601Labels = labelEmbedding2 ∘ raw38601step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38601 raw38601Labels raw38601step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1103 node1103Labels := by rfl

def raw38602 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw38602Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38602step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![2, -1, -1], ![2, 2, -4]]
def raw38602step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38602step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![2, -1, -1], ![2, 2, -4]]
def raw38602step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38602 raw38602Labels = mixedMoment B node1858 node1858Labels := by
  calc
    mixedMoment B raw38602 raw38602Labels = mixedMoment B raw38602step0 raw38602step0Labels := by
      have ha : raw38602step0 = (fun i j => raw38602 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38602step0 raw38602; decide +kernel
      have hl : raw38602step0Labels = raw38602Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38602 raw38602Labels permutation31 permutation7
    mixedMoment B raw38602step0 raw38602step0Labels = mixedMoment B raw38602step1 raw38602step1Labels := by
      have ha : raw38602step1 = raw38602step0 := by apply Matrix.ext; unfold raw38602step1 raw38602step0; decide +kernel
      have hl : raw38602step0Labels = labelEmbedding4 ∘ raw38602step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38602step0 raw38602step0Labels raw38602step1Labels labelEmbedding4 hl
    _ = mixedMoment B node1858 node1858Labels := by rfl

def raw38603 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw38603Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38603step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw38603step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38603 raw38603Labels = mixedMoment B node1104 node1104Labels := by
  calc
    mixedMoment B raw38603 raw38603Labels = mixedMoment B raw38603step0 raw38603step0Labels := by
      have ha : raw38603step0 = raw38603 := by apply Matrix.ext; unfold raw38603step0 raw38603; decide +kernel
      have hl : raw38603Labels = labelEmbedding2 ∘ raw38603step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38603 raw38603Labels raw38603step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1104 node1104Labels := by rfl

def raw38604 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw38604Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38604step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![2, -1, -1], ![-2, 0, 2], ![-2, -1, 3]]
def raw38604step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38604step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw38604step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38604step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw38604step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38604 raw38604Labels = mixedMoment B node3237 node3237Labels := by
  calc
    mixedMoment B raw38604 raw38604Labels = mixedMoment B raw38604step0 raw38604step0Labels := by
      have ha : raw38604step0 = (fun i j => raw38604 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38604step0 raw38604; decide +kernel
      have hl : raw38604step0Labels = raw38604Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38604 raw38604Labels permutation8 permutation7
    mixedMoment B raw38604step0 raw38604step0Labels = mixedMoment B raw38604step1 raw38604step1Labels := by
      have ha : raw38604step1 = -raw38604step0 := by apply Matrix.ext; change ∀ i j, raw38604step1 i j = -(raw38604step0 i j); unfold raw38604step1 raw38604step0; decide +kernel
      have hl : raw38604step1Labels = raw38604step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38604step1 raw38604step1Labels = mixedMoment B raw38604step2 raw38604step2Labels := by
      have ha : raw38604step2 = raw38604step1 := by apply Matrix.ext; unfold raw38604step2 raw38604step1; decide +kernel
      have hl : raw38604step1Labels = labelEmbedding4 ∘ raw38604step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38604step1 raw38604step1Labels raw38604step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3237 node3237Labels := by rfl

def raw38605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw38605Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38605step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw38605step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38605 raw38605Labels = mixedMoment B node1105 node1105Labels := by
  calc
    mixedMoment B raw38605 raw38605Labels = mixedMoment B raw38605step0 raw38605step0Labels := by
      have ha : raw38605step0 = raw38605 := by apply Matrix.ext; unfold raw38605step0 raw38605; decide +kernel
      have hl : raw38605Labels = labelEmbedding2 ∘ raw38605step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38605 raw38605Labels raw38605step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1105 node1105Labels := by rfl

def raw38606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw38606Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38606step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw38606step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38606step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw38606step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38606 raw38606Labels = mixedMoment B node1887 node1887Labels := by
  calc
    mixedMoment B raw38606 raw38606Labels = mixedMoment B raw38606step0 raw38606step0Labels := by
      have ha : raw38606step0 = (fun i j => raw38606 (permutation688 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38606step0 raw38606; decide +kernel
      have hl : raw38606step0Labels = raw38606Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38606 raw38606Labels permutation688 permutation7
    mixedMoment B raw38606step0 raw38606step0Labels = mixedMoment B raw38606step1 raw38606step1Labels := by
      have ha : raw38606step1 = raw38606step0 := by apply Matrix.ext; unfold raw38606step1 raw38606step0; decide +kernel
      have hl : raw38606step0Labels = labelEmbedding4 ∘ raw38606step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38606step0 raw38606step0Labels raw38606step1Labels labelEmbedding4 hl
    _ = mixedMoment B node1887 node1887Labels := by rfl

def raw38607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw38607Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38607step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw38607step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38607 raw38607Labels = mixedMoment B node1106 node1106Labels := by
  calc
    mixedMoment B raw38607 raw38607Labels = mixedMoment B raw38607step0 raw38607step0Labels := by
      have ha : raw38607step0 = raw38607 := by apply Matrix.ext; unfold raw38607step0 raw38607; decide +kernel
      have hl : raw38607Labels = labelEmbedding2 ∘ raw38607step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38607 raw38607Labels raw38607step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1106 node1106Labels := by rfl

def raw38608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw38608Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38608step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw38608step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38608step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw38608step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38608step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw38608step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38608 raw38608Labels = mixedMoment B node3249 node3249Labels := by
  calc
    mixedMoment B raw38608 raw38608Labels = mixedMoment B raw38608step0 raw38608step0Labels := by
      have ha : raw38608step0 = (fun i j => raw38608 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38608step0 raw38608; decide +kernel
      have hl : raw38608step0Labels = raw38608Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38608 raw38608Labels permutation152 permutation7
    mixedMoment B raw38608step0 raw38608step0Labels = mixedMoment B raw38608step1 raw38608step1Labels := by
      have ha : raw38608step1 = -raw38608step0 := by apply Matrix.ext; change ∀ i j, raw38608step1 i j = -(raw38608step0 i j); unfold raw38608step1 raw38608step0; decide +kernel
      have hl : raw38608step1Labels = raw38608step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38608step1 raw38608step1Labels = mixedMoment B raw38608step2 raw38608step2Labels := by
      have ha : raw38608step2 = raw38608step1 := by apply Matrix.ext; unfold raw38608step2 raw38608step1; decide +kernel
      have hl : raw38608step1Labels = labelEmbedding4 ∘ raw38608step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38608step1 raw38608step1Labels raw38608step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3249 node3249Labels := by rfl

def raw38609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38609Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38609step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38609 raw38609Labels = mixedMoment B node1107 node1107Labels := by
  calc
    mixedMoment B raw38609 raw38609Labels = mixedMoment B raw38609step0 raw38609step0Labels := by
      have ha : raw38609step0 = raw38609 := by apply Matrix.ext; unfold raw38609step0 raw38609; decide +kernel
      have hl : raw38609Labels = labelEmbedding2 ∘ raw38609step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38609 raw38609Labels raw38609step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1107 node1107Labels := by rfl

def raw38610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38610Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38610step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw38610step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38610step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw38610step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38610step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw38610step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38610 raw38610Labels = mixedMoment B node3250 node3250Labels := by
  calc
    mixedMoment B raw38610 raw38610Labels = mixedMoment B raw38610step0 raw38610step0Labels := by
      have ha : raw38610step0 = (fun i j => raw38610 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38610step0 raw38610; decide +kernel
      have hl : raw38610step0Labels = raw38610Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38610 raw38610Labels permutation152 permutation7
    mixedMoment B raw38610step0 raw38610step0Labels = mixedMoment B raw38610step1 raw38610step1Labels := by
      have ha : raw38610step1 = -raw38610step0 := by apply Matrix.ext; change ∀ i j, raw38610step1 i j = -(raw38610step0 i j); unfold raw38610step1 raw38610step0; decide +kernel
      have hl : raw38610step1Labels = raw38610step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38610step1 raw38610step1Labels = mixedMoment B raw38610step2 raw38610step2Labels := by
      have ha : raw38610step2 = raw38610step1 := by apply Matrix.ext; unfold raw38610step2 raw38610step1; decide +kernel
      have hl : raw38610step1Labels = labelEmbedding4 ∘ raw38610step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38610step1 raw38610step1Labels raw38610step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3250 node3250Labels := by rfl

def raw38611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38611Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38611step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38611step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38611 raw38611Labels = mixedMoment B node1108 node1108Labels := by
  calc
    mixedMoment B raw38611 raw38611Labels = mixedMoment B raw38611step0 raw38611step0Labels := by
      have ha : raw38611step0 = raw38611 := by apply Matrix.ext; unfold raw38611step0 raw38611; decide +kernel
      have hl : raw38611Labels = labelEmbedding2 ∘ raw38611step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38611 raw38611Labels raw38611step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1108 node1108Labels := by rfl

def raw38612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38612Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38612step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw38612step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38612step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw38612step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38612step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw38612step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38612 raw38612Labels = mixedMoment B node3251 node3251Labels := by
  calc
    mixedMoment B raw38612 raw38612Labels = mixedMoment B raw38612step0 raw38612step0Labels := by
      have ha : raw38612step0 = (fun i j => raw38612 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38612step0 raw38612; decide +kernel
      have hl : raw38612step0Labels = raw38612Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38612 raw38612Labels permutation152 permutation7
    mixedMoment B raw38612step0 raw38612step0Labels = mixedMoment B raw38612step1 raw38612step1Labels := by
      have ha : raw38612step1 = -raw38612step0 := by apply Matrix.ext; change ∀ i j, raw38612step1 i j = -(raw38612step0 i j); unfold raw38612step1 raw38612step0; decide +kernel
      have hl : raw38612step1Labels = raw38612step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38612step1 raw38612step1Labels = mixedMoment B raw38612step2 raw38612step2Labels := by
      have ha : raw38612step2 = raw38612step1 := by apply Matrix.ext; unfold raw38612step2 raw38612step1; decide +kernel
      have hl : raw38612step1Labels = labelEmbedding4 ∘ raw38612step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38612step1 raw38612step1Labels raw38612step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3251 node3251Labels := by rfl

def raw38613 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw38613Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw38613step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38613 raw38613Labels = mixedMoment B node1109 node1109Labels := by
  calc
    mixedMoment B raw38613 raw38613Labels = mixedMoment B raw38613step0 raw38613step0Labels := by
      have ha : raw38613step0 = raw38613 := by apply Matrix.ext; unfold raw38613step0 raw38613; decide +kernel
      have hl : raw38613Labels = labelEmbedding2 ∘ raw38613step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38613 raw38613Labels raw38613step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1109 node1109Labels := by rfl

def raw38614 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw38614Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw38614step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw38614step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38614 raw38614Labels = mixedMoment B node1849 node1849Labels := by
  calc
    mixedMoment B raw38614 raw38614Labels = mixedMoment B raw38614step0 raw38614step0Labels := by
      have ha : raw38614step0 = (fun i j => raw38614 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38614step0 raw38614; decide +kernel
      have hl : raw38614step0Labels = raw38614Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38614 raw38614Labels permutation151 permutation7
    mixedMoment B raw38614step0 raw38614step0Labels = mixedMoment B raw38614step1 raw38614step1Labels := by
      have ha : raw38614step1 = raw38614step0 := by apply Matrix.ext; unfold raw38614step1 raw38614step0; decide +kernel
      have hl : raw38614step0Labels = labelEmbedding4 ∘ raw38614step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38614step0 raw38614step0Labels raw38614step1Labels labelEmbedding4 hl
    _ = mixedMoment B node1849 node1849Labels := by rfl

def raw38615 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw38615Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw38615step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38615 raw38615Labels = mixedMoment B node1110 node1110Labels := by
  calc
    mixedMoment B raw38615 raw38615Labels = mixedMoment B raw38615step0 raw38615step0Labels := by
      have ha : raw38615step0 = raw38615 := by apply Matrix.ext; unfold raw38615step0 raw38615; decide +kernel
      have hl : raw38615Labels = labelEmbedding2 ∘ raw38615step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38615 raw38615Labels raw38615step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1110 node1110Labels := by rfl

def raw38616 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw38616Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-2, -1, 3]]
def raw38616step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, 1, -3]]
def raw38616step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38616step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, 1, -3]]
def raw38616step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38616 raw38616Labels = mixedMoment B node3252 node3252Labels := by
  calc
    mixedMoment B raw38616 raw38616Labels = mixedMoment B raw38616step0 raw38616step0Labels := by
      have ha : raw38616step0 = (fun i j => raw38616 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38616step0 raw38616; decide +kernel
      have hl : raw38616step0Labels = raw38616Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38616 raw38616Labels permutation32 permutation7
    mixedMoment B raw38616step0 raw38616step0Labels = mixedMoment B raw38616step1 raw38616step1Labels := by
      have ha : raw38616step1 = -raw38616step0 := by apply Matrix.ext; change ∀ i j, raw38616step1 i j = -(raw38616step0 i j); unfold raw38616step1 raw38616step0; decide +kernel
      have hl : raw38616step1Labels = raw38616step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38616step1 raw38616step1Labels = mixedMoment B raw38616step2 raw38616step2Labels := by
      have ha : raw38616step2 = raw38616step1 := by apply Matrix.ext; unfold raw38616step2 raw38616step1; decide +kernel
      have hl : raw38616step1Labels = labelEmbedding4 ∘ raw38616step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38616step1 raw38616step1Labels raw38616step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3252 node3252Labels := by rfl

def raw38617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38617Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38617step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38617step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38617 raw38617Labels = mixedMoment B node1122 node1122Labels := by
  calc
    mixedMoment B raw38617 raw38617Labels = mixedMoment B raw38617step0 raw38617step0Labels := by
      have ha : raw38617step0 = raw38617 := by apply Matrix.ext; unfold raw38617step0 raw38617; decide +kernel
      have hl : raw38617Labels = labelEmbedding2 ∘ raw38617step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38617 raw38617Labels raw38617step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1122 node1122Labels := by rfl

def raw38618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38618Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw38618step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38618step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38618step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38618step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38618step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38618 raw38618Labels = mixedMoment B node3253 node3253Labels := by
  calc
    mixedMoment B raw38618 raw38618Labels = mixedMoment B raw38618step0 raw38618step0Labels := by
      have ha : raw38618step0 = (fun i j => raw38618 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38618step0 raw38618; decide +kernel
      have hl : raw38618step0Labels = raw38618Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38618 raw38618Labels permutation152 permutation7
    mixedMoment B raw38618step0 raw38618step0Labels = mixedMoment B raw38618step1 raw38618step1Labels := by
      have ha : raw38618step1 = -raw38618step0 := by apply Matrix.ext; change ∀ i j, raw38618step1 i j = -(raw38618step0 i j); unfold raw38618step1 raw38618step0; decide +kernel
      have hl : raw38618step1Labels = raw38618step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38618step1 raw38618step1Labels = mixedMoment B raw38618step2 raw38618step2Labels := by
      have ha : raw38618step2 = raw38618step1 := by apply Matrix.ext; unfold raw38618step2 raw38618step1; decide +kernel
      have hl : raw38618step1Labels = labelEmbedding4 ∘ raw38618step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38618step1 raw38618step1Labels raw38618step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3253 node3253Labels := by rfl

def raw38619 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw38619Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw38619step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38619 raw38619Labels = mixedMoment B node1123 node1123Labels := by
  calc
    mixedMoment B raw38619 raw38619Labels = mixedMoment B raw38619step0 raw38619step0Labels := by
      have ha : raw38619step0 = raw38619 := by apply Matrix.ext; unfold raw38619step0 raw38619; decide +kernel
      have hl : raw38619Labels = labelEmbedding2 ∘ raw38619step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38619 raw38619Labels raw38619step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1123 node1123Labels := by rfl

def raw38620 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw38620Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 2, -4]]
def raw38620step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 2, -4]]
def raw38620step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38620 raw38620Labels = mixedMoment B node1937 node1937Labels := by
  calc
    mixedMoment B raw38620 raw38620Labels = mixedMoment B raw38620step0 raw38620step0Labels := by
      have ha : raw38620step0 = (fun i j => raw38620 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38620step0 raw38620; decide +kernel
      have hl : raw38620step0Labels = raw38620Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38620 raw38620Labels permutation151 permutation7
    mixedMoment B raw38620step0 raw38620step0Labels = mixedMoment B raw38620step1 raw38620step1Labels := by
      have ha : raw38620step1 = raw38620step0 := by apply Matrix.ext; unfold raw38620step1 raw38620step0; decide +kernel
      have hl : raw38620step0Labels = labelEmbedding4 ∘ raw38620step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38620step0 raw38620step0Labels raw38620step1Labels labelEmbedding4 hl
    _ = mixedMoment B node1937 node1937Labels := by rfl

def raw38621 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw38621Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw38621step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38621 raw38621Labels = mixedMoment B node1124 node1124Labels := by
  calc
    mixedMoment B raw38621 raw38621Labels = mixedMoment B raw38621step0 raw38621step0Labels := by
      have ha : raw38621step0 = raw38621 := by apply Matrix.ext; unfold raw38621step0 raw38621; decide +kernel
      have hl : raw38621Labels = labelEmbedding2 ∘ raw38621step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38621 raw38621Labels raw38621step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1124 node1124Labels := by rfl

def raw38622 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw38622Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![1, -2, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw38622step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![2, 0, -2]]
def raw38622step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38622step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![2, 0, -2]]
def raw38622step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38622 raw38622Labels = mixedMoment B node3254 node3254Labels := by
  calc
    mixedMoment B raw38622 raw38622Labels = mixedMoment B raw38622step0 raw38622step0Labels := by
      have ha : raw38622step0 = (fun i j => raw38622 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38622step0 raw38622; decide +kernel
      have hl : raw38622step0Labels = raw38622Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38622 raw38622Labels permutation32 permutation7
    mixedMoment B raw38622step0 raw38622step0Labels = mixedMoment B raw38622step1 raw38622step1Labels := by
      have ha : raw38622step1 = -raw38622step0 := by apply Matrix.ext; change ∀ i j, raw38622step1 i j = -(raw38622step0 i j); unfold raw38622step1 raw38622step0; decide +kernel
      have hl : raw38622step1Labels = raw38622step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38622step1 raw38622step1Labels = mixedMoment B raw38622step2 raw38622step2Labels := by
      have ha : raw38622step2 = raw38622step1 := by apply Matrix.ext; unfold raw38622step2 raw38622step1; decide +kernel
      have hl : raw38622step1Labels = labelEmbedding4 ∘ raw38622step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38622step1 raw38622step1Labels raw38622step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3254 node3254Labels := by rfl

def raw38623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38623Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38623step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38623 raw38623Labels = mixedMoment B node1126 node1126Labels := by
  calc
    mixedMoment B raw38623 raw38623Labels = mixedMoment B raw38623step0 raw38623step0Labels := by
      have ha : raw38623step0 = raw38623 := by apply Matrix.ext; unfold raw38623step0 raw38623; decide +kernel
      have hl : raw38623Labels = labelEmbedding2 ∘ raw38623step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38623 raw38623Labels raw38623step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1126 node1126Labels := by rfl

def raw38624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38624Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38624step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw38624step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38624step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38624step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38624step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38624step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38624 raw38624Labels = mixedMoment B node3256 node3256Labels := by
  calc
    mixedMoment B raw38624 raw38624Labels = mixedMoment B raw38624step0 raw38624step0Labels := by
      have ha : raw38624step0 = (fun i j => raw38624 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38624step0 raw38624; decide +kernel
      have hl : raw38624step0Labels = raw38624Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38624 raw38624Labels permutation152 permutation7
    mixedMoment B raw38624step0 raw38624step0Labels = mixedMoment B raw38624step1 raw38624step1Labels := by
      have ha : raw38624step1 = -raw38624step0 := by apply Matrix.ext; change ∀ i j, raw38624step1 i j = -(raw38624step0 i j); unfold raw38624step1 raw38624step0; decide +kernel
      have hl : raw38624step1Labels = raw38624step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38624step1 raw38624step1Labels = mixedMoment B raw38624step2 raw38624step2Labels := by
      have ha : raw38624step2 = raw38624step1 := by apply Matrix.ext; unfold raw38624step2 raw38624step1; decide +kernel
      have hl : raw38624step1Labels = labelEmbedding4 ∘ raw38624step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38624step1 raw38624step1Labels raw38624step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3256 node3256Labels := by rfl

def raw38625 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38625Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38625step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38625 raw38625Labels = mixedMoment B node1128 node1128Labels := by
  calc
    mixedMoment B raw38625 raw38625Labels = mixedMoment B raw38625step0 raw38625step0Labels := by
      have ha : raw38625step0 = raw38625 := by apply Matrix.ext; unfold raw38625step0 raw38625; decide +kernel
      have hl : raw38625Labels = labelEmbedding2 ∘ raw38625step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38625 raw38625Labels raw38625step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1128 node1128Labels := by rfl

def raw38626 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38626Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw38626step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw38626step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38626 raw38626Labels = mixedMoment B node2184 node2184Labels := by
  calc
    mixedMoment B raw38626 raw38626Labels = mixedMoment B raw38626step0 raw38626step0Labels := by
      have ha : raw38626step0 = (fun i j => raw38626 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38626step0 raw38626; decide +kernel
      have hl : raw38626step0Labels = raw38626Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38626 raw38626Labels permutation145 permutation7
    mixedMoment B raw38626step0 raw38626step0Labels = mixedMoment B raw38626step1 raw38626step1Labels := by
      have ha : raw38626step1 = raw38626step0 := by apply Matrix.ext; unfold raw38626step1 raw38626step0; decide +kernel
      have hl : raw38626step0Labels = labelEmbedding4 ∘ raw38626step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38626step0 raw38626step0Labels raw38626step1Labels labelEmbedding4 hl
    _ = mixedMoment B node2184 node2184Labels := by rfl

def raw38627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38627Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38627step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38627step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38627 raw38627Labels = mixedMoment B node1129 node1129Labels := by
  calc
    mixedMoment B raw38627 raw38627Labels = mixedMoment B raw38627step0 raw38627step0Labels := by
      have ha : raw38627step0 = raw38627 := by apply Matrix.ext; unfold raw38627step0 raw38627; decide +kernel
      have hl : raw38627Labels = labelEmbedding2 ∘ raw38627step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38627 raw38627Labels raw38627step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1129 node1129Labels := by rfl

def raw38628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38628Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw38628step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38628step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38628step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38628step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38628step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38628 raw38628Labels = mixedMoment B node3263 node3263Labels := by
  calc
    mixedMoment B raw38628 raw38628Labels = mixedMoment B raw38628step0 raw38628step0Labels := by
      have ha : raw38628step0 = (fun i j => raw38628 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38628step0 raw38628; decide +kernel
      have hl : raw38628step0Labels = raw38628Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38628 raw38628Labels permutation152 permutation7
    mixedMoment B raw38628step0 raw38628step0Labels = mixedMoment B raw38628step1 raw38628step1Labels := by
      have ha : raw38628step1 = -raw38628step0 := by apply Matrix.ext; change ∀ i j, raw38628step1 i j = -(raw38628step0 i j); unfold raw38628step1 raw38628step0; decide +kernel
      have hl : raw38628step1Labels = raw38628step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38628step1 raw38628step1Labels = mixedMoment B raw38628step2 raw38628step2Labels := by
      have ha : raw38628step2 = raw38628step1 := by apply Matrix.ext; unfold raw38628step2 raw38628step1; decide +kernel
      have hl : raw38628step1Labels = labelEmbedding4 ∘ raw38628step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38628step1 raw38628step1Labels raw38628step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3263 node3263Labels := by rfl

def raw38629 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38629Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38629step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38629 raw38629Labels = mixedMoment B node1131 node1131Labels := by
  calc
    mixedMoment B raw38629 raw38629Labels = mixedMoment B raw38629step0 raw38629step0Labels := by
      have ha : raw38629step0 = raw38629 := by apply Matrix.ext; unfold raw38629step0 raw38629; decide +kernel
      have hl : raw38629Labels = labelEmbedding2 ∘ raw38629step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38629 raw38629Labels raw38629step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1131 node1131Labels := by rfl

def raw38630 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38630Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw38630step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw38630step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38630step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw38630step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38630 raw38630Labels = mixedMoment B node3264 node3264Labels := by
  calc
    mixedMoment B raw38630 raw38630Labels = mixedMoment B raw38630step0 raw38630step0Labels := by
      have ha : raw38630step0 = (fun i j => raw38630 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38630step0 raw38630; decide +kernel
      have hl : raw38630step0Labels = raw38630Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38630 raw38630Labels permutation32 permutation7
    mixedMoment B raw38630step0 raw38630step0Labels = mixedMoment B raw38630step1 raw38630step1Labels := by
      have ha : raw38630step1 = -raw38630step0 := by apply Matrix.ext; change ∀ i j, raw38630step1 i j = -(raw38630step0 i j); unfold raw38630step1 raw38630step0; decide +kernel
      have hl : raw38630step1Labels = raw38630step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38630step1 raw38630step1Labels = mixedMoment B raw38630step2 raw38630step2Labels := by
      have ha : raw38630step2 = raw38630step1 := by apply Matrix.ext; unfold raw38630step2 raw38630step1; decide +kernel
      have hl : raw38630step1Labels = labelEmbedding4 ∘ raw38630step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38630step1 raw38630step1Labels raw38630step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3264 node3264Labels := by rfl

def raw38631 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38631Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38631step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38631 raw38631Labels = mixedMoment B node1134 node1134Labels := by
  calc
    mixedMoment B raw38631 raw38631Labels = mixedMoment B raw38631step0 raw38631step0Labels := by
      have ha : raw38631step0 = raw38631 := by apply Matrix.ext; unfold raw38631step0 raw38631; decide +kernel
      have hl : raw38631Labels = labelEmbedding2 ∘ raw38631step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38631 raw38631Labels raw38631step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1134 node1134Labels := by rfl

def raw38632 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38632Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw38632step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38632step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw38632step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38632step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw38632step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38632 raw38632Labels = mixedMoment B node3265 node3265Labels := by
  calc
    mixedMoment B raw38632 raw38632Labels = mixedMoment B raw38632step0 raw38632step0Labels := by
      have ha : raw38632step0 = (fun i j => raw38632 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38632step0 raw38632; decide +kernel
      have hl : raw38632step0Labels = raw38632Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38632 raw38632Labels permutation32 permutation7
    mixedMoment B raw38632step0 raw38632step0Labels = mixedMoment B raw38632step1 raw38632step1Labels := by
      have ha : raw38632step1 = -raw38632step0 := by apply Matrix.ext; change ∀ i j, raw38632step1 i j = -(raw38632step0 i j); unfold raw38632step1 raw38632step0; decide +kernel
      have hl : raw38632step1Labels = raw38632step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38632step1 raw38632step1Labels = mixedMoment B raw38632step2 raw38632step2Labels := by
      have ha : raw38632step2 = raw38632step1 := by apply Matrix.ext; unfold raw38632step2 raw38632step1; decide +kernel
      have hl : raw38632step1Labels = labelEmbedding4 ∘ raw38632step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38632step1 raw38632step1Labels raw38632step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3265 node3265Labels := by rfl

def raw38633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38633Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38633step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38633step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38633 raw38633Labels = mixedMoment B node1135 node1135Labels := by
  calc
    mixedMoment B raw38633 raw38633Labels = mixedMoment B raw38633step0 raw38633step0Labels := by
      have ha : raw38633step0 = raw38633 := by apply Matrix.ext; unfold raw38633step0 raw38633; decide +kernel
      have hl : raw38633Labels = labelEmbedding2 ∘ raw38633step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38633 raw38633Labels raw38633step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1135 node1135Labels := by rfl

def raw38634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38634Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38634step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw38634step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38634step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38634step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38634step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38634step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38634 raw38634Labels = mixedMoment B node3269 node3269Labels := by
  calc
    mixedMoment B raw38634 raw38634Labels = mixedMoment B raw38634step0 raw38634step0Labels := by
      have ha : raw38634step0 = (fun i j => raw38634 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38634step0 raw38634; decide +kernel
      have hl : raw38634step0Labels = raw38634Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38634 raw38634Labels permutation170 permutation7
    mixedMoment B raw38634step0 raw38634step0Labels = mixedMoment B raw38634step1 raw38634step1Labels := by
      have ha : raw38634step1 = -raw38634step0 := by apply Matrix.ext; change ∀ i j, raw38634step1 i j = -(raw38634step0 i j); unfold raw38634step1 raw38634step0; decide +kernel
      have hl : raw38634step1Labels = raw38634step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38634step1 raw38634step1Labels = mixedMoment B raw38634step2 raw38634step2Labels := by
      have ha : raw38634step2 = raw38634step1 := by apply Matrix.ext; unfold raw38634step2 raw38634step1; decide +kernel
      have hl : raw38634step1Labels = labelEmbedding4 ∘ raw38634step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38634step1 raw38634step1Labels raw38634step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3269 node3269Labels := by rfl

def raw38635 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38635Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38635step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38635 raw38635Labels = mixedMoment B node1136 node1136Labels := by
  calc
    mixedMoment B raw38635 raw38635Labels = mixedMoment B raw38635step0 raw38635step0Labels := by
      have ha : raw38635step0 = raw38635 := by apply Matrix.ext; unfold raw38635step0 raw38635; decide +kernel
      have hl : raw38635Labels = labelEmbedding2 ∘ raw38635step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38635 raw38635Labels raw38635step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1136 node1136Labels := by rfl

def raw38636 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38636Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw38636step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38636step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw38636step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38636step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw38636step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38636 raw38636Labels = mixedMoment B node3273 node3273Labels := by
  calc
    mixedMoment B raw38636 raw38636Labels = mixedMoment B raw38636step0 raw38636step0Labels := by
      have ha : raw38636step0 = (fun i j => raw38636 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38636step0 raw38636; decide +kernel
      have hl : raw38636step0Labels = raw38636Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38636 raw38636Labels permutation32 permutation7
    mixedMoment B raw38636step0 raw38636step0Labels = mixedMoment B raw38636step1 raw38636step1Labels := by
      have ha : raw38636step1 = -raw38636step0 := by apply Matrix.ext; change ∀ i j, raw38636step1 i j = -(raw38636step0 i j); unfold raw38636step1 raw38636step0; decide +kernel
      have hl : raw38636step1Labels = raw38636step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38636step1 raw38636step1Labels = mixedMoment B raw38636step2 raw38636step2Labels := by
      have ha : raw38636step2 = raw38636step1 := by apply Matrix.ext; unfold raw38636step2 raw38636step1; decide +kernel
      have hl : raw38636step1Labels = labelEmbedding4 ∘ raw38636step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38636step1 raw38636step1Labels raw38636step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3273 node3273Labels := by rfl

def raw38637 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38637Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38637step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38637 raw38637Labels = mixedMoment B node1138 node1138Labels := by
  calc
    mixedMoment B raw38637 raw38637Labels = mixedMoment B raw38637step0 raw38637step0Labels := by
      have ha : raw38637step0 = raw38637 := by apply Matrix.ext; unfold raw38637step0 raw38637; decide +kernel
      have hl : raw38637Labels = labelEmbedding2 ∘ raw38637step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38637 raw38637Labels raw38637step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1138 node1138Labels := by rfl

def raw38638 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38638Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw38638step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw38638step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38638step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw38638step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38638 raw38638Labels = mixedMoment B node3270 node3270Labels := by
  calc
    mixedMoment B raw38638 raw38638Labels = mixedMoment B raw38638step0 raw38638step0Labels := by
      have ha : raw38638step0 = (fun i j => raw38638 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38638step0 raw38638; decide +kernel
      have hl : raw38638step0Labels = raw38638Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38638 raw38638Labels permutation34 permutation7
    mixedMoment B raw38638step0 raw38638step0Labels = mixedMoment B raw38638step1 raw38638step1Labels := by
      have ha : raw38638step1 = -raw38638step0 := by apply Matrix.ext; change ∀ i j, raw38638step1 i j = -(raw38638step0 i j); unfold raw38638step1 raw38638step0; decide +kernel
      have hl : raw38638step1Labels = raw38638step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38638step1 raw38638step1Labels = mixedMoment B raw38638step2 raw38638step2Labels := by
      have ha : raw38638step2 = raw38638step1 := by apply Matrix.ext; unfold raw38638step2 raw38638step1; decide +kernel
      have hl : raw38638step1Labels = labelEmbedding4 ∘ raw38638step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38638step1 raw38638step1Labels raw38638step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3270 node3270Labels := by rfl

def raw38639 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38639Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38639step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38639 raw38639Labels = mixedMoment B node1139 node1139Labels := by
  calc
    mixedMoment B raw38639 raw38639Labels = mixedMoment B raw38639step0 raw38639step0Labels := by
      have ha : raw38639step0 = raw38639 := by apply Matrix.ext; unfold raw38639step0 raw38639; decide +kernel
      have hl : raw38639Labels = labelEmbedding2 ∘ raw38639step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38639 raw38639Labels raw38639step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1139 node1139Labels := by rfl

def raw38640 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38640Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw38640step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw38640step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38640step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw38640step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38640 raw38640Labels = mixedMoment B node3274 node3274Labels := by
  calc
    mixedMoment B raw38640 raw38640Labels = mixedMoment B raw38640step0 raw38640step0Labels := by
      have ha : raw38640step0 = (fun i j => raw38640 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38640step0 raw38640; decide +kernel
      have hl : raw38640step0Labels = raw38640Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38640 raw38640Labels permutation32 permutation7
    mixedMoment B raw38640step0 raw38640step0Labels = mixedMoment B raw38640step1 raw38640step1Labels := by
      have ha : raw38640step1 = -raw38640step0 := by apply Matrix.ext; change ∀ i j, raw38640step1 i j = -(raw38640step0 i j); unfold raw38640step1 raw38640step0; decide +kernel
      have hl : raw38640step1Labels = raw38640step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38640step1 raw38640step1Labels = mixedMoment B raw38640step2 raw38640step2Labels := by
      have ha : raw38640step2 = raw38640step1 := by apply Matrix.ext; unfold raw38640step2 raw38640step1; decide +kernel
      have hl : raw38640step1Labels = labelEmbedding4 ∘ raw38640step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38640step1 raw38640step1Labels raw38640step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3274 node3274Labels := by rfl

def raw38641 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw38641Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38641step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw38641step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38641 raw38641Labels = mixedMoment B node1140 node1140Labels := by
  calc
    mixedMoment B raw38641 raw38641Labels = mixedMoment B raw38641step0 raw38641step0Labels := by
      have ha : raw38641step0 = raw38641 := by apply Matrix.ext; unfold raw38641step0 raw38641; decide +kernel
      have hl : raw38641Labels = labelEmbedding2 ∘ raw38641step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38641 raw38641Labels raw38641step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1140 node1140Labels := by rfl

def raw38642 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw38642Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38642step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![2, 2, -4]]
def raw38642step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38642step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![2, 2, -4]]
def raw38642step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38642 raw38642Labels = mixedMoment B node3275 node3275Labels := by
  calc
    mixedMoment B raw38642 raw38642Labels = mixedMoment B raw38642step0 raw38642step0Labels := by
      have ha : raw38642step0 = (fun i j => raw38642 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38642step0 raw38642; decide +kernel
      have hl : raw38642step0Labels = raw38642Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38642 raw38642Labels permutation31 permutation7
    mixedMoment B raw38642step0 raw38642step0Labels = mixedMoment B raw38642step1 raw38642step1Labels := by
      have ha : raw38642step1 = raw38642step0 := by apply Matrix.ext; unfold raw38642step1 raw38642step0; decide +kernel
      have hl : raw38642step0Labels = labelEmbedding4 ∘ raw38642step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38642step0 raw38642step0Labels raw38642step1Labels labelEmbedding4 hl
    _ = mixedMoment B node3275 node3275Labels := by rfl

def raw38643 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw38643Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38643step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw38643step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38643 raw38643Labels = mixedMoment B node1143 node1143Labels := by
  calc
    mixedMoment B raw38643 raw38643Labels = mixedMoment B raw38643step0 raw38643step0Labels := by
      have ha : raw38643step0 = raw38643 := by apply Matrix.ext; unfold raw38643step0 raw38643; decide +kernel
      have hl : raw38643Labels = labelEmbedding2 ∘ raw38643step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38643 raw38643Labels raw38643step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1143 node1143Labels := by rfl

def raw38644 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw38644Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38644step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![2, 2, -4]]
def raw38644step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38644step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![2, 2, -4]]
def raw38644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38644 raw38644Labels = mixedMoment B node2167 node2167Labels := by
  calc
    mixedMoment B raw38644 raw38644Labels = mixedMoment B raw38644step0 raw38644step0Labels := by
      have ha : raw38644step0 = (fun i j => raw38644 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38644step0 raw38644; decide +kernel
      have hl : raw38644step0Labels = raw38644Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38644 raw38644Labels permutation31 permutation7
    mixedMoment B raw38644step0 raw38644step0Labels = mixedMoment B raw38644step1 raw38644step1Labels := by
      have ha : raw38644step1 = raw38644step0 := by apply Matrix.ext; unfold raw38644step1 raw38644step0; decide +kernel
      have hl : raw38644step0Labels = labelEmbedding4 ∘ raw38644step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38644step0 raw38644step0Labels raw38644step1Labels labelEmbedding4 hl
    _ = mixedMoment B node2167 node2167Labels := by rfl

def raw38645 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw38645Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38645step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw38645step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38645 raw38645Labels = mixedMoment B node1144 node1144Labels := by
  calc
    mixedMoment B raw38645 raw38645Labels = mixedMoment B raw38645step0 raw38645step0Labels := by
      have ha : raw38645step0 = raw38645 := by apply Matrix.ext; unfold raw38645step0 raw38645; decide +kernel
      have hl : raw38645Labels = labelEmbedding2 ∘ raw38645step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38645 raw38645Labels raw38645step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1144 node1144Labels := by rfl

def raw38646 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw38646Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38646step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw38646step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 1, -2], ![2, 1, -3]]
def raw38646step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38646step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 1, -2], ![2, 1, -3]]
def raw38646step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38646 raw38646Labels = mixedMoment B node3276 node3276Labels := by
  calc
    mixedMoment B raw38646 raw38646Labels = mixedMoment B raw38646step0 raw38646step0Labels := by
      have ha : raw38646step0 = (fun i j => raw38646 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38646step0 raw38646; decide +kernel
      have hl : raw38646step0Labels = raw38646Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38646 raw38646Labels permutation8 permutation7
    mixedMoment B raw38646step0 raw38646step0Labels = mixedMoment B raw38646step1 raw38646step1Labels := by
      have ha : raw38646step1 = -raw38646step0 := by apply Matrix.ext; change ∀ i j, raw38646step1 i j = -(raw38646step0 i j); unfold raw38646step1 raw38646step0; decide +kernel
      have hl : raw38646step1Labels = raw38646step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38646step1 raw38646step1Labels = mixedMoment B raw38646step2 raw38646step2Labels := by
      have ha : raw38646step2 = raw38646step1 := by apply Matrix.ext; unfold raw38646step2 raw38646step1; decide +kernel
      have hl : raw38646step1Labels = labelEmbedding4 ∘ raw38646step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38646step1 raw38646step1Labels raw38646step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3276 node3276Labels := by rfl

def raw38647 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw38647Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38647step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw38647step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38647 raw38647Labels = mixedMoment B node1145 node1145Labels := by
  calc
    mixedMoment B raw38647 raw38647Labels = mixedMoment B raw38647step0 raw38647step0Labels := by
      have ha : raw38647step0 = raw38647 := by apply Matrix.ext; unfold raw38647step0 raw38647; decide +kernel
      have hl : raw38647Labels = labelEmbedding2 ∘ raw38647step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38647 raw38647Labels raw38647step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1145 node1145Labels := by rfl

def raw38648 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw38648Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38648step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw38648step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38648step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 2, -3], ![2, 0, -2]]
def raw38648step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38648step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 2, -3], ![2, 0, -2]]
def raw38648step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38648 raw38648Labels = mixedMoment B node3277 node3277Labels := by
  calc
    mixedMoment B raw38648 raw38648Labels = mixedMoment B raw38648step0 raw38648step0Labels := by
      have ha : raw38648step0 = (fun i j => raw38648 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38648step0 raw38648; decide +kernel
      have hl : raw38648step0Labels = raw38648Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38648 raw38648Labels permutation9 permutation7
    mixedMoment B raw38648step0 raw38648step0Labels = mixedMoment B raw38648step1 raw38648step1Labels := by
      have ha : raw38648step1 = -raw38648step0 := by apply Matrix.ext; change ∀ i j, raw38648step1 i j = -(raw38648step0 i j); unfold raw38648step1 raw38648step0; decide +kernel
      have hl : raw38648step1Labels = raw38648step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38648step1 raw38648step1Labels = mixedMoment B raw38648step2 raw38648step2Labels := by
      have ha : raw38648step2 = raw38648step1 := by apply Matrix.ext; unfold raw38648step2 raw38648step1; decide +kernel
      have hl : raw38648step1Labels = labelEmbedding4 ∘ raw38648step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38648step1 raw38648step1Labels raw38648step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3277 node3277Labels := by rfl

def raw38649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38649Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38649step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38649 raw38649Labels = mixedMoment B node1187 node1187Labels := by
  calc
    mixedMoment B raw38649 raw38649Labels = mixedMoment B raw38649step0 raw38649step0Labels := by
      have ha : raw38649step0 = raw38649 := by apply Matrix.ext; unfold raw38649step0 raw38649; decide +kernel
      have hl : raw38649Labels = labelEmbedding2 ∘ raw38649step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38649 raw38649Labels raw38649step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1187 node1187Labels := by rfl

def raw38650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38650Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw38650step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38650step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38650step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38650step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38650step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38650 raw38650Labels = mixedMoment B node3244 node3244Labels := by
  calc
    mixedMoment B raw38650 raw38650Labels = mixedMoment B raw38650step0 raw38650step0Labels := by
      have ha : raw38650step0 = (fun i j => raw38650 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38650step0 raw38650; decide +kernel
      have hl : raw38650step0Labels = raw38650Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38650 raw38650Labels permutation152 permutation7
    mixedMoment B raw38650step0 raw38650step0Labels = mixedMoment B raw38650step1 raw38650step1Labels := by
      have ha : raw38650step1 = -raw38650step0 := by apply Matrix.ext; change ∀ i j, raw38650step1 i j = -(raw38650step0 i j); unfold raw38650step1 raw38650step0; decide +kernel
      have hl : raw38650step1Labels = raw38650step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38650step1 raw38650step1Labels = mixedMoment B raw38650step2 raw38650step2Labels := by
      have ha : raw38650step2 = raw38650step1 := by apply Matrix.ext; unfold raw38650step2 raw38650step1; decide +kernel
      have hl : raw38650step1Labels = labelEmbedding4 ∘ raw38650step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38650step1 raw38650step1Labels raw38650step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3244 node3244Labels := by rfl

def raw38651 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38651Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38651step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38651 raw38651Labels = mixedMoment B node1188 node1188Labels := by
  calc
    mixedMoment B raw38651 raw38651Labels = mixedMoment B raw38651step0 raw38651step0Labels := by
      have ha : raw38651step0 = raw38651 := by apply Matrix.ext; unfold raw38651step0 raw38651; decide +kernel
      have hl : raw38651Labels = labelEmbedding2 ∘ raw38651step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38651 raw38651Labels raw38651step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1188 node1188Labels := by rfl

def raw38652 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38652Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw38652step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38652step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38652step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38652step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38652 raw38652Labels = mixedMoment B node3245 node3245Labels := by
  calc
    mixedMoment B raw38652 raw38652Labels = mixedMoment B raw38652step0 raw38652step0Labels := by
      have ha : raw38652step0 = (fun i j => raw38652 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38652step0 raw38652; decide +kernel
      have hl : raw38652step0Labels = raw38652Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38652 raw38652Labels permutation32 permutation7
    mixedMoment B raw38652step0 raw38652step0Labels = mixedMoment B raw38652step1 raw38652step1Labels := by
      have ha : raw38652step1 = -raw38652step0 := by apply Matrix.ext; change ∀ i j, raw38652step1 i j = -(raw38652step0 i j); unfold raw38652step1 raw38652step0; decide +kernel
      have hl : raw38652step1Labels = raw38652step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38652step1 raw38652step1Labels = mixedMoment B raw38652step2 raw38652step2Labels := by
      have ha : raw38652step2 = raw38652step1 := by apply Matrix.ext; unfold raw38652step2 raw38652step1; decide +kernel
      have hl : raw38652step1Labels = labelEmbedding4 ∘ raw38652step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38652step1 raw38652step1Labels raw38652step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3245 node3245Labels := by rfl

def raw38653 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw38653Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38653step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw38653step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38653 raw38653Labels = mixedMoment B node1190 node1190Labels := by
  calc
    mixedMoment B raw38653 raw38653Labels = mixedMoment B raw38653step0 raw38653step0Labels := by
      have ha : raw38653step0 = raw38653 := by apply Matrix.ext; unfold raw38653step0 raw38653; decide +kernel
      have hl : raw38653Labels = labelEmbedding2 ∘ raw38653step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38653 raw38653Labels raw38653step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1190 node1190Labels := by rfl

def raw38654 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw38654Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38654step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![2, -2, 0], ![2, 2, -4]]
def raw38654step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38654step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![2, -2, 0], ![2, 2, -4]]
def raw38654step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38654 raw38654Labels = mixedMoment B node1952 node1952Labels := by
  calc
    mixedMoment B raw38654 raw38654Labels = mixedMoment B raw38654step0 raw38654step0Labels := by
      have ha : raw38654step0 = (fun i j => raw38654 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38654step0 raw38654; decide +kernel
      have hl : raw38654step0Labels = raw38654Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38654 raw38654Labels permutation31 permutation7
    mixedMoment B raw38654step0 raw38654step0Labels = mixedMoment B raw38654step1 raw38654step1Labels := by
      have ha : raw38654step1 = raw38654step0 := by apply Matrix.ext; unfold raw38654step1 raw38654step0; decide +kernel
      have hl : raw38654step0Labels = labelEmbedding4 ∘ raw38654step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38654step0 raw38654step0Labels raw38654step1Labels labelEmbedding4 hl
    _ = mixedMoment B node1952 node1952Labels := by rfl

def raw38655 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw38655Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38655step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw38655step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38655 raw38655Labels = mixedMoment B node1193 node1193Labels := by
  calc
    mixedMoment B raw38655 raw38655Labels = mixedMoment B raw38655step0 raw38655step0Labels := by
      have ha : raw38655step0 = raw38655 := by apply Matrix.ext; unfold raw38655step0 raw38655; decide +kernel
      have hl : raw38655Labels = labelEmbedding2 ∘ raw38655step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38655 raw38655Labels raw38655step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1193 node1193Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
