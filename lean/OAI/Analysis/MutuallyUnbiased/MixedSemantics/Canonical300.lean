import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw38400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38400Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38400step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw38400step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38400step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38400step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38400step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38400step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38400 raw38400Labels = mixedMoment B node1554 node1554Labels := by
  calc
    mixedMoment B raw38400 raw38400Labels = mixedMoment B raw38400step0 raw38400step0Labels := by
      have ha : raw38400step0 = (fun i j => raw38400 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38400step0 raw38400; decide +kernel
      have hl : raw38400step0Labels = raw38400Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38400 raw38400Labels permutation158 permutation7
    mixedMoment B raw38400step0 raw38400step0Labels = mixedMoment B raw38400step1 raw38400step1Labels := by
      have ha : raw38400step1 = -raw38400step0 := by apply Matrix.ext; change ∀ i j, raw38400step1 i j = -(raw38400step0 i j); unfold raw38400step1 raw38400step0; decide +kernel
      have hl : raw38400step1Labels = raw38400step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38400step1 raw38400step1Labels = mixedMoment B raw38400step2 raw38400step2Labels := by
      have ha : raw38400step2 = raw38400step1 := by apply Matrix.ext; unfold raw38400step2 raw38400step1; decide +kernel
      have hl : raw38400step1Labels = labelEmbedding4 ∘ raw38400step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38400step1 raw38400step1Labels raw38400step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1554 node1554Labels := by rfl

def raw38401 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw38401Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw38401step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38401 raw38401Labels = mixedMoment B node867 node867Labels := by
  calc
    mixedMoment B raw38401 raw38401Labels = mixedMoment B raw38401step0 raw38401step0Labels := by
      have ha : raw38401step0 = raw38401 := by apply Matrix.ext; unfold raw38401step0 raw38401; decide +kernel
      have hl : raw38401Labels = labelEmbedding2 ∘ raw38401step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38401 raw38401Labels raw38401step0Labels labelEmbedding2 hl
    _ = mixedMoment B node867 node867Labels := by rfl

def raw38402 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw38402Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, -1, 4]]
def raw38402step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw38402step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38402step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw38402step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38402 raw38402Labels = mixedMoment B node1555 node1555Labels := by
  calc
    mixedMoment B raw38402 raw38402Labels = mixedMoment B raw38402step0 raw38402step0Labels := by
      have ha : raw38402step0 = (fun i j => raw38402 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38402step0 raw38402; decide +kernel
      have hl : raw38402step0Labels = raw38402Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38402 raw38402Labels permutation34 permutation7
    mixedMoment B raw38402step0 raw38402step0Labels = mixedMoment B raw38402step1 raw38402step1Labels := by
      have ha : raw38402step1 = -raw38402step0 := by apply Matrix.ext; change ∀ i j, raw38402step1 i j = -(raw38402step0 i j); unfold raw38402step1 raw38402step0; decide +kernel
      have hl : raw38402step1Labels = raw38402step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38402step1 raw38402step1Labels = mixedMoment B raw38402step2 raw38402step2Labels := by
      have ha : raw38402step2 = raw38402step1 := by apply Matrix.ext; unfold raw38402step2 raw38402step1; decide +kernel
      have hl : raw38402step1Labels = labelEmbedding4 ∘ raw38402step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38402step1 raw38402step1Labels raw38402step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1555 node1555Labels := by rfl

def raw38403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38403Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38403step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38403step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38403 raw38403Labels = mixedMoment B node868 node868Labels := by
  calc
    mixedMoment B raw38403 raw38403Labels = mixedMoment B raw38403step0 raw38403step0Labels := by
      have ha : raw38403step0 = raw38403 := by apply Matrix.ext; unfold raw38403step0 raw38403; decide +kernel
      have hl : raw38403Labels = labelEmbedding2 ∘ raw38403step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38403 raw38403Labels raw38403step0Labels labelEmbedding2 hl
    _ = mixedMoment B node868 node868Labels := by rfl

def raw38404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38404Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38404step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw38404step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38404step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw38404step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38404step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw38404step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38404 raw38404Labels = mixedMoment B node1566 node1566Labels := by
  calc
    mixedMoment B raw38404 raw38404Labels = mixedMoment B raw38404step0 raw38404step0Labels := by
      have ha : raw38404step0 = (fun i j => raw38404 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38404step0 raw38404; decide +kernel
      have hl : raw38404step0Labels = raw38404Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38404 raw38404Labels permutation152 permutation7
    mixedMoment B raw38404step0 raw38404step0Labels = mixedMoment B raw38404step1 raw38404step1Labels := by
      have ha : raw38404step1 = -raw38404step0 := by apply Matrix.ext; change ∀ i j, raw38404step1 i j = -(raw38404step0 i j); unfold raw38404step1 raw38404step0; decide +kernel
      have hl : raw38404step1Labels = raw38404step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38404step1 raw38404step1Labels = mixedMoment B raw38404step2 raw38404step2Labels := by
      have ha : raw38404step2 = raw38404step1 := by apply Matrix.ext; unfold raw38404step2 raw38404step1; decide +kernel
      have hl : raw38404step1Labels = labelEmbedding4 ∘ raw38404step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38404step1 raw38404step1Labels raw38404step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1566 node1566Labels := by rfl

def raw38405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38405Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38405step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38405 raw38405Labels = mixedMoment B node869 node869Labels := by
  calc
    mixedMoment B raw38405 raw38405Labels = mixedMoment B raw38405step0 raw38405step0Labels := by
      have ha : raw38405step0 = raw38405 := by apply Matrix.ext; unfold raw38405step0 raw38405; decide +kernel
      have hl : raw38405Labels = labelEmbedding2 ∘ raw38405step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38405 raw38405Labels raw38405step0Labels labelEmbedding2 hl
    _ = mixedMoment B node869 node869Labels := by rfl

def raw38406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38406Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38406step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw38406step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38406step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38406step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38406step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38406step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38406 raw38406Labels = mixedMoment B node1561 node1561Labels := by
  calc
    mixedMoment B raw38406 raw38406Labels = mixedMoment B raw38406step0 raw38406step0Labels := by
      have ha : raw38406step0 = (fun i j => raw38406 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38406step0 raw38406; decide +kernel
      have hl : raw38406step0Labels = raw38406Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38406 raw38406Labels permutation164 permutation7
    mixedMoment B raw38406step0 raw38406step0Labels = mixedMoment B raw38406step1 raw38406step1Labels := by
      have ha : raw38406step1 = -raw38406step0 := by apply Matrix.ext; change ∀ i j, raw38406step1 i j = -(raw38406step0 i j); unfold raw38406step1 raw38406step0; decide +kernel
      have hl : raw38406step1Labels = raw38406step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38406step1 raw38406step1Labels = mixedMoment B raw38406step2 raw38406step2Labels := by
      have ha : raw38406step2 = raw38406step1 := by apply Matrix.ext; unfold raw38406step2 raw38406step1; decide +kernel
      have hl : raw38406step1Labels = labelEmbedding4 ∘ raw38406step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38406step1 raw38406step1Labels raw38406step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1561 node1561Labels := by rfl

def raw38407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38407Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38407step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38407 raw38407Labels = mixedMoment B node870 node870Labels := by
  calc
    mixedMoment B raw38407 raw38407Labels = mixedMoment B raw38407step0 raw38407step0Labels := by
      have ha : raw38407step0 = raw38407 := by apply Matrix.ext; unfold raw38407step0 raw38407; decide +kernel
      have hl : raw38407Labels = labelEmbedding2 ∘ raw38407step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38407 raw38407Labels raw38407step0Labels labelEmbedding2 hl
    _ = mixedMoment B node870 node870Labels := by rfl

def raw38408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38408Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38408step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw38408step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38408step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw38408step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38408step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw38408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38408 raw38408Labels = mixedMoment B node1567 node1567Labels := by
  calc
    mixedMoment B raw38408 raw38408Labels = mixedMoment B raw38408step0 raw38408step0Labels := by
      have ha : raw38408step0 = (fun i j => raw38408 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38408step0 raw38408; decide +kernel
      have hl : raw38408step0Labels = raw38408Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38408 raw38408Labels permutation152 permutation7
    mixedMoment B raw38408step0 raw38408step0Labels = mixedMoment B raw38408step1 raw38408step1Labels := by
      have ha : raw38408step1 = -raw38408step0 := by apply Matrix.ext; change ∀ i j, raw38408step1 i j = -(raw38408step0 i j); unfold raw38408step1 raw38408step0; decide +kernel
      have hl : raw38408step1Labels = raw38408step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38408step1 raw38408step1Labels = mixedMoment B raw38408step2 raw38408step2Labels := by
      have ha : raw38408step2 = raw38408step1 := by apply Matrix.ext; unfold raw38408step2 raw38408step1; decide +kernel
      have hl : raw38408step1Labels = labelEmbedding4 ∘ raw38408step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38408step1 raw38408step1Labels raw38408step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1567 node1567Labels := by rfl

def raw38409 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw38409Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw38409step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38409 raw38409Labels = mixedMoment B node871 node871Labels := by
  calc
    mixedMoment B raw38409 raw38409Labels = mixedMoment B raw38409step0 raw38409step0Labels := by
      have ha : raw38409step0 = raw38409 := by apply Matrix.ext; unfold raw38409step0 raw38409; decide +kernel
      have hl : raw38409Labels = labelEmbedding2 ∘ raw38409step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38409 raw38409Labels raw38409step0Labels labelEmbedding2 hl
    _ = mixedMoment B node871 node871Labels := by rfl

def raw38410 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw38410Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw38410step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38410step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw38410step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38410step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw38410step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38410 raw38410Labels = mixedMoment B node1568 node1568Labels := by
  calc
    mixedMoment B raw38410 raw38410Labels = mixedMoment B raw38410step0 raw38410step0Labels := by
      have ha : raw38410step0 = (fun i j => raw38410 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38410step0 raw38410; decide +kernel
      have hl : raw38410step0Labels = raw38410Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38410 raw38410Labels permutation32 permutation7
    mixedMoment B raw38410step0 raw38410step0Labels = mixedMoment B raw38410step1 raw38410step1Labels := by
      have ha : raw38410step1 = -raw38410step0 := by apply Matrix.ext; change ∀ i j, raw38410step1 i j = -(raw38410step0 i j); unfold raw38410step1 raw38410step0; decide +kernel
      have hl : raw38410step1Labels = raw38410step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38410step1 raw38410step1Labels = mixedMoment B raw38410step2 raw38410step2Labels := by
      have ha : raw38410step2 = raw38410step1 := by apply Matrix.ext; unfold raw38410step2 raw38410step1; decide +kernel
      have hl : raw38410step1Labels = labelEmbedding4 ∘ raw38410step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38410step1 raw38410step1Labels raw38410step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1568 node1568Labels := by rfl

def raw38411 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw38411Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw38411step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38411 raw38411Labels = mixedMoment B node872 node872Labels := by
  calc
    mixedMoment B raw38411 raw38411Labels = mixedMoment B raw38411step0 raw38411step0Labels := by
      have ha : raw38411step0 = raw38411 := by apply Matrix.ext; unfold raw38411step0 raw38411; decide +kernel
      have hl : raw38411Labels = labelEmbedding2 ∘ raw38411step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38411 raw38411Labels raw38411step0Labels labelEmbedding2 hl
    _ = mixedMoment B node872 node872Labels := by rfl

def raw38412 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw38412Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 0, 3]]
def raw38412step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38412step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw38412step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38412step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw38412step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38412 raw38412Labels = mixedMoment B node1562 node1562Labels := by
  calc
    mixedMoment B raw38412 raw38412Labels = mixedMoment B raw38412step0 raw38412step0Labels := by
      have ha : raw38412step0 = (fun i j => raw38412 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38412step0 raw38412; decide +kernel
      have hl : raw38412step0Labels = raw38412Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38412 raw38412Labels permutation34 permutation7
    mixedMoment B raw38412step0 raw38412step0Labels = mixedMoment B raw38412step1 raw38412step1Labels := by
      have ha : raw38412step1 = -raw38412step0 := by apply Matrix.ext; change ∀ i j, raw38412step1 i j = -(raw38412step0 i j); unfold raw38412step1 raw38412step0; decide +kernel
      have hl : raw38412step1Labels = raw38412step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38412step1 raw38412step1Labels = mixedMoment B raw38412step2 raw38412step2Labels := by
      have ha : raw38412step2 = raw38412step1 := by apply Matrix.ext; unfold raw38412step2 raw38412step1; decide +kernel
      have hl : raw38412step1Labels = labelEmbedding4 ∘ raw38412step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38412step1 raw38412step1Labels raw38412step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1562 node1562Labels := by rfl

def raw38413 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw38413Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw38413step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38413 raw38413Labels = mixedMoment B node873 node873Labels := by
  calc
    mixedMoment B raw38413 raw38413Labels = mixedMoment B raw38413step0 raw38413step0Labels := by
      have ha : raw38413step0 = raw38413 := by apply Matrix.ext; unfold raw38413step0 raw38413; decide +kernel
      have hl : raw38413Labels = labelEmbedding2 ∘ raw38413step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38413 raw38413Labels raw38413step0Labels labelEmbedding2 hl
    _ = mixedMoment B node873 node873Labels := by rfl

def raw38414 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw38414Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw38414step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38414step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw38414step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38414step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw38414step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38414 raw38414Labels = mixedMoment B node1569 node1569Labels := by
  calc
    mixedMoment B raw38414 raw38414Labels = mixedMoment B raw38414step0 raw38414step0Labels := by
      have ha : raw38414step0 = (fun i j => raw38414 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38414step0 raw38414; decide +kernel
      have hl : raw38414step0Labels = raw38414Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38414 raw38414Labels permutation32 permutation7
    mixedMoment B raw38414step0 raw38414step0Labels = mixedMoment B raw38414step1 raw38414step1Labels := by
      have ha : raw38414step1 = -raw38414step0 := by apply Matrix.ext; change ∀ i j, raw38414step1 i j = -(raw38414step0 i j); unfold raw38414step1 raw38414step0; decide +kernel
      have hl : raw38414step1Labels = raw38414step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38414step1 raw38414step1Labels = mixedMoment B raw38414step2 raw38414step2Labels := by
      have ha : raw38414step2 = raw38414step1 := by apply Matrix.ext; unfold raw38414step2 raw38414step1; decide +kernel
      have hl : raw38414step1Labels = labelEmbedding4 ∘ raw38414step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38414step1 raw38414step1Labels raw38414step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1569 node1569Labels := by rfl

def raw38415 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw38415Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw38415step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38415 raw38415Labels = mixedMoment B node874 node874Labels := by
  calc
    mixedMoment B raw38415 raw38415Labels = mixedMoment B raw38415step0 raw38415step0Labels := by
      have ha : raw38415step0 = raw38415 := by apply Matrix.ext; unfold raw38415step0 raw38415; decide +kernel
      have hl : raw38415Labels = labelEmbedding2 ∘ raw38415step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38415 raw38415Labels raw38415step0Labels labelEmbedding2 hl
    _ = mixedMoment B node874 node874Labels := by rfl

def raw38416 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw38416Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw38416step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38416step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw38416step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38416step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw38416step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38416 raw38416Labels = mixedMoment B node1570 node1570Labels := by
  calc
    mixedMoment B raw38416 raw38416Labels = mixedMoment B raw38416step0 raw38416step0Labels := by
      have ha : raw38416step0 = (fun i j => raw38416 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38416step0 raw38416; decide +kernel
      have hl : raw38416step0Labels = raw38416Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38416 raw38416Labels permutation33 permutation7
    mixedMoment B raw38416step0 raw38416step0Labels = mixedMoment B raw38416step1 raw38416step1Labels := by
      have ha : raw38416step1 = -raw38416step0 := by apply Matrix.ext; change ∀ i j, raw38416step1 i j = -(raw38416step0 i j); unfold raw38416step1 raw38416step0; decide +kernel
      have hl : raw38416step1Labels = raw38416step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38416step1 raw38416step1Labels = mixedMoment B raw38416step2 raw38416step2Labels := by
      have ha : raw38416step2 = raw38416step1 := by apply Matrix.ext; unfold raw38416step2 raw38416step1; decide +kernel
      have hl : raw38416step1Labels = labelEmbedding4 ∘ raw38416step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38416step1 raw38416step1Labels raw38416step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1570 node1570Labels := by rfl

def raw38417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38417Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38417 raw38417Labels = mixedMoment B node875 node875Labels := by
  calc
    mixedMoment B raw38417 raw38417Labels = mixedMoment B raw38417step0 raw38417step0Labels := by
      have ha : raw38417step0 = raw38417 := by apply Matrix.ext; unfold raw38417step0 raw38417; decide +kernel
      have hl : raw38417Labels = labelEmbedding2 ∘ raw38417step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38417 raw38417Labels raw38417step0Labels labelEmbedding2 hl
    _ = mixedMoment B node875 node875Labels := by rfl

def raw38418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38418Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw38418step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38418step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38418step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38418step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38418step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38418 raw38418Labels = mixedMoment B node1551 node1551Labels := by
  calc
    mixedMoment B raw38418 raw38418Labels = mixedMoment B raw38418step0 raw38418step0Labels := by
      have ha : raw38418step0 = (fun i j => raw38418 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38418step0 raw38418; decide +kernel
      have hl : raw38418step0Labels = raw38418Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38418 raw38418Labels permutation152 permutation7
    mixedMoment B raw38418step0 raw38418step0Labels = mixedMoment B raw38418step1 raw38418step1Labels := by
      have ha : raw38418step1 = -raw38418step0 := by apply Matrix.ext; change ∀ i j, raw38418step1 i j = -(raw38418step0 i j); unfold raw38418step1 raw38418step0; decide +kernel
      have hl : raw38418step1Labels = raw38418step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38418step1 raw38418step1Labels = mixedMoment B raw38418step2 raw38418step2Labels := by
      have ha : raw38418step2 = raw38418step1 := by apply Matrix.ext; unfold raw38418step2 raw38418step1; decide +kernel
      have hl : raw38418step1Labels = labelEmbedding4 ∘ raw38418step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38418step1 raw38418step1Labels raw38418step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1551 node1551Labels := by rfl

def raw38419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38419Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38419step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38419 raw38419Labels = mixedMoment B node876 node876Labels := by
  calc
    mixedMoment B raw38419 raw38419Labels = mixedMoment B raw38419step0 raw38419step0Labels := by
      have ha : raw38419step0 = raw38419 := by apply Matrix.ext; unfold raw38419step0 raw38419; decide +kernel
      have hl : raw38419Labels = labelEmbedding2 ∘ raw38419step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38419 raw38419Labels raw38419step0Labels labelEmbedding2 hl
    _ = mixedMoment B node876 node876Labels := by rfl

def raw38420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38420Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38420step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw38420step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38420step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38420step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38420step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38420step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38420 raw38420Labels = mixedMoment B node1552 node1552Labels := by
  calc
    mixedMoment B raw38420 raw38420Labels = mixedMoment B raw38420step0 raw38420step0Labels := by
      have ha : raw38420step0 = (fun i j => raw38420 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38420step0 raw38420; decide +kernel
      have hl : raw38420step0Labels = raw38420Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38420 raw38420Labels permutation152 permutation7
    mixedMoment B raw38420step0 raw38420step0Labels = mixedMoment B raw38420step1 raw38420step1Labels := by
      have ha : raw38420step1 = -raw38420step0 := by apply Matrix.ext; change ∀ i j, raw38420step1 i j = -(raw38420step0 i j); unfold raw38420step1 raw38420step0; decide +kernel
      have hl : raw38420step1Labels = raw38420step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38420step1 raw38420step1Labels = mixedMoment B raw38420step2 raw38420step2Labels := by
      have ha : raw38420step2 = raw38420step1 := by apply Matrix.ext; unfold raw38420step2 raw38420step1; decide +kernel
      have hl : raw38420step1Labels = labelEmbedding4 ∘ raw38420step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38420step1 raw38420step1Labels raw38420step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1552 node1552Labels := by rfl

def raw38421 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw38421Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw38421step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38421 raw38421Labels = mixedMoment B node877 node877Labels := by
  calc
    mixedMoment B raw38421 raw38421Labels = mixedMoment B raw38421step0 raw38421step0Labels := by
      have ha : raw38421step0 = raw38421 := by apply Matrix.ext; unfold raw38421step0 raw38421; decide +kernel
      have hl : raw38421Labels = labelEmbedding2 ∘ raw38421step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38421 raw38421Labels raw38421step0Labels labelEmbedding2 hl
    _ = mixedMoment B node877 node877Labels := by rfl

def raw38422 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw38422Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 1, -4]]
def raw38422step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38422step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 1, -4]]
def raw38422step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38422 raw38422Labels = mixedMoment B node968 node968Labels := by
  calc
    mixedMoment B raw38422 raw38422Labels = mixedMoment B raw38422step0 raw38422step0Labels := by
      have ha : raw38422step0 = (fun i j => raw38422 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38422step0 raw38422; decide +kernel
      have hl : raw38422step0Labels = raw38422Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38422 raw38422Labels permutation145 permutation7
    mixedMoment B raw38422step0 raw38422step0Labels = mixedMoment B raw38422step1 raw38422step1Labels := by
      have ha : raw38422step1 = raw38422step0 := by apply Matrix.ext; unfold raw38422step1 raw38422step0; decide +kernel
      have hl : raw38422step0Labels = labelEmbedding4 ∘ raw38422step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38422step0 raw38422step0Labels raw38422step1Labels labelEmbedding4 hl
    _ = mixedMoment B node968 node968Labels := by rfl

def raw38423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38423Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38423step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38423 raw38423Labels = mixedMoment B node879 node879Labels := by
  calc
    mixedMoment B raw38423 raw38423Labels = mixedMoment B raw38423step0 raw38423step0Labels := by
      have ha : raw38423step0 = raw38423 := by apply Matrix.ext; unfold raw38423step0 raw38423; decide +kernel
      have hl : raw38423Labels = labelEmbedding2 ∘ raw38423step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38423 raw38423Labels raw38423step0Labels labelEmbedding2 hl
    _ = mixedMoment B node879 node879Labels := by rfl

def raw38424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38424Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw38424step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38424step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38424step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38424step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38424step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38424 raw38424Labels = mixedMoment B node1556 node1556Labels := by
  calc
    mixedMoment B raw38424 raw38424Labels = mixedMoment B raw38424step0 raw38424step0Labels := by
      have ha : raw38424step0 = (fun i j => raw38424 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38424step0 raw38424; decide +kernel
      have hl : raw38424step0Labels = raw38424Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38424 raw38424Labels permutation153 permutation7
    mixedMoment B raw38424step0 raw38424step0Labels = mixedMoment B raw38424step1 raw38424step1Labels := by
      have ha : raw38424step1 = -raw38424step0 := by apply Matrix.ext; change ∀ i j, raw38424step1 i j = -(raw38424step0 i j); unfold raw38424step1 raw38424step0; decide +kernel
      have hl : raw38424step1Labels = raw38424step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38424step1 raw38424step1Labels = mixedMoment B raw38424step2 raw38424step2Labels := by
      have ha : raw38424step2 = raw38424step1 := by apply Matrix.ext; unfold raw38424step2 raw38424step1; decide +kernel
      have hl : raw38424step1Labels = labelEmbedding4 ∘ raw38424step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38424step1 raw38424step1Labels raw38424step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1556 node1556Labels := by rfl

def raw38425 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw38425Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw38425step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38425 raw38425Labels = mixedMoment B node881 node881Labels := by
  calc
    mixedMoment B raw38425 raw38425Labels = mixedMoment B raw38425step0 raw38425step0Labels := by
      have ha : raw38425step0 = raw38425 := by apply Matrix.ext; unfold raw38425step0 raw38425; decide +kernel
      have hl : raw38425Labels = labelEmbedding2 ∘ raw38425step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38425 raw38425Labels raw38425step0Labels labelEmbedding2 hl
    _ = mixedMoment B node881 node881Labels := by rfl

def raw38426 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw38426Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, -1, 3]]
def raw38426step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38426step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw38426step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38426step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw38426step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38426 raw38426Labels = mixedMoment B node1559 node1559Labels := by
  calc
    mixedMoment B raw38426 raw38426Labels = mixedMoment B raw38426step0 raw38426step0Labels := by
      have ha : raw38426step0 = (fun i j => raw38426 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38426step0 raw38426; decide +kernel
      have hl : raw38426step0Labels = raw38426Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38426 raw38426Labels permutation32 permutation7
    mixedMoment B raw38426step0 raw38426step0Labels = mixedMoment B raw38426step1 raw38426step1Labels := by
      have ha : raw38426step1 = -raw38426step0 := by apply Matrix.ext; change ∀ i j, raw38426step1 i j = -(raw38426step0 i j); unfold raw38426step1 raw38426step0; decide +kernel
      have hl : raw38426step1Labels = raw38426step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38426step1 raw38426step1Labels = mixedMoment B raw38426step2 raw38426step2Labels := by
      have ha : raw38426step2 = raw38426step1 := by apply Matrix.ext; unfold raw38426step2 raw38426step1; decide +kernel
      have hl : raw38426step1Labels = labelEmbedding4 ∘ raw38426step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38426step1 raw38426step1Labels raw38426step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1559 node1559Labels := by rfl

def raw38427 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw38427Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw38427step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38427 raw38427Labels = mixedMoment B node882 node882Labels := by
  calc
    mixedMoment B raw38427 raw38427Labels = mixedMoment B raw38427step0 raw38427step0Labels := by
      have ha : raw38427step0 = raw38427 := by apply Matrix.ext; unfold raw38427step0 raw38427; decide +kernel
      have hl : raw38427Labels = labelEmbedding2 ∘ raw38427step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38427 raw38427Labels raw38427step0Labels labelEmbedding2 hl
    _ = mixedMoment B node882 node882Labels := by rfl

def raw38428 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw38428Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 1, 2]]
def raw38428step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38428step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def raw38428step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38428step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def raw38428step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38428 raw38428Labels = mixedMoment B node1558 node1558Labels := by
  calc
    mixedMoment B raw38428 raw38428Labels = mixedMoment B raw38428step0 raw38428step0Labels := by
      have ha : raw38428step0 = (fun i j => raw38428 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38428step0 raw38428; decide +kernel
      have hl : raw38428step0Labels = raw38428Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38428 raw38428Labels permutation32 permutation7
    mixedMoment B raw38428step0 raw38428step0Labels = mixedMoment B raw38428step1 raw38428step1Labels := by
      have ha : raw38428step1 = -raw38428step0 := by apply Matrix.ext; change ∀ i j, raw38428step1 i j = -(raw38428step0 i j); unfold raw38428step1 raw38428step0; decide +kernel
      have hl : raw38428step1Labels = raw38428step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38428step1 raw38428step1Labels = mixedMoment B raw38428step2 raw38428step2Labels := by
      have ha : raw38428step2 = raw38428step1 := by apply Matrix.ext; unfold raw38428step2 raw38428step1; decide +kernel
      have hl : raw38428step1Labels = labelEmbedding4 ∘ raw38428step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38428step1 raw38428step1Labels raw38428step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1558 node1558Labels := by rfl

def raw38429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38429Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38429step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38429 raw38429Labels = mixedMoment B node885 node885Labels := by
  calc
    mixedMoment B raw38429 raw38429Labels = mixedMoment B raw38429step0 raw38429step0Labels := by
      have ha : raw38429step0 = raw38429 := by apply Matrix.ext; unfold raw38429step0 raw38429; decide +kernel
      have hl : raw38429Labels = labelEmbedding2 ∘ raw38429step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38429 raw38429Labels raw38429step0Labels labelEmbedding2 hl
    _ = mixedMoment B node885 node885Labels := by rfl

def raw38430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38430Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38430step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw38430step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38430step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38430step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38430step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38430step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38430 raw38430Labels = mixedMoment B node1563 node1563Labels := by
  calc
    mixedMoment B raw38430 raw38430Labels = mixedMoment B raw38430step0 raw38430step0Labels := by
      have ha : raw38430step0 = (fun i j => raw38430 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38430step0 raw38430; decide +kernel
      have hl : raw38430step0Labels = raw38430Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38430 raw38430Labels permutation170 permutation7
    mixedMoment B raw38430step0 raw38430step0Labels = mixedMoment B raw38430step1 raw38430step1Labels := by
      have ha : raw38430step1 = -raw38430step0 := by apply Matrix.ext; change ∀ i j, raw38430step1 i j = -(raw38430step0 i j); unfold raw38430step1 raw38430step0; decide +kernel
      have hl : raw38430step1Labels = raw38430step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38430step1 raw38430step1Labels = mixedMoment B raw38430step2 raw38430step2Labels := by
      have ha : raw38430step2 = raw38430step1 := by apply Matrix.ext; unfold raw38430step2 raw38430step1; decide +kernel
      have hl : raw38430step1Labels = labelEmbedding4 ∘ raw38430step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38430step1 raw38430step1Labels raw38430step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1563 node1563Labels := by rfl

def raw38431 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw38431Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw38431step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38431 raw38431Labels = mixedMoment B node887 node887Labels := by
  calc
    mixedMoment B raw38431 raw38431Labels = mixedMoment B raw38431step0 raw38431step0Labels := by
      have ha : raw38431step0 = raw38431 := by apply Matrix.ext; unfold raw38431step0 raw38431; decide +kernel
      have hl : raw38431Labels = labelEmbedding2 ∘ raw38431step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38431 raw38431Labels raw38431step0Labels labelEmbedding2 hl
    _ = mixedMoment B node887 node887Labels := by rfl

def raw38432 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw38432Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, 0, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw38432step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38432step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw38432step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38432step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw38432step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38432 raw38432Labels = mixedMoment B node1573 node1573Labels := by
  calc
    mixedMoment B raw38432 raw38432Labels = mixedMoment B raw38432step0 raw38432step0Labels := by
      have ha : raw38432step0 = (fun i j => raw38432 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38432step0 raw38432; decide +kernel
      have hl : raw38432step0Labels = raw38432Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38432 raw38432Labels permutation33 permutation7
    mixedMoment B raw38432step0 raw38432step0Labels = mixedMoment B raw38432step1 raw38432step1Labels := by
      have ha : raw38432step1 = -raw38432step0 := by apply Matrix.ext; change ∀ i j, raw38432step1 i j = -(raw38432step0 i j); unfold raw38432step1 raw38432step0; decide +kernel
      have hl : raw38432step1Labels = raw38432step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38432step1 raw38432step1Labels = mixedMoment B raw38432step2 raw38432step2Labels := by
      have ha : raw38432step2 = raw38432step1 := by apply Matrix.ext; unfold raw38432step2 raw38432step1; decide +kernel
      have hl : raw38432step1Labels = labelEmbedding4 ∘ raw38432step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38432step1 raw38432step1Labels raw38432step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1573 node1573Labels := by rfl

def raw38433 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw38433Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw38433step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38433 raw38433Labels = mixedMoment B node888 node888Labels := by
  calc
    mixedMoment B raw38433 raw38433Labels = mixedMoment B raw38433step0 raw38433step0Labels := by
      have ha : raw38433step0 = raw38433 := by apply Matrix.ext; unfold raw38433step0 raw38433; decide +kernel
      have hl : raw38433Labels = labelEmbedding2 ∘ raw38433step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38433 raw38433Labels raw38433step0Labels labelEmbedding2 hl
    _ = mixedMoment B node888 node888Labels := by rfl

def raw38434 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw38434Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 1, 2]]
def raw38434step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38434step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -1, -2]]
def raw38434step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38434step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -1, -2]]
def raw38434step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38434 raw38434Labels = mixedMoment B node1564 node1564Labels := by
  calc
    mixedMoment B raw38434 raw38434Labels = mixedMoment B raw38434step0 raw38434step0Labels := by
      have ha : raw38434step0 = (fun i j => raw38434 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38434step0 raw38434; decide +kernel
      have hl : raw38434step0Labels = raw38434Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38434 raw38434Labels permutation34 permutation7
    mixedMoment B raw38434step0 raw38434step0Labels = mixedMoment B raw38434step1 raw38434step1Labels := by
      have ha : raw38434step1 = -raw38434step0 := by apply Matrix.ext; change ∀ i j, raw38434step1 i j = -(raw38434step0 i j); unfold raw38434step1 raw38434step0; decide +kernel
      have hl : raw38434step1Labels = raw38434step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38434step1 raw38434step1Labels = mixedMoment B raw38434step2 raw38434step2Labels := by
      have ha : raw38434step2 = raw38434step1 := by apply Matrix.ext; unfold raw38434step2 raw38434step1; decide +kernel
      have hl : raw38434step1Labels = labelEmbedding4 ∘ raw38434step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38434step1 raw38434step1Labels raw38434step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1564 node1564Labels := by rfl

def raw38435 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw38435Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw38435step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38435 raw38435Labels = mixedMoment B node891 node891Labels := by
  calc
    mixedMoment B raw38435 raw38435Labels = mixedMoment B raw38435step0 raw38435step0Labels := by
      have ha : raw38435step0 = raw38435 := by apply Matrix.ext; unfold raw38435step0 raw38435; decide +kernel
      have hl : raw38435Labels = labelEmbedding2 ∘ raw38435step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38435 raw38435Labels raw38435step0Labels labelEmbedding2 hl
    _ = mixedMoment B node891 node891Labels := by rfl

def raw38436 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw38436Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 0, 2]]
def raw38436step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38436step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw38436step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38436step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw38436step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38436 raw38436Labels = mixedMoment B node1565 node1565Labels := by
  calc
    mixedMoment B raw38436 raw38436Labels = mixedMoment B raw38436step0 raw38436step0Labels := by
      have ha : raw38436step0 = (fun i j => raw38436 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38436step0 raw38436; decide +kernel
      have hl : raw38436step0Labels = raw38436Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38436 raw38436Labels permutation34 permutation7
    mixedMoment B raw38436step0 raw38436step0Labels = mixedMoment B raw38436step1 raw38436step1Labels := by
      have ha : raw38436step1 = -raw38436step0 := by apply Matrix.ext; change ∀ i j, raw38436step1 i j = -(raw38436step0 i j); unfold raw38436step1 raw38436step0; decide +kernel
      have hl : raw38436step1Labels = raw38436step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38436step1 raw38436step1Labels = mixedMoment B raw38436step2 raw38436step2Labels := by
      have ha : raw38436step2 = raw38436step1 := by apply Matrix.ext; unfold raw38436step2 raw38436step1; decide +kernel
      have hl : raw38436step1Labels = labelEmbedding4 ∘ raw38436step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38436step1 raw38436step1Labels raw38436step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1565 node1565Labels := by rfl

def raw38437 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw38437Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw38437step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38437 raw38437Labels = mixedMoment B node892 node892Labels := by
  calc
    mixedMoment B raw38437 raw38437Labels = mixedMoment B raw38437step0 raw38437step0Labels := by
      have ha : raw38437step0 = raw38437 := by apply Matrix.ext; unfold raw38437step0 raw38437; decide +kernel
      have hl : raw38437Labels = labelEmbedding2 ∘ raw38437step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38437 raw38437Labels raw38437step0Labels labelEmbedding2 hl
    _ = mixedMoment B node892 node892Labels := by rfl

def raw38438 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw38438Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw38438step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38438step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw38438step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38438step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw38438step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38438 raw38438Labels = mixedMoment B node1575 node1575Labels := by
  calc
    mixedMoment B raw38438 raw38438Labels = mixedMoment B raw38438step0 raw38438step0Labels := by
      have ha : raw38438step0 = (fun i j => raw38438 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38438step0 raw38438; decide +kernel
      have hl : raw38438step0Labels = raw38438Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38438 raw38438Labels permutation35 permutation7
    mixedMoment B raw38438step0 raw38438step0Labels = mixedMoment B raw38438step1 raw38438step1Labels := by
      have ha : raw38438step1 = -raw38438step0 := by apply Matrix.ext; change ∀ i j, raw38438step1 i j = -(raw38438step0 i j); unfold raw38438step1 raw38438step0; decide +kernel
      have hl : raw38438step1Labels = raw38438step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38438step1 raw38438step1Labels = mixedMoment B raw38438step2 raw38438step2Labels := by
      have ha : raw38438step2 = raw38438step1 := by apply Matrix.ext; unfold raw38438step2 raw38438step1; decide +kernel
      have hl : raw38438step1Labels = labelEmbedding4 ∘ raw38438step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38438step1 raw38438step1Labels raw38438step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1575 node1575Labels := by rfl

def raw38439 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw38439Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38439step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw38439step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38439 raw38439Labels = mixedMoment B node893 node893Labels := by
  calc
    mixedMoment B raw38439 raw38439Labels = mixedMoment B raw38439step0 raw38439step0Labels := by
      have ha : raw38439step0 = raw38439 := by apply Matrix.ext; unfold raw38439step0 raw38439; decide +kernel
      have hl : raw38439Labels = labelEmbedding2 ∘ raw38439step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38439 raw38439Labels raw38439step0Labels labelEmbedding2 hl
    _ = mixedMoment B node893 node893Labels := by rfl

def raw38440 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw38440Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38440step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-2, 1, 1], ![-2, -2, 4]]
def raw38440step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38440step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![2, -1, -1], ![2, 2, -4]]
def raw38440step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38440step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![2, -1, -1], ![2, 2, -4]]
def raw38440step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38440 raw38440Labels = mixedMoment B node1578 node1578Labels := by
  calc
    mixedMoment B raw38440 raw38440Labels = mixedMoment B raw38440step0 raw38440step0Labels := by
      have ha : raw38440step0 = (fun i j => raw38440 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38440step0 raw38440; decide +kernel
      have hl : raw38440step0Labels = raw38440Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38440 raw38440Labels permutation8 permutation7
    mixedMoment B raw38440step0 raw38440step0Labels = mixedMoment B raw38440step1 raw38440step1Labels := by
      have ha : raw38440step1 = -raw38440step0 := by apply Matrix.ext; change ∀ i j, raw38440step1 i j = -(raw38440step0 i j); unfold raw38440step1 raw38440step0; decide +kernel
      have hl : raw38440step1Labels = raw38440step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38440step1 raw38440step1Labels = mixedMoment B raw38440step2 raw38440step2Labels := by
      have ha : raw38440step2 = raw38440step1 := by apply Matrix.ext; unfold raw38440step2 raw38440step1; decide +kernel
      have hl : raw38440step1Labels = labelEmbedding4 ∘ raw38440step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38440step1 raw38440step1Labels raw38440step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1578 node1578Labels := by rfl

def raw38441 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -2, 0], ![3, 1, -4]]
def raw38441Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38441step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -2, 0], ![3, 1, -4]]
def raw38441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38441 raw38441Labels = mixedMoment B node894 node894Labels := by
  calc
    mixedMoment B raw38441 raw38441Labels = mixedMoment B raw38441step0 raw38441step0Labels := by
      have ha : raw38441step0 = raw38441 := by apply Matrix.ext; unfold raw38441step0 raw38441; decide +kernel
      have hl : raw38441Labels = labelEmbedding2 ∘ raw38441step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38441 raw38441Labels raw38441step0Labels labelEmbedding2 hl
    _ = mixedMoment B node894 node894Labels := by rfl

def raw38442 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -2, 0], ![3, 1, -4]]
def raw38442Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38442step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![3, 1, -4]]
def raw38442step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38442step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![3, 1, -4]]
def raw38442step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38442 raw38442Labels = mixedMoment B node961 node961Labels := by
  calc
    mixedMoment B raw38442 raw38442Labels = mixedMoment B raw38442step0 raw38442step0Labels := by
      have ha : raw38442step0 = (fun i j => raw38442 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38442step0 raw38442; decide +kernel
      have hl : raw38442step0Labels = raw38442Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38442 raw38442Labels permutation31 permutation7
    mixedMoment B raw38442step0 raw38442step0Labels = mixedMoment B raw38442step1 raw38442step1Labels := by
      have ha : raw38442step1 = raw38442step0 := by apply Matrix.ext; unfold raw38442step1 raw38442step0; decide +kernel
      have hl : raw38442step0Labels = labelEmbedding4 ∘ raw38442step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38442step0 raw38442step0Labels raw38442step1Labels labelEmbedding4 hl
    _ = mixedMoment B node961 node961Labels := by rfl

def raw38443 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw38443Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38443step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw38443step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38443 raw38443Labels = mixedMoment B node897 node897Labels := by
  calc
    mixedMoment B raw38443 raw38443Labels = mixedMoment B raw38443step0 raw38443step0Labels := by
      have ha : raw38443step0 = raw38443 := by apply Matrix.ext; unfold raw38443step0 raw38443; decide +kernel
      have hl : raw38443Labels = labelEmbedding2 ∘ raw38443step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38443 raw38443Labels raw38443step0Labels labelEmbedding2 hl
    _ = mixedMoment B node897 node897Labels := by rfl

def raw38444 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw38444Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38444step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, -2, 3], ![-3, 1, 2]]
def raw38444step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38444step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 2, -3], ![3, -1, -2]]
def raw38444step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38444step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 2, -3], ![3, -1, -2]]
def raw38444step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38444 raw38444Labels = mixedMoment B node1577 node1577Labels := by
  calc
    mixedMoment B raw38444 raw38444Labels = mixedMoment B raw38444step0 raw38444step0Labels := by
      have ha : raw38444step0 = (fun i j => raw38444 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38444step0 raw38444; decide +kernel
      have hl : raw38444step0Labels = raw38444Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38444 raw38444Labels permutation9 permutation7
    mixedMoment B raw38444step0 raw38444step0Labels = mixedMoment B raw38444step1 raw38444step1Labels := by
      have ha : raw38444step1 = -raw38444step0 := by apply Matrix.ext; change ∀ i j, raw38444step1 i j = -(raw38444step0 i j); unfold raw38444step1 raw38444step0; decide +kernel
      have hl : raw38444step1Labels = raw38444step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38444step1 raw38444step1Labels = mixedMoment B raw38444step2 raw38444step2Labels := by
      have ha : raw38444step2 = raw38444step1 := by apply Matrix.ext; unfold raw38444step2 raw38444step1; decide +kernel
      have hl : raw38444step1Labels = labelEmbedding4 ∘ raw38444step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38444step1 raw38444step1Labels raw38444step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1577 node1577Labels := by rfl

def raw38445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw38445Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38445step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw38445step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38445 raw38445Labels = mixedMoment B node898 node898Labels := by
  calc
    mixedMoment B raw38445 raw38445Labels = mixedMoment B raw38445step0 raw38445step0Labels := by
      have ha : raw38445step0 = raw38445 := by apply Matrix.ext; unfold raw38445step0 raw38445; decide +kernel
      have hl : raw38445Labels = labelEmbedding2 ∘ raw38445step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38445 raw38445Labels raw38445step0Labels labelEmbedding2 hl
    _ = mixedMoment B node898 node898Labels := by rfl

def raw38446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw38446Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38446step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw38446step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38446step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw38446step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38446step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw38446step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38446 raw38446Labels = mixedMoment B node1586 node1586Labels := by
  calc
    mixedMoment B raw38446 raw38446Labels = mixedMoment B raw38446step0 raw38446step0Labels := by
      have ha : raw38446step0 = (fun i j => raw38446 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38446step0 raw38446; decide +kernel
      have hl : raw38446step0Labels = raw38446Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38446 raw38446Labels permutation176 permutation7
    mixedMoment B raw38446step0 raw38446step0Labels = mixedMoment B raw38446step1 raw38446step1Labels := by
      have ha : raw38446step1 = -raw38446step0 := by apply Matrix.ext; change ∀ i j, raw38446step1 i j = -(raw38446step0 i j); unfold raw38446step1 raw38446step0; decide +kernel
      have hl : raw38446step1Labels = raw38446step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38446step1 raw38446step1Labels = mixedMoment B raw38446step2 raw38446step2Labels := by
      have ha : raw38446step2 = raw38446step1 := by apply Matrix.ext; unfold raw38446step2 raw38446step1; decide +kernel
      have hl : raw38446step1Labels = labelEmbedding4 ∘ raw38446step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38446step1 raw38446step1Labels raw38446step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1586 node1586Labels := by rfl

def raw38447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw38447Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw38447step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38447 raw38447Labels = mixedMoment B node899 node899Labels := by
  calc
    mixedMoment B raw38447 raw38447Labels = mixedMoment B raw38447step0 raw38447step0Labels := by
      have ha : raw38447step0 = raw38447 := by apply Matrix.ext; unfold raw38447step0 raw38447; decide +kernel
      have hl : raw38447Labels = labelEmbedding2 ∘ raw38447step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38447 raw38447Labels raw38447step0Labels labelEmbedding2 hl
    _ = mixedMoment B node899 node899Labels := by rfl

def raw38448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw38448Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw38448step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38448step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw38448step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38448step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw38448step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38448 raw38448Labels = mixedMoment B node1587 node1587Labels := by
  calc
    mixedMoment B raw38448 raw38448Labels = mixedMoment B raw38448step0 raw38448step0Labels := by
      have ha : raw38448step0 = (fun i j => raw38448 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38448step0 raw38448; decide +kernel
      have hl : raw38448step0Labels = raw38448Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38448 raw38448Labels permutation176 permutation7
    mixedMoment B raw38448step0 raw38448step0Labels = mixedMoment B raw38448step1 raw38448step1Labels := by
      have ha : raw38448step1 = -raw38448step0 := by apply Matrix.ext; change ∀ i j, raw38448step1 i j = -(raw38448step0 i j); unfold raw38448step1 raw38448step0; decide +kernel
      have hl : raw38448step1Labels = raw38448step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38448step1 raw38448step1Labels = mixedMoment B raw38448step2 raw38448step2Labels := by
      have ha : raw38448step2 = raw38448step1 := by apply Matrix.ext; unfold raw38448step2 raw38448step1; decide +kernel
      have hl : raw38448step1Labels = labelEmbedding4 ∘ raw38448step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38448step1 raw38448step1Labels raw38448step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1587 node1587Labels := by rfl

def raw38449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38449Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38449step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38449step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38449 raw38449Labels = mixedMoment B node900 node900Labels := by
  calc
    mixedMoment B raw38449 raw38449Labels = mixedMoment B raw38449step0 raw38449step0Labels := by
      have ha : raw38449step0 = raw38449 := by apply Matrix.ext; unfold raw38449step0 raw38449; decide +kernel
      have hl : raw38449Labels = labelEmbedding2 ∘ raw38449step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38449 raw38449Labels raw38449step0Labels labelEmbedding2 hl
    _ = mixedMoment B node900 node900Labels := by rfl

def raw38450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38450Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38450step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw38450step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38450step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw38450step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38450step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw38450step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38450 raw38450Labels = mixedMoment B node1588 node1588Labels := by
  calc
    mixedMoment B raw38450 raw38450Labels = mixedMoment B raw38450step0 raw38450step0Labels := by
      have ha : raw38450step0 = (fun i j => raw38450 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38450step0 raw38450; decide +kernel
      have hl : raw38450step0Labels = raw38450Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38450 raw38450Labels permutation176 permutation7
    mixedMoment B raw38450step0 raw38450step0Labels = mixedMoment B raw38450step1 raw38450step1Labels := by
      have ha : raw38450step1 = -raw38450step0 := by apply Matrix.ext; change ∀ i j, raw38450step1 i j = -(raw38450step0 i j); unfold raw38450step1 raw38450step0; decide +kernel
      have hl : raw38450step1Labels = raw38450step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38450step1 raw38450step1Labels = mixedMoment B raw38450step2 raw38450step2Labels := by
      have ha : raw38450step2 = raw38450step1 := by apply Matrix.ext; unfold raw38450step2 raw38450step1; decide +kernel
      have hl : raw38450step1Labels = labelEmbedding4 ∘ raw38450step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38450step1 raw38450step1Labels raw38450step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1588 node1588Labels := by rfl

def raw38451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38451Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38451step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38451 raw38451Labels = mixedMoment B node901 node901Labels := by
  calc
    mixedMoment B raw38451 raw38451Labels = mixedMoment B raw38451step0 raw38451step0Labels := by
      have ha : raw38451step0 = raw38451 := by apply Matrix.ext; unfold raw38451step0 raw38451; decide +kernel
      have hl : raw38451Labels = labelEmbedding2 ∘ raw38451step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38451 raw38451Labels raw38451step0Labels labelEmbedding2 hl
    _ = mixedMoment B node901 node901Labels := by rfl

def raw38452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38452Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38452step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw38452step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38452step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw38452step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38452step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw38452step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38452 raw38452Labels = mixedMoment B node1589 node1589Labels := by
  calc
    mixedMoment B raw38452 raw38452Labels = mixedMoment B raw38452step0 raw38452step0Labels := by
      have ha : raw38452step0 = (fun i j => raw38452 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38452step0 raw38452; decide +kernel
      have hl : raw38452step0Labels = raw38452Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38452 raw38452Labels permutation176 permutation7
    mixedMoment B raw38452step0 raw38452step0Labels = mixedMoment B raw38452step1 raw38452step1Labels := by
      have ha : raw38452step1 = -raw38452step0 := by apply Matrix.ext; change ∀ i j, raw38452step1 i j = -(raw38452step0 i j); unfold raw38452step1 raw38452step0; decide +kernel
      have hl : raw38452step1Labels = raw38452step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38452step1 raw38452step1Labels = mixedMoment B raw38452step2 raw38452step2Labels := by
      have ha : raw38452step2 = raw38452step1 := by apply Matrix.ext; unfold raw38452step2 raw38452step1; decide +kernel
      have hl : raw38452step1Labels = labelEmbedding4 ∘ raw38452step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38452step1 raw38452step1Labels raw38452step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1589 node1589Labels := by rfl

def raw38453 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw38453Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw38453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38453 raw38453Labels = mixedMoment B node902 node902Labels := by
  calc
    mixedMoment B raw38453 raw38453Labels = mixedMoment B raw38453step0 raw38453step0Labels := by
      have ha : raw38453step0 = raw38453 := by apply Matrix.ext; unfold raw38453step0 raw38453; decide +kernel
      have hl : raw38453Labels = labelEmbedding2 ∘ raw38453step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38453 raw38453Labels raw38453step0Labels labelEmbedding2 hl
    _ = mixedMoment B node902 node902Labels := by rfl

def raw38454 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw38454Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 0, 3]]
def raw38454step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38454step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def raw38454step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38454step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def raw38454step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38454 raw38454Labels = mixedMoment B node1590 node1590Labels := by
  calc
    mixedMoment B raw38454 raw38454Labels = mixedMoment B raw38454step0 raw38454step0Labels := by
      have ha : raw38454step0 = (fun i j => raw38454 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38454step0 raw38454; decide +kernel
      have hl : raw38454step0Labels = raw38454Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38454 raw38454Labels permutation38 permutation7
    mixedMoment B raw38454step0 raw38454step0Labels = mixedMoment B raw38454step1 raw38454step1Labels := by
      have ha : raw38454step1 = -raw38454step0 := by apply Matrix.ext; change ∀ i j, raw38454step1 i j = -(raw38454step0 i j); unfold raw38454step1 raw38454step0; decide +kernel
      have hl : raw38454step1Labels = raw38454step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38454step1 raw38454step1Labels = mixedMoment B raw38454step2 raw38454step2Labels := by
      have ha : raw38454step2 = raw38454step1 := by apply Matrix.ext; unfold raw38454step2 raw38454step1; decide +kernel
      have hl : raw38454step1Labels = labelEmbedding4 ∘ raw38454step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38454step1 raw38454step1Labels raw38454step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1590 node1590Labels := by rfl

def raw38455 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw38455Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw38455step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38455 raw38455Labels = mixedMoment B node903 node903Labels := by
  calc
    mixedMoment B raw38455 raw38455Labels = mixedMoment B raw38455step0 raw38455step0Labels := by
      have ha : raw38455step0 = raw38455 := by apply Matrix.ext; unfold raw38455step0 raw38455; decide +kernel
      have hl : raw38455Labels = labelEmbedding2 ∘ raw38455step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38455 raw38455Labels raw38455step0Labels labelEmbedding2 hl
    _ = mixedMoment B node903 node903Labels := by rfl

def raw38456 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw38456Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![-2, 0, 2], ![-2, -1, 3]]
def raw38456step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38456step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw38456step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38456step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw38456step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38456 raw38456Labels = mixedMoment B node1591 node1591Labels := by
  calc
    mixedMoment B raw38456 raw38456Labels = mixedMoment B raw38456step0 raw38456step0Labels := by
      have ha : raw38456step0 = (fun i j => raw38456 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38456step0 raw38456; decide +kernel
      have hl : raw38456step0Labels = raw38456Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38456 raw38456Labels permutation38 permutation7
    mixedMoment B raw38456step0 raw38456step0Labels = mixedMoment B raw38456step1 raw38456step1Labels := by
      have ha : raw38456step1 = -raw38456step0 := by apply Matrix.ext; change ∀ i j, raw38456step1 i j = -(raw38456step0 i j); unfold raw38456step1 raw38456step0; decide +kernel
      have hl : raw38456step1Labels = raw38456step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38456step1 raw38456step1Labels = mixedMoment B raw38456step2 raw38456step2Labels := by
      have ha : raw38456step2 = raw38456step1 := by apply Matrix.ext; unfold raw38456step2 raw38456step1; decide +kernel
      have hl : raw38456step1Labels = labelEmbedding4 ∘ raw38456step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38456step1 raw38456step1Labels raw38456step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1591 node1591Labels := by rfl

def raw38457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38457Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38457step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38457step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38457 raw38457Labels = mixedMoment B node915 node915Labels := by
  calc
    mixedMoment B raw38457 raw38457Labels = mixedMoment B raw38457step0 raw38457step0Labels := by
      have ha : raw38457step0 = raw38457 := by apply Matrix.ext; unfold raw38457step0 raw38457; decide +kernel
      have hl : raw38457Labels = labelEmbedding2 ∘ raw38457step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38457 raw38457Labels raw38457step0Labels labelEmbedding2 hl
    _ = mixedMoment B node915 node915Labels := by rfl

def raw38458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38458Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw38458step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38458step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38458step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38458step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38458step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38458 raw38458Labels = mixedMoment B node1632 node1632Labels := by
  calc
    mixedMoment B raw38458 raw38458Labels = mixedMoment B raw38458step0 raw38458step0Labels := by
      have ha : raw38458step0 = (fun i j => raw38458 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38458step0 raw38458; decide +kernel
      have hl : raw38458step0Labels = raw38458Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38458 raw38458Labels permutation176 permutation7
    mixedMoment B raw38458step0 raw38458step0Labels = mixedMoment B raw38458step1 raw38458step1Labels := by
      have ha : raw38458step1 = -raw38458step0 := by apply Matrix.ext; change ∀ i j, raw38458step1 i j = -(raw38458step0 i j); unfold raw38458step1 raw38458step0; decide +kernel
      have hl : raw38458step1Labels = raw38458step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38458step1 raw38458step1Labels = mixedMoment B raw38458step2 raw38458step2Labels := by
      have ha : raw38458step2 = raw38458step1 := by apply Matrix.ext; unfold raw38458step2 raw38458step1; decide +kernel
      have hl : raw38458step1Labels = labelEmbedding4 ∘ raw38458step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38458step1 raw38458step1Labels raw38458step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1632 node1632Labels := by rfl

def raw38459 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw38459Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw38459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38459 raw38459Labels = mixedMoment B node916 node916Labels := by
  calc
    mixedMoment B raw38459 raw38459Labels = mixedMoment B raw38459step0 raw38459step0Labels := by
      have ha : raw38459step0 = raw38459 := by apply Matrix.ext; unfold raw38459step0 raw38459; decide +kernel
      have hl : raw38459Labels = labelEmbedding2 ∘ raw38459step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38459 raw38459Labels raw38459step0Labels labelEmbedding2 hl
    _ = mixedMoment B node916 node916Labels := by rfl

def raw38460 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw38460Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 0, 3]]
def raw38460step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38460step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw38460step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38460step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw38460step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38460 raw38460Labels = mixedMoment B node1633 node1633Labels := by
  calc
    mixedMoment B raw38460 raw38460Labels = mixedMoment B raw38460step0 raw38460step0Labels := by
      have ha : raw38460step0 = (fun i j => raw38460 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38460step0 raw38460; decide +kernel
      have hl : raw38460step0Labels = raw38460Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38460 raw38460Labels permutation38 permutation7
    mixedMoment B raw38460step0 raw38460step0Labels = mixedMoment B raw38460step1 raw38460step1Labels := by
      have ha : raw38460step1 = -raw38460step0 := by apply Matrix.ext; change ∀ i j, raw38460step1 i j = -(raw38460step0 i j); unfold raw38460step1 raw38460step0; decide +kernel
      have hl : raw38460step1Labels = raw38460step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38460step1 raw38460step1Labels = mixedMoment B raw38460step2 raw38460step2Labels := by
      have ha : raw38460step2 = raw38460step1 := by apply Matrix.ext; unfold raw38460step2 raw38460step1; decide +kernel
      have hl : raw38460step1Labels = labelEmbedding4 ∘ raw38460step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38460step1 raw38460step1Labels raw38460step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1633 node1633Labels := by rfl

def raw38461 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw38461Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw38461step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38461 raw38461Labels = mixedMoment B node917 node917Labels := by
  calc
    mixedMoment B raw38461 raw38461Labels = mixedMoment B raw38461step0 raw38461step0Labels := by
      have ha : raw38461step0 = raw38461 := by apply Matrix.ext; unfold raw38461step0 raw38461; decide +kernel
      have hl : raw38461Labels = labelEmbedding2 ∘ raw38461step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38461 raw38461Labels raw38461step0Labels labelEmbedding2 hl
    _ = mixedMoment B node917 node917Labels := by rfl

def raw38462 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw38462Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw38462step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw38462step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38462step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw38462step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38462 raw38462Labels = mixedMoment B node1634 node1634Labels := by
  calc
    mixedMoment B raw38462 raw38462Labels = mixedMoment B raw38462step0 raw38462step0Labels := by
      have ha : raw38462step0 = (fun i j => raw38462 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38462step0 raw38462; decide +kernel
      have hl : raw38462step0Labels = raw38462Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38462 raw38462Labels permutation38 permutation7
    mixedMoment B raw38462step0 raw38462step0Labels = mixedMoment B raw38462step1 raw38462step1Labels := by
      have ha : raw38462step1 = -raw38462step0 := by apply Matrix.ext; change ∀ i j, raw38462step1 i j = -(raw38462step0 i j); unfold raw38462step1 raw38462step0; decide +kernel
      have hl : raw38462step1Labels = raw38462step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38462step1 raw38462step1Labels = mixedMoment B raw38462step2 raw38462step2Labels := by
      have ha : raw38462step2 = raw38462step1 := by apply Matrix.ext; unfold raw38462step2 raw38462step1; decide +kernel
      have hl : raw38462step1Labels = labelEmbedding4 ∘ raw38462step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38462step1 raw38462step1Labels raw38462step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1634 node1634Labels := by rfl

def raw38463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38463Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38463step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38463 raw38463Labels = mixedMoment B node919 node919Labels := by
  calc
    mixedMoment B raw38463 raw38463Labels = mixedMoment B raw38463step0 raw38463step0Labels := by
      have ha : raw38463step0 = raw38463 := by apply Matrix.ext; unfold raw38463step0 raw38463; decide +kernel
      have hl : raw38463Labels = labelEmbedding2 ∘ raw38463step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38463 raw38463Labels raw38463step0Labels labelEmbedding2 hl
    _ = mixedMoment B node919 node919Labels := by rfl

def raw38464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38464Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw38464step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38464step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38464step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38464step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38464step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38464 raw38464Labels = mixedMoment B node1664 node1664Labels := by
  calc
    mixedMoment B raw38464 raw38464Labels = mixedMoment B raw38464step0 raw38464step0Labels := by
      have ha : raw38464step0 = (fun i j => raw38464 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38464step0 raw38464; decide +kernel
      have hl : raw38464step0Labels = raw38464Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38464 raw38464Labels permutation152 permutation7
    mixedMoment B raw38464step0 raw38464step0Labels = mixedMoment B raw38464step1 raw38464step1Labels := by
      have ha : raw38464step1 = -raw38464step0 := by apply Matrix.ext; change ∀ i j, raw38464step1 i j = -(raw38464step0 i j); unfold raw38464step1 raw38464step0; decide +kernel
      have hl : raw38464step1Labels = raw38464step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38464step1 raw38464step1Labels = mixedMoment B raw38464step2 raw38464step2Labels := by
      have ha : raw38464step2 = raw38464step1 := by apply Matrix.ext; unfold raw38464step2 raw38464step1; decide +kernel
      have hl : raw38464step1Labels = labelEmbedding4 ∘ raw38464step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38464step1 raw38464step1Labels raw38464step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1664 node1664Labels := by rfl

def raw38465 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38465Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38465step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38465 raw38465Labels = mixedMoment B node921 node921Labels := by
  calc
    mixedMoment B raw38465 raw38465Labels = mixedMoment B raw38465step0 raw38465step0Labels := by
      have ha : raw38465step0 = raw38465 := by apply Matrix.ext; unfold raw38465step0 raw38465; decide +kernel
      have hl : raw38465Labels = labelEmbedding2 ∘ raw38465step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38465 raw38465Labels raw38465step0Labels labelEmbedding2 hl
    _ = mixedMoment B node921 node921Labels := by rfl

def raw38466 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38466Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw38466step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38466step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw38466step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38466step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw38466step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38466 raw38466Labels = mixedMoment B node1666 node1666Labels := by
  calc
    mixedMoment B raw38466 raw38466Labels = mixedMoment B raw38466step0 raw38466step0Labels := by
      have ha : raw38466step0 = (fun i j => raw38466 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38466step0 raw38466; decide +kernel
      have hl : raw38466step0Labels = raw38466Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38466 raw38466Labels permutation32 permutation7
    mixedMoment B raw38466step0 raw38466step0Labels = mixedMoment B raw38466step1 raw38466step1Labels := by
      have ha : raw38466step1 = -raw38466step0 := by apply Matrix.ext; change ∀ i j, raw38466step1 i j = -(raw38466step0 i j); unfold raw38466step1 raw38466step0; decide +kernel
      have hl : raw38466step1Labels = raw38466step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38466step1 raw38466step1Labels = mixedMoment B raw38466step2 raw38466step2Labels := by
      have ha : raw38466step2 = raw38466step1 := by apply Matrix.ext; unfold raw38466step2 raw38466step1; decide +kernel
      have hl : raw38466step1Labels = labelEmbedding4 ∘ raw38466step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38466step1 raw38466step1Labels raw38466step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1666 node1666Labels := by rfl

def raw38467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38467Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38467step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38467 raw38467Labels = mixedMoment B node922 node922Labels := by
  calc
    mixedMoment B raw38467 raw38467Labels = mixedMoment B raw38467step0 raw38467step0Labels := by
      have ha : raw38467step0 = raw38467 := by apply Matrix.ext; unfold raw38467step0 raw38467; decide +kernel
      have hl : raw38467Labels = labelEmbedding2 ∘ raw38467step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38467 raw38467Labels raw38467step0Labels labelEmbedding2 hl
    _ = mixedMoment B node922 node922Labels := by rfl

def raw38468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38468Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38468step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw38468step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38468step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38468step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38468step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38468step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38468 raw38468Labels = mixedMoment B node1673 node1673Labels := by
  calc
    mixedMoment B raw38468 raw38468Labels = mixedMoment B raw38468step0 raw38468step0Labels := by
      have ha : raw38468step0 = (fun i j => raw38468 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38468step0 raw38468; decide +kernel
      have hl : raw38468step0Labels = raw38468Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38468 raw38468Labels permutation152 permutation7
    mixedMoment B raw38468step0 raw38468step0Labels = mixedMoment B raw38468step1 raw38468step1Labels := by
      have ha : raw38468step1 = -raw38468step0 := by apply Matrix.ext; change ∀ i j, raw38468step1 i j = -(raw38468step0 i j); unfold raw38468step1 raw38468step0; decide +kernel
      have hl : raw38468step1Labels = raw38468step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38468step1 raw38468step1Labels = mixedMoment B raw38468step2 raw38468step2Labels := by
      have ha : raw38468step2 = raw38468step1 := by apply Matrix.ext; unfold raw38468step2 raw38468step1; decide +kernel
      have hl : raw38468step1Labels = labelEmbedding4 ∘ raw38468step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38468step1 raw38468step1Labels raw38468step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1673 node1673Labels := by rfl

def raw38469 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38469Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38469step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38469 raw38469Labels = mixedMoment B node924 node924Labels := by
  calc
    mixedMoment B raw38469 raw38469Labels = mixedMoment B raw38469step0 raw38469step0Labels := by
      have ha : raw38469step0 = raw38469 := by apply Matrix.ext; unfold raw38469step0 raw38469; decide +kernel
      have hl : raw38469Labels = labelEmbedding2 ∘ raw38469step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38469 raw38469Labels raw38469step0Labels labelEmbedding2 hl
    _ = mixedMoment B node924 node924Labels := by rfl

def raw38470 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38470Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw38470step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38470step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw38470step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38470step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw38470step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38470 raw38470Labels = mixedMoment B node1674 node1674Labels := by
  calc
    mixedMoment B raw38470 raw38470Labels = mixedMoment B raw38470step0 raw38470step0Labels := by
      have ha : raw38470step0 = (fun i j => raw38470 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38470step0 raw38470; decide +kernel
      have hl : raw38470step0Labels = raw38470Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38470 raw38470Labels permutation32 permutation7
    mixedMoment B raw38470step0 raw38470step0Labels = mixedMoment B raw38470step1 raw38470step1Labels := by
      have ha : raw38470step1 = -raw38470step0 := by apply Matrix.ext; change ∀ i j, raw38470step1 i j = -(raw38470step0 i j); unfold raw38470step1 raw38470step0; decide +kernel
      have hl : raw38470step1Labels = raw38470step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38470step1 raw38470step1Labels = mixedMoment B raw38470step2 raw38470step2Labels := by
      have ha : raw38470step2 = raw38470step1 := by apply Matrix.ext; unfold raw38470step2 raw38470step1; decide +kernel
      have hl : raw38470step1Labels = labelEmbedding4 ∘ raw38470step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38470step1 raw38470step1Labels raw38470step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1674 node1674Labels := by rfl

def raw38471 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38471Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38471step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38471 raw38471Labels = mixedMoment B node927 node927Labels := by
  calc
    mixedMoment B raw38471 raw38471Labels = mixedMoment B raw38471step0 raw38471step0Labels := by
      have ha : raw38471step0 = raw38471 := by apply Matrix.ext; unfold raw38471step0 raw38471; decide +kernel
      have hl : raw38471Labels = labelEmbedding2 ∘ raw38471step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38471 raw38471Labels raw38471step0Labels labelEmbedding2 hl
    _ = mixedMoment B node927 node927Labels := by rfl

def raw38472 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38472Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw38472step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38472step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw38472step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38472step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw38472step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38472 raw38472Labels = mixedMoment B node1675 node1675Labels := by
  calc
    mixedMoment B raw38472 raw38472Labels = mixedMoment B raw38472step0 raw38472step0Labels := by
      have ha : raw38472step0 = (fun i j => raw38472 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38472step0 raw38472; decide +kernel
      have hl : raw38472step0Labels = raw38472Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38472 raw38472Labels permutation32 permutation7
    mixedMoment B raw38472step0 raw38472step0Labels = mixedMoment B raw38472step1 raw38472step1Labels := by
      have ha : raw38472step1 = -raw38472step0 := by apply Matrix.ext; change ∀ i j, raw38472step1 i j = -(raw38472step0 i j); unfold raw38472step1 raw38472step0; decide +kernel
      have hl : raw38472step1Labels = raw38472step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38472step1 raw38472step1Labels = mixedMoment B raw38472step2 raw38472step2Labels := by
      have ha : raw38472step2 = raw38472step1 := by apply Matrix.ext; unfold raw38472step2 raw38472step1; decide +kernel
      have hl : raw38472step1Labels = labelEmbedding4 ∘ raw38472step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38472step1 raw38472step1Labels raw38472step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1675 node1675Labels := by rfl

def raw38473 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw38473Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38473step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw38473step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38473 raw38473Labels = mixedMoment B node928 node928Labels := by
  calc
    mixedMoment B raw38473 raw38473Labels = mixedMoment B raw38473step0 raw38473step0Labels := by
      have ha : raw38473step0 = raw38473 := by apply Matrix.ext; unfold raw38473step0 raw38473; decide +kernel
      have hl : raw38473Labels = labelEmbedding2 ∘ raw38473step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38473 raw38473Labels raw38473step0Labels labelEmbedding2 hl
    _ = mixedMoment B node928 node928Labels := by rfl

def raw38474 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw38474Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38474step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw38474step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38474step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw38474step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38474 raw38474Labels = mixedMoment B node1677 node1677Labels := by
  calc
    mixedMoment B raw38474 raw38474Labels = mixedMoment B raw38474step0 raw38474step0Labels := by
      have ha : raw38474step0 = (fun i j => raw38474 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38474step0 raw38474; decide +kernel
      have hl : raw38474step0Labels = raw38474Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38474 raw38474Labels permutation31 permutation7
    mixedMoment B raw38474step0 raw38474step0Labels = mixedMoment B raw38474step1 raw38474step1Labels := by
      have ha : raw38474step1 = raw38474step0 := by apply Matrix.ext; unfold raw38474step1 raw38474step0; decide +kernel
      have hl : raw38474step0Labels = labelEmbedding4 ∘ raw38474step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38474step0 raw38474step0Labels raw38474step1Labels labelEmbedding4 hl
    _ = mixedMoment B node1677 node1677Labels := by rfl

def raw38475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38475Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38475step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38475step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38475 raw38475Labels = mixedMoment B node929 node929Labels := by
  calc
    mixedMoment B raw38475 raw38475Labels = mixedMoment B raw38475step0 raw38475step0Labels := by
      have ha : raw38475step0 = raw38475 := by apply Matrix.ext; unfold raw38475step0 raw38475; decide +kernel
      have hl : raw38475Labels = labelEmbedding2 ∘ raw38475step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38475 raw38475Labels raw38475step0Labels labelEmbedding2 hl
    _ = mixedMoment B node929 node929Labels := by rfl

def raw38476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38476Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw38476step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38476step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38476step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38476step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38476step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38476 raw38476Labels = mixedMoment B node1680 node1680Labels := by
  calc
    mixedMoment B raw38476 raw38476Labels = mixedMoment B raw38476step0 raw38476step0Labels := by
      have ha : raw38476step0 = (fun i j => raw38476 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38476step0 raw38476; decide +kernel
      have hl : raw38476step0Labels = raw38476Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38476 raw38476Labels permutation170 permutation7
    mixedMoment B raw38476step0 raw38476step0Labels = mixedMoment B raw38476step1 raw38476step1Labels := by
      have ha : raw38476step1 = -raw38476step0 := by apply Matrix.ext; change ∀ i j, raw38476step1 i j = -(raw38476step0 i j); unfold raw38476step1 raw38476step0; decide +kernel
      have hl : raw38476step1Labels = raw38476step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38476step1 raw38476step1Labels = mixedMoment B raw38476step2 raw38476step2Labels := by
      have ha : raw38476step2 = raw38476step1 := by apply Matrix.ext; unfold raw38476step2 raw38476step1; decide +kernel
      have hl : raw38476step1Labels = labelEmbedding4 ∘ raw38476step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38476step1 raw38476step1Labels raw38476step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1680 node1680Labels := by rfl

def raw38477 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38477Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38477step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38477 raw38477Labels = mixedMoment B node930 node930Labels := by
  calc
    mixedMoment B raw38477 raw38477Labels = mixedMoment B raw38477step0 raw38477step0Labels := by
      have ha : raw38477step0 = raw38477 := by apply Matrix.ext; unfold raw38477step0 raw38477; decide +kernel
      have hl : raw38477Labels = labelEmbedding2 ∘ raw38477step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38477 raw38477Labels raw38477step0Labels labelEmbedding2 hl
    _ = mixedMoment B node930 node930Labels := by rfl

def raw38478 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38478Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw38478step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw38478step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38478step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw38478step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38478 raw38478Labels = mixedMoment B node1690 node1690Labels := by
  calc
    mixedMoment B raw38478 raw38478Labels = mixedMoment B raw38478step0 raw38478step0Labels := by
      have ha : raw38478step0 = (fun i j => raw38478 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38478step0 raw38478; decide +kernel
      have hl : raw38478step0Labels = raw38478Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38478 raw38478Labels permutation32 permutation7
    mixedMoment B raw38478step0 raw38478step0Labels = mixedMoment B raw38478step1 raw38478step1Labels := by
      have ha : raw38478step1 = -raw38478step0 := by apply Matrix.ext; change ∀ i j, raw38478step1 i j = -(raw38478step0 i j); unfold raw38478step1 raw38478step0; decide +kernel
      have hl : raw38478step1Labels = raw38478step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38478step1 raw38478step1Labels = mixedMoment B raw38478step2 raw38478step2Labels := by
      have ha : raw38478step2 = raw38478step1 := by apply Matrix.ext; unfold raw38478step2 raw38478step1; decide +kernel
      have hl : raw38478step1Labels = labelEmbedding4 ∘ raw38478step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38478step1 raw38478step1Labels raw38478step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1690 node1690Labels := by rfl

def raw38479 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38479Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38479step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38479 raw38479Labels = mixedMoment B node932 node932Labels := by
  calc
    mixedMoment B raw38479 raw38479Labels = mixedMoment B raw38479step0 raw38479step0Labels := by
      have ha : raw38479step0 = raw38479 := by apply Matrix.ext; unfold raw38479step0 raw38479; decide +kernel
      have hl : raw38479Labels = labelEmbedding2 ∘ raw38479step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38479 raw38479Labels raw38479step0Labels labelEmbedding2 hl
    _ = mixedMoment B node932 node932Labels := by rfl

def raw38480 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38480Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw38480step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38480step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw38480step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38480step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw38480step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38480 raw38480Labels = mixedMoment B node1681 node1681Labels := by
  calc
    mixedMoment B raw38480 raw38480Labels = mixedMoment B raw38480step0 raw38480step0Labels := by
      have ha : raw38480step0 = (fun i j => raw38480 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38480step0 raw38480; decide +kernel
      have hl : raw38480step0Labels = raw38480Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38480 raw38480Labels permutation34 permutation7
    mixedMoment B raw38480step0 raw38480step0Labels = mixedMoment B raw38480step1 raw38480step1Labels := by
      have ha : raw38480step1 = -raw38480step0 := by apply Matrix.ext; change ∀ i j, raw38480step1 i j = -(raw38480step0 i j); unfold raw38480step1 raw38480step0; decide +kernel
      have hl : raw38480step1Labels = raw38480step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38480step1 raw38480step1Labels = mixedMoment B raw38480step2 raw38480step2Labels := by
      have ha : raw38480step2 = raw38480step1 := by apply Matrix.ext; unfold raw38480step2 raw38480step1; decide +kernel
      have hl : raw38480step1Labels = labelEmbedding4 ∘ raw38480step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38480step1 raw38480step1Labels raw38480step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1681 node1681Labels := by rfl

def raw38481 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38481Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38481step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38481 raw38481Labels = mixedMoment B node933 node933Labels := by
  calc
    mixedMoment B raw38481 raw38481Labels = mixedMoment B raw38481step0 raw38481step0Labels := by
      have ha : raw38481step0 = raw38481 := by apply Matrix.ext; unfold raw38481step0 raw38481; decide +kernel
      have hl : raw38481Labels = labelEmbedding2 ∘ raw38481step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38481 raw38481Labels raw38481step0Labels labelEmbedding2 hl
    _ = mixedMoment B node933 node933Labels := by rfl

def raw38482 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38482Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw38482step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38482step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw38482step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38482step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw38482step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38482 raw38482Labels = mixedMoment B node1691 node1691Labels := by
  calc
    mixedMoment B raw38482 raw38482Labels = mixedMoment B raw38482step0 raw38482step0Labels := by
      have ha : raw38482step0 = (fun i j => raw38482 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38482step0 raw38482; decide +kernel
      have hl : raw38482step0Labels = raw38482Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38482 raw38482Labels permutation32 permutation7
    mixedMoment B raw38482step0 raw38482step0Labels = mixedMoment B raw38482step1 raw38482step1Labels := by
      have ha : raw38482step1 = -raw38482step0 := by apply Matrix.ext; change ∀ i j, raw38482step1 i j = -(raw38482step0 i j); unfold raw38482step1 raw38482step0; decide +kernel
      have hl : raw38482step1Labels = raw38482step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38482step1 raw38482step1Labels = mixedMoment B raw38482step2 raw38482step2Labels := by
      have ha : raw38482step2 = raw38482step1 := by apply Matrix.ext; unfold raw38482step2 raw38482step1; decide +kernel
      have hl : raw38482step1Labels = labelEmbedding4 ∘ raw38482step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38482step1 raw38482step1Labels raw38482step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1691 node1691Labels := by rfl

def raw38483 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw38483Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38483step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw38483step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38483 raw38483Labels = mixedMoment B node934 node934Labels := by
  calc
    mixedMoment B raw38483 raw38483Labels = mixedMoment B raw38483step0 raw38483step0Labels := by
      have ha : raw38483step0 = raw38483 := by apply Matrix.ext; unfold raw38483step0 raw38483; decide +kernel
      have hl : raw38483Labels = labelEmbedding2 ∘ raw38483step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38483 raw38483Labels raw38483step0Labels labelEmbedding2 hl
    _ = mixedMoment B node934 node934Labels := by rfl

def raw38484 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw38484Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38484step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-2, -2, 4]]
def raw38484step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38484step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw38484step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38484step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw38484step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38484 raw38484Labels = mixedMoment B node1692 node1692Labels := by
  calc
    mixedMoment B raw38484 raw38484Labels = mixedMoment B raw38484step0 raw38484step0Labels := by
      have ha : raw38484step0 = (fun i j => raw38484 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38484step0 raw38484; decide +kernel
      have hl : raw38484step0Labels = raw38484Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38484 raw38484Labels permutation8 permutation7
    mixedMoment B raw38484step0 raw38484step0Labels = mixedMoment B raw38484step1 raw38484step1Labels := by
      have ha : raw38484step1 = -raw38484step0 := by apply Matrix.ext; change ∀ i j, raw38484step1 i j = -(raw38484step0 i j); unfold raw38484step1 raw38484step0; decide +kernel
      have hl : raw38484step1Labels = raw38484step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38484step1 raw38484step1Labels = mixedMoment B raw38484step2 raw38484step2Labels := by
      have ha : raw38484step2 = raw38484step1 := by apply Matrix.ext; unfold raw38484step2 raw38484step1; decide +kernel
      have hl : raw38484step1Labels = labelEmbedding4 ∘ raw38484step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38484step1 raw38484step1Labels raw38484step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1692 node1692Labels := by rfl

def raw38485 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw38485Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38485step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw38485step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38485 raw38485Labels = mixedMoment B node937 node937Labels := by
  calc
    mixedMoment B raw38485 raw38485Labels = mixedMoment B raw38485step0 raw38485step0Labels := by
      have ha : raw38485step0 = raw38485 := by apply Matrix.ext; unfold raw38485step0 raw38485; decide +kernel
      have hl : raw38485Labels = labelEmbedding2 ∘ raw38485step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38485 raw38485Labels raw38485step0Labels labelEmbedding2 hl
    _ = mixedMoment B node937 node937Labels := by rfl

def raw38486 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw38486Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38486step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-3, 0, 3]]
def raw38486step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38486step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw38486step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38486step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw38486step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38486 raw38486Labels = mixedMoment B node1683 node1683Labels := by
  calc
    mixedMoment B raw38486 raw38486Labels = mixedMoment B raw38486step0 raw38486step0Labels := by
      have ha : raw38486step0 = (fun i j => raw38486 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38486step0 raw38486; decide +kernel
      have hl : raw38486step0Labels = raw38486Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38486 raw38486Labels permutation8 permutation7
    mixedMoment B raw38486step0 raw38486step0Labels = mixedMoment B raw38486step1 raw38486step1Labels := by
      have ha : raw38486step1 = -raw38486step0 := by apply Matrix.ext; change ∀ i j, raw38486step1 i j = -(raw38486step0 i j); unfold raw38486step1 raw38486step0; decide +kernel
      have hl : raw38486step1Labels = raw38486step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38486step1 raw38486step1Labels = mixedMoment B raw38486step2 raw38486step2Labels := by
      have ha : raw38486step2 = raw38486step1 := by apply Matrix.ext; unfold raw38486step2 raw38486step1; decide +kernel
      have hl : raw38486step1Labels = labelEmbedding4 ∘ raw38486step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38486step1 raw38486step1Labels raw38486step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1683 node1683Labels := by rfl

def raw38487 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw38487Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38487step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw38487step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38487 raw38487Labels = mixedMoment B node938 node938Labels := by
  calc
    mixedMoment B raw38487 raw38487Labels = mixedMoment B raw38487step0 raw38487step0Labels := by
      have ha : raw38487step0 = raw38487 := by apply Matrix.ext; unfold raw38487step0 raw38487; decide +kernel
      have hl : raw38487Labels = labelEmbedding2 ∘ raw38487step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38487 raw38487Labels raw38487step0Labels labelEmbedding2 hl
    _ = mixedMoment B node938 node938Labels := by rfl

def raw38488 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw38488Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38488step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw38488step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38488step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw38488step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38488step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw38488step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38488 raw38488Labels = mixedMoment B node1693 node1693Labels := by
  calc
    mixedMoment B raw38488 raw38488Labels = mixedMoment B raw38488step0 raw38488step0Labels := by
      have ha : raw38488step0 = (fun i j => raw38488 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38488step0 raw38488; decide +kernel
      have hl : raw38488step0Labels = raw38488Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38488 raw38488Labels permutation8 permutation7
    mixedMoment B raw38488step0 raw38488step0Labels = mixedMoment B raw38488step1 raw38488step1Labels := by
      have ha : raw38488step1 = -raw38488step0 := by apply Matrix.ext; change ∀ i j, raw38488step1 i j = -(raw38488step0 i j); unfold raw38488step1 raw38488step0; decide +kernel
      have hl : raw38488step1Labels = raw38488step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38488step1 raw38488step1Labels = mixedMoment B raw38488step2 raw38488step2Labels := by
      have ha : raw38488step2 = raw38488step1 := by apply Matrix.ext; unfold raw38488step2 raw38488step1; decide +kernel
      have hl : raw38488step1Labels = labelEmbedding4 ∘ raw38488step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38488step1 raw38488step1Labels raw38488step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1693 node1693Labels := by rfl

def raw38489 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw38489Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38489step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw38489step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38489 raw38489Labels = mixedMoment B node939 node939Labels := by
  calc
    mixedMoment B raw38489 raw38489Labels = mixedMoment B raw38489step0 raw38489step0Labels := by
      have ha : raw38489step0 = raw38489 := by apply Matrix.ext; unfold raw38489step0 raw38489; decide +kernel
      have hl : raw38489Labels = labelEmbedding2 ∘ raw38489step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38489 raw38489Labels raw38489step0Labels labelEmbedding2 hl
    _ = mixedMoment B node939 node939Labels := by rfl

def raw38490 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw38490Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38490step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw38490step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38490step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw38490step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38490step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw38490step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38490 raw38490Labels = mixedMoment B node1694 node1694Labels := by
  calc
    mixedMoment B raw38490 raw38490Labels = mixedMoment B raw38490step0 raw38490step0Labels := by
      have ha : raw38490step0 = (fun i j => raw38490 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38490step0 raw38490; decide +kernel
      have hl : raw38490step0Labels = raw38490Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38490 raw38490Labels permutation9 permutation7
    mixedMoment B raw38490step0 raw38490step0Labels = mixedMoment B raw38490step1 raw38490step1Labels := by
      have ha : raw38490step1 = -raw38490step0 := by apply Matrix.ext; change ∀ i j, raw38490step1 i j = -(raw38490step0 i j); unfold raw38490step1 raw38490step0; decide +kernel
      have hl : raw38490step1Labels = raw38490step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38490step1 raw38490step1Labels = mixedMoment B raw38490step2 raw38490step2Labels := by
      have ha : raw38490step2 = raw38490step1 := by apply Matrix.ext; unfold raw38490step2 raw38490step1; decide +kernel
      have hl : raw38490step1Labels = labelEmbedding4 ∘ raw38490step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38490step1 raw38490step1Labels raw38490step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1694 node1694Labels := by rfl

def raw38491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38491Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38491step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38491 raw38491Labels = mixedMoment B node955 node955Labels := by
  calc
    mixedMoment B raw38491 raw38491Labels = mixedMoment B raw38491step0 raw38491step0Labels := by
      have ha : raw38491step0 = raw38491 := by apply Matrix.ext; unfold raw38491step0 raw38491; decide +kernel
      have hl : raw38491Labels = labelEmbedding2 ∘ raw38491step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38491 raw38491Labels raw38491step0Labels labelEmbedding2 hl
    _ = mixedMoment B node955 node955Labels := by rfl

def raw38492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38492Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38492step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw38492step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38492step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38492step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38492step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw38492step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38492 raw38492Labels = mixedMoment B node1542 node1542Labels := by
  calc
    mixedMoment B raw38492 raw38492Labels = mixedMoment B raw38492step0 raw38492step0Labels := by
      have ha : raw38492step0 = (fun i j => raw38492 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38492step0 raw38492; decide +kernel
      have hl : raw38492step0Labels = raw38492Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38492 raw38492Labels permutation152 permutation7
    mixedMoment B raw38492step0 raw38492step0Labels = mixedMoment B raw38492step1 raw38492step1Labels := by
      have ha : raw38492step1 = -raw38492step0 := by apply Matrix.ext; change ∀ i j, raw38492step1 i j = -(raw38492step0 i j); unfold raw38492step1 raw38492step0; decide +kernel
      have hl : raw38492step1Labels = raw38492step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38492step1 raw38492step1Labels = mixedMoment B raw38492step2 raw38492step2Labels := by
      have ha : raw38492step2 = raw38492step1 := by apply Matrix.ext; unfold raw38492step2 raw38492step1; decide +kernel
      have hl : raw38492step1Labels = labelEmbedding4 ∘ raw38492step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38492step1 raw38492step1Labels raw38492step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1542 node1542Labels := by rfl

def raw38493 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw38493Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw38493step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38493 raw38493Labels = mixedMoment B node956 node956Labels := by
  calc
    mixedMoment B raw38493 raw38493Labels = mixedMoment B raw38493step0 raw38493step0Labels := by
      have ha : raw38493step0 = raw38493 := by apply Matrix.ext; unfold raw38493step0 raw38493; decide +kernel
      have hl : raw38493Labels = labelEmbedding2 ∘ raw38493step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38493 raw38493Labels raw38493step0Labels labelEmbedding2 hl
    _ = mixedMoment B node956 node956Labels := by rfl

def raw38494 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw38494Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw38494step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw38494step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38494step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw38494step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38494 raw38494Labels = mixedMoment B node1543 node1543Labels := by
  calc
    mixedMoment B raw38494 raw38494Labels = mixedMoment B raw38494step0 raw38494step0Labels := by
      have ha : raw38494step0 = (fun i j => raw38494 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38494step0 raw38494; decide +kernel
      have hl : raw38494step0Labels = raw38494Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38494 raw38494Labels permutation32 permutation7
    mixedMoment B raw38494step0 raw38494step0Labels = mixedMoment B raw38494step1 raw38494step1Labels := by
      have ha : raw38494step1 = -raw38494step0 := by apply Matrix.ext; change ∀ i j, raw38494step1 i j = -(raw38494step0 i j); unfold raw38494step1 raw38494step0; decide +kernel
      have hl : raw38494step1Labels = raw38494step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38494step1 raw38494step1Labels = mixedMoment B raw38494step2 raw38494step2Labels := by
      have ha : raw38494step2 = raw38494step1 := by apply Matrix.ext; unfold raw38494step2 raw38494step1; decide +kernel
      have hl : raw38494step1Labels = labelEmbedding4 ∘ raw38494step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38494step1 raw38494step1Labels raw38494step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1543 node1543Labels := by rfl

def raw38495 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw38495Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw38495step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38495 raw38495Labels = mixedMoment B node957 node957Labels := by
  calc
    mixedMoment B raw38495 raw38495Labels = mixedMoment B raw38495step0 raw38495step0Labels := by
      have ha : raw38495step0 = raw38495 := by apply Matrix.ext; unfold raw38495step0 raw38495; decide +kernel
      have hl : raw38495Labels = labelEmbedding2 ∘ raw38495step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38495 raw38495Labels raw38495step0Labels labelEmbedding2 hl
    _ = mixedMoment B node957 node957Labels := by rfl

def raw38496 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw38496Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw38496step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw38496step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38496step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw38496step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38496 raw38496Labels = mixedMoment B node1544 node1544Labels := by
  calc
    mixedMoment B raw38496 raw38496Labels = mixedMoment B raw38496step0 raw38496step0Labels := by
      have ha : raw38496step0 = (fun i j => raw38496 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38496step0 raw38496; decide +kernel
      have hl : raw38496step0Labels = raw38496Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38496 raw38496Labels permutation32 permutation7
    mixedMoment B raw38496step0 raw38496step0Labels = mixedMoment B raw38496step1 raw38496step1Labels := by
      have ha : raw38496step1 = -raw38496step0 := by apply Matrix.ext; change ∀ i j, raw38496step1 i j = -(raw38496step0 i j); unfold raw38496step1 raw38496step0; decide +kernel
      have hl : raw38496step1Labels = raw38496step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38496step1 raw38496step1Labels = mixedMoment B raw38496step2 raw38496step2Labels := by
      have ha : raw38496step2 = raw38496step1 := by apply Matrix.ext; unfold raw38496step2 raw38496step1; decide +kernel
      have hl : raw38496step1Labels = labelEmbedding4 ∘ raw38496step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38496step1 raw38496step1Labels raw38496step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1544 node1544Labels := by rfl

def raw38497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38497Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38497step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38497 raw38497Labels = mixedMoment B node958 node958Labels := by
  calc
    mixedMoment B raw38497 raw38497Labels = mixedMoment B raw38497step0 raw38497step0Labels := by
      have ha : raw38497step0 = raw38497 := by apply Matrix.ext; unfold raw38497step0 raw38497; decide +kernel
      have hl : raw38497Labels = labelEmbedding2 ∘ raw38497step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38497 raw38497Labels raw38497step0Labels labelEmbedding2 hl
    _ = mixedMoment B node958 node958Labels := by rfl

def raw38498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38498Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw38498step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38498step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38498step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38498step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38498step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38498 raw38498Labels = mixedMoment B node1545 node1545Labels := by
  calc
    mixedMoment B raw38498 raw38498Labels = mixedMoment B raw38498step0 raw38498step0Labels := by
      have ha : raw38498step0 = (fun i j => raw38498 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38498step0 raw38498; decide +kernel
      have hl : raw38498step0Labels = raw38498Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38498 raw38498Labels permutation152 permutation7
    mixedMoment B raw38498step0 raw38498step0Labels = mixedMoment B raw38498step1 raw38498step1Labels := by
      have ha : raw38498step1 = -raw38498step0 := by apply Matrix.ext; change ∀ i j, raw38498step1 i j = -(raw38498step0 i j); unfold raw38498step1 raw38498step0; decide +kernel
      have hl : raw38498step1Labels = raw38498step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38498step1 raw38498step1Labels = mixedMoment B raw38498step2 raw38498step2Labels := by
      have ha : raw38498step2 = raw38498step1 := by apply Matrix.ext; unfold raw38498step2 raw38498step1; decide +kernel
      have hl : raw38498step1Labels = labelEmbedding4 ∘ raw38498step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38498step1 raw38498step1Labels raw38498step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1545 node1545Labels := by rfl

def raw38499 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw38499Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw38499step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38499 raw38499Labels = mixedMoment B node959 node959Labels := by
  calc
    mixedMoment B raw38499 raw38499Labels = mixedMoment B raw38499step0 raw38499step0Labels := by
      have ha : raw38499step0 = raw38499 := by apply Matrix.ext; unfold raw38499step0 raw38499; decide +kernel
      have hl : raw38499Labels = labelEmbedding2 ∘ raw38499step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38499 raw38499Labels raw38499step0Labels labelEmbedding2 hl
    _ = mixedMoment B node959 node959Labels := by rfl

def raw38500 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw38500Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw38500step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38500step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38500step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38500step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38500step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38500 raw38500Labels = mixedMoment B node1546 node1546Labels := by
  calc
    mixedMoment B raw38500 raw38500Labels = mixedMoment B raw38500step0 raw38500step0Labels := by
      have ha : raw38500step0 = (fun i j => raw38500 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38500step0 raw38500; decide +kernel
      have hl : raw38500step0Labels = raw38500Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38500 raw38500Labels permutation32 permutation7
    mixedMoment B raw38500step0 raw38500step0Labels = mixedMoment B raw38500step1 raw38500step1Labels := by
      have ha : raw38500step1 = -raw38500step0 := by apply Matrix.ext; change ∀ i j, raw38500step1 i j = -(raw38500step0 i j); unfold raw38500step1 raw38500step0; decide +kernel
      have hl : raw38500step1Labels = raw38500step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38500step1 raw38500step1Labels = mixedMoment B raw38500step2 raw38500step2Labels := by
      have ha : raw38500step2 = raw38500step1 := by apply Matrix.ext; unfold raw38500step2 raw38500step1; decide +kernel
      have hl : raw38500step1Labels = labelEmbedding4 ∘ raw38500step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38500step1 raw38500step1Labels raw38500step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1546 node1546Labels := by rfl

def raw38501 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw38501Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw38501step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38501 raw38501Labels = mixedMoment B node960 node960Labels := by
  calc
    mixedMoment B raw38501 raw38501Labels = mixedMoment B raw38501step0 raw38501step0Labels := by
      have ha : raw38501step0 = raw38501 := by apply Matrix.ext; unfold raw38501step0 raw38501; decide +kernel
      have hl : raw38501Labels = labelEmbedding2 ∘ raw38501step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38501 raw38501Labels raw38501step0Labels labelEmbedding2 hl
    _ = mixedMoment B node960 node960Labels := by rfl

def raw38502 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw38502Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw38502step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38502step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38502step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38502step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38502 raw38502Labels = mixedMoment B node1547 node1547Labels := by
  calc
    mixedMoment B raw38502 raw38502Labels = mixedMoment B raw38502step0 raw38502step0Labels := by
      have ha : raw38502step0 = (fun i j => raw38502 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38502step0 raw38502; decide +kernel
      have hl : raw38502step0Labels = raw38502Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38502 raw38502Labels permutation32 permutation7
    mixedMoment B raw38502step0 raw38502step0Labels = mixedMoment B raw38502step1 raw38502step1Labels := by
      have ha : raw38502step1 = -raw38502step0 := by apply Matrix.ext; change ∀ i j, raw38502step1 i j = -(raw38502step0 i j); unfold raw38502step1 raw38502step0; decide +kernel
      have hl : raw38502step1Labels = raw38502step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38502step1 raw38502step1Labels = mixedMoment B raw38502step2 raw38502step2Labels := by
      have ha : raw38502step2 = raw38502step1 := by apply Matrix.ext; unfold raw38502step2 raw38502step1; decide +kernel
      have hl : raw38502step1Labels = labelEmbedding4 ∘ raw38502step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38502step1 raw38502step1Labels raw38502step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1547 node1547Labels := by rfl

def raw38503 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 1, -2], ![3, 0, -3]]
def raw38503Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38503step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 1, -2], ![3, 0, -3]]
def raw38503step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38503 raw38503Labels = mixedMoment B node962 node962Labels := by
  calc
    mixedMoment B raw38503 raw38503Labels = mixedMoment B raw38503step0 raw38503step0Labels := by
      have ha : raw38503step0 = raw38503 := by apply Matrix.ext; unfold raw38503step0 raw38503; decide +kernel
      have hl : raw38503Labels = labelEmbedding2 ∘ raw38503step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38503 raw38503Labels raw38503step0Labels labelEmbedding2 hl
    _ = mixedMoment B node962 node962Labels := by rfl

def raw38504 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 1, -2], ![3, 0, -3]]
def raw38504Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38504step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-2, 1, 1], ![-3, 0, 3]]
def raw38504step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38504step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![2, -1, -1], ![3, 0, -3]]
def raw38504step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38504step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![2, -1, -1], ![3, 0, -3]]
def raw38504step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38504 raw38504Labels = mixedMoment B node1548 node1548Labels := by
  calc
    mixedMoment B raw38504 raw38504Labels = mixedMoment B raw38504step0 raw38504step0Labels := by
      have ha : raw38504step0 = (fun i j => raw38504 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38504step0 raw38504; decide +kernel
      have hl : raw38504step0Labels = raw38504Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38504 raw38504Labels permutation8 permutation7
    mixedMoment B raw38504step0 raw38504step0Labels = mixedMoment B raw38504step1 raw38504step1Labels := by
      have ha : raw38504step1 = -raw38504step0 := by apply Matrix.ext; change ∀ i j, raw38504step1 i j = -(raw38504step0 i j); unfold raw38504step1 raw38504step0; decide +kernel
      have hl : raw38504step1Labels = raw38504step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38504step1 raw38504step1Labels = mixedMoment B raw38504step2 raw38504step2Labels := by
      have ha : raw38504step2 = raw38504step1 := by apply Matrix.ext; unfold raw38504step2 raw38504step1; decide +kernel
      have hl : raw38504step1Labels = labelEmbedding4 ∘ raw38504step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38504step1 raw38504step1Labels raw38504step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1548 node1548Labels := by rfl

def raw38505 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![2, 0, -2], ![2, 1, -3]]
def raw38505Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38505step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![2, 0, -2], ![2, 1, -3]]
def raw38505step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38505 raw38505Labels = mixedMoment B node963 node963Labels := by
  calc
    mixedMoment B raw38505 raw38505Labels = mixedMoment B raw38505step0 raw38505step0Labels := by
      have ha : raw38505step0 = raw38505 := by apply Matrix.ext; unfold raw38505step0 raw38505; decide +kernel
      have hl : raw38505Labels = labelEmbedding2 ∘ raw38505step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38505 raw38505Labels raw38505step0Labels labelEmbedding2 hl
    _ = mixedMoment B node963 node963Labels := by rfl

def raw38506 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![2, 0, -2], ![2, 1, -3]]
def raw38506Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38506step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-2, 0, 2], ![-3, 1, 2]]
def raw38506step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38506step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![2, 0, -2], ![3, -1, -2]]
def raw38506step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38506step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![2, 0, -2], ![3, -1, -2]]
def raw38506step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38506 raw38506Labels = mixedMoment B node1549 node1549Labels := by
  calc
    mixedMoment B raw38506 raw38506Labels = mixedMoment B raw38506step0 raw38506step0Labels := by
      have ha : raw38506step0 = (fun i j => raw38506 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38506step0 raw38506; decide +kernel
      have hl : raw38506step0Labels = raw38506Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38506 raw38506Labels permutation8 permutation7
    mixedMoment B raw38506step0 raw38506step0Labels = mixedMoment B raw38506step1 raw38506step1Labels := by
      have ha : raw38506step1 = -raw38506step0 := by apply Matrix.ext; change ∀ i j, raw38506step1 i j = -(raw38506step0 i j); unfold raw38506step1 raw38506step0; decide +kernel
      have hl : raw38506step1Labels = raw38506step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38506step1 raw38506step1Labels = mixedMoment B raw38506step2 raw38506step2Labels := by
      have ha : raw38506step2 = raw38506step1 := by apply Matrix.ext; unfold raw38506step2 raw38506step1; decide +kernel
      have hl : raw38506step1Labels = labelEmbedding4 ∘ raw38506step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38506step1 raw38506step1Labels raw38506step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1549 node1549Labels := by rfl

def raw38507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw38507Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw38507step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38507 raw38507Labels = mixedMoment B node964 node964Labels := by
  calc
    mixedMoment B raw38507 raw38507Labels = mixedMoment B raw38507step0 raw38507step0Labels := by
      have ha : raw38507step0 = raw38507 := by apply Matrix.ext; unfold raw38507step0 raw38507; decide +kernel
      have hl : raw38507Labels = labelEmbedding2 ∘ raw38507step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38507 raw38507Labels raw38507step0Labels labelEmbedding2 hl
    _ = mixedMoment B node964 node964Labels := by rfl

def raw38508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw38508Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw38508step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38508step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw38508step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38508step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw38508step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38508 raw38508Labels = mixedMoment B node1580 node1580Labels := by
  calc
    mixedMoment B raw38508 raw38508Labels = mixedMoment B raw38508step0 raw38508step0Labels := by
      have ha : raw38508step0 = (fun i j => raw38508 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38508step0 raw38508; decide +kernel
      have hl : raw38508step0Labels = raw38508Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38508 raw38508Labels permutation152 permutation7
    mixedMoment B raw38508step0 raw38508step0Labels = mixedMoment B raw38508step1 raw38508step1Labels := by
      have ha : raw38508step1 = -raw38508step0 := by apply Matrix.ext; change ∀ i j, raw38508step1 i j = -(raw38508step0 i j); unfold raw38508step1 raw38508step0; decide +kernel
      have hl : raw38508step1Labels = raw38508step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38508step1 raw38508step1Labels = mixedMoment B raw38508step2 raw38508step2Labels := by
      have ha : raw38508step2 = raw38508step1 := by apply Matrix.ext; unfold raw38508step2 raw38508step1; decide +kernel
      have hl : raw38508step1Labels = labelEmbedding4 ∘ raw38508step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38508step1 raw38508step1Labels raw38508step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1580 node1580Labels := by rfl

def raw38509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw38509Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw38509step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38509 raw38509Labels = mixedMoment B node965 node965Labels := by
  calc
    mixedMoment B raw38509 raw38509Labels = mixedMoment B raw38509step0 raw38509step0Labels := by
      have ha : raw38509step0 = raw38509 := by apply Matrix.ext; unfold raw38509step0 raw38509; decide +kernel
      have hl : raw38509Labels = labelEmbedding2 ∘ raw38509step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38509 raw38509Labels raw38509step0Labels labelEmbedding2 hl
    _ = mixedMoment B node965 node965Labels := by rfl

def raw38510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw38510Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38510step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw38510step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38510step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw38510step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38510step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw38510step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38510 raw38510Labels = mixedMoment B node1581 node1581Labels := by
  calc
    mixedMoment B raw38510 raw38510Labels = mixedMoment B raw38510step0 raw38510step0Labels := by
      have ha : raw38510step0 = (fun i j => raw38510 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38510step0 raw38510; decide +kernel
      have hl : raw38510step0Labels = raw38510Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38510 raw38510Labels permutation152 permutation7
    mixedMoment B raw38510step0 raw38510step0Labels = mixedMoment B raw38510step1 raw38510step1Labels := by
      have ha : raw38510step1 = -raw38510step0 := by apply Matrix.ext; change ∀ i j, raw38510step1 i j = -(raw38510step0 i j); unfold raw38510step1 raw38510step0; decide +kernel
      have hl : raw38510step1Labels = raw38510step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38510step1 raw38510step1Labels = mixedMoment B raw38510step2 raw38510step2Labels := by
      have ha : raw38510step2 = raw38510step1 := by apply Matrix.ext; unfold raw38510step2 raw38510step1; decide +kernel
      have hl : raw38510step1Labels = labelEmbedding4 ∘ raw38510step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38510step1 raw38510step1Labels raw38510step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1581 node1581Labels := by rfl

def raw38511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw38511Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38511step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw38511step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38511 raw38511Labels = mixedMoment B node966 node966Labels := by
  calc
    mixedMoment B raw38511 raw38511Labels = mixedMoment B raw38511step0 raw38511step0Labels := by
      have ha : raw38511step0 = raw38511 := by apply Matrix.ext; unfold raw38511step0 raw38511; decide +kernel
      have hl : raw38511Labels = labelEmbedding2 ∘ raw38511step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38511 raw38511Labels raw38511step0Labels labelEmbedding2 hl
    _ = mixedMoment B node966 node966Labels := by rfl

def raw38512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw38512Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw38512step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38512step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38512step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38512step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38512step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38512 raw38512Labels = mixedMoment B node1582 node1582Labels := by
  calc
    mixedMoment B raw38512 raw38512Labels = mixedMoment B raw38512step0 raw38512step0Labels := by
      have ha : raw38512step0 = (fun i j => raw38512 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38512step0 raw38512; decide +kernel
      have hl : raw38512step0Labels = raw38512Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38512 raw38512Labels permutation152 permutation7
    mixedMoment B raw38512step0 raw38512step0Labels = mixedMoment B raw38512step1 raw38512step1Labels := by
      have ha : raw38512step1 = -raw38512step0 := by apply Matrix.ext; change ∀ i j, raw38512step1 i j = -(raw38512step0 i j); unfold raw38512step1 raw38512step0; decide +kernel
      have hl : raw38512step1Labels = raw38512step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38512step1 raw38512step1Labels = mixedMoment B raw38512step2 raw38512step2Labels := by
      have ha : raw38512step2 = raw38512step1 := by apply Matrix.ext; unfold raw38512step2 raw38512step1; decide +kernel
      have hl : raw38512step1Labels = labelEmbedding4 ∘ raw38512step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38512step1 raw38512step1Labels raw38512step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1582 node1582Labels := by rfl

def raw38513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw38513Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw38513step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38513 raw38513Labels = mixedMoment B node967 node967Labels := by
  calc
    mixedMoment B raw38513 raw38513Labels = mixedMoment B raw38513step0 raw38513step0Labels := by
      have ha : raw38513step0 = raw38513 := by apply Matrix.ext; unfold raw38513step0 raw38513; decide +kernel
      have hl : raw38513Labels = labelEmbedding2 ∘ raw38513step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38513 raw38513Labels raw38513step0Labels labelEmbedding2 hl
    _ = mixedMoment B node967 node967Labels := by rfl

def raw38514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw38514Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38514step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw38514step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38514step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38514step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38514step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38514step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38514 raw38514Labels = mixedMoment B node1583 node1583Labels := by
  calc
    mixedMoment B raw38514 raw38514Labels = mixedMoment B raw38514step0 raw38514step0Labels := by
      have ha : raw38514step0 = (fun i j => raw38514 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38514step0 raw38514; decide +kernel
      have hl : raw38514step0Labels = raw38514Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38514 raw38514Labels permutation152 permutation7
    mixedMoment B raw38514step0 raw38514step0Labels = mixedMoment B raw38514step1 raw38514step1Labels := by
      have ha : raw38514step1 = -raw38514step0 := by apply Matrix.ext; change ∀ i j, raw38514step1 i j = -(raw38514step0 i j); unfold raw38514step1 raw38514step0; decide +kernel
      have hl : raw38514step1Labels = raw38514step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38514step1 raw38514step1Labels = mixedMoment B raw38514step2 raw38514step2Labels := by
      have ha : raw38514step2 = raw38514step1 := by apply Matrix.ext; unfold raw38514step2 raw38514step1; decide +kernel
      have hl : raw38514step1Labels = labelEmbedding4 ∘ raw38514step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38514step1 raw38514step1Labels raw38514step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1583 node1583Labels := by rfl

def raw38515 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def raw38515Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def raw38515step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38515 raw38515Labels = mixedMoment B node969 node969Labels := by
  calc
    mixedMoment B raw38515 raw38515Labels = mixedMoment B raw38515step0 raw38515step0Labels := by
      have ha : raw38515step0 = raw38515 := by apply Matrix.ext; unfold raw38515step0 raw38515; decide +kernel
      have hl : raw38515Labels = labelEmbedding2 ∘ raw38515step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38515 raw38515Labels raw38515step0Labels labelEmbedding2 hl
    _ = mixedMoment B node969 node969Labels := by rfl

def raw38516 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def raw38516Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-3, 0, 3]]
def raw38516step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38516step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, 0, -3]]
def raw38516step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38516step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, 0, -3]]
def raw38516step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38516 raw38516Labels = mixedMoment B node1584 node1584Labels := by
  calc
    mixedMoment B raw38516 raw38516Labels = mixedMoment B raw38516step0 raw38516step0Labels := by
      have ha : raw38516step0 = (fun i j => raw38516 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38516step0 raw38516; decide +kernel
      have hl : raw38516step0Labels = raw38516Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38516 raw38516Labels permutation32 permutation7
    mixedMoment B raw38516step0 raw38516step0Labels = mixedMoment B raw38516step1 raw38516step1Labels := by
      have ha : raw38516step1 = -raw38516step0 := by apply Matrix.ext; change ∀ i j, raw38516step1 i j = -(raw38516step0 i j); unfold raw38516step1 raw38516step0; decide +kernel
      have hl : raw38516step1Labels = raw38516step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38516step1 raw38516step1Labels = mixedMoment B raw38516step2 raw38516step2Labels := by
      have ha : raw38516step2 = raw38516step1 := by apply Matrix.ext; unfold raw38516step2 raw38516step1; decide +kernel
      have hl : raw38516step1Labels = labelEmbedding4 ∘ raw38516step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38516step1 raw38516step1Labels raw38516step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1584 node1584Labels := by rfl

def raw38517 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw38517Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw38517step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38517 raw38517Labels = mixedMoment B node970 node970Labels := by
  calc
    mixedMoment B raw38517 raw38517Labels = mixedMoment B raw38517step0 raw38517step0Labels := by
      have ha : raw38517step0 = raw38517 := by apply Matrix.ext; unfold raw38517step0 raw38517; decide +kernel
      have hl : raw38517Labels = labelEmbedding2 ∘ raw38517step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38517 raw38517Labels raw38517step0Labels labelEmbedding2 hl
    _ = mixedMoment B node970 node970Labels := by rfl

def raw38518 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw38518Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-3, 1, 2]]
def raw38518step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38518step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw38518step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38518step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw38518step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38518 raw38518Labels = mixedMoment B node1585 node1585Labels := by
  calc
    mixedMoment B raw38518 raw38518Labels = mixedMoment B raw38518step0 raw38518step0Labels := by
      have ha : raw38518step0 = (fun i j => raw38518 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38518step0 raw38518; decide +kernel
      have hl : raw38518step0Labels = raw38518Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38518 raw38518Labels permutation32 permutation7
    mixedMoment B raw38518step0 raw38518step0Labels = mixedMoment B raw38518step1 raw38518step1Labels := by
      have ha : raw38518step1 = -raw38518step0 := by apply Matrix.ext; change ∀ i j, raw38518step1 i j = -(raw38518step0 i j); unfold raw38518step1 raw38518step0; decide +kernel
      have hl : raw38518step1Labels = raw38518step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38518step1 raw38518step1Labels = mixedMoment B raw38518step2 raw38518step2Labels := by
      have ha : raw38518step2 = raw38518step1 := by apply Matrix.ext; unfold raw38518step2 raw38518step1; decide +kernel
      have hl : raw38518step1Labels = labelEmbedding4 ∘ raw38518step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38518step1 raw38518step1Labels raw38518step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1585 node1585Labels := by rfl

def raw38519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38519Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38519step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38519 raw38519Labels = mixedMoment B node977 node977Labels := by
  calc
    mixedMoment B raw38519 raw38519Labels = mixedMoment B raw38519step0 raw38519step0Labels := by
      have ha : raw38519step0 = raw38519 := by apply Matrix.ext; unfold raw38519step0 raw38519; decide +kernel
      have hl : raw38519Labels = labelEmbedding2 ∘ raw38519step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38519 raw38519Labels raw38519step0Labels labelEmbedding2 hl
    _ = mixedMoment B node977 node977Labels := by rfl

def raw38520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38520Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw38520step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38520step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38520step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38520step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38520step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38520 raw38520Labels = mixedMoment B node1597 node1597Labels := by
  calc
    mixedMoment B raw38520 raw38520Labels = mixedMoment B raw38520step0 raw38520step0Labels := by
      have ha : raw38520step0 = (fun i j => raw38520 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38520step0 raw38520; decide +kernel
      have hl : raw38520step0Labels = raw38520Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38520 raw38520Labels permutation158 permutation7
    mixedMoment B raw38520step0 raw38520step0Labels = mixedMoment B raw38520step1 raw38520step1Labels := by
      have ha : raw38520step1 = -raw38520step0 := by apply Matrix.ext; change ∀ i j, raw38520step1 i j = -(raw38520step0 i j); unfold raw38520step1 raw38520step0; decide +kernel
      have hl : raw38520step1Labels = raw38520step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38520step1 raw38520step1Labels = mixedMoment B raw38520step2 raw38520step2Labels := by
      have ha : raw38520step2 = raw38520step1 := by apply Matrix.ext; unfold raw38520step2 raw38520step1; decide +kernel
      have hl : raw38520step1Labels = labelEmbedding4 ∘ raw38520step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38520step1 raw38520step1Labels raw38520step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1597 node1597Labels := by rfl

def raw38521 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw38521Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw38521step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38521 raw38521Labels = mixedMoment B node979 node979Labels := by
  calc
    mixedMoment B raw38521 raw38521Labels = mixedMoment B raw38521step0 raw38521step0Labels := by
      have ha : raw38521step0 = raw38521 := by apply Matrix.ext; unfold raw38521step0 raw38521; decide +kernel
      have hl : raw38521Labels = labelEmbedding2 ∘ raw38521step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38521 raw38521Labels raw38521step0Labels labelEmbedding2 hl
    _ = mixedMoment B node979 node979Labels := by rfl

def raw38522 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw38522Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw38522step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38522step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw38522step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38522step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw38522step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38522 raw38522Labels = mixedMoment B node1599 node1599Labels := by
  calc
    mixedMoment B raw38522 raw38522Labels = mixedMoment B raw38522step0 raw38522step0Labels := by
      have ha : raw38522step0 = (fun i j => raw38522 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38522step0 raw38522; decide +kernel
      have hl : raw38522step0Labels = raw38522Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38522 raw38522Labels permutation34 permutation7
    mixedMoment B raw38522step0 raw38522step0Labels = mixedMoment B raw38522step1 raw38522step1Labels := by
      have ha : raw38522step1 = -raw38522step0 := by apply Matrix.ext; change ∀ i j, raw38522step1 i j = -(raw38522step0 i j); unfold raw38522step1 raw38522step0; decide +kernel
      have hl : raw38522step1Labels = raw38522step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38522step1 raw38522step1Labels = mixedMoment B raw38522step2 raw38522step2Labels := by
      have ha : raw38522step2 = raw38522step1 := by apply Matrix.ext; unfold raw38522step2 raw38522step1; decide +kernel
      have hl : raw38522step1Labels = labelEmbedding4 ∘ raw38522step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38522step1 raw38522step1Labels raw38522step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1599 node1599Labels := by rfl

def raw38523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38523Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38523step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38523 raw38523Labels = mixedMoment B node980 node980Labels := by
  calc
    mixedMoment B raw38523 raw38523Labels = mixedMoment B raw38523step0 raw38523step0Labels := by
      have ha : raw38523step0 = raw38523 := by apply Matrix.ext; unfold raw38523step0 raw38523; decide +kernel
      have hl : raw38523Labels = labelEmbedding2 ∘ raw38523step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38523 raw38523Labels raw38523step0Labels labelEmbedding2 hl
    _ = mixedMoment B node980 node980Labels := by rfl

def raw38524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38524Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw38524step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38524step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38524step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38524step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38524step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38524 raw38524Labels = mixedMoment B node1616 node1616Labels := by
  calc
    mixedMoment B raw38524 raw38524Labels = mixedMoment B raw38524step0 raw38524step0Labels := by
      have ha : raw38524step0 = (fun i j => raw38524 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38524step0 raw38524; decide +kernel
      have hl : raw38524step0Labels = raw38524Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38524 raw38524Labels permutation152 permutation7
    mixedMoment B raw38524step0 raw38524step0Labels = mixedMoment B raw38524step1 raw38524step1Labels := by
      have ha : raw38524step1 = -raw38524step0 := by apply Matrix.ext; change ∀ i j, raw38524step1 i j = -(raw38524step0 i j); unfold raw38524step1 raw38524step0; decide +kernel
      have hl : raw38524step1Labels = raw38524step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38524step1 raw38524step1Labels = mixedMoment B raw38524step2 raw38524step2Labels := by
      have ha : raw38524step2 = raw38524step1 := by apply Matrix.ext; unfold raw38524step2 raw38524step1; decide +kernel
      have hl : raw38524step1Labels = labelEmbedding4 ∘ raw38524step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38524step1 raw38524step1Labels raw38524step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1616 node1616Labels := by rfl

def raw38525 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38525Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38525step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38525 raw38525Labels = mixedMoment B node982 node982Labels := by
  calc
    mixedMoment B raw38525 raw38525Labels = mixedMoment B raw38525step0 raw38525step0Labels := by
      have ha : raw38525step0 = raw38525 := by apply Matrix.ext; unfold raw38525step0 raw38525; decide +kernel
      have hl : raw38525Labels = labelEmbedding2 ∘ raw38525step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38525 raw38525Labels raw38525step0Labels labelEmbedding2 hl
    _ = mixedMoment B node982 node982Labels := by rfl

def raw38526 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38526Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw38526step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38526step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38526step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38526step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38526step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38526 raw38526Labels = mixedMoment B node1617 node1617Labels := by
  calc
    mixedMoment B raw38526 raw38526Labels = mixedMoment B raw38526step0 raw38526step0Labels := by
      have ha : raw38526step0 = (fun i j => raw38526 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38526step0 raw38526; decide +kernel
      have hl : raw38526step0Labels = raw38526Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38526 raw38526Labels permutation32 permutation7
    mixedMoment B raw38526step0 raw38526step0Labels = mixedMoment B raw38526step1 raw38526step1Labels := by
      have ha : raw38526step1 = -raw38526step0 := by apply Matrix.ext; change ∀ i j, raw38526step1 i j = -(raw38526step0 i j); unfold raw38526step1 raw38526step0; decide +kernel
      have hl : raw38526step1Labels = raw38526step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38526step1 raw38526step1Labels = mixedMoment B raw38526step2 raw38526step2Labels := by
      have ha : raw38526step2 = raw38526step1 := by apply Matrix.ext; unfold raw38526step2 raw38526step1; decide +kernel
      have hl : raw38526step1Labels = labelEmbedding4 ∘ raw38526step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38526step1 raw38526step1Labels raw38526step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1617 node1617Labels := by rfl

def raw38527 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38527Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38527step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38527 raw38527Labels = mixedMoment B node985 node985Labels := by
  calc
    mixedMoment B raw38527 raw38527Labels = mixedMoment B raw38527step0 raw38527step0Labels := by
      have ha : raw38527step0 = raw38527 := by apply Matrix.ext; unfold raw38527step0 raw38527; decide +kernel
      have hl : raw38527Labels = labelEmbedding2 ∘ raw38527step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38527 raw38527Labels raw38527step0Labels labelEmbedding2 hl
    _ = mixedMoment B node985 node985Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
