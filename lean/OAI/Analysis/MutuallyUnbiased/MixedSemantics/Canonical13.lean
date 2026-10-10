import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw1664 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![1, 0, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw1664Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw1664step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw1664step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1664step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw1664step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1664 raw1664Labels = mixedMoment B node1924 node1924Labels := by
  calc
    mixedMoment B raw1664 raw1664Labels = mixedMoment B raw1664step0 raw1664step0Labels := by
      have ha : raw1664step0 = (fun i j => raw1664 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1664step0 raw1664; decide +kernel
      have hl : raw1664step0Labels = raw1664Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1664 raw1664Labels permutation34 permutation6
    mixedMoment B raw1664step0 raw1664step0Labels = mixedMoment B raw1664step1 raw1664step1Labels := by
      have ha : raw1664step1 = -raw1664step0 := by apply Matrix.ext; change ∀ i j, raw1664step1 i j = -(raw1664step0 i j); unfold raw1664step1 raw1664step0; decide +kernel
      have hl : raw1664step1Labels = raw1664step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1664step1 raw1664step1Labels = mixedMoment B raw1664step2 raw1664step2Labels := by
      have ha : raw1664step2 = raw1664step1 := by apply Matrix.ext; unfold raw1664step2 raw1664step1; decide +kernel
      have hl : raw1664step1Labels = labelEmbedding1 ∘ raw1664step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1664step1 raw1664step1Labels raw1664step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1924 node1924Labels := by rfl

def raw1665 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1665step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1665step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1665step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1665step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1665 raw1665Labels = mixedMoment B node4746 node4746Labels := by
  calc
    mixedMoment B raw1665 raw1665Labels = mixedMoment B raw1665step0 raw1665step0Labels := by
      have ha : raw1665step0 = (fun i j => raw1665 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1665step0 raw1665; decide +kernel
      have hl : raw1665step0Labels = raw1665Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1665 raw1665Labels permutation152 permutation4
    mixedMoment B raw1665step0 raw1665step0Labels = mixedMoment B raw1665step1 raw1665step1Labels := by
      have ha : raw1665step1 = raw1665step0 := by apply Matrix.ext; unfold raw1665step1 raw1665step0; decide +kernel
      have hl : raw1665step0Labels = labelEmbedding7 ∘ raw1665step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1665step0 raw1665step0Labels raw1665step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4746 node4746Labels := by rfl

def raw1666 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1666Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1666step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1666step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1666 raw1666Labels = mixedMoment B node1925 node1925Labels := by
  calc
    mixedMoment B raw1666 raw1666Labels = mixedMoment B raw1666step0 raw1666step0Labels := by
      have ha : raw1666step0 = (fun i j => raw1666 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1666step0 raw1666; decide +kernel
      have hl : raw1666step0Labels = raw1666Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1666 raw1666Labels permutation152 permutation4
    _ = mixedMoment B node1925 node1925Labels := by rfl

def raw1667 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1667Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1667step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw1667step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1667step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1667step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1667step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1667step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1667 raw1667Labels = mixedMoment B node1925 node1925Labels := by
  calc
    mixedMoment B raw1667 raw1667Labels = mixedMoment B raw1667step0 raw1667step0Labels := by
      have ha : raw1667step0 = (fun i j => raw1667 (permutation173 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1667step0 raw1667; decide +kernel
      have hl : raw1667step0Labels = raw1667Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1667 raw1667Labels permutation173 permutation6
    mixedMoment B raw1667step0 raw1667step0Labels = mixedMoment B raw1667step1 raw1667step1Labels := by
      have ha : raw1667step1 = -raw1667step0 := by apply Matrix.ext; change ∀ i j, raw1667step1 i j = -(raw1667step0 i j); unfold raw1667step1 raw1667step0; decide +kernel
      have hl : raw1667step1Labels = raw1667step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1667step1 raw1667step1Labels = mixedMoment B raw1667step2 raw1667step2Labels := by
      have ha : raw1667step2 = raw1667step1 := by apply Matrix.ext; unfold raw1667step2 raw1667step1; decide +kernel
      have hl : raw1667step1Labels = labelEmbedding1 ∘ raw1667step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1667step1 raw1667step1Labels raw1667step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1925 node1925Labels := by rfl

def raw1668 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![-2, 3, -1]]
def raw1668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw1668step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw1668step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1668 raw1668Labels = mixedMoment B node4747 node4747Labels := by
  calc
    mixedMoment B raw1668 raw1668Labels = mixedMoment B raw1668step0 raw1668step0Labels := by
      have ha : raw1668step0 = (fun i j => raw1668 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1668step0 raw1668; decide +kernel
      have hl : raw1668step0Labels = raw1668Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1668 raw1668Labels permutation32 permutation4
    mixedMoment B raw1668step0 raw1668step0Labels = mixedMoment B raw1668step1 raw1668step1Labels := by
      have ha : raw1668step1 = raw1668step0 := by apply Matrix.ext; unfold raw1668step1 raw1668step0; decide +kernel
      have hl : raw1668step0Labels = labelEmbedding7 ∘ raw1668step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1668step0 raw1668step0Labels raw1668step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4747 node4747Labels := by rfl

def raw1669 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![-2, 3, -1]]
def raw1669Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw1669step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1669 raw1669Labels = mixedMoment B node1926 node1926Labels := by
  calc
    mixedMoment B raw1669 raw1669Labels = mixedMoment B raw1669step0 raw1669step0Labels := by
      have ha : raw1669step0 = (fun i j => raw1669 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1669step0 raw1669; decide +kernel
      have hl : raw1669step0Labels = raw1669Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1669 raw1669Labels permutation32 permutation4
    _ = mixedMoment B node1926 node1926Labels := by rfl

def raw1670 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![-2, 3, -1]]
def raw1670Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw1670step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw1670step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1670step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw1670step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1670 raw1670Labels = mixedMoment B node1948 node1948Labels := by
  calc
    mixedMoment B raw1670 raw1670Labels = mixedMoment B raw1670step0 raw1670step0Labels := by
      have ha : raw1670step0 = (fun i j => raw1670 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1670step0 raw1670; decide +kernel
      have hl : raw1670step0Labels = raw1670Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1670 raw1670Labels permutation35 permutation6
    mixedMoment B raw1670step0 raw1670step0Labels = mixedMoment B raw1670step1 raw1670step1Labels := by
      have ha : raw1670step1 = -raw1670step0 := by apply Matrix.ext; change ∀ i j, raw1670step1 i j = -(raw1670step0 i j); unfold raw1670step1 raw1670step0; decide +kernel
      have hl : raw1670step1Labels = raw1670step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1670step1 raw1670step1Labels = mixedMoment B raw1670step2 raw1670step2Labels := by
      have ha : raw1670step2 = raw1670step1 := by apply Matrix.ext; unfold raw1670step2 raw1670step1; decide +kernel
      have hl : raw1670step1Labels = labelEmbedding1 ∘ raw1670step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1670step1 raw1670step1Labels raw1670step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1948 node1948Labels := by rfl

def raw1671 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1671step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1671step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1671 raw1671Labels = mixedMoment B node4749 node4749Labels := by
  calc
    mixedMoment B raw1671 raw1671Labels = mixedMoment B raw1671step0 raw1671step0Labels := by
      have ha : raw1671step0 = (fun i j => raw1671 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1671step0 raw1671; decide +kernel
      have hl : raw1671step0Labels = raw1671Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1671 raw1671Labels permutation32 permutation4
    mixedMoment B raw1671step0 raw1671step0Labels = mixedMoment B raw1671step1 raw1671step1Labels := by
      have ha : raw1671step1 = raw1671step0 := by apply Matrix.ext; unfold raw1671step1 raw1671step0; decide +kernel
      have hl : raw1671step0Labels = labelEmbedding7 ∘ raw1671step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1671step0 raw1671step0Labels raw1671step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4749 node4749Labels := by rfl

def raw1672 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1672Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1672step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1672 raw1672Labels = mixedMoment B node1928 node1928Labels := by
  calc
    mixedMoment B raw1672 raw1672Labels = mixedMoment B raw1672step0 raw1672step0Labels := by
      have ha : raw1672step0 = (fun i j => raw1672 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1672step0 raw1672; decide +kernel
      have hl : raw1672step0Labels = raw1672Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1672 raw1672Labels permutation32 permutation4
    _ = mixedMoment B node1928 node1928Labels := by rfl

def raw1673 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1673Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw1673step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1673step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1673step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1673step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1673 raw1673Labels = mixedMoment B node1928 node1928Labels := by
  calc
    mixedMoment B raw1673 raw1673Labels = mixedMoment B raw1673step0 raw1673step0Labels := by
      have ha : raw1673step0 = (fun i j => raw1673 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1673step0 raw1673; decide +kernel
      have hl : raw1673step0Labels = raw1673Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1673 raw1673Labels permutation34 permutation6
    mixedMoment B raw1673step0 raw1673step0Labels = mixedMoment B raw1673step1 raw1673step1Labels := by
      have ha : raw1673step1 = -raw1673step0 := by apply Matrix.ext; change ∀ i j, raw1673step1 i j = -(raw1673step0 i j); unfold raw1673step1 raw1673step0; decide +kernel
      have hl : raw1673step1Labels = raw1673step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1673step1 raw1673step1Labels = mixedMoment B raw1673step2 raw1673step2Labels := by
      have ha : raw1673step2 = raw1673step1 := by apply Matrix.ext; unfold raw1673step2 raw1673step1; decide +kernel
      have hl : raw1673step1Labels = labelEmbedding1 ∘ raw1673step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1673step1 raw1673step1Labels raw1673step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1928 node1928Labels := by rfl

def raw1674 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1674step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1674step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1674 raw1674Labels = mixedMoment B node4750 node4750Labels := by
  calc
    mixedMoment B raw1674 raw1674Labels = mixedMoment B raw1674step0 raw1674step0Labels := by
      have ha : raw1674step0 = (fun i j => raw1674 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1674step0 raw1674; decide +kernel
      have hl : raw1674step0Labels = raw1674Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1674 raw1674Labels permutation32 permutation4
    mixedMoment B raw1674step0 raw1674step0Labels = mixedMoment B raw1674step1 raw1674step1Labels := by
      have ha : raw1674step1 = raw1674step0 := by apply Matrix.ext; unfold raw1674step1 raw1674step0; decide +kernel
      have hl : raw1674step0Labels = labelEmbedding7 ∘ raw1674step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1674step0 raw1674step0Labels raw1674step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4750 node4750Labels := by rfl

def raw1675 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1675Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1675step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1675 raw1675Labels = mixedMoment B node1929 node1929Labels := by
  calc
    mixedMoment B raw1675 raw1675Labels = mixedMoment B raw1675step0 raw1675step0Labels := by
      have ha : raw1675step0 = (fun i j => raw1675 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1675step0 raw1675; decide +kernel
      have hl : raw1675step0Labels = raw1675Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1675 raw1675Labels permutation32 permutation4
    _ = mixedMoment B node1929 node1929Labels := by rfl

def raw1676 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 0, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1676Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw1676step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1676step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw1676step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1676step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw1676step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1676 raw1676Labels = mixedMoment B node1949 node1949Labels := by
  calc
    mixedMoment B raw1676 raw1676Labels = mixedMoment B raw1676step0 raw1676step0Labels := by
      have ha : raw1676step0 = (fun i j => raw1676 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1676step0 raw1676; decide +kernel
      have hl : raw1676step0Labels = raw1676Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1676 raw1676Labels permutation35 permutation6
    mixedMoment B raw1676step0 raw1676step0Labels = mixedMoment B raw1676step1 raw1676step1Labels := by
      have ha : raw1676step1 = -raw1676step0 := by apply Matrix.ext; change ∀ i j, raw1676step1 i j = -(raw1676step0 i j); unfold raw1676step1 raw1676step0; decide +kernel
      have hl : raw1676step1Labels = raw1676step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1676step1 raw1676step1Labels = mixedMoment B raw1676step2 raw1676step2Labels := by
      have ha : raw1676step2 = raw1676step1 := by apply Matrix.ext; unfold raw1676step2 raw1676step1; decide +kernel
      have hl : raw1676step1Labels = labelEmbedding1 ∘ raw1676step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1676step1 raw1676step1Labels raw1676step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1949 node1949Labels := by rfl

def raw1677 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 1, -3], ![-2, 3, -1]]
def raw1677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1677step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw1677step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1677step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw1677step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1677 raw1677Labels = mixedMoment B node4754 node4754Labels := by
  calc
    mixedMoment B raw1677 raw1677Labels = mixedMoment B raw1677step0 raw1677step0Labels := by
      have ha : raw1677step0 = (fun i j => raw1677 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1677step0 raw1677; decide +kernel
      have hl : raw1677step0Labels = raw1677Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1677 raw1677Labels permutation8 permutation4
    mixedMoment B raw1677step0 raw1677step0Labels = mixedMoment B raw1677step1 raw1677step1Labels := by
      have ha : raw1677step1 = raw1677step0 := by apply Matrix.ext; unfold raw1677step1 raw1677step0; decide +kernel
      have hl : raw1677step0Labels = labelEmbedding7 ∘ raw1677step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1677step0 raw1677step0Labels raw1677step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4754 node4754Labels := by rfl

def raw1678 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 1, -3], ![-2, 3, -1]]
def raw1678Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1678step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw1678step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1678 raw1678Labels = mixedMoment B node1951 node1951Labels := by
  calc
    mixedMoment B raw1678 raw1678Labels = mixedMoment B raw1678step0 raw1678step0Labels := by
      have ha : raw1678step0 = (fun i j => raw1678 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1678step0 raw1678; decide +kernel
      have hl : raw1678step0Labels = raw1678Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1678 raw1678Labels permutation8 permutation4
    _ = mixedMoment B node1951 node1951Labels := by rfl

def raw1679 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![0, -1, 1], ![2, 1, -3], ![-2, 3, -1]]
def raw1679Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1679step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw1679step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1679step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw1679step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1679step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw1679step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1679 raw1679Labels = mixedMoment B node1951 node1951Labels := by
  calc
    mixedMoment B raw1679 raw1679Labels = mixedMoment B raw1679step0 raw1679step0Labels := by
      have ha : raw1679step0 = (fun i j => raw1679 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1679step0 raw1679; decide +kernel
      have hl : raw1679step0Labels = raw1679Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1679 raw1679Labels permutation9 permutation6
    mixedMoment B raw1679step0 raw1679step0Labels = mixedMoment B raw1679step1 raw1679step1Labels := by
      have ha : raw1679step1 = -raw1679step0 := by apply Matrix.ext; change ∀ i j, raw1679step1 i j = -(raw1679step0 i j); unfold raw1679step1 raw1679step0; decide +kernel
      have hl : raw1679step1Labels = raw1679step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1679step1 raw1679step1Labels = mixedMoment B raw1679step2 raw1679step2Labels := by
      have ha : raw1679step2 = raw1679step1 := by apply Matrix.ext; unfold raw1679step2 raw1679step1; decide +kernel
      have hl : raw1679step1Labels = labelEmbedding1 ∘ raw1679step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1679step1 raw1679step1Labels raw1679step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1951 node1951Labels := by rfl

def raw1680 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, 2, -2], ![-1, 3, -2]]
def raw1680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1680step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw1680step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1680step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw1680step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1680 raw1680Labels = mixedMoment B node4755 node4755Labels := by
  calc
    mixedMoment B raw1680 raw1680Labels = mixedMoment B raw1680step0 raw1680step0Labels := by
      have ha : raw1680step0 = (fun i j => raw1680 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1680step0 raw1680; decide +kernel
      have hl : raw1680step0Labels = raw1680Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1680 raw1680Labels permutation152 permutation4
    mixedMoment B raw1680step0 raw1680step0Labels = mixedMoment B raw1680step1 raw1680step1Labels := by
      have ha : raw1680step1 = raw1680step0 := by apply Matrix.ext; unfold raw1680step1 raw1680step0; decide +kernel
      have hl : raw1680step0Labels = labelEmbedding7 ∘ raw1680step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1680step0 raw1680step0Labels raw1680step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4755 node4755Labels := by rfl

def raw1681 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, 2, -2], ![-1, 3, -2]]
def raw1681Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1681step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw1681step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1681 raw1681Labels = mixedMoment B node1954 node1954Labels := by
  calc
    mixedMoment B raw1681 raw1681Labels = mixedMoment B raw1681step0 raw1681step0Labels := by
      have ha : raw1681step0 = (fun i j => raw1681 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1681step0 raw1681; decide +kernel
      have hl : raw1681step0Labels = raw1681Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1681 raw1681Labels permutation152 permutation4
    _ = mixedMoment B node1954 node1954Labels := by rfl

def raw1682 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, 2, -2], ![-1, 3, -2]]
def raw1682Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1682step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 0, 2], ![-2, -1, 3]]
def raw1682step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1682step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw1682step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1682step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw1682step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1682 raw1682Labels = mixedMoment B node1985 node1985Labels := by
  calc
    mixedMoment B raw1682 raw1682Labels = mixedMoment B raw1682step0 raw1682step0Labels := by
      have ha : raw1682step0 = (fun i j => raw1682 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1682step0 raw1682; decide +kernel
      have hl : raw1682step0Labels = raw1682Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1682 raw1682Labels permutation200 permutation6
    mixedMoment B raw1682step0 raw1682step0Labels = mixedMoment B raw1682step1 raw1682step1Labels := by
      have ha : raw1682step1 = -raw1682step0 := by apply Matrix.ext; change ∀ i j, raw1682step1 i j = -(raw1682step0 i j); unfold raw1682step1 raw1682step0; decide +kernel
      have hl : raw1682step1Labels = raw1682step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1682step1 raw1682step1Labels = mixedMoment B raw1682step2 raw1682step2Labels := by
      have ha : raw1682step2 = raw1682step1 := by apply Matrix.ext; unfold raw1682step2 raw1682step1; decide +kernel
      have hl : raw1682step1Labels = labelEmbedding1 ∘ raw1682step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1682step1 raw1682step1Labels raw1682step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1985 node1985Labels := by rfl

def raw1683 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw1683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1683step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1683step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1683step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1683step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1683 raw1683Labels = mixedMoment B node4758 node4758Labels := by
  calc
    mixedMoment B raw1683 raw1683Labels = mixedMoment B raw1683step0 raw1683step0Labels := by
      have ha : raw1683step0 = (fun i j => raw1683 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1683step0 raw1683; decide +kernel
      have hl : raw1683step0Labels = raw1683Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1683 raw1683Labels permutation152 permutation4
    mixedMoment B raw1683step0 raw1683step0Labels = mixedMoment B raw1683step1 raw1683step1Labels := by
      have ha : raw1683step1 = raw1683step0 := by apply Matrix.ext; unfold raw1683step1 raw1683step0; decide +kernel
      have hl : raw1683step0Labels = labelEmbedding7 ∘ raw1683step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1683step0 raw1683step0Labels raw1683step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4758 node4758Labels := by rfl

def raw1684 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw1684Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1684step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1684step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1684 raw1684Labels = mixedMoment B node1958 node1958Labels := by
  calc
    mixedMoment B raw1684 raw1684Labels = mixedMoment B raw1684step0 raw1684step0Labels := by
      have ha : raw1684step0 = (fun i j => raw1684 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1684step0 raw1684; decide +kernel
      have hl : raw1684step0Labels = raw1684Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1684 raw1684Labels permutation152 permutation4
    _ = mixedMoment B node1958 node1958Labels := by rfl

def raw1685 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw1685Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1685step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw1685step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1685step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1685step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1685step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1685step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1685 raw1685Labels = mixedMoment B node2069 node2069Labels := by
  calc
    mixedMoment B raw1685 raw1685Labels = mixedMoment B raw1685step0 raw1685step0Labels := by
      have ha : raw1685step0 = (fun i j => raw1685 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1685step0 raw1685; decide +kernel
      have hl : raw1685step0Labels = raw1685Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1685 raw1685Labels permutation200 permutation6
    mixedMoment B raw1685step0 raw1685step0Labels = mixedMoment B raw1685step1 raw1685step1Labels := by
      have ha : raw1685step1 = -raw1685step0 := by apply Matrix.ext; change ∀ i j, raw1685step1 i j = -(raw1685step0 i j); unfold raw1685step1 raw1685step0; decide +kernel
      have hl : raw1685step1Labels = raw1685step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1685step1 raw1685step1Labels = mixedMoment B raw1685step2 raw1685step2Labels := by
      have ha : raw1685step2 = raw1685step1 := by apply Matrix.ext; unfold raw1685step2 raw1685step1; decide +kernel
      have hl : raw1685step1Labels = labelEmbedding1 ∘ raw1685step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1685step1 raw1685step1Labels raw1685step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2069 node2069Labels := by rfl

def raw1686 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1686step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1686step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1686step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1686step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1686 raw1686Labels = mixedMoment B node4759 node4759Labels := by
  calc
    mixedMoment B raw1686 raw1686Labels = mixedMoment B raw1686step0 raw1686step0Labels := by
      have ha : raw1686step0 = (fun i j => raw1686 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1686step0 raw1686; decide +kernel
      have hl : raw1686step0Labels = raw1686Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1686 raw1686Labels permutation152 permutation4
    mixedMoment B raw1686step0 raw1686step0Labels = mixedMoment B raw1686step1 raw1686step1Labels := by
      have ha : raw1686step1 = raw1686step0 := by apply Matrix.ext; unfold raw1686step1 raw1686step0; decide +kernel
      have hl : raw1686step0Labels = labelEmbedding7 ∘ raw1686step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1686step0 raw1686step0Labels raw1686step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4759 node4759Labels := by rfl

def raw1687 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1687Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1687step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1687step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1687 raw1687Labels = mixedMoment B node1959 node1959Labels := by
  calc
    mixedMoment B raw1687 raw1687Labels = mixedMoment B raw1687step0 raw1687step0Labels := by
      have ha : raw1687step0 = (fun i j => raw1687 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1687step0 raw1687; decide +kernel
      have hl : raw1687step0Labels = raw1687Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1687 raw1687Labels permutation152 permutation4
    _ = mixedMoment B node1959 node1959Labels := by rfl

def raw1688 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1688Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1688step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw1688step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1688step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw1688step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1688 raw1688Labels = mixedMoment B node2170 node2170Labels := by
  calc
    mixedMoment B raw1688 raw1688Labels = mixedMoment B raw1688step0 raw1688step0Labels := by
      have ha : raw1688step0 = (fun i j => raw1688 (permutation662 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1688step0 raw1688; decide +kernel
      have hl : raw1688step0Labels = raw1688Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1688 raw1688Labels permutation662 permutation6
    mixedMoment B raw1688step0 raw1688step0Labels = mixedMoment B raw1688step1 raw1688step1Labels := by
      have ha : raw1688step1 = raw1688step0 := by apply Matrix.ext; unfold raw1688step1 raw1688step0; decide +kernel
      have hl : raw1688step0Labels = labelEmbedding1 ∘ raw1688step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1688step0 raw1688step0Labels raw1688step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2170 node2170Labels := by rfl

def raw1689 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1689step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1689step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1689step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1689step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1689 raw1689Labels = mixedMoment B node4760 node4760Labels := by
  calc
    mixedMoment B raw1689 raw1689Labels = mixedMoment B raw1689step0 raw1689step0Labels := by
      have ha : raw1689step0 = (fun i j => raw1689 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1689step0 raw1689; decide +kernel
      have hl : raw1689step0Labels = raw1689Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1689 raw1689Labels permutation152 permutation4
    mixedMoment B raw1689step0 raw1689step0Labels = mixedMoment B raw1689step1 raw1689step1Labels := by
      have ha : raw1689step1 = raw1689step0 := by apply Matrix.ext; unfold raw1689step1 raw1689step0; decide +kernel
      have hl : raw1689step0Labels = labelEmbedding7 ∘ raw1689step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1689step0 raw1689step0Labels raw1689step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4760 node4760Labels := by rfl

def raw1690 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1690Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1690step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1690step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1690 raw1690Labels = mixedMoment B node1960 node1960Labels := by
  calc
    mixedMoment B raw1690 raw1690Labels = mixedMoment B raw1690step0 raw1690step0Labels := by
      have ha : raw1690step0 = (fun i j => raw1690 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1690step0 raw1690; decide +kernel
      have hl : raw1690step0Labels = raw1690Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1690 raw1690Labels permutation152 permutation4
    _ = mixedMoment B node1960 node1960Labels := by rfl

def raw1691 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1691Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1691step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw1691step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1691step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1691step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1691step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1691step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1691 raw1691Labels = mixedMoment B node2173 node2173Labels := by
  calc
    mixedMoment B raw1691 raw1691Labels = mixedMoment B raw1691step0 raw1691step0Labels := by
      have ha : raw1691step0 = (fun i j => raw1691 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1691step0 raw1691; decide +kernel
      have hl : raw1691step0Labels = raw1691Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1691 raw1691Labels permutation152 permutation6
    mixedMoment B raw1691step0 raw1691step0Labels = mixedMoment B raw1691step1 raw1691step1Labels := by
      have ha : raw1691step1 = -raw1691step0 := by apply Matrix.ext; change ∀ i j, raw1691step1 i j = -(raw1691step0 i j); unfold raw1691step1 raw1691step0; decide +kernel
      have hl : raw1691step1Labels = raw1691step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1691step1 raw1691step1Labels = mixedMoment B raw1691step2 raw1691step2Labels := by
      have ha : raw1691step2 = raw1691step1 := by apply Matrix.ext; unfold raw1691step2 raw1691step1; decide +kernel
      have hl : raw1691step1Labels = labelEmbedding1 ∘ raw1691step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1691step1 raw1691step1Labels raw1691step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2173 node2173Labels := by rfl

def raw1692 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1692step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1692step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1692step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1692step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1692 raw1692Labels = mixedMoment B node4763 node4763Labels := by
  calc
    mixedMoment B raw1692 raw1692Labels = mixedMoment B raw1692step0 raw1692step0Labels := by
      have ha : raw1692step0 = (fun i j => raw1692 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1692step0 raw1692; decide +kernel
      have hl : raw1692step0Labels = raw1692Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1692 raw1692Labels permutation152 permutation4
    mixedMoment B raw1692step0 raw1692step0Labels = mixedMoment B raw1692step1 raw1692step1Labels := by
      have ha : raw1692step1 = raw1692step0 := by apply Matrix.ext; unfold raw1692step1 raw1692step0; decide +kernel
      have hl : raw1692step0Labels = labelEmbedding7 ∘ raw1692step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1692step0 raw1692step0Labels raw1692step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4763 node4763Labels := by rfl

def raw1693 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1693Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1693step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1693step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1693 raw1693Labels = mixedMoment B node1963 node1963Labels := by
  calc
    mixedMoment B raw1693 raw1693Labels = mixedMoment B raw1693step0 raw1693step0Labels := by
      have ha : raw1693step0 = (fun i j => raw1693 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1693step0 raw1693; decide +kernel
      have hl : raw1693step0Labels = raw1693Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1693 raw1693Labels permutation152 permutation4
    _ = mixedMoment B node1963 node1963Labels := by rfl

def raw1694 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1694Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1694step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw1694step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1694step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1694step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1694step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1694step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1694 raw1694Labels = mixedMoment B node2174 node2174Labels := by
  calc
    mixedMoment B raw1694 raw1694Labels = mixedMoment B raw1694step0 raw1694step0Labels := by
      have ha : raw1694step0 = (fun i j => raw1694 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1694step0 raw1694; decide +kernel
      have hl : raw1694step0Labels = raw1694Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1694 raw1694Labels permutation152 permutation6
    mixedMoment B raw1694step0 raw1694step0Labels = mixedMoment B raw1694step1 raw1694step1Labels := by
      have ha : raw1694step1 = -raw1694step0 := by apply Matrix.ext; change ∀ i j, raw1694step1 i j = -(raw1694step0 i j); unfold raw1694step1 raw1694step0; decide +kernel
      have hl : raw1694step1Labels = raw1694step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1694step1 raw1694step1Labels = mixedMoment B raw1694step2 raw1694step2Labels := by
      have ha : raw1694step2 = raw1694step1 := by apply Matrix.ext; unfold raw1694step2 raw1694step1; decide +kernel
      have hl : raw1694step1Labels = labelEmbedding1 ∘ raw1694step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1694step1 raw1694step1Labels raw1694step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2174 node2174Labels := by rfl

def raw1695 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1695step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1695step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1695step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1695step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1695 raw1695Labels = mixedMoment B node4764 node4764Labels := by
  calc
    mixedMoment B raw1695 raw1695Labels = mixedMoment B raw1695step0 raw1695step0Labels := by
      have ha : raw1695step0 = (fun i j => raw1695 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1695step0 raw1695; decide +kernel
      have hl : raw1695step0Labels = raw1695Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1695 raw1695Labels permutation152 permutation4
    mixedMoment B raw1695step0 raw1695step0Labels = mixedMoment B raw1695step1 raw1695step1Labels := by
      have ha : raw1695step1 = raw1695step0 := by apply Matrix.ext; unfold raw1695step1 raw1695step0; decide +kernel
      have hl : raw1695step0Labels = labelEmbedding7 ∘ raw1695step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1695step0 raw1695step0Labels raw1695step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4764 node4764Labels := by rfl

def raw1696 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1696Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1696step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1696 raw1696Labels = mixedMoment B node1964 node1964Labels := by
  calc
    mixedMoment B raw1696 raw1696Labels = mixedMoment B raw1696step0 raw1696step0Labels := by
      have ha : raw1696step0 = (fun i j => raw1696 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1696step0 raw1696; decide +kernel
      have hl : raw1696step0Labels = raw1696Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1696 raw1696Labels permutation152 permutation4
    _ = mixedMoment B node1964 node1964Labels := by rfl

def raw1697 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1697Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1697step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw1697step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1697step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1697step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1697step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1697step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1697 raw1697Labels = mixedMoment B node2182 node2182Labels := by
  calc
    mixedMoment B raw1697 raw1697Labels = mixedMoment B raw1697step0 raw1697step0Labels := by
      have ha : raw1697step0 = (fun i j => raw1697 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1697step0 raw1697; decide +kernel
      have hl : raw1697step0Labels = raw1697Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1697 raw1697Labels permutation152 permutation6
    mixedMoment B raw1697step0 raw1697step0Labels = mixedMoment B raw1697step1 raw1697step1Labels := by
      have ha : raw1697step1 = -raw1697step0 := by apply Matrix.ext; change ∀ i j, raw1697step1 i j = -(raw1697step0 i j); unfold raw1697step1 raw1697step0; decide +kernel
      have hl : raw1697step1Labels = raw1697step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1697step1 raw1697step1Labels = mixedMoment B raw1697step2 raw1697step2Labels := by
      have ha : raw1697step2 = raw1697step1 := by apply Matrix.ext; unfold raw1697step2 raw1697step1; decide +kernel
      have hl : raw1697step1Labels = labelEmbedding1 ∘ raw1697step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1697step1 raw1697step1Labels raw1697step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2182 node2182Labels := by rfl

def raw1698 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1698step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1698step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1698step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1698step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1698 raw1698Labels = mixedMoment B node4766 node4766Labels := by
  calc
    mixedMoment B raw1698 raw1698Labels = mixedMoment B raw1698step0 raw1698step0Labels := by
      have ha : raw1698step0 = (fun i j => raw1698 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1698step0 raw1698; decide +kernel
      have hl : raw1698step0Labels = raw1698Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1698 raw1698Labels permutation152 permutation4
    mixedMoment B raw1698step0 raw1698step0Labels = mixedMoment B raw1698step1 raw1698step1Labels := by
      have ha : raw1698step1 = raw1698step0 := by apply Matrix.ext; unfold raw1698step1 raw1698step0; decide +kernel
      have hl : raw1698step0Labels = labelEmbedding7 ∘ raw1698step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1698step0 raw1698step0Labels raw1698step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4766 node4766Labels := by rfl

def raw1699 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1699Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1699step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1699step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1699 raw1699Labels = mixedMoment B node1966 node1966Labels := by
  calc
    mixedMoment B raw1699 raw1699Labels = mixedMoment B raw1699step0 raw1699step0Labels := by
      have ha : raw1699step0 = (fun i j => raw1699 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1699step0 raw1699; decide +kernel
      have hl : raw1699step0Labels = raw1699Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1699 raw1699Labels permutation152 permutation4
    _ = mixedMoment B node1966 node1966Labels := by rfl

def raw1700 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1700Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1700step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw1700step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1700step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw1700step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1700step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw1700step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1700 raw1700Labels = mixedMoment B node2177 node2177Labels := by
  calc
    mixedMoment B raw1700 raw1700Labels = mixedMoment B raw1700step0 raw1700step0Labels := by
      have ha : raw1700step0 = (fun i j => raw1700 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1700step0 raw1700; decide +kernel
      have hl : raw1700step0Labels = raw1700Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1700 raw1700Labels permutation154 permutation6
    mixedMoment B raw1700step0 raw1700step0Labels = mixedMoment B raw1700step1 raw1700step1Labels := by
      have ha : raw1700step1 = -raw1700step0 := by apply Matrix.ext; change ∀ i j, raw1700step1 i j = -(raw1700step0 i j); unfold raw1700step1 raw1700step0; decide +kernel
      have hl : raw1700step1Labels = raw1700step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1700step1 raw1700step1Labels = mixedMoment B raw1700step2 raw1700step2Labels := by
      have ha : raw1700step2 = raw1700step1 := by apply Matrix.ext; unfold raw1700step2 raw1700step1; decide +kernel
      have hl : raw1700step1Labels = labelEmbedding1 ∘ raw1700step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1700step1 raw1700step1Labels raw1700step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2177 node2177Labels := by rfl

def raw1701 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1701step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1701step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1701step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1701step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1701 raw1701Labels = mixedMoment B node4767 node4767Labels := by
  calc
    mixedMoment B raw1701 raw1701Labels = mixedMoment B raw1701step0 raw1701step0Labels := by
      have ha : raw1701step0 = (fun i j => raw1701 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1701step0 raw1701; decide +kernel
      have hl : raw1701step0Labels = raw1701Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1701 raw1701Labels permutation152 permutation4
    mixedMoment B raw1701step0 raw1701step0Labels = mixedMoment B raw1701step1 raw1701step1Labels := by
      have ha : raw1701step1 = raw1701step0 := by apply Matrix.ext; unfold raw1701step1 raw1701step0; decide +kernel
      have hl : raw1701step0Labels = labelEmbedding7 ∘ raw1701step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1701step0 raw1701step0Labels raw1701step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4767 node4767Labels := by rfl

def raw1702 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1702Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1702step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1702step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1702 raw1702Labels = mixedMoment B node1967 node1967Labels := by
  calc
    mixedMoment B raw1702 raw1702Labels = mixedMoment B raw1702step0 raw1702step0Labels := by
      have ha : raw1702step0 = (fun i j => raw1702 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1702step0 raw1702; decide +kernel
      have hl : raw1702step0Labels = raw1702Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1702 raw1702Labels permutation152 permutation4
    _ = mixedMoment B node1967 node1967Labels := by rfl

def raw1703 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1703Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1703step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw1703step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1703step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1703step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1703step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1703step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1703 raw1703Labels = mixedMoment B node2183 node2183Labels := by
  calc
    mixedMoment B raw1703 raw1703Labels = mixedMoment B raw1703step0 raw1703step0Labels := by
      have ha : raw1703step0 = (fun i j => raw1703 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1703step0 raw1703; decide +kernel
      have hl : raw1703step0Labels = raw1703Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1703 raw1703Labels permutation152 permutation6
    mixedMoment B raw1703step0 raw1703step0Labels = mixedMoment B raw1703step1 raw1703step1Labels := by
      have ha : raw1703step1 = -raw1703step0 := by apply Matrix.ext; change ∀ i j, raw1703step1 i j = -(raw1703step0 i j); unfold raw1703step1 raw1703step0; decide +kernel
      have hl : raw1703step1Labels = raw1703step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1703step1 raw1703step1Labels = mixedMoment B raw1703step2 raw1703step2Labels := by
      have ha : raw1703step2 = raw1703step1 := by apply Matrix.ext; unfold raw1703step2 raw1703step1; decide +kernel
      have hl : raw1703step1Labels = labelEmbedding1 ∘ raw1703step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1703step1 raw1703step1Labels raw1703step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2183 node2183Labels := by rfl

def raw1704 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, 3, -2]]
def raw1704Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw1704step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw1704step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1704 raw1704Labels = mixedMoment B node4769 node4769Labels := by
  calc
    mixedMoment B raw1704 raw1704Labels = mixedMoment B raw1704step0 raw1704step0Labels := by
      have ha : raw1704step0 = (fun i j => raw1704 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1704step0 raw1704; decide +kernel
      have hl : raw1704step0Labels = raw1704Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1704 raw1704Labels permutation32 permutation4
    mixedMoment B raw1704step0 raw1704step0Labels = mixedMoment B raw1704step1 raw1704step1Labels := by
      have ha : raw1704step1 = raw1704step0 := by apply Matrix.ext; unfold raw1704step1 raw1704step0; decide +kernel
      have hl : raw1704step0Labels = labelEmbedding7 ∘ raw1704step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1704step0 raw1704step0Labels raw1704step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4769 node4769Labels := by rfl

def raw1705 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, 3, -2]]
def raw1705Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw1705step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1705 raw1705Labels = mixedMoment B node1969 node1969Labels := by
  calc
    mixedMoment B raw1705 raw1705Labels = mixedMoment B raw1705step0 raw1705step0Labels := by
      have ha : raw1705step0 = (fun i j => raw1705 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1705step0 raw1705; decide +kernel
      have hl : raw1705step0Labels = raw1705Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1705 raw1705Labels permutation32 permutation4
    _ = mixedMoment B node1969 node1969Labels := by rfl

def raw1706 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, 3, -2]]
def raw1706Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw1706step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw1706step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1706step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw1706step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1706 raw1706Labels = mixedMoment B node2185 node2185Labels := by
  calc
    mixedMoment B raw1706 raw1706Labels = mixedMoment B raw1706step0 raw1706step0Labels := by
      have ha : raw1706step0 = (fun i j => raw1706 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1706step0 raw1706; decide +kernel
      have hl : raw1706step0Labels = raw1706Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1706 raw1706Labels permutation32 permutation6
    mixedMoment B raw1706step0 raw1706step0Labels = mixedMoment B raw1706step1 raw1706step1Labels := by
      have ha : raw1706step1 = -raw1706step0 := by apply Matrix.ext; change ∀ i j, raw1706step1 i j = -(raw1706step0 i j); unfold raw1706step1 raw1706step0; decide +kernel
      have hl : raw1706step1Labels = raw1706step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1706step1 raw1706step1Labels = mixedMoment B raw1706step2 raw1706step2Labels := by
      have ha : raw1706step2 = raw1706step1 := by apply Matrix.ext; unfold raw1706step2 raw1706step1; decide +kernel
      have hl : raw1706step1Labels = labelEmbedding1 ∘ raw1706step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1706step1 raw1706step1Labels raw1706step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2185 node2185Labels := by rfl

def raw1707 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2], ![-2, 3, -1]]
def raw1707Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw1707step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw1707step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1707 raw1707Labels = mixedMoment B node4770 node4770Labels := by
  calc
    mixedMoment B raw1707 raw1707Labels = mixedMoment B raw1707step0 raw1707step0Labels := by
      have ha : raw1707step0 = (fun i j => raw1707 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1707step0 raw1707; decide +kernel
      have hl : raw1707step0Labels = raw1707Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1707 raw1707Labels permutation32 permutation4
    mixedMoment B raw1707step0 raw1707step0Labels = mixedMoment B raw1707step1 raw1707step1Labels := by
      have ha : raw1707step1 = raw1707step0 := by apply Matrix.ext; unfold raw1707step1 raw1707step0; decide +kernel
      have hl : raw1707step0Labels = labelEmbedding7 ∘ raw1707step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1707step0 raw1707step0Labels raw1707step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4770 node4770Labels := by rfl

def raw1708 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2], ![-2, 3, -1]]
def raw1708Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw1708step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1708 raw1708Labels = mixedMoment B node1970 node1970Labels := by
  calc
    mixedMoment B raw1708 raw1708Labels = mixedMoment B raw1708step0 raw1708step0Labels := by
      have ha : raw1708step0 = (fun i j => raw1708 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1708step0 raw1708; decide +kernel
      have hl : raw1708step0Labels = raw1708Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1708 raw1708Labels permutation32 permutation4
    _ = mixedMoment B node1970 node1970Labels := by rfl

def raw1709 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2], ![-2, 3, -1]]
def raw1709Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw1709step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw1709step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1709step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw1709step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1709 raw1709Labels = mixedMoment B node2186 node2186Labels := by
  calc
    mixedMoment B raw1709 raw1709Labels = mixedMoment B raw1709step0 raw1709step0Labels := by
      have ha : raw1709step0 = (fun i j => raw1709 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1709step0 raw1709; decide +kernel
      have hl : raw1709step0Labels = raw1709Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1709 raw1709Labels permutation33 permutation6
    mixedMoment B raw1709step0 raw1709step0Labels = mixedMoment B raw1709step1 raw1709step1Labels := by
      have ha : raw1709step1 = -raw1709step0 := by apply Matrix.ext; change ∀ i j, raw1709step1 i j = -(raw1709step0 i j); unfold raw1709step1 raw1709step0; decide +kernel
      have hl : raw1709step1Labels = raw1709step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1709step1 raw1709step1Labels = mixedMoment B raw1709step2 raw1709step2Labels := by
      have ha : raw1709step2 = raw1709step1 := by apply Matrix.ext; unfold raw1709step2 raw1709step1; decide +kernel
      have hl : raw1709step1Labels = labelEmbedding1 ∘ raw1709step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1709step1 raw1709step1Labels raw1709step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2186 node2186Labels := by rfl

def raw1710 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 3, -3]]
def raw1710Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1710step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1710step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1710step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1710step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1710 raw1710Labels = mixedMoment B node4778 node4778Labels := by
  calc
    mixedMoment B raw1710 raw1710Labels = mixedMoment B raw1710step0 raw1710step0Labels := by
      have ha : raw1710step0 = (fun i j => raw1710 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1710step0 raw1710; decide +kernel
      have hl : raw1710step0Labels = raw1710Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1710 raw1710Labels permutation152 permutation4
    mixedMoment B raw1710step0 raw1710step0Labels = mixedMoment B raw1710step1 raw1710step1Labels := by
      have ha : raw1710step1 = raw1710step0 := by apply Matrix.ext; unfold raw1710step1 raw1710step0; decide +kernel
      have hl : raw1710step0Labels = labelEmbedding7 ∘ raw1710step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1710step0 raw1710step0Labels raw1710step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4778 node4778Labels := by rfl

def raw1711 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 3, -3]]
def raw1711Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1711step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1711step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1711 raw1711Labels = mixedMoment B node1986 node1986Labels := by
  calc
    mixedMoment B raw1711 raw1711Labels = mixedMoment B raw1711step0 raw1711step0Labels := by
      have ha : raw1711step0 = (fun i j => raw1711 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1711step0 raw1711; decide +kernel
      have hl : raw1711step0Labels = raw1711Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1711 raw1711Labels permutation152 permutation4
    _ = mixedMoment B node1986 node1986Labels := by rfl

def raw1712 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 3, -3]]
def raw1712Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1712step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1712step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1712step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1712step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1712 raw1712Labels = mixedMoment B node1986 node1986Labels := by
  calc
    mixedMoment B raw1712 raw1712Labels = mixedMoment B raw1712step0 raw1712step0Labels := by
      have ha : raw1712step0 = (fun i j => raw1712 (permutation662 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1712step0 raw1712; decide +kernel
      have hl : raw1712step0Labels = raw1712Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1712 raw1712Labels permutation662 permutation6
    mixedMoment B raw1712step0 raw1712step0Labels = mixedMoment B raw1712step1 raw1712step1Labels := by
      have ha : raw1712step1 = raw1712step0 := by apply Matrix.ext; unfold raw1712step1 raw1712step0; decide +kernel
      have hl : raw1712step0Labels = labelEmbedding1 ∘ raw1712step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1712step0 raw1712step0Labels raw1712step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1986 node1986Labels := by rfl

def raw1713 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1713Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1713step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1713step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1713step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1713 raw1713Labels = mixedMoment B node4779 node4779Labels := by
  calc
    mixedMoment B raw1713 raw1713Labels = mixedMoment B raw1713step0 raw1713step0Labels := by
      have ha : raw1713step0 = (fun i j => raw1713 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1713step0 raw1713; decide +kernel
      have hl : raw1713step0Labels = raw1713Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1713 raw1713Labels permutation152 permutation4
    mixedMoment B raw1713step0 raw1713step0Labels = mixedMoment B raw1713step1 raw1713step1Labels := by
      have ha : raw1713step1 = raw1713step0 := by apply Matrix.ext; unfold raw1713step1 raw1713step0; decide +kernel
      have hl : raw1713step0Labels = labelEmbedding7 ∘ raw1713step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1713step0 raw1713step0Labels raw1713step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4779 node4779Labels := by rfl

def raw1714 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1714Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1714step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1714step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1714 raw1714Labels = mixedMoment B node1987 node1987Labels := by
  calc
    mixedMoment B raw1714 raw1714Labels = mixedMoment B raw1714step0 raw1714step0Labels := by
      have ha : raw1714step0 = (fun i j => raw1714 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1714step0 raw1714; decide +kernel
      have hl : raw1714step0Labels = raw1714Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1714 raw1714Labels permutation152 permutation4
    _ = mixedMoment B node1987 node1987Labels := by rfl

def raw1715 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1715Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1715step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw1715step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1715step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1715step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1715step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1715step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1715 raw1715Labels = mixedMoment B node1996 node1996Labels := by
  calc
    mixedMoment B raw1715 raw1715Labels = mixedMoment B raw1715step0 raw1715step0Labels := by
      have ha : raw1715step0 = (fun i j => raw1715 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1715step0 raw1715; decide +kernel
      have hl : raw1715step0Labels = raw1715Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1715 raw1715Labels permutation176 permutation6
    mixedMoment B raw1715step0 raw1715step0Labels = mixedMoment B raw1715step1 raw1715step1Labels := by
      have ha : raw1715step1 = -raw1715step0 := by apply Matrix.ext; change ∀ i j, raw1715step1 i j = -(raw1715step0 i j); unfold raw1715step1 raw1715step0; decide +kernel
      have hl : raw1715step1Labels = raw1715step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1715step1 raw1715step1Labels = mixedMoment B raw1715step2 raw1715step2Labels := by
      have ha : raw1715step2 = raw1715step1 := by apply Matrix.ext; unfold raw1715step2 raw1715step1; decide +kernel
      have hl : raw1715step1Labels = labelEmbedding1 ∘ raw1715step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1715step1 raw1715step1Labels raw1715step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1996 node1996Labels := by rfl

def raw1716 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1716Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1716step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1716step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1716step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1716 raw1716Labels = mixedMoment B node4782 node4782Labels := by
  calc
    mixedMoment B raw1716 raw1716Labels = mixedMoment B raw1716step0 raw1716step0Labels := by
      have ha : raw1716step0 = (fun i j => raw1716 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1716step0 raw1716; decide +kernel
      have hl : raw1716step0Labels = raw1716Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1716 raw1716Labels permutation152 permutation4
    mixedMoment B raw1716step0 raw1716step0Labels = mixedMoment B raw1716step1 raw1716step1Labels := by
      have ha : raw1716step1 = raw1716step0 := by apply Matrix.ext; unfold raw1716step1 raw1716step0; decide +kernel
      have hl : raw1716step0Labels = labelEmbedding7 ∘ raw1716step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1716step0 raw1716step0Labels raw1716step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4782 node4782Labels := by rfl

def raw1717 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1717Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1717step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1717 raw1717Labels = mixedMoment B node1990 node1990Labels := by
  calc
    mixedMoment B raw1717 raw1717Labels = mixedMoment B raw1717step0 raw1717step0Labels := by
      have ha : raw1717step0 = (fun i j => raw1717 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1717step0 raw1717; decide +kernel
      have hl : raw1717step0Labels = raw1717Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1717 raw1717Labels permutation152 permutation4
    _ = mixedMoment B node1990 node1990Labels := by rfl

def raw1718 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1718Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1718step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw1718step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1718step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1718step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1718step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1718 raw1718Labels = mixedMoment B node1997 node1997Labels := by
  calc
    mixedMoment B raw1718 raw1718Labels = mixedMoment B raw1718step0 raw1718step0Labels := by
      have ha : raw1718step0 = (fun i j => raw1718 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1718step0 raw1718; decide +kernel
      have hl : raw1718step0Labels = raw1718Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1718 raw1718Labels permutation176 permutation6
    mixedMoment B raw1718step0 raw1718step0Labels = mixedMoment B raw1718step1 raw1718step1Labels := by
      have ha : raw1718step1 = -raw1718step0 := by apply Matrix.ext; change ∀ i j, raw1718step1 i j = -(raw1718step0 i j); unfold raw1718step1 raw1718step0; decide +kernel
      have hl : raw1718step1Labels = raw1718step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1718step1 raw1718step1Labels = mixedMoment B raw1718step2 raw1718step2Labels := by
      have ha : raw1718step2 = raw1718step1 := by apply Matrix.ext; unfold raw1718step2 raw1718step1; decide +kernel
      have hl : raw1718step1Labels = labelEmbedding1 ∘ raw1718step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1718step1 raw1718step1Labels raw1718step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1997 node1997Labels := by rfl

def raw1719 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw1719Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1719step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1719step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1719step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1719 raw1719Labels = mixedMoment B node4787 node4787Labels := by
  calc
    mixedMoment B raw1719 raw1719Labels = mixedMoment B raw1719step0 raw1719step0Labels := by
      have ha : raw1719step0 = (fun i j => raw1719 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1719step0 raw1719; decide +kernel
      have hl : raw1719step0Labels = raw1719Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1719 raw1719Labels permutation152 permutation4
    mixedMoment B raw1719step0 raw1719step0Labels = mixedMoment B raw1719step1 raw1719step1Labels := by
      have ha : raw1719step1 = raw1719step0 := by apply Matrix.ext; unfold raw1719step1 raw1719step0; decide +kernel
      have hl : raw1719step0Labels = labelEmbedding7 ∘ raw1719step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1719step0 raw1719step0Labels raw1719step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4787 node4787Labels := by rfl

def raw1720 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw1720Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1720step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1720step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1720 raw1720Labels = mixedMoment B node2000 node2000Labels := by
  calc
    mixedMoment B raw1720 raw1720Labels = mixedMoment B raw1720step0 raw1720step0Labels := by
      have ha : raw1720step0 = (fun i j => raw1720 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1720step0 raw1720; decide +kernel
      have hl : raw1720step0Labels = raw1720Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1720 raw1720Labels permutation152 permutation4
    _ = mixedMoment B node2000 node2000Labels := by rfl

def raw1721 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw1721Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1721step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw1721step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1721step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1721step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1721step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1721step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1721 raw1721Labels = mixedMoment B node2000 node2000Labels := by
  calc
    mixedMoment B raw1721 raw1721Labels = mixedMoment B raw1721step0 raw1721step0Labels := by
      have ha : raw1721step0 = (fun i j => raw1721 (permutation177 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1721step0 raw1721; decide +kernel
      have hl : raw1721step0Labels = raw1721Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1721 raw1721Labels permutation177 permutation6
    mixedMoment B raw1721step0 raw1721step0Labels = mixedMoment B raw1721step1 raw1721step1Labels := by
      have ha : raw1721step1 = -raw1721step0 := by apply Matrix.ext; change ∀ i j, raw1721step1 i j = -(raw1721step0 i j); unfold raw1721step1 raw1721step0; decide +kernel
      have hl : raw1721step1Labels = raw1721step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1721step1 raw1721step1Labels = mixedMoment B raw1721step2 raw1721step2Labels := by
      have ha : raw1721step2 = raw1721step1 := by apply Matrix.ext; unfold raw1721step2 raw1721step1; decide +kernel
      have hl : raw1721step1Labels = labelEmbedding1 ∘ raw1721step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1721step1 raw1721step1Labels raw1721step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2000 node2000Labels := by rfl

def raw1722 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![-1, 3, -2]]
def raw1722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw1722step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw1722step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1722 raw1722Labels = mixedMoment B node4788 node4788Labels := by
  calc
    mixedMoment B raw1722 raw1722Labels = mixedMoment B raw1722step0 raw1722step0Labels := by
      have ha : raw1722step0 = (fun i j => raw1722 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1722step0 raw1722; decide +kernel
      have hl : raw1722step0Labels = raw1722Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1722 raw1722Labels permutation32 permutation4
    mixedMoment B raw1722step0 raw1722step0Labels = mixedMoment B raw1722step1 raw1722step1Labels := by
      have ha : raw1722step1 = raw1722step0 := by apply Matrix.ext; unfold raw1722step1 raw1722step0; decide +kernel
      have hl : raw1722step0Labels = labelEmbedding7 ∘ raw1722step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1722step0 raw1722step0Labels raw1722step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4788 node4788Labels := by rfl

def raw1723 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![-1, 3, -2]]
def raw1723Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw1723step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1723 raw1723Labels = mixedMoment B node2003 node2003Labels := by
  calc
    mixedMoment B raw1723 raw1723Labels = mixedMoment B raw1723step0 raw1723step0Labels := by
      have ha : raw1723step0 = (fun i j => raw1723 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1723step0 raw1723; decide +kernel
      have hl : raw1723step0Labels = raw1723Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1723 raw1723Labels permutation32 permutation4
    _ = mixedMoment B node2003 node2003Labels := by rfl

def raw1724 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![-1, 3, -2]]
def raw1724Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![-2, -1, 3]]
def raw1724step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw1724step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw1724step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1724 raw1724Labels = mixedMoment B node2006 node2006Labels := by
  calc
    mixedMoment B raw1724 raw1724Labels = mixedMoment B raw1724step0 raw1724step0Labels := by
      have ha : raw1724step0 = (fun i j => raw1724 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1724step0 raw1724; decide +kernel
      have hl : raw1724step0Labels = raw1724Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1724 raw1724Labels permutation38 permutation6
    mixedMoment B raw1724step0 raw1724step0Labels = mixedMoment B raw1724step1 raw1724step1Labels := by
      have ha : raw1724step1 = -raw1724step0 := by apply Matrix.ext; change ∀ i j, raw1724step1 i j = -(raw1724step0 i j); unfold raw1724step1 raw1724step0; decide +kernel
      have hl : raw1724step1Labels = raw1724step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1724step1 raw1724step1Labels = mixedMoment B raw1724step2 raw1724step2Labels := by
      have ha : raw1724step2 = raw1724step1 := by apply Matrix.ext; unfold raw1724step2 raw1724step1; decide +kernel
      have hl : raw1724step1Labels = labelEmbedding1 ∘ raw1724step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1724step1 raw1724step1Labels raw1724step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2006 node2006Labels := by rfl

def raw1725 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw1725Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1725step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1725step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1725step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1725step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1725 raw1725Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw1725 raw1725Labels = mixedMoment B raw1725step0 raw1725step0Labels := by
      have ha : raw1725step0 = (fun i j => raw1725 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1725step0 raw1725; decide +kernel
      have hl : raw1725step0Labels = raw1725Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1725 raw1725Labels permutation152 permutation4
    mixedMoment B raw1725step0 raw1725step0Labels = mixedMoment B raw1725step1 raw1725step1Labels := by
      have ha : raw1725step1 = raw1725step0 := by apply Matrix.ext; unfold raw1725step1 raw1725step0; decide +kernel
      have hl : raw1725step0Labels = labelEmbedding7 ∘ raw1725step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1725step0 raw1725step0Labels raw1725step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

def raw1726 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw1726Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1726step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1726step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1726 raw1726Labels = mixedMoment B node2016 node2016Labels := by
  calc
    mixedMoment B raw1726 raw1726Labels = mixedMoment B raw1726step0 raw1726step0Labels := by
      have ha : raw1726step0 = (fun i j => raw1726 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1726step0 raw1726; decide +kernel
      have hl : raw1726step0Labels = raw1726Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1726 raw1726Labels permutation152 permutation4
    _ = mixedMoment B node2016 node2016Labels := by rfl

def raw1727 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw1727Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1727step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw1727step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1727step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1727step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1727step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1727step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1727 raw1727Labels = mixedMoment B node2075 node2075Labels := by
  calc
    mixedMoment B raw1727 raw1727Labels = mixedMoment B raw1727step0 raw1727step0Labels := by
      have ha : raw1727step0 = (fun i j => raw1727 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1727step0 raw1727; decide +kernel
      have hl : raw1727step0Labels = raw1727Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1727 raw1727Labels permutation200 permutation6
    mixedMoment B raw1727step0 raw1727step0Labels = mixedMoment B raw1727step1 raw1727step1Labels := by
      have ha : raw1727step1 = -raw1727step0 := by apply Matrix.ext; change ∀ i j, raw1727step1 i j = -(raw1727step0 i j); unfold raw1727step1 raw1727step0; decide +kernel
      have hl : raw1727step1Labels = raw1727step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1727step1 raw1727step1Labels = mixedMoment B raw1727step2 raw1727step2Labels := by
      have ha : raw1727step2 = raw1727step1 := by apply Matrix.ext; unfold raw1727step2 raw1727step1; decide +kernel
      have hl : raw1727step1Labels = labelEmbedding1 ∘ raw1727step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1727step1 raw1727step1Labels raw1727step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2075 node2075Labels := by rfl

def raw1728 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 3, -3]]
def raw1728Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1728step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1728step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1728 raw1728Labels = mixedMoment B node4800 node4800Labels := by
  calc
    mixedMoment B raw1728 raw1728Labels = mixedMoment B raw1728step0 raw1728step0Labels := by
      have ha : raw1728step0 = (fun i j => raw1728 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1728step0 raw1728; decide +kernel
      have hl : raw1728step0Labels = raw1728Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1728 raw1728Labels permutation32 permutation4
    mixedMoment B raw1728step0 raw1728step0Labels = mixedMoment B raw1728step1 raw1728step1Labels := by
      have ha : raw1728step1 = raw1728step0 := by apply Matrix.ext; unfold raw1728step1 raw1728step0; decide +kernel
      have hl : raw1728step0Labels = labelEmbedding7 ∘ raw1728step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1728step0 raw1728step0Labels raw1728step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4800 node4800Labels := by rfl

def raw1729 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 3, -3]]
def raw1729Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1729step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1729 raw1729Labels = mixedMoment B node2018 node2018Labels := by
  calc
    mixedMoment B raw1729 raw1729Labels = mixedMoment B raw1729step0 raw1729step0Labels := by
      have ha : raw1729step0 = (fun i j => raw1729 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1729step0 raw1729; decide +kernel
      have hl : raw1729step0Labels = raw1729Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1729 raw1729Labels permutation32 permutation4
    _ = mixedMoment B node2018 node2018Labels := by rfl

def raw1730 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 3, -3]]
def raw1730Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1730step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1730step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1730 raw1730Labels = mixedMoment B node2018 node2018Labels := by
  calc
    mixedMoment B raw1730 raw1730Labels = mixedMoment B raw1730step0 raw1730step0Labels := by
      have ha : raw1730step0 = (fun i j => raw1730 (permutation143 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1730step0 raw1730; decide +kernel
      have hl : raw1730step0Labels = raw1730Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1730 raw1730Labels permutation143 permutation6
    mixedMoment B raw1730step0 raw1730step0Labels = mixedMoment B raw1730step1 raw1730step1Labels := by
      have ha : raw1730step1 = raw1730step0 := by apply Matrix.ext; unfold raw1730step1 raw1730step0; decide +kernel
      have hl : raw1730step0Labels = labelEmbedding1 ∘ raw1730step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1730step0 raw1730step0Labels raw1730step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2018 node2018Labels := by rfl

def raw1731 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1731Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1731step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1731step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1731step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1731 raw1731Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw1731 raw1731Labels = mixedMoment B raw1731step0 raw1731step0Labels := by
      have ha : raw1731step0 = (fun i j => raw1731 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1731step0 raw1731; decide +kernel
      have hl : raw1731step0Labels = raw1731Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1731 raw1731Labels permutation152 permutation4
    mixedMoment B raw1731step0 raw1731step0Labels = mixedMoment B raw1731step1 raw1731step1Labels := by
      have ha : raw1731step1 = raw1731step0 := by apply Matrix.ext; unfold raw1731step1 raw1731step0; decide +kernel
      have hl : raw1731step0Labels = labelEmbedding7 ∘ raw1731step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1731step0 raw1731step0Labels raw1731step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4801 node4801Labels := by rfl

def raw1732 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1732Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1732step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1732step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1732 raw1732Labels = mixedMoment B node2019 node2019Labels := by
  calc
    mixedMoment B raw1732 raw1732Labels = mixedMoment B raw1732step0 raw1732step0Labels := by
      have ha : raw1732step0 = (fun i j => raw1732 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1732step0 raw1732; decide +kernel
      have hl : raw1732step0Labels = raw1732Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1732 raw1732Labels permutation152 permutation4
    _ = mixedMoment B node2019 node2019Labels := by rfl

def raw1733 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1733Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1733step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw1733step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1733step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw1733step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1733step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw1733step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1733 raw1733Labels = mixedMoment B node2190 node2190Labels := by
  calc
    mixedMoment B raw1733 raw1733Labels = mixedMoment B raw1733step0 raw1733step0Labels := by
      have ha : raw1733step0 = (fun i j => raw1733 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1733step0 raw1733; decide +kernel
      have hl : raw1733step0Labels = raw1733Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1733 raw1733Labels permutation160 permutation6
    mixedMoment B raw1733step0 raw1733step0Labels = mixedMoment B raw1733step1 raw1733step1Labels := by
      have ha : raw1733step1 = -raw1733step0 := by apply Matrix.ext; change ∀ i j, raw1733step1 i j = -(raw1733step0 i j); unfold raw1733step1 raw1733step0; decide +kernel
      have hl : raw1733step1Labels = raw1733step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1733step1 raw1733step1Labels = mixedMoment B raw1733step2 raw1733step2Labels := by
      have ha : raw1733step2 = raw1733step1 := by apply Matrix.ext; unfold raw1733step2 raw1733step1; decide +kernel
      have hl : raw1733step1Labels = labelEmbedding1 ∘ raw1733step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1733step1 raw1733step1Labels raw1733step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2190 node2190Labels := by rfl

def raw1734 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw1734Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1734step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1734step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1734step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1734step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1734 raw1734Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw1734 raw1734Labels = mixedMoment B raw1734step0 raw1734step0Labels := by
      have ha : raw1734step0 = (fun i j => raw1734 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1734step0 raw1734; decide +kernel
      have hl : raw1734step0Labels = raw1734Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1734 raw1734Labels permutation152 permutation4
    mixedMoment B raw1734step0 raw1734step0Labels = mixedMoment B raw1734step1 raw1734step1Labels := by
      have ha : raw1734step1 = raw1734step0 := by apply Matrix.ext; unfold raw1734step1 raw1734step0; decide +kernel
      have hl : raw1734step0Labels = labelEmbedding7 ∘ raw1734step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1734step0 raw1734step0Labels raw1734step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw1735 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw1735Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1735step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1735step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1735 raw1735Labels = mixedMoment B node2020 node2020Labels := by
  calc
    mixedMoment B raw1735 raw1735Labels = mixedMoment B raw1735step0 raw1735step0Labels := by
      have ha : raw1735step0 = (fun i j => raw1735 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1735step0 raw1735; decide +kernel
      have hl : raw1735step0Labels = raw1735Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1735 raw1735Labels permutation152 permutation4
    _ = mixedMoment B node2020 node2020Labels := by rfl

def raw1736 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw1736Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw1736step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1736step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw1736step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1736step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw1736step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1736 raw1736Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw1736 raw1736Labels = mixedMoment B raw1736step0 raw1736step0Labels := by
      have ha : raw1736step0 = (fun i j => raw1736 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1736step0 raw1736; decide +kernel
      have hl : raw1736step0Labels = raw1736Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1736 raw1736Labels permutation158 permutation6
    mixedMoment B raw1736step0 raw1736step0Labels = mixedMoment B raw1736step1 raw1736step1Labels := by
      have ha : raw1736step1 = -raw1736step0 := by apply Matrix.ext; change ∀ i j, raw1736step1 i j = -(raw1736step0 i j); unfold raw1736step1 raw1736step0; decide +kernel
      have hl : raw1736step1Labels = raw1736step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1736step1 raw1736step1Labels = mixedMoment B raw1736step2 raw1736step2Labels := by
      have ha : raw1736step2 = raw1736step1 := by apply Matrix.ext; unfold raw1736step2 raw1736step1; decide +kernel
      have hl : raw1736step1Labels = labelEmbedding1 ∘ raw1736step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1736step1 raw1736step1Labels raw1736step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2202 node2202Labels := by rfl

def raw1737 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1737Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw1737step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw1737step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1737 raw1737Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw1737 raw1737Labels = mixedMoment B raw1737step0 raw1737step0Labels := by
      have ha : raw1737step0 = (fun i j => raw1737 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1737step0 raw1737; decide +kernel
      have hl : raw1737step0Labels = raw1737Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1737 raw1737Labels permutation32 permutation4
    mixedMoment B raw1737step0 raw1737step0Labels = mixedMoment B raw1737step1 raw1737step1Labels := by
      have ha : raw1737step1 = raw1737step0 := by apply Matrix.ext; unfold raw1737step1 raw1737step0; decide +kernel
      have hl : raw1737step0Labels = labelEmbedding7 ∘ raw1737step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1737step0 raw1737step0Labels raw1737step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4804 node4804Labels := by rfl

def raw1738 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1738Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw1738step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1738 raw1738Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw1738 raw1738Labels = mixedMoment B raw1738step0 raw1738step0Labels := by
      have ha : raw1738step0 = (fun i j => raw1738 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1738step0 raw1738; decide +kernel
      have hl : raw1738step0Labels = raw1738Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1738 raw1738Labels permutation32 permutation4
    _ = mixedMoment B node2022 node2022Labels := by rfl

def raw1739 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1739Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw1739step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw1739step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw1739step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1739 raw1739Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw1739 raw1739Labels = mixedMoment B raw1739step0 raw1739step0Labels := by
      have ha : raw1739step0 = (fun i j => raw1739 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1739step0 raw1739; decide +kernel
      have hl : raw1739step0Labels = raw1739Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1739 raw1739Labels permutation34 permutation6
    mixedMoment B raw1739step0 raw1739step0Labels = mixedMoment B raw1739step1 raw1739step1Labels := by
      have ha : raw1739step1 = -raw1739step0 := by apply Matrix.ext; change ∀ i j, raw1739step1 i j = -(raw1739step0 i j); unfold raw1739step1 raw1739step0; decide +kernel
      have hl : raw1739step1Labels = raw1739step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1739step1 raw1739step1Labels = mixedMoment B raw1739step2 raw1739step2Labels := by
      have ha : raw1739step2 = raw1739step1 := by apply Matrix.ext; unfold raw1739step2 raw1739step1; decide +kernel
      have hl : raw1739step1Labels = labelEmbedding1 ∘ raw1739step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1739step1 raw1739step1Labels raw1739step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

def raw1740 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1740Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1740step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1740step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1740step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1740 raw1740Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw1740 raw1740Labels = mixedMoment B raw1740step0 raw1740step0Labels := by
      have ha : raw1740step0 = (fun i j => raw1740 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1740step0 raw1740; decide +kernel
      have hl : raw1740step0Labels = raw1740Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1740 raw1740Labels permutation152 permutation4
    mixedMoment B raw1740step0 raw1740step0Labels = mixedMoment B raw1740step1 raw1740step1Labels := by
      have ha : raw1740step1 = raw1740step0 := by apply Matrix.ext; unfold raw1740step1 raw1740step0; decide +kernel
      have hl : raw1740step0Labels = labelEmbedding7 ∘ raw1740step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1740step0 raw1740step0Labels raw1740step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4805 node4805Labels := by rfl

def raw1741 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1741Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1741step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1741 raw1741Labels = mixedMoment B node2023 node2023Labels := by
  calc
    mixedMoment B raw1741 raw1741Labels = mixedMoment B raw1741step0 raw1741step0Labels := by
      have ha : raw1741step0 = (fun i j => raw1741 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1741step0 raw1741; decide +kernel
      have hl : raw1741step0Labels = raw1741Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1741 raw1741Labels permutation152 permutation4
    _ = mixedMoment B node2023 node2023Labels := by rfl

def raw1742 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1742Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw1742step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1742step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1742step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1742step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1742step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1742 raw1742Labels = mixedMoment B node2214 node2214Labels := by
  calc
    mixedMoment B raw1742 raw1742Labels = mixedMoment B raw1742step0 raw1742step0Labels := by
      have ha : raw1742step0 = (fun i j => raw1742 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1742step0 raw1742; decide +kernel
      have hl : raw1742step0Labels = raw1742Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1742 raw1742Labels permutation170 permutation6
    mixedMoment B raw1742step0 raw1742step0Labels = mixedMoment B raw1742step1 raw1742step1Labels := by
      have ha : raw1742step1 = -raw1742step0 := by apply Matrix.ext; change ∀ i j, raw1742step1 i j = -(raw1742step0 i j); unfold raw1742step1 raw1742step0; decide +kernel
      have hl : raw1742step1Labels = raw1742step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1742step1 raw1742step1Labels = mixedMoment B raw1742step2 raw1742step2Labels := by
      have ha : raw1742step2 = raw1742step1 := by apply Matrix.ext; unfold raw1742step2 raw1742step1; decide +kernel
      have hl : raw1742step1Labels = labelEmbedding1 ∘ raw1742step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1742step1 raw1742step1Labels raw1742step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2214 node2214Labels := by rfl

def raw1743 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1743Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1743step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1743step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1743 raw1743Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw1743 raw1743Labels = mixedMoment B raw1743step0 raw1743step0Labels := by
      have ha : raw1743step0 = (fun i j => raw1743 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1743step0 raw1743; decide +kernel
      have hl : raw1743step0Labels = raw1743Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1743 raw1743Labels permutation32 permutation4
    mixedMoment B raw1743step0 raw1743step0Labels = mixedMoment B raw1743step1 raw1743step1Labels := by
      have ha : raw1743step1 = raw1743step0 := by apply Matrix.ext; unfold raw1743step1 raw1743step0; decide +kernel
      have hl : raw1743step0Labels = labelEmbedding7 ∘ raw1743step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1743step0 raw1743step0Labels raw1743step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw1744 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1744Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1744step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1744 raw1744Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw1744 raw1744Labels = mixedMoment B raw1744step0 raw1744step0Labels := by
      have ha : raw1744step0 = (fun i j => raw1744 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1744step0 raw1744; decide +kernel
      have hl : raw1744step0Labels = raw1744Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1744 raw1744Labels permutation32 permutation4
    _ = mixedMoment B node2025 node2025Labels := by rfl

def raw1745 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1745Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw1745step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw1745step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1745step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw1745step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1745 raw1745Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw1745 raw1745Labels = mixedMoment B raw1745step0 raw1745step0Labels := by
      have ha : raw1745step0 = (fun i j => raw1745 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1745step0 raw1745; decide +kernel
      have hl : raw1745step0Labels = raw1745Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1745 raw1745Labels permutation32 permutation6
    mixedMoment B raw1745step0 raw1745step0Labels = mixedMoment B raw1745step1 raw1745step1Labels := by
      have ha : raw1745step1 = -raw1745step0 := by apply Matrix.ext; change ∀ i j, raw1745step1 i j = -(raw1745step0 i j); unfold raw1745step1 raw1745step0; decide +kernel
      have hl : raw1745step1Labels = raw1745step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1745step1 raw1745step1Labels = mixedMoment B raw1745step2 raw1745step2Labels := by
      have ha : raw1745step2 = raw1745step1 := by apply Matrix.ext; unfold raw1745step2 raw1745step1; decide +kernel
      have hl : raw1745step1Labels = labelEmbedding1 ∘ raw1745step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1745step1 raw1745step1Labels raw1745step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

def raw1746 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1746Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1746step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1746step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1746 raw1746Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw1746 raw1746Labels = mixedMoment B raw1746step0 raw1746step0Labels := by
      have ha : raw1746step0 = (fun i j => raw1746 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1746step0 raw1746; decide +kernel
      have hl : raw1746step0Labels = raw1746Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1746 raw1746Labels permutation32 permutation4
    mixedMoment B raw1746step0 raw1746step0Labels = mixedMoment B raw1746step1 raw1746step1Labels := by
      have ha : raw1746step1 = raw1746step0 := by apply Matrix.ext; unfold raw1746step1 raw1746step0; decide +kernel
      have hl : raw1746step0Labels = labelEmbedding7 ∘ raw1746step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1746step0 raw1746step0Labels raw1746step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

def raw1747 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1747Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1747step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1747 raw1747Labels = mixedMoment B node2028 node2028Labels := by
  calc
    mixedMoment B raw1747 raw1747Labels = mixedMoment B raw1747step0 raw1747step0Labels := by
      have ha : raw1747step0 = (fun i j => raw1747 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1747step0 raw1747; decide +kernel
      have hl : raw1747step0Labels = raw1747Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1747 raw1747Labels permutation32 permutation4
    _ = mixedMoment B node2028 node2028Labels := by rfl

def raw1748 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1748Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw1748step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw1748step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1748step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw1748step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1748 raw1748Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw1748 raw1748Labels = mixedMoment B raw1748step0 raw1748step0Labels := by
      have ha : raw1748step0 = (fun i j => raw1748 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1748step0 raw1748; decide +kernel
      have hl : raw1748step0Labels = raw1748Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1748 raw1748Labels permutation34 permutation6
    mixedMoment B raw1748step0 raw1748step0Labels = mixedMoment B raw1748step1 raw1748step1Labels := by
      have ha : raw1748step1 = -raw1748step0 := by apply Matrix.ext; change ∀ i j, raw1748step1 i j = -(raw1748step0 i j); unfold raw1748step1 raw1748step0; decide +kernel
      have hl : raw1748step1Labels = raw1748step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1748step1 raw1748step1Labels = mixedMoment B raw1748step2 raw1748step2Labels := by
      have ha : raw1748step2 = raw1748step1 := by apply Matrix.ext; unfold raw1748step2 raw1748step1; decide +kernel
      have hl : raw1748step1Labels = labelEmbedding1 ∘ raw1748step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1748step1 raw1748step1Labels raw1748step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2215 node2215Labels := by rfl

def raw1749 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1749Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1749step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1749step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1749step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1749 raw1749Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw1749 raw1749Labels = mixedMoment B raw1749step0 raw1749step0Labels := by
      have ha : raw1749step0 = (fun i j => raw1749 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1749step0 raw1749; decide +kernel
      have hl : raw1749step0Labels = raw1749Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1749 raw1749Labels permutation32 permutation4
    mixedMoment B raw1749step0 raw1749step0Labels = mixedMoment B raw1749step1 raw1749step1Labels := by
      have ha : raw1749step1 = raw1749step0 := by apply Matrix.ext; unfold raw1749step1 raw1749step0; decide +kernel
      have hl : raw1749step0Labels = labelEmbedding7 ∘ raw1749step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1749step0 raw1749step0Labels raw1749step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4811 node4811Labels := by rfl

def raw1750 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1750Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1750step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1750 raw1750Labels = mixedMoment B node2029 node2029Labels := by
  calc
    mixedMoment B raw1750 raw1750Labels = mixedMoment B raw1750step0 raw1750step0Labels := by
      have ha : raw1750step0 = (fun i j => raw1750 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1750step0 raw1750; decide +kernel
      have hl : raw1750step0Labels = raw1750Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1750 raw1750Labels permutation32 permutation4
    _ = mixedMoment B node2029 node2029Labels := by rfl

def raw1751 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1751Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw1751step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw1751step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw1751step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1751 raw1751Labels = mixedMoment B node2225 node2225Labels := by
  calc
    mixedMoment B raw1751 raw1751Labels = mixedMoment B raw1751step0 raw1751step0Labels := by
      have ha : raw1751step0 = (fun i j => raw1751 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1751step0 raw1751; decide +kernel
      have hl : raw1751step0Labels = raw1751Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1751 raw1751Labels permutation32 permutation6
    mixedMoment B raw1751step0 raw1751step0Labels = mixedMoment B raw1751step1 raw1751step1Labels := by
      have ha : raw1751step1 = -raw1751step0 := by apply Matrix.ext; change ∀ i j, raw1751step1 i j = -(raw1751step0 i j); unfold raw1751step1 raw1751step0; decide +kernel
      have hl : raw1751step1Labels = raw1751step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1751step1 raw1751step1Labels = mixedMoment B raw1751step2 raw1751step2Labels := by
      have ha : raw1751step2 = raw1751step1 := by apply Matrix.ext; unfold raw1751step2 raw1751step1; decide +kernel
      have hl : raw1751step1Labels = labelEmbedding1 ∘ raw1751step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1751step1 raw1751step1Labels raw1751step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2225 node2225Labels := by rfl

def raw1752 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw1752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1752step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1752step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1752step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1752step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1752 raw1752Labels = mixedMoment B node4826 node4826Labels := by
  calc
    mixedMoment B raw1752 raw1752Labels = mixedMoment B raw1752step0 raw1752step0Labels := by
      have ha : raw1752step0 = (fun i j => raw1752 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1752step0 raw1752; decide +kernel
      have hl : raw1752step0Labels = raw1752Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1752 raw1752Labels permutation152 permutation4
    mixedMoment B raw1752step0 raw1752step0Labels = mixedMoment B raw1752step1 raw1752step1Labels := by
      have ha : raw1752step1 = raw1752step0 := by apply Matrix.ext; unfold raw1752step1 raw1752step0; decide +kernel
      have hl : raw1752step0Labels = labelEmbedding7 ∘ raw1752step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1752step0 raw1752step0Labels raw1752step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4826 node4826Labels := by rfl

def raw1753 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw1753Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1753step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1753 raw1753Labels = mixedMoment B node2046 node2046Labels := by
  calc
    mixedMoment B raw1753 raw1753Labels = mixedMoment B raw1753step0 raw1753step0Labels := by
      have ha : raw1753step0 = (fun i j => raw1753 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1753step0 raw1753; decide +kernel
      have hl : raw1753step0Labels = raw1753Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1753 raw1753Labels permutation152 permutation4
    _ = mixedMoment B node2046 node2046Labels := by rfl

def raw1754 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw1754Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1754step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw1754step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1754step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1754step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1754step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1754step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1754 raw1754Labels = mixedMoment B node2077 node2077Labels := by
  calc
    mixedMoment B raw1754 raw1754Labels = mixedMoment B raw1754step0 raw1754step0Labels := by
      have ha : raw1754step0 = (fun i j => raw1754 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1754step0 raw1754; decide +kernel
      have hl : raw1754step0Labels = raw1754Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1754 raw1754Labels permutation176 permutation6
    mixedMoment B raw1754step0 raw1754step0Labels = mixedMoment B raw1754step1 raw1754step1Labels := by
      have ha : raw1754step1 = -raw1754step0 := by apply Matrix.ext; change ∀ i j, raw1754step1 i j = -(raw1754step0 i j); unfold raw1754step1 raw1754step0; decide +kernel
      have hl : raw1754step1Labels = raw1754step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1754step1 raw1754step1Labels = mixedMoment B raw1754step2 raw1754step2Labels := by
      have ha : raw1754step2 = raw1754step1 := by apply Matrix.ext; unfold raw1754step2 raw1754step1; decide +kernel
      have hl : raw1754step1Labels = labelEmbedding1 ∘ raw1754step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1754step1 raw1754step1Labels raw1754step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2077 node2077Labels := by rfl

def raw1755 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![1, 2, -3]]
def raw1755Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw1755step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw1755step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1755 raw1755Labels = mixedMoment B node4827 node4827Labels := by
  calc
    mixedMoment B raw1755 raw1755Labels = mixedMoment B raw1755step0 raw1755step0Labels := by
      have ha : raw1755step0 = (fun i j => raw1755 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1755step0 raw1755; decide +kernel
      have hl : raw1755step0Labels = raw1755Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1755 raw1755Labels permutation32 permutation4
    mixedMoment B raw1755step0 raw1755step0Labels = mixedMoment B raw1755step1 raw1755step1Labels := by
      have ha : raw1755step1 = raw1755step0 := by apply Matrix.ext; unfold raw1755step1 raw1755step0; decide +kernel
      have hl : raw1755step0Labels = labelEmbedding7 ∘ raw1755step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1755step0 raw1755step0Labels raw1755step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4827 node4827Labels := by rfl

def raw1756 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![1, 2, -3]]
def raw1756Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw1756step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1756 raw1756Labels = mixedMoment B node2047 node2047Labels := by
  calc
    mixedMoment B raw1756 raw1756Labels = mixedMoment B raw1756step0 raw1756step0Labels := by
      have ha : raw1756step0 = (fun i j => raw1756 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1756step0 raw1756; decide +kernel
      have hl : raw1756step0Labels = raw1756Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1756 raw1756Labels permutation32 permutation4
    _ = mixedMoment B node2047 node2047Labels := by rfl

def raw1757 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![1, 2, -3]]
def raw1757Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw1757step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw1757step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1757step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw1757step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1757 raw1757Labels = mixedMoment B node2079 node2079Labels := by
  calc
    mixedMoment B raw1757 raw1757Labels = mixedMoment B raw1757step0 raw1757step0Labels := by
      have ha : raw1757step0 = (fun i j => raw1757 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1757step0 raw1757; decide +kernel
      have hl : raw1757step0Labels = raw1757Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1757 raw1757Labels permutation38 permutation6
    mixedMoment B raw1757step0 raw1757step0Labels = mixedMoment B raw1757step1 raw1757step1Labels := by
      have ha : raw1757step1 = -raw1757step0 := by apply Matrix.ext; change ∀ i j, raw1757step1 i j = -(raw1757step0 i j); unfold raw1757step1 raw1757step0; decide +kernel
      have hl : raw1757step1Labels = raw1757step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1757step1 raw1757step1Labels = mixedMoment B raw1757step2 raw1757step2Labels := by
      have ha : raw1757step2 = raw1757step1 := by apply Matrix.ext; unfold raw1757step2 raw1757step1; decide +kernel
      have hl : raw1757step1Labels = labelEmbedding1 ∘ raw1757step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1757step1 raw1757step1Labels raw1757step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2079 node2079Labels := by rfl

def raw1758 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 1, 1], ![1, 1, -2], ![0, 2, -2]]
def raw1758Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw1758step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw1758step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1758 raw1758Labels = mixedMoment B node4828 node4828Labels := by
  calc
    mixedMoment B raw1758 raw1758Labels = mixedMoment B raw1758step0 raw1758step0Labels := by
      have ha : raw1758step0 = (fun i j => raw1758 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1758step0 raw1758; decide +kernel
      have hl : raw1758step0Labels = raw1758Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1758 raw1758Labels permutation32 permutation4
    mixedMoment B raw1758step0 raw1758step0Labels = mixedMoment B raw1758step1 raw1758step1Labels := by
      have ha : raw1758step1 = raw1758step0 := by apply Matrix.ext; unfold raw1758step1 raw1758step0; decide +kernel
      have hl : raw1758step0Labels = labelEmbedding7 ∘ raw1758step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1758step0 raw1758step0Labels raw1758step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4828 node4828Labels := by rfl

def raw1759 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 1, 1], ![1, 1, -2], ![0, 2, -2]]
def raw1759Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw1759step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1759 raw1759Labels = mixedMoment B node2048 node2048Labels := by
  calc
    mixedMoment B raw1759 raw1759Labels = mixedMoment B raw1759step0 raw1759step0Labels := by
      have ha : raw1759step0 = (fun i j => raw1759 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1759step0 raw1759; decide +kernel
      have hl : raw1759step0Labels = raw1759Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1759 raw1759Labels permutation32 permutation4
    _ = mixedMoment B node2048 node2048Labels := by rfl

def raw1760 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 1, 1], ![1, 1, -2], ![0, 2, -2]]
def raw1760Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw1760step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw1760step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1760step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw1760step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1760 raw1760Labels = mixedMoment B node2082 node2082Labels := by
  calc
    mixedMoment B raw1760 raw1760Labels = mixedMoment B raw1760step0 raw1760step0Labels := by
      have ha : raw1760step0 = (fun i j => raw1760 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1760step0 raw1760; decide +kernel
      have hl : raw1760step0Labels = raw1760Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1760 raw1760Labels permutation38 permutation6
    mixedMoment B raw1760step0 raw1760step0Labels = mixedMoment B raw1760step1 raw1760step1Labels := by
      have ha : raw1760step1 = -raw1760step0 := by apply Matrix.ext; change ∀ i j, raw1760step1 i j = -(raw1760step0 i j); unfold raw1760step1 raw1760step0; decide +kernel
      have hl : raw1760step1Labels = raw1760step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1760step1 raw1760step1Labels = mixedMoment B raw1760step2 raw1760step2Labels := by
      have ha : raw1760step2 = raw1760step1 := by apply Matrix.ext; unfold raw1760step2 raw1760step1; decide +kernel
      have hl : raw1760step1Labels = labelEmbedding1 ∘ raw1760step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1760step1 raw1760step1Labels raw1760step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2082 node2082Labels := by rfl

def raw1761 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw1761Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1761step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw1761step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1761step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw1761step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1761 raw1761Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw1761 raw1761Labels = mixedMoment B raw1761step0 raw1761step0Labels := by
      have ha : raw1761step0 = (fun i j => raw1761 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1761step0 raw1761; decide +kernel
      have hl : raw1761step0Labels = raw1761Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1761 raw1761Labels permutation152 permutation4
    mixedMoment B raw1761step0 raw1761step0Labels = mixedMoment B raw1761step1 raw1761step1Labels := by
      have ha : raw1761step1 = raw1761step0 := by apply Matrix.ext; unfold raw1761step1 raw1761step0; decide +kernel
      have hl : raw1761step0Labels = labelEmbedding7 ∘ raw1761step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1761step0 raw1761step0Labels raw1761step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4831 node4831Labels := by rfl

def raw1762 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw1762Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1762step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw1762step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1762 raw1762Labels = mixedMoment B node2051 node2051Labels := by
  calc
    mixedMoment B raw1762 raw1762Labels = mixedMoment B raw1762step0 raw1762step0Labels := by
      have ha : raw1762step0 = (fun i j => raw1762 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1762step0 raw1762; decide +kernel
      have hl : raw1762step0Labels = raw1762Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1762 raw1762Labels permutation152 permutation4
    _ = mixedMoment B node2051 node2051Labels := by rfl

def raw1763 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw1763Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw1763step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1763step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1763step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1763step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1763step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1763 raw1763Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw1763 raw1763Labels = mixedMoment B raw1763step0 raw1763step0Labels := by
      have ha : raw1763step0 = (fun i j => raw1763 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1763step0 raw1763; decide +kernel
      have hl : raw1763step0Labels = raw1763Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1763 raw1763Labels permutation152 permutation6
    mixedMoment B raw1763step0 raw1763step0Labels = mixedMoment B raw1763step1 raw1763step1Labels := by
      have ha : raw1763step1 = -raw1763step0 := by apply Matrix.ext; change ∀ i j, raw1763step1 i j = -(raw1763step0 i j); unfold raw1763step1 raw1763step0; decide +kernel
      have hl : raw1763step1Labels = raw1763step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1763step1 raw1763step1Labels = mixedMoment B raw1763step2 raw1763step2Labels := by
      have ha : raw1763step2 = raw1763step1 := by apply Matrix.ext; unfold raw1763step2 raw1763step1; decide +kernel
      have hl : raw1763step1Labels = labelEmbedding1 ∘ raw1763step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1763step1 raw1763step1Labels raw1763step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2191 node2191Labels := by rfl

def raw1764 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, 2, -3]]
def raw1764Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw1764step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw1764step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1764 raw1764Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw1764 raw1764Labels = mixedMoment B raw1764step0 raw1764step0Labels := by
      have ha : raw1764step0 = (fun i j => raw1764 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1764step0 raw1764; decide +kernel
      have hl : raw1764step0Labels = raw1764Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1764 raw1764Labels permutation32 permutation4
    mixedMoment B raw1764step0 raw1764step0Labels = mixedMoment B raw1764step1 raw1764step1Labels := by
      have ha : raw1764step1 = raw1764step0 := by apply Matrix.ext; unfold raw1764step1 raw1764step0; decide +kernel
      have hl : raw1764step0Labels = labelEmbedding7 ∘ raw1764step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1764step0 raw1764step0Labels raw1764step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4832 node4832Labels := by rfl

def raw1765 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, 2, -3]]
def raw1765Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw1765step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1765 raw1765Labels = mixedMoment B node2052 node2052Labels := by
  calc
    mixedMoment B raw1765 raw1765Labels = mixedMoment B raw1765step0 raw1765step0Labels := by
      have ha : raw1765step0 = (fun i j => raw1765 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1765step0 raw1765; decide +kernel
      have hl : raw1765step0Labels = raw1765Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1765 raw1765Labels permutation32 permutation4
    _ = mixedMoment B node2052 node2052Labels := by rfl

def raw1766 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, 2, -3]]
def raw1766Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw1766step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw1766step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1766step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw1766step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1766 raw1766Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw1766 raw1766Labels = mixedMoment B raw1766step0 raw1766step0Labels := by
      have ha : raw1766step0 = (fun i j => raw1766 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1766step0 raw1766; decide +kernel
      have hl : raw1766step0Labels = raw1766Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1766 raw1766Labels permutation32 permutation6
    mixedMoment B raw1766step0 raw1766step0Labels = mixedMoment B raw1766step1 raw1766step1Labels := by
      have ha : raw1766step1 = -raw1766step0 := by apply Matrix.ext; change ∀ i j, raw1766step1 i j = -(raw1766step0 i j); unfold raw1766step1 raw1766step0; decide +kernel
      have hl : raw1766step1Labels = raw1766step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1766step1 raw1766step1Labels = mixedMoment B raw1766step2 raw1766step2Labels := by
      have ha : raw1766step2 = raw1766step1 := by apply Matrix.ext; unfold raw1766step2 raw1766step1; decide +kernel
      have hl : raw1766step1Labels = labelEmbedding1 ∘ raw1766step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1766step1 raw1766step1Labels raw1766step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2193 node2193Labels := by rfl

def raw1767 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw1767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw1767step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw1767step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1767 raw1767Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw1767 raw1767Labels = mixedMoment B raw1767step0 raw1767step0Labels := by
      have ha : raw1767step0 = (fun i j => raw1767 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1767step0 raw1767; decide +kernel
      have hl : raw1767step0Labels = raw1767Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1767 raw1767Labels permutation32 permutation4
    mixedMoment B raw1767step0 raw1767step0Labels = mixedMoment B raw1767step1 raw1767step1Labels := by
      have ha : raw1767step1 = raw1767step0 := by apply Matrix.ext; unfold raw1767step1 raw1767step0; decide +kernel
      have hl : raw1767step0Labels = labelEmbedding7 ∘ raw1767step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1767step0 raw1767step0Labels raw1767step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw1768 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw1768Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw1768step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1768 raw1768Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw1768 raw1768Labels = mixedMoment B raw1768step0 raw1768step0Labels := by
      have ha : raw1768step0 = (fun i j => raw1768 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1768step0 raw1768; decide +kernel
      have hl : raw1768step0Labels = raw1768Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1768 raw1768Labels permutation32 permutation4
    _ = mixedMoment B node2054 node2054Labels := by rfl

def raw1769 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw1769Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw1769step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1769step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1769step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1769step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1769 raw1769Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw1769 raw1769Labels = mixedMoment B raw1769step0 raw1769step0Labels := by
      have ha : raw1769step0 = (fun i j => raw1769 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1769step0 raw1769; decide +kernel
      have hl : raw1769step0Labels = raw1769Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1769 raw1769Labels permutation33 permutation6
    mixedMoment B raw1769step0 raw1769step0Labels = mixedMoment B raw1769step1 raw1769step1Labels := by
      have ha : raw1769step1 = -raw1769step0 := by apply Matrix.ext; change ∀ i j, raw1769step1 i j = -(raw1769step0 i j); unfold raw1769step1 raw1769step0; decide +kernel
      have hl : raw1769step1Labels = raw1769step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1769step1 raw1769step1Labels = mixedMoment B raw1769step2 raw1769step2Labels := by
      have ha : raw1769step2 = raw1769step1 := by apply Matrix.ext; unfold raw1769step2 raw1769step1; decide +kernel
      have hl : raw1769step1Labels = labelEmbedding1 ∘ raw1769step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1769step1 raw1769step1Labels raw1769step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2206 node2206Labels := by rfl

def raw1770 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1770step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1770step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1770 raw1770Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw1770 raw1770Labels = mixedMoment B raw1770step0 raw1770step0Labels := by
      have ha : raw1770step0 = (fun i j => raw1770 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1770step0 raw1770; decide +kernel
      have hl : raw1770step0Labels = raw1770Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1770 raw1770Labels permutation32 permutation4
    mixedMoment B raw1770step0 raw1770step0Labels = mixedMoment B raw1770step1 raw1770step1Labels := by
      have ha : raw1770step1 = raw1770step0 := by apply Matrix.ext; unfold raw1770step1 raw1770step0; decide +kernel
      have hl : raw1770step0Labels = labelEmbedding7 ∘ raw1770step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1770step0 raw1770step0Labels raw1770step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

def raw1771 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1771Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1771step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1771 raw1771Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw1771 raw1771Labels = mixedMoment B raw1771step0 raw1771step0Labels := by
      have ha : raw1771step0 = (fun i j => raw1771 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1771step0 raw1771; decide +kernel
      have hl : raw1771step0Labels = raw1771Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1771 raw1771Labels permutation32 permutation4
    _ = mixedMoment B node2058 node2058Labels := by rfl

def raw1772 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1772Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw1772step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw1772step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1772step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw1772step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1772 raw1772Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw1772 raw1772Labels = mixedMoment B raw1772step0 raw1772step0Labels := by
      have ha : raw1772step0 = (fun i j => raw1772 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1772step0 raw1772; decide +kernel
      have hl : raw1772step0Labels = raw1772Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1772 raw1772Labels permutation36 permutation6
    mixedMoment B raw1772step0 raw1772step0Labels = mixedMoment B raw1772step1 raw1772step1Labels := by
      have ha : raw1772step1 = -raw1772step0 := by apply Matrix.ext; change ∀ i j, raw1772step1 i j = -(raw1772step0 i j); unfold raw1772step1 raw1772step0; decide +kernel
      have hl : raw1772step1Labels = raw1772step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1772step1 raw1772step1Labels = mixedMoment B raw1772step2 raw1772step2Labels := by
      have ha : raw1772step2 = raw1772step1 := by apply Matrix.ext; unfold raw1772step2 raw1772step1; decide +kernel
      have hl : raw1772step1Labels = labelEmbedding1 ∘ raw1772step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1772step1 raw1772step1Labels raw1772step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2216 node2216Labels := by rfl

def raw1773 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 1, -2], ![-2, 3, -1]]
def raw1773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1773step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw1773step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1773step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw1773step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1773 raw1773Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw1773 raw1773Labels = mixedMoment B raw1773step0 raw1773step0Labels := by
      have ha : raw1773step0 = (fun i j => raw1773 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1773step0 raw1773; decide +kernel
      have hl : raw1773step0Labels = raw1773Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1773 raw1773Labels permutation8 permutation4
    mixedMoment B raw1773step0 raw1773step0Labels = mixedMoment B raw1773step1 raw1773step1Labels := by
      have ha : raw1773step1 = raw1773step0 := by apply Matrix.ext; unfold raw1773step1 raw1773step0; decide +kernel
      have hl : raw1773step0Labels = labelEmbedding7 ∘ raw1773step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1773step0 raw1773step0Labels raw1773step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4843 node4843Labels := by rfl

def raw1774 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 1, -2], ![-2, 3, -1]]
def raw1774Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1774step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw1774step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1774 raw1774Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw1774 raw1774Labels = mixedMoment B raw1774step0 raw1774step0Labels := by
      have ha : raw1774step0 = (fun i j => raw1774 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1774step0 raw1774; decide +kernel
      have hl : raw1774step0Labels = raw1774Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1774 raw1774Labels permutation8 permutation4
    _ = mixedMoment B node2062 node2062Labels := by rfl

def raw1775 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![1, 1, -2], ![-2, 3, -1]]
def raw1775Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1775step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw1775step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1775step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw1775step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1775step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw1775step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1775 raw1775Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw1775 raw1775Labels = mixedMoment B raw1775step0 raw1775step0Labels := by
      have ha : raw1775step0 = (fun i j => raw1775 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1775step0 raw1775; decide +kernel
      have hl : raw1775step0Labels = raw1775Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1775 raw1775Labels permutation9 permutation6
    mixedMoment B raw1775step0 raw1775step0Labels = mixedMoment B raw1775step1 raw1775step1Labels := by
      have ha : raw1775step1 = -raw1775step0 := by apply Matrix.ext; change ∀ i j, raw1775step1 i j = -(raw1775step0 i j); unfold raw1775step1 raw1775step0; decide +kernel
      have hl : raw1775step1Labels = raw1775step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1775step1 raw1775step1Labels = mixedMoment B raw1775step2 raw1775step2Labels := by
      have ha : raw1775step2 = raw1775step1 := by apply Matrix.ext; unfold raw1775step2 raw1775step1; decide +kernel
      have hl : raw1775step1Labels = labelEmbedding1 ∘ raw1775step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1775step1 raw1775step1Labels raw1775step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2230 node2230Labels := by rfl

def raw1776 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 2, 0], ![1, 2, -3]]
def raw1776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1776step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw1776step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1776step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw1776step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1776 raw1776Labels = mixedMoment B node4845 node4845Labels := by
  calc
    mixedMoment B raw1776 raw1776Labels = mixedMoment B raw1776step0 raw1776step0Labels := by
      have ha : raw1776step0 = (fun i j => raw1776 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1776step0 raw1776; decide +kernel
      have hl : raw1776step0Labels = raw1776Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1776 raw1776Labels permutation8 permutation4
    mixedMoment B raw1776step0 raw1776step0Labels = mixedMoment B raw1776step1 raw1776step1Labels := by
      have ha : raw1776step1 = raw1776step0 := by apply Matrix.ext; unfold raw1776step1 raw1776step0; decide +kernel
      have hl : raw1776step0Labels = labelEmbedding7 ∘ raw1776step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1776step0 raw1776step0Labels raw1776step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4845 node4845Labels := by rfl

def raw1777 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 2, 0], ![1, 2, -3]]
def raw1777Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1777step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw1777step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1777 raw1777Labels = mixedMoment B node2065 node2065Labels := by
  calc
    mixedMoment B raw1777 raw1777Labels = mixedMoment B raw1777step0 raw1777step0Labels := by
      have ha : raw1777step0 = (fun i j => raw1777 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1777step0 raw1777; decide +kernel
      have hl : raw1777step0Labels = raw1777Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1777 raw1777Labels permutation8 permutation4
    _ = mixedMoment B node2065 node2065Labels := by rfl

def raw1778 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, -1, 0], ![-2, 2, 0], ![1, 2, -3]]
def raw1778Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1778step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw1778step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1778step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw1778step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1778step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw1778step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1778 raw1778Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw1778 raw1778Labels = mixedMoment B raw1778step0 raw1778step0Labels := by
      have ha : raw1778step0 = (fun i j => raw1778 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1778step0 raw1778; decide +kernel
      have hl : raw1778step0Labels = raw1778Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1778 raw1778Labels permutation8 permutation6
    mixedMoment B raw1778step0 raw1778step0Labels = mixedMoment B raw1778step1 raw1778step1Labels := by
      have ha : raw1778step1 = -raw1778step0 := by apply Matrix.ext; change ∀ i j, raw1778step1 i j = -(raw1778step0 i j); unfold raw1778step1 raw1778step0; decide +kernel
      have hl : raw1778step1Labels = raw1778step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1778step1 raw1778step1Labels = mixedMoment B raw1778step2 raw1778step2Labels := by
      have ha : raw1778step2 = raw1778step1 := by apply Matrix.ext; unfold raw1778step2 raw1778step1; decide +kernel
      have hl : raw1778step1Labels = labelEmbedding1 ∘ raw1778step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1778step1 raw1778step1Labels raw1778step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2218 node2218Labels := by rfl

def raw1779 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw1779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1779step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1779step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1779step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1779step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1779 raw1779Labels = mixedMoment B node4859 node4859Labels := by
  calc
    mixedMoment B raw1779 raw1779Labels = mixedMoment B raw1779step0 raw1779step0Labels := by
      have ha : raw1779step0 = (fun i j => raw1779 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1779step0 raw1779; decide +kernel
      have hl : raw1779step0Labels = raw1779Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1779 raw1779Labels permutation152 permutation4
    mixedMoment B raw1779step0 raw1779step0Labels = mixedMoment B raw1779step1 raw1779step1Labels := by
      have ha : raw1779step1 = raw1779step0 := by apply Matrix.ext; unfold raw1779step1 raw1779step0; decide +kernel
      have hl : raw1779step0Labels = labelEmbedding7 ∘ raw1779step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1779step0 raw1779step0Labels raw1779step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4859 node4859Labels := by rfl

def raw1780 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw1780Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1780step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1780step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1780 raw1780Labels = mixedMoment B node2100 node2100Labels := by
  calc
    mixedMoment B raw1780 raw1780Labels = mixedMoment B raw1780step0 raw1780step0Labels := by
      have ha : raw1780step0 = (fun i j => raw1780 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1780step0 raw1780; decide +kernel
      have hl : raw1780step0Labels = raw1780Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1780 raw1780Labels permutation152 permutation4
    _ = mixedMoment B node2100 node2100Labels := by rfl

def raw1781 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw1781Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1781step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw1781step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1781step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1781step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1781step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1781step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1781 raw1781Labels = mixedMoment B node2100 node2100Labels := by
  calc
    mixedMoment B raw1781 raw1781Labels = mixedMoment B raw1781step0 raw1781step0Labels := by
      have ha : raw1781step0 = (fun i j => raw1781 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1781step0 raw1781; decide +kernel
      have hl : raw1781step0Labels = raw1781Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1781 raw1781Labels permutation176 permutation6
    mixedMoment B raw1781step0 raw1781step0Labels = mixedMoment B raw1781step1 raw1781step1Labels := by
      have ha : raw1781step1 = -raw1781step0 := by apply Matrix.ext; change ∀ i j, raw1781step1 i j = -(raw1781step0 i j); unfold raw1781step1 raw1781step0; decide +kernel
      have hl : raw1781step1Labels = raw1781step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1781step1 raw1781step1Labels = mixedMoment B raw1781step2 raw1781step2Labels := by
      have ha : raw1781step2 = raw1781step1 := by apply Matrix.ext; unfold raw1781step2 raw1781step1; decide +kernel
      have hl : raw1781step1Labels = labelEmbedding1 ∘ raw1781step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1781step1 raw1781step1Labels raw1781step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2100 node2100Labels := by rfl

def raw1782 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw1782Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1782step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1782step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1782step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1782 raw1782Labels = mixedMoment B node4860 node4860Labels := by
  calc
    mixedMoment B raw1782 raw1782Labels = mixedMoment B raw1782step0 raw1782step0Labels := by
      have ha : raw1782step0 = (fun i j => raw1782 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1782step0 raw1782; decide +kernel
      have hl : raw1782step0Labels = raw1782Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1782 raw1782Labels permutation32 permutation4
    mixedMoment B raw1782step0 raw1782step0Labels = mixedMoment B raw1782step1 raw1782step1Labels := by
      have ha : raw1782step1 = raw1782step0 := by apply Matrix.ext; unfold raw1782step1 raw1782step0; decide +kernel
      have hl : raw1782step0Labels = labelEmbedding7 ∘ raw1782step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1782step0 raw1782step0Labels raw1782step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4860 node4860Labels := by rfl

def raw1783 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw1783Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1783step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1783 raw1783Labels = mixedMoment B node2101 node2101Labels := by
  calc
    mixedMoment B raw1783 raw1783Labels = mixedMoment B raw1783step0 raw1783step0Labels := by
      have ha : raw1783step0 = (fun i j => raw1783 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1783step0 raw1783; decide +kernel
      have hl : raw1783step0Labels = raw1783Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1783 raw1783Labels permutation32 permutation4
    _ = mixedMoment B node2101 node2101Labels := by rfl

def raw1784 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw1784Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1784step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1784step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1784step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1784step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1784 raw1784Labels = mixedMoment B node2101 node2101Labels := by
  calc
    mixedMoment B raw1784 raw1784Labels = mixedMoment B raw1784step0 raw1784step0Labels := by
      have ha : raw1784step0 = (fun i j => raw1784 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1784step0 raw1784; decide +kernel
      have hl : raw1784step0Labels = raw1784Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1784 raw1784Labels permutation38 permutation6
    mixedMoment B raw1784step0 raw1784step0Labels = mixedMoment B raw1784step1 raw1784step1Labels := by
      have ha : raw1784step1 = -raw1784step0 := by apply Matrix.ext; change ∀ i j, raw1784step1 i j = -(raw1784step0 i j); unfold raw1784step1 raw1784step0; decide +kernel
      have hl : raw1784step1Labels = raw1784step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1784step1 raw1784step1Labels = mixedMoment B raw1784step2 raw1784step2Labels := by
      have ha : raw1784step2 = raw1784step1 := by apply Matrix.ext; unfold raw1784step2 raw1784step1; decide +kernel
      have hl : raw1784step1Labels = labelEmbedding1 ∘ raw1784step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1784step1 raw1784step1Labels raw1784step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2101 node2101Labels := by rfl

def raw1785 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 1, 1], ![0, 3, -3]]
def raw1785Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1785step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1785step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1785step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1785step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1785 raw1785Labels = mixedMoment B node4862 node4862Labels := by
  calc
    mixedMoment B raw1785 raw1785Labels = mixedMoment B raw1785step0 raw1785step0Labels := by
      have ha : raw1785step0 = (fun i j => raw1785 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1785step0 raw1785; decide +kernel
      have hl : raw1785step0Labels = raw1785Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1785 raw1785Labels permutation8 permutation4
    mixedMoment B raw1785step0 raw1785step0Labels = mixedMoment B raw1785step1 raw1785step1Labels := by
      have ha : raw1785step1 = raw1785step0 := by apply Matrix.ext; unfold raw1785step1 raw1785step0; decide +kernel
      have hl : raw1785step0Labels = labelEmbedding7 ∘ raw1785step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1785step0 raw1785step0Labels raw1785step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4862 node4862Labels := by rfl

def raw1786 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 1, 1], ![0, 3, -3]]
def raw1786Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1786step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1786step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1786 raw1786Labels = mixedMoment B node2103 node2103Labels := by
  calc
    mixedMoment B raw1786 raw1786Labels = mixedMoment B raw1786step0 raw1786step0Labels := by
      have ha : raw1786step0 = (fun i j => raw1786 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1786step0 raw1786; decide +kernel
      have hl : raw1786step0Labels = raw1786Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1786 raw1786Labels permutation8 permutation4
    _ = mixedMoment B node2103 node2103Labels := by rfl

def raw1787 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 1, 1], ![0, 3, -3]]
def raw1787Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1787step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1787step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1787step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw1787step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1787 raw1787Labels = mixedMoment B node2103 node2103Labels := by
  calc
    mixedMoment B raw1787 raw1787Labels = mixedMoment B raw1787step0 raw1787step0Labels := by
      have ha : raw1787step0 = (fun i j => raw1787 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1787step0 raw1787; decide +kernel
      have hl : raw1787step0Labels = raw1787Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1787 raw1787Labels permutation29 permutation6
    mixedMoment B raw1787step0 raw1787step0Labels = mixedMoment B raw1787step1 raw1787step1Labels := by
      have ha : raw1787step1 = raw1787step0 := by apply Matrix.ext; unfold raw1787step1 raw1787step0; decide +kernel
      have hl : raw1787step0Labels = labelEmbedding1 ∘ raw1787step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1787step0 raw1787step0Labels raw1787step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2103 node2103Labels := by rfl

def raw1788 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw1788Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1788step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1788step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1788step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1788 raw1788Labels = mixedMoment B node4864 node4864Labels := by
  calc
    mixedMoment B raw1788 raw1788Labels = mixedMoment B raw1788step0 raw1788step0Labels := by
      have ha : raw1788step0 = (fun i j => raw1788 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1788step0 raw1788; decide +kernel
      have hl : raw1788step0Labels = raw1788Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1788 raw1788Labels permutation152 permutation4
    mixedMoment B raw1788step0 raw1788step0Labels = mixedMoment B raw1788step1 raw1788step1Labels := by
      have ha : raw1788step1 = raw1788step0 := by apply Matrix.ext; unfold raw1788step1 raw1788step0; decide +kernel
      have hl : raw1788step0Labels = labelEmbedding7 ∘ raw1788step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1788step0 raw1788step0Labels raw1788step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4864 node4864Labels := by rfl

def raw1789 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw1789Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1789step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1789 raw1789Labels = mixedMoment B node2105 node2105Labels := by
  calc
    mixedMoment B raw1789 raw1789Labels = mixedMoment B raw1789step0 raw1789step0Labels := by
      have ha : raw1789step0 = (fun i j => raw1789 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1789step0 raw1789; decide +kernel
      have hl : raw1789step0Labels = raw1789Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1789 raw1789Labels permutation152 permutation4
    _ = mixedMoment B node2105 node2105Labels := by rfl

def raw1790 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw1790Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw1790step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1790step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw1790step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1790step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw1790step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1790 raw1790Labels = mixedMoment B node2241 node2241Labels := by
  calc
    mixedMoment B raw1790 raw1790Labels = mixedMoment B raw1790step0 raw1790step0Labels := by
      have ha : raw1790step0 = (fun i j => raw1790 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1790step0 raw1790; decide +kernel
      have hl : raw1790step0Labels = raw1790Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1790 raw1790Labels permutation182 permutation6
    mixedMoment B raw1790step0 raw1790step0Labels = mixedMoment B raw1790step1 raw1790step1Labels := by
      have ha : raw1790step1 = -raw1790step0 := by apply Matrix.ext; change ∀ i j, raw1790step1 i j = -(raw1790step0 i j); unfold raw1790step1 raw1790step0; decide +kernel
      have hl : raw1790step1Labels = raw1790step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1790step1 raw1790step1Labels = mixedMoment B raw1790step2 raw1790step2Labels := by
      have ha : raw1790step2 = raw1790step1 := by apply Matrix.ext; unfold raw1790step2 raw1790step1; decide +kernel
      have hl : raw1790step1Labels = labelEmbedding1 ∘ raw1790step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1790step1 raw1790step1Labels raw1790step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2241 node2241Labels := by rfl

def raw1791 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1791Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1791step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1791step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1791 raw1791Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw1791 raw1791Labels = mixedMoment B raw1791step0 raw1791step0Labels := by
      have ha : raw1791step0 = (fun i j => raw1791 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1791step0 raw1791; decide +kernel
      have hl : raw1791step0Labels = raw1791Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1791 raw1791Labels permutation32 permutation4
    mixedMoment B raw1791step0 raw1791step0Labels = mixedMoment B raw1791step1 raw1791step1Labels := by
      have ha : raw1791step1 = raw1791step0 := by apply Matrix.ext; unfold raw1791step1 raw1791step0; decide +kernel
      have hl : raw1791step0Labels = labelEmbedding7 ∘ raw1791step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1791step0 raw1791step0Labels raw1791step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4865 node4865Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
