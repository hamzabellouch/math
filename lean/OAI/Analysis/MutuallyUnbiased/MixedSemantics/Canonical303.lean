import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw38784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw38784Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38784step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw38784step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38784step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw38784step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38784step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw38784step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38784 raw38784Labels = mixedMoment B node1891 node1891Labels := by
  calc
    mixedMoment B raw38784 raw38784Labels = mixedMoment B raw38784step0 raw38784step0Labels := by
      have ha : raw38784step0 = (fun i j => raw38784 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38784step0 raw38784; decide +kernel
      have hl : raw38784step0Labels = raw38784Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38784 raw38784Labels permutation153 permutation7
    mixedMoment B raw38784step0 raw38784step0Labels = mixedMoment B raw38784step1 raw38784step1Labels := by
      have ha : raw38784step1 = -raw38784step0 := by apply Matrix.ext; change ∀ i j, raw38784step1 i j = -(raw38784step0 i j); unfold raw38784step1 raw38784step0; decide +kernel
      have hl : raw38784step1Labels = raw38784step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38784step1 raw38784step1Labels = mixedMoment B raw38784step2 raw38784step2Labels := by
      have ha : raw38784step2 = raw38784step1 := by apply Matrix.ext; unfold raw38784step2 raw38784step1; decide +kernel
      have hl : raw38784step1Labels = labelEmbedding4 ∘ raw38784step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38784step1 raw38784step1Labels raw38784step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1891 node1891Labels := by rfl

def raw38785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw38785Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38785step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw38785step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38785 raw38785Labels = mixedMoment B node1868 node1868Labels := by
  calc
    mixedMoment B raw38785 raw38785Labels = mixedMoment B raw38785step0 raw38785step0Labels := by
      have ha : raw38785step0 = raw38785 := by apply Matrix.ext; unfold raw38785step0 raw38785; decide +kernel
      have hl : raw38785Labels = labelEmbedding2 ∘ raw38785step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38785 raw38785Labels raw38785step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1868 node1868Labels := by rfl

def raw38786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw38786Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 1, 2]]
def raw38786step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38786step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -1, -2]]
def raw38786step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38786step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -1, -2]]
def raw38786step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38786 raw38786Labels = mixedMoment B node1885 node1885Labels := by
  calc
    mixedMoment B raw38786 raw38786Labels = mixedMoment B raw38786step0 raw38786step0Labels := by
      have ha : raw38786step0 = (fun i j => raw38786 (permutation154 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38786step0 raw38786; decide +kernel
      have hl : raw38786step0Labels = raw38786Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38786 raw38786Labels permutation154 permutation7
    mixedMoment B raw38786step0 raw38786step0Labels = mixedMoment B raw38786step1 raw38786step1Labels := by
      have ha : raw38786step1 = -raw38786step0 := by apply Matrix.ext; change ∀ i j, raw38786step1 i j = -(raw38786step0 i j); unfold raw38786step1 raw38786step0; decide +kernel
      have hl : raw38786step1Labels = raw38786step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38786step1 raw38786step1Labels = mixedMoment B raw38786step2 raw38786step2Labels := by
      have ha : raw38786step2 = raw38786step1 := by apply Matrix.ext; unfold raw38786step2 raw38786step1; decide +kernel
      have hl : raw38786step1Labels = labelEmbedding4 ∘ raw38786step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38786step1 raw38786step1Labels raw38786step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1885 node1885Labels := by rfl

def raw38787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw38787Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw38787step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38787 raw38787Labels = mixedMoment B node1870 node1870Labels := by
  calc
    mixedMoment B raw38787 raw38787Labels = mixedMoment B raw38787step0 raw38787step0Labels := by
      have ha : raw38787step0 = raw38787 := by apply Matrix.ext; unfold raw38787step0 raw38787; decide +kernel
      have hl : raw38787Labels = labelEmbedding2 ∘ raw38787step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38787 raw38787Labels raw38787step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1870 node1870Labels := by rfl

def raw38788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw38788Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 0, 2]]
def raw38788step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38788step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw38788step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38788step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw38788step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38788 raw38788Labels = mixedMoment B node1886 node1886Labels := by
  calc
    mixedMoment B raw38788 raw38788Labels = mixedMoment B raw38788step0 raw38788step0Labels := by
      have ha : raw38788step0 = (fun i j => raw38788 (permutation154 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38788step0 raw38788; decide +kernel
      have hl : raw38788step0Labels = raw38788Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38788 raw38788Labels permutation154 permutation7
    mixedMoment B raw38788step0 raw38788step0Labels = mixedMoment B raw38788step1 raw38788step1Labels := by
      have ha : raw38788step1 = -raw38788step0 := by apply Matrix.ext; change ∀ i j, raw38788step1 i j = -(raw38788step0 i j); unfold raw38788step1 raw38788step0; decide +kernel
      have hl : raw38788step1Labels = raw38788step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38788step1 raw38788step1Labels = mixedMoment B raw38788step2 raw38788step2Labels := by
      have ha : raw38788step2 = raw38788step1 := by apply Matrix.ext; unfold raw38788step2 raw38788step1; decide +kernel
      have hl : raw38788step1Labels = labelEmbedding4 ∘ raw38788step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38788step1 raw38788step1Labels raw38788step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1886 node1886Labels := by rfl

def raw38789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw38789Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw38789step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38789 raw38789Labels = mixedMoment B node1871 node1871Labels := by
  calc
    mixedMoment B raw38789 raw38789Labels = mixedMoment B raw38789step0 raw38789step0Labels := by
      have ha : raw38789step0 = raw38789 := by apply Matrix.ext; unfold raw38789step0 raw38789; decide +kernel
      have hl : raw38789Labels = labelEmbedding2 ∘ raw38789step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38789 raw38789Labels raw38789step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1871 node1871Labels := by rfl

def raw38790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw38790Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw38790step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38790step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw38790step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38790step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw38790step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38790 raw38790Labels = mixedMoment B node1892 node1892Labels := by
  calc
    mixedMoment B raw38790 raw38790Labels = mixedMoment B raw38790step0 raw38790step0Labels := by
      have ha : raw38790step0 = (fun i j => raw38790 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38790step0 raw38790; decide +kernel
      have hl : raw38790step0Labels = raw38790Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38790 raw38790Labels permutation155 permutation7
    mixedMoment B raw38790step0 raw38790step0Labels = mixedMoment B raw38790step1 raw38790step1Labels := by
      have ha : raw38790step1 = -raw38790step0 := by apply Matrix.ext; change ∀ i j, raw38790step1 i j = -(raw38790step0 i j); unfold raw38790step1 raw38790step0; decide +kernel
      have hl : raw38790step1Labels = raw38790step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38790step1 raw38790step1Labels = mixedMoment B raw38790step2 raw38790step2Labels := by
      have ha : raw38790step2 = raw38790step1 := by apply Matrix.ext; unfold raw38790step2 raw38790step1; decide +kernel
      have hl : raw38790step1Labels = labelEmbedding4 ∘ raw38790step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38790step1 raw38790step1Labels raw38790step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1892 node1892Labels := by rfl

def raw38791 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw38791Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw38791step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38791 raw38791Labels = mixedMoment B node1873 node1873Labels := by
  calc
    mixedMoment B raw38791 raw38791Labels = mixedMoment B raw38791step0 raw38791step0Labels := by
      have ha : raw38791step0 = raw38791 := by apply Matrix.ext; unfold raw38791step0 raw38791; decide +kernel
      have hl : raw38791Labels = labelEmbedding2 ∘ raw38791step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38791 raw38791Labels raw38791step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1873 node1873Labels := by rfl

def raw38792 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw38792Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, 1, -1], ![-1, -2, 3], ![-3, 1, 2]]
def raw38792step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -1, -2]]
def raw38792step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38792step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -1, -2]]
def raw38792step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38792 raw38792Labels = mixedMoment B node1893 node1893Labels := by
  calc
    mixedMoment B raw38792 raw38792Labels = mixedMoment B raw38792step0 raw38792step0Labels := by
      have ha : raw38792step0 = (fun i j => raw38792 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38792step0 raw38792; decide +kernel
      have hl : raw38792step0Labels = raw38792Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38792 raw38792Labels permutation33 permutation7
    mixedMoment B raw38792step0 raw38792step0Labels = mixedMoment B raw38792step1 raw38792step1Labels := by
      have ha : raw38792step1 = -raw38792step0 := by apply Matrix.ext; change ∀ i j, raw38792step1 i j = -(raw38792step0 i j); unfold raw38792step1 raw38792step0; decide +kernel
      have hl : raw38792step1Labels = raw38792step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38792step1 raw38792step1Labels = mixedMoment B raw38792step2 raw38792step2Labels := by
      have ha : raw38792step2 = raw38792step1 := by apply Matrix.ext; unfold raw38792step2 raw38792step1; decide +kernel
      have hl : raw38792step1Labels = labelEmbedding4 ∘ raw38792step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38792step1 raw38792step1Labels raw38792step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1893 node1893Labels := by rfl

def raw38793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38793Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38793step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38793 raw38793Labels = mixedMoment B node1874 node1874Labels := by
  calc
    mixedMoment B raw38793 raw38793Labels = mixedMoment B raw38793step0 raw38793step0Labels := by
      have ha : raw38793step0 = raw38793 := by apply Matrix.ext; unfold raw38793step0 raw38793; decide +kernel
      have hl : raw38793Labels = labelEmbedding2 ∘ raw38793step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38793 raw38793Labels raw38793step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1874 node1874Labels := by rfl

def raw38794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38794Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38794step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 0, 3]]
def raw38794step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38794step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw38794step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38794step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw38794step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38794 raw38794Labels = mixedMoment B node1896 node1896Labels := by
  calc
    mixedMoment B raw38794 raw38794Labels = mixedMoment B raw38794step0 raw38794step0Labels := by
      have ha : raw38794step0 = (fun i j => raw38794 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38794step0 raw38794; decide +kernel
      have hl : raw38794step0Labels = raw38794Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38794 raw38794Labels permutation160 permutation7
    mixedMoment B raw38794step0 raw38794step0Labels = mixedMoment B raw38794step1 raw38794step1Labels := by
      have ha : raw38794step1 = -raw38794step0 := by apply Matrix.ext; change ∀ i j, raw38794step1 i j = -(raw38794step0 i j); unfold raw38794step1 raw38794step0; decide +kernel
      have hl : raw38794step1Labels = raw38794step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38794step1 raw38794step1Labels = mixedMoment B raw38794step2 raw38794step2Labels := by
      have ha : raw38794step2 = raw38794step1 := by apply Matrix.ext; unfold raw38794step2 raw38794step1; decide +kernel
      have hl : raw38794step1Labels = labelEmbedding4 ∘ raw38794step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38794step1 raw38794step1Labels raw38794step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1896 node1896Labels := by rfl

def raw38795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38795Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38795step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38795step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38795 raw38795Labels = mixedMoment B node1875 node1875Labels := by
  calc
    mixedMoment B raw38795 raw38795Labels = mixedMoment B raw38795step0 raw38795step0Labels := by
      have ha : raw38795step0 = raw38795 := by apply Matrix.ext; unfold raw38795step0 raw38795; decide +kernel
      have hl : raw38795Labels = labelEmbedding2 ∘ raw38795step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38795 raw38795Labels raw38795step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1875 node1875Labels := by rfl

def raw38796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38796Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw38796step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38796step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw38796step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38796step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw38796step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38796 raw38796Labels = mixedMoment B node1905 node1905Labels := by
  calc
    mixedMoment B raw38796 raw38796Labels = mixedMoment B raw38796step0 raw38796step0Labels := by
      have ha : raw38796step0 = (fun i j => raw38796 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38796step0 raw38796; decide +kernel
      have hl : raw38796step0Labels = raw38796Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38796 raw38796Labels permutation158 permutation7
    mixedMoment B raw38796step0 raw38796step0Labels = mixedMoment B raw38796step1 raw38796step1Labels := by
      have ha : raw38796step1 = -raw38796step0 := by apply Matrix.ext; change ∀ i j, raw38796step1 i j = -(raw38796step0 i j); unfold raw38796step1 raw38796step0; decide +kernel
      have hl : raw38796step1Labels = raw38796step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38796step1 raw38796step1Labels = mixedMoment B raw38796step2 raw38796step2Labels := by
      have ha : raw38796step2 = raw38796step1 := by apply Matrix.ext; unfold raw38796step2 raw38796step1; decide +kernel
      have hl : raw38796step1Labels = labelEmbedding4 ∘ raw38796step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38796step1 raw38796step1Labels raw38796step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1905 node1905Labels := by rfl

def raw38797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38797Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38797step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38797step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38797 raw38797Labels = mixedMoment B node1876 node1876Labels := by
  calc
    mixedMoment B raw38797 raw38797Labels = mixedMoment B raw38797step0 raw38797step0Labels := by
      have ha : raw38797step0 = raw38797 := by apply Matrix.ext; unfold raw38797step0 raw38797; decide +kernel
      have hl : raw38797Labels = labelEmbedding2 ∘ raw38797step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38797 raw38797Labels raw38797step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1876 node1876Labels := by rfl

def raw38798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38798Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw38798step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38798step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw38798step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38798step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw38798step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38798 raw38798Labels = mixedMoment B node1906 node1906Labels := by
  calc
    mixedMoment B raw38798 raw38798Labels = mixedMoment B raw38798step0 raw38798step0Labels := by
      have ha : raw38798step0 = (fun i j => raw38798 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38798step0 raw38798; decide +kernel
      have hl : raw38798step0Labels = raw38798Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38798 raw38798Labels permutation158 permutation7
    mixedMoment B raw38798step0 raw38798step0Labels = mixedMoment B raw38798step1 raw38798step1Labels := by
      have ha : raw38798step1 = -raw38798step0 := by apply Matrix.ext; change ∀ i j, raw38798step1 i j = -(raw38798step0 i j); unfold raw38798step1 raw38798step0; decide +kernel
      have hl : raw38798step1Labels = raw38798step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38798step1 raw38798step1Labels = mixedMoment B raw38798step2 raw38798step2Labels := by
      have ha : raw38798step2 = raw38798step1 := by apply Matrix.ext; unfold raw38798step2 raw38798step1; decide +kernel
      have hl : raw38798step1Labels = labelEmbedding4 ∘ raw38798step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38798step1 raw38798step1Labels raw38798step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1906 node1906Labels := by rfl

def raw38799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38799Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38799step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38799step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38799 raw38799Labels = mixedMoment B node1877 node1877Labels := by
  calc
    mixedMoment B raw38799 raw38799Labels = mixedMoment B raw38799step0 raw38799step0Labels := by
      have ha : raw38799step0 = raw38799 := by apply Matrix.ext; unfold raw38799step0 raw38799; decide +kernel
      have hl : raw38799Labels = labelEmbedding2 ∘ raw38799step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38799 raw38799Labels raw38799step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1877 node1877Labels := by rfl

def raw38800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38800Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38800step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw38800step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38800step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw38800step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38800step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw38800step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38800 raw38800Labels = mixedMoment B node1935 node1935Labels := by
  calc
    mixedMoment B raw38800 raw38800Labels = mixedMoment B raw38800step0 raw38800step0Labels := by
      have ha : raw38800step0 = (fun i j => raw38800 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38800step0 raw38800; decide +kernel
      have hl : raw38800step0Labels = raw38800Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38800 raw38800Labels permutation152 permutation7
    mixedMoment B raw38800step0 raw38800step0Labels = mixedMoment B raw38800step1 raw38800step1Labels := by
      have ha : raw38800step1 = -raw38800step0 := by apply Matrix.ext; change ∀ i j, raw38800step1 i j = -(raw38800step0 i j); unfold raw38800step1 raw38800step0; decide +kernel
      have hl : raw38800step1Labels = raw38800step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38800step1 raw38800step1Labels = mixedMoment B raw38800step2 raw38800step2Labels := by
      have ha : raw38800step2 = raw38800step1 := by apply Matrix.ext; unfold raw38800step2 raw38800step1; decide +kernel
      have hl : raw38800step1Labels = labelEmbedding4 ∘ raw38800step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38800step1 raw38800step1Labels raw38800step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1935 node1935Labels := by rfl

def raw38801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38801Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38801step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38801 raw38801Labels = mixedMoment B node1878 node1878Labels := by
  calc
    mixedMoment B raw38801 raw38801Labels = mixedMoment B raw38801step0 raw38801step0Labels := by
      have ha : raw38801step0 = raw38801 := by apply Matrix.ext; unfold raw38801step0 raw38801; decide +kernel
      have hl : raw38801Labels = labelEmbedding2 ∘ raw38801step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38801 raw38801Labels raw38801step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1878 node1878Labels := by rfl

def raw38802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38802Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw38802step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38802step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw38802step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38802step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw38802step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38802 raw38802Labels = mixedMoment B node1919 node1919Labels := by
  calc
    mixedMoment B raw38802 raw38802Labels = mixedMoment B raw38802step0 raw38802step0Labels := by
      have ha : raw38802step0 = (fun i j => raw38802 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38802step0 raw38802; decide +kernel
      have hl : raw38802step0Labels = raw38802Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38802 raw38802Labels permutation164 permutation7
    mixedMoment B raw38802step0 raw38802step0Labels = mixedMoment B raw38802step1 raw38802step1Labels := by
      have ha : raw38802step1 = -raw38802step0 := by apply Matrix.ext; change ∀ i j, raw38802step1 i j = -(raw38802step0 i j); unfold raw38802step1 raw38802step0; decide +kernel
      have hl : raw38802step1Labels = raw38802step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38802step1 raw38802step1Labels = mixedMoment B raw38802step2 raw38802step2Labels := by
      have ha : raw38802step2 = raw38802step1 := by apply Matrix.ext; unfold raw38802step2 raw38802step1; decide +kernel
      have hl : raw38802step1Labels = labelEmbedding4 ∘ raw38802step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38802step1 raw38802step1Labels raw38802step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1919 node1919Labels := by rfl

def raw38803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38803Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38803step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38803 raw38803Labels = mixedMoment B node1879 node1879Labels := by
  calc
    mixedMoment B raw38803 raw38803Labels = mixedMoment B raw38803step0 raw38803step0Labels := by
      have ha : raw38803step0 = raw38803 := by apply Matrix.ext; unfold raw38803step0 raw38803; decide +kernel
      have hl : raw38803Labels = labelEmbedding2 ∘ raw38803step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38803 raw38803Labels raw38803step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1879 node1879Labels := by rfl

def raw38804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38804Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38804step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw38804step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38804step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw38804step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38804step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw38804step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38804 raw38804Labels = mixedMoment B node1936 node1936Labels := by
  calc
    mixedMoment B raw38804 raw38804Labels = mixedMoment B raw38804step0 raw38804step0Labels := by
      have ha : raw38804step0 = (fun i j => raw38804 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38804step0 raw38804; decide +kernel
      have hl : raw38804step0Labels = raw38804Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38804 raw38804Labels permutation152 permutation7
    mixedMoment B raw38804step0 raw38804step0Labels = mixedMoment B raw38804step1 raw38804step1Labels := by
      have ha : raw38804step1 = -raw38804step0 := by apply Matrix.ext; change ∀ i j, raw38804step1 i j = -(raw38804step0 i j); unfold raw38804step1 raw38804step0; decide +kernel
      have hl : raw38804step1Labels = raw38804step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38804step1 raw38804step1Labels = mixedMoment B raw38804step2 raw38804step2Labels := by
      have ha : raw38804step2 = raw38804step1 := by apply Matrix.ext; unfold raw38804step2 raw38804step1; decide +kernel
      have hl : raw38804step1Labels = labelEmbedding4 ∘ raw38804step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38804step1 raw38804step1Labels raw38804step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1936 node1936Labels := by rfl

def raw38805 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw38805Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw38805step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38805 raw38805Labels = mixedMoment B node1880 node1880Labels := by
  calc
    mixedMoment B raw38805 raw38805Labels = mixedMoment B raw38805step0 raw38805step0Labels := by
      have ha : raw38805step0 = raw38805 := by apply Matrix.ext; unfold raw38805step0 raw38805; decide +kernel
      have hl : raw38805Labels = labelEmbedding2 ∘ raw38805step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38805 raw38805Labels raw38805step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1880 node1880Labels := by rfl

def raw38806 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw38806Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw38806step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 1, -3]]
def raw38806step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38806step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 1, -3]]
def raw38806step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38806 raw38806Labels = mixedMoment B node1938 node1938Labels := by
  calc
    mixedMoment B raw38806 raw38806Labels = mixedMoment B raw38806step0 raw38806step0Labels := by
      have ha : raw38806step0 = (fun i j => raw38806 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38806step0 raw38806; decide +kernel
      have hl : raw38806step0Labels = raw38806Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38806 raw38806Labels permutation32 permutation7
    mixedMoment B raw38806step0 raw38806step0Labels = mixedMoment B raw38806step1 raw38806step1Labels := by
      have ha : raw38806step1 = -raw38806step0 := by apply Matrix.ext; change ∀ i j, raw38806step1 i j = -(raw38806step0 i j); unfold raw38806step1 raw38806step0; decide +kernel
      have hl : raw38806step1Labels = raw38806step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38806step1 raw38806step1Labels = mixedMoment B raw38806step2 raw38806step2Labels := by
      have ha : raw38806step2 = raw38806step1 := by apply Matrix.ext; unfold raw38806step2 raw38806step1; decide +kernel
      have hl : raw38806step1Labels = labelEmbedding4 ∘ raw38806step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38806step1 raw38806step1Labels raw38806step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1938 node1938Labels := by rfl

def raw38807 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw38807Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw38807step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38807 raw38807Labels = mixedMoment B node1881 node1881Labels := by
  calc
    mixedMoment B raw38807 raw38807Labels = mixedMoment B raw38807step0 raw38807step0Labels := by
      have ha : raw38807step0 = raw38807 := by apply Matrix.ext; unfold raw38807step0 raw38807; decide +kernel
      have hl : raw38807Labels = labelEmbedding2 ∘ raw38807step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38807 raw38807Labels raw38807step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1881 node1881Labels := by rfl

def raw38808 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw38808Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 2, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw38808step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, 0, -2]]
def raw38808step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38808step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, 0, -2]]
def raw38808step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38808 raw38808Labels = mixedMoment B node1939 node1939Labels := by
  calc
    mixedMoment B raw38808 raw38808Labels = mixedMoment B raw38808step0 raw38808step0Labels := by
      have ha : raw38808step0 = (fun i j => raw38808 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38808step0 raw38808; decide +kernel
      have hl : raw38808step0Labels = raw38808Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38808 raw38808Labels permutation33 permutation7
    mixedMoment B raw38808step0 raw38808step0Labels = mixedMoment B raw38808step1 raw38808step1Labels := by
      have ha : raw38808step1 = -raw38808step0 := by apply Matrix.ext; change ∀ i j, raw38808step1 i j = -(raw38808step0 i j); unfold raw38808step1 raw38808step0; decide +kernel
      have hl : raw38808step1Labels = raw38808step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38808step1 raw38808step1Labels = mixedMoment B raw38808step2 raw38808step2Labels := by
      have ha : raw38808step2 = raw38808step1 := by apply Matrix.ext; unfold raw38808step2 raw38808step1; decide +kernel
      have hl : raw38808step1Labels = labelEmbedding4 ∘ raw38808step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38808step1 raw38808step1Labels raw38808step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1939 node1939Labels := by rfl

def raw38809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw38809Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38809step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw38809step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38809 raw38809Labels = mixedMoment B node1897 node1897Labels := by
  calc
    mixedMoment B raw38809 raw38809Labels = mixedMoment B raw38809step0 raw38809step0Labels := by
      have ha : raw38809step0 = raw38809 := by apply Matrix.ext; unfold raw38809step0 raw38809; decide +kernel
      have hl : raw38809Labels = labelEmbedding2 ∘ raw38809step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38809 raw38809Labels raw38809step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1897 node1897Labels := by rfl

def raw38810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw38810Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38810step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw38810step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38810step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw38810step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38810step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw38810step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38810 raw38810Labels = mixedMoment B node1907 node1907Labels := by
  calc
    mixedMoment B raw38810 raw38810Labels = mixedMoment B raw38810step0 raw38810step0Labels := by
      have ha : raw38810step0 = (fun i j => raw38810 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38810step0 raw38810; decide +kernel
      have hl : raw38810step0Labels = raw38810Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38810 raw38810Labels permutation164 permutation7
    mixedMoment B raw38810step0 raw38810step0Labels = mixedMoment B raw38810step1 raw38810step1Labels := by
      have ha : raw38810step1 = -raw38810step0 := by apply Matrix.ext; change ∀ i j, raw38810step1 i j = -(raw38810step0 i j); unfold raw38810step1 raw38810step0; decide +kernel
      have hl : raw38810step1Labels = raw38810step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38810step1 raw38810step1Labels = mixedMoment B raw38810step2 raw38810step2Labels := by
      have ha : raw38810step2 = raw38810step1 := by apply Matrix.ext; unfold raw38810step2 raw38810step1; decide +kernel
      have hl : raw38810step1Labels = labelEmbedding4 ∘ raw38810step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38810step1 raw38810step1Labels raw38810step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1907 node1907Labels := by rfl

def raw38811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38811Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38811step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38811step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38811 raw38811Labels = mixedMoment B node1898 node1898Labels := by
  calc
    mixedMoment B raw38811 raw38811Labels = mixedMoment B raw38811step0 raw38811step0Labels := by
      have ha : raw38811step0 = raw38811 := by apply Matrix.ext; unfold raw38811step0 raw38811; decide +kernel
      have hl : raw38811Labels = labelEmbedding2 ∘ raw38811step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38811 raw38811Labels raw38811step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1898 node1898Labels := by rfl

def raw38812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38812Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw38812step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38812step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw38812step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38812step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw38812step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38812 raw38812Labels = mixedMoment B node1940 node1940Labels := by
  calc
    mixedMoment B raw38812 raw38812Labels = mixedMoment B raw38812step0 raw38812step0Labels := by
      have ha : raw38812step0 = (fun i j => raw38812 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38812step0 raw38812; decide +kernel
      have hl : raw38812step0Labels = raw38812Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38812 raw38812Labels permutation152 permutation7
    mixedMoment B raw38812step0 raw38812step0Labels = mixedMoment B raw38812step1 raw38812step1Labels := by
      have ha : raw38812step1 = -raw38812step0 := by apply Matrix.ext; change ∀ i j, raw38812step1 i j = -(raw38812step0 i j); unfold raw38812step1 raw38812step0; decide +kernel
      have hl : raw38812step1Labels = raw38812step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38812step1 raw38812step1Labels = mixedMoment B raw38812step2 raw38812step2Labels := by
      have ha : raw38812step2 = raw38812step1 := by apply Matrix.ext; unfold raw38812step2 raw38812step1; decide +kernel
      have hl : raw38812step1Labels = labelEmbedding4 ∘ raw38812step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38812step1 raw38812step1Labels raw38812step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1940 node1940Labels := by rfl

def raw38813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38813Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38813step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38813step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38813 raw38813Labels = mixedMoment B node1900 node1900Labels := by
  calc
    mixedMoment B raw38813 raw38813Labels = mixedMoment B raw38813step0 raw38813step0Labels := by
      have ha : raw38813step0 = raw38813 := by apply Matrix.ext; unfold raw38813step0 raw38813; decide +kernel
      have hl : raw38813Labels = labelEmbedding2 ∘ raw38813step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38813 raw38813Labels raw38813step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1900 node1900Labels := by rfl

def raw38814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38814Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38814step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw38814step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38814step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw38814step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38814step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw38814step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38814 raw38814Labels = mixedMoment B node1921 node1921Labels := by
  calc
    mixedMoment B raw38814 raw38814Labels = mixedMoment B raw38814step0 raw38814step0Labels := by
      have ha : raw38814step0 = (fun i j => raw38814 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38814step0 raw38814; decide +kernel
      have hl : raw38814step0Labels = raw38814Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38814 raw38814Labels permutation164 permutation7
    mixedMoment B raw38814step0 raw38814step0Labels = mixedMoment B raw38814step1 raw38814step1Labels := by
      have ha : raw38814step1 = -raw38814step0 := by apply Matrix.ext; change ∀ i j, raw38814step1 i j = -(raw38814step0 i j); unfold raw38814step1 raw38814step0; decide +kernel
      have hl : raw38814step1Labels = raw38814step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38814step1 raw38814step1Labels = mixedMoment B raw38814step2 raw38814step2Labels := by
      have ha : raw38814step2 = raw38814step1 := by apply Matrix.ext; unfold raw38814step2 raw38814step1; decide +kernel
      have hl : raw38814step1Labels = labelEmbedding4 ∘ raw38814step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38814step1 raw38814step1Labels raw38814step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1921 node1921Labels := by rfl

def raw38815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38815Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38815step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38815step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38815 raw38815Labels = mixedMoment B node1901 node1901Labels := by
  calc
    mixedMoment B raw38815 raw38815Labels = mixedMoment B raw38815step0 raw38815step0Labels := by
      have ha : raw38815step0 = raw38815 := by apply Matrix.ext; unfold raw38815step0 raw38815; decide +kernel
      have hl : raw38815Labels = labelEmbedding2 ∘ raw38815step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38815 raw38815Labels raw38815step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1901 node1901Labels := by rfl

def raw38816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38816Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38816step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw38816step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38816step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw38816step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38816step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw38816step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38816 raw38816Labels = mixedMoment B node1941 node1941Labels := by
  calc
    mixedMoment B raw38816 raw38816Labels = mixedMoment B raw38816step0 raw38816step0Labels := by
      have ha : raw38816step0 = (fun i j => raw38816 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38816step0 raw38816; decide +kernel
      have hl : raw38816step0Labels = raw38816Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38816 raw38816Labels permutation152 permutation7
    mixedMoment B raw38816step0 raw38816step0Labels = mixedMoment B raw38816step1 raw38816step1Labels := by
      have ha : raw38816step1 = -raw38816step0 := by apply Matrix.ext; change ∀ i j, raw38816step1 i j = -(raw38816step0 i j); unfold raw38816step1 raw38816step0; decide +kernel
      have hl : raw38816step1Labels = raw38816step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38816step1 raw38816step1Labels = mixedMoment B raw38816step2 raw38816step2Labels := by
      have ha : raw38816step2 = raw38816step1 := by apply Matrix.ext; unfold raw38816step2 raw38816step1; decide +kernel
      have hl : raw38816step1Labels = labelEmbedding4 ∘ raw38816step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38816step1 raw38816step1Labels raw38816step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1941 node1941Labels := by rfl

def raw38817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw38817Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38817step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw38817step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38817 raw38817Labels = mixedMoment B node1909 node1909Labels := by
  calc
    mixedMoment B raw38817 raw38817Labels = mixedMoment B raw38817step0 raw38817step0Labels := by
      have ha : raw38817step0 = raw38817 := by apply Matrix.ext; unfold raw38817step0 raw38817; decide +kernel
      have hl : raw38817Labels = labelEmbedding2 ∘ raw38817step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38817 raw38817Labels raw38817step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1909 node1909Labels := by rfl

def raw38818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw38818Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38818step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw38818step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38818step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw38818step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38818step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw38818step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38818 raw38818Labels = mixedMoment B node1909 node1909Labels := by
  calc
    mixedMoment B raw38818 raw38818Labels = mixedMoment B raw38818step0 raw38818step0Labels := by
      have ha : raw38818step0 = (fun i j => raw38818 (permutation159 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38818step0 raw38818; decide +kernel
      have hl : raw38818step0Labels = raw38818Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38818 raw38818Labels permutation159 permutation7
    mixedMoment B raw38818step0 raw38818step0Labels = mixedMoment B raw38818step1 raw38818step1Labels := by
      have ha : raw38818step1 = -raw38818step0 := by apply Matrix.ext; change ∀ i j, raw38818step1 i j = -(raw38818step0 i j); unfold raw38818step1 raw38818step0; decide +kernel
      have hl : raw38818step1Labels = raw38818step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38818step1 raw38818step1Labels = mixedMoment B raw38818step2 raw38818step2Labels := by
      have ha : raw38818step2 = raw38818step1 := by apply Matrix.ext; unfold raw38818step2 raw38818step1; decide +kernel
      have hl : raw38818step1Labels = labelEmbedding4 ∘ raw38818step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38818step1 raw38818step1Labels raw38818step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1909 node1909Labels := by rfl

def raw38819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38819Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38819step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38819step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38819 raw38819Labels = mixedMoment B node1913 node1913Labels := by
  calc
    mixedMoment B raw38819 raw38819Labels = mixedMoment B raw38819step0 raw38819step0Labels := by
      have ha : raw38819step0 = raw38819 := by apply Matrix.ext; unfold raw38819step0 raw38819; decide +kernel
      have hl : raw38819Labels = labelEmbedding2 ∘ raw38819step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38819 raw38819Labels raw38819step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1913 node1913Labels := by rfl

def raw38820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38820Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38820step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw38820step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38820step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw38820step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38820step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw38820step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38820 raw38820Labels = mixedMoment B node1922 node1922Labels := by
  calc
    mixedMoment B raw38820 raw38820Labels = mixedMoment B raw38820step0 raw38820step0Labels := by
      have ha : raw38820step0 = (fun i j => raw38820 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38820step0 raw38820; decide +kernel
      have hl : raw38820step0Labels = raw38820Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38820 raw38820Labels permutation170 permutation7
    mixedMoment B raw38820step0 raw38820step0Labels = mixedMoment B raw38820step1 raw38820step1Labels := by
      have ha : raw38820step1 = -raw38820step0 := by apply Matrix.ext; change ∀ i j, raw38820step1 i j = -(raw38820step0 i j); unfold raw38820step1 raw38820step0; decide +kernel
      have hl : raw38820step1Labels = raw38820step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38820step1 raw38820step1Labels = mixedMoment B raw38820step2 raw38820step2Labels := by
      have ha : raw38820step2 = raw38820step1 := by apply Matrix.ext; unfold raw38820step2 raw38820step1; decide +kernel
      have hl : raw38820step1Labels = labelEmbedding4 ∘ raw38820step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38820step1 raw38820step1Labels raw38820step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1922 node1922Labels := by rfl

def raw38821 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw38821Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw38821step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38821 raw38821Labels = mixedMoment B node1915 node1915Labels := by
  calc
    mixedMoment B raw38821 raw38821Labels = mixedMoment B raw38821step0 raw38821step0Labels := by
      have ha : raw38821step0 = raw38821 := by apply Matrix.ext; unfold raw38821step0 raw38821; decide +kernel
      have hl : raw38821Labels = labelEmbedding2 ∘ raw38821step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38821 raw38821Labels raw38821step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1915 node1915Labels := by rfl

def raw38822 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw38822Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw38822step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38822step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw38822step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38822step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw38822step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38822 raw38822Labels = mixedMoment B node1946 node1946Labels := by
  calc
    mixedMoment B raw38822 raw38822Labels = mixedMoment B raw38822step0 raw38822step0Labels := by
      have ha : raw38822step0 = (fun i j => raw38822 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38822step0 raw38822; decide +kernel
      have hl : raw38822step0Labels = raw38822Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38822 raw38822Labels permutation33 permutation7
    mixedMoment B raw38822step0 raw38822step0Labels = mixedMoment B raw38822step1 raw38822step1Labels := by
      have ha : raw38822step1 = -raw38822step0 := by apply Matrix.ext; change ∀ i j, raw38822step1 i j = -(raw38822step0 i j); unfold raw38822step1 raw38822step0; decide +kernel
      have hl : raw38822step1Labels = raw38822step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38822step1 raw38822step1Labels = mixedMoment B raw38822step2 raw38822step2Labels := by
      have ha : raw38822step2 = raw38822step1 := by apply Matrix.ext; unfold raw38822step2 raw38822step1; decide +kernel
      have hl : raw38822step1Labels = labelEmbedding4 ∘ raw38822step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38822step1 raw38822step1Labels raw38822step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1946 node1946Labels := by rfl

def raw38823 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw38823Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw38823step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38823 raw38823Labels = mixedMoment B node1917 node1917Labels := by
  calc
    mixedMoment B raw38823 raw38823Labels = mixedMoment B raw38823step0 raw38823step0Labels := by
      have ha : raw38823step0 = raw38823 := by apply Matrix.ext; unfold raw38823step0 raw38823; decide +kernel
      have hl : raw38823Labels = labelEmbedding2 ∘ raw38823step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38823 raw38823Labels raw38823step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1917 node1917Labels := by rfl

def raw38824 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw38824Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw38824step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw38824step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38824step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw38824step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38824 raw38824Labels = mixedMoment B node1924 node1924Labels := by
  calc
    mixedMoment B raw38824 raw38824Labels = mixedMoment B raw38824step0 raw38824step0Labels := by
      have ha : raw38824step0 = (fun i j => raw38824 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38824step0 raw38824; decide +kernel
      have hl : raw38824step0Labels = raw38824Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38824 raw38824Labels permutation34 permutation7
    mixedMoment B raw38824step0 raw38824step0Labels = mixedMoment B raw38824step1 raw38824step1Labels := by
      have ha : raw38824step1 = -raw38824step0 := by apply Matrix.ext; change ∀ i j, raw38824step1 i j = -(raw38824step0 i j); unfold raw38824step1 raw38824step0; decide +kernel
      have hl : raw38824step1Labels = raw38824step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38824step1 raw38824step1Labels = mixedMoment B raw38824step2 raw38824step2Labels := by
      have ha : raw38824step2 = raw38824step1 := by apply Matrix.ext; unfold raw38824step2 raw38824step1; decide +kernel
      have hl : raw38824step1Labels = labelEmbedding4 ∘ raw38824step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38824step1 raw38824step1Labels raw38824step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1924 node1924Labels := by rfl

def raw38825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38825Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38825step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38825step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38825 raw38825Labels = mixedMoment B node1925 node1925Labels := by
  calc
    mixedMoment B raw38825 raw38825Labels = mixedMoment B raw38825step0 raw38825step0Labels := by
      have ha : raw38825step0 = raw38825 := by apply Matrix.ext; unfold raw38825step0 raw38825; decide +kernel
      have hl : raw38825Labels = labelEmbedding2 ∘ raw38825step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38825 raw38825Labels raw38825step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1925 node1925Labels := by rfl

def raw38826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38826Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw38826step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38826step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38826step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38826step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38826step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38826 raw38826Labels = mixedMoment B node1925 node1925Labels := by
  calc
    mixedMoment B raw38826 raw38826Labels = mixedMoment B raw38826step0 raw38826step0Labels := by
      have ha : raw38826step0 = (fun i j => raw38826 (permutation173 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38826step0 raw38826; decide +kernel
      have hl : raw38826step0Labels = raw38826Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38826 raw38826Labels permutation173 permutation7
    mixedMoment B raw38826step0 raw38826step0Labels = mixedMoment B raw38826step1 raw38826step1Labels := by
      have ha : raw38826step1 = -raw38826step0 := by apply Matrix.ext; change ∀ i j, raw38826step1 i j = -(raw38826step0 i j); unfold raw38826step1 raw38826step0; decide +kernel
      have hl : raw38826step1Labels = raw38826step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38826step1 raw38826step1Labels = mixedMoment B raw38826step2 raw38826step2Labels := by
      have ha : raw38826step2 = raw38826step1 := by apply Matrix.ext; unfold raw38826step2 raw38826step1; decide +kernel
      have hl : raw38826step1Labels = labelEmbedding4 ∘ raw38826step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38826step1 raw38826step1Labels raw38826step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1925 node1925Labels := by rfl

def raw38827 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw38827Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw38827step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38827 raw38827Labels = mixedMoment B node1926 node1926Labels := by
  calc
    mixedMoment B raw38827 raw38827Labels = mixedMoment B raw38827step0 raw38827step0Labels := by
      have ha : raw38827step0 = raw38827 := by apply Matrix.ext; unfold raw38827step0 raw38827; decide +kernel
      have hl : raw38827Labels = labelEmbedding2 ∘ raw38827step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38827 raw38827Labels raw38827step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1926 node1926Labels := by rfl

def raw38828 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw38828Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw38828step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw38828step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38828step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw38828step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38828 raw38828Labels = mixedMoment B node1948 node1948Labels := by
  calc
    mixedMoment B raw38828 raw38828Labels = mixedMoment B raw38828step0 raw38828step0Labels := by
      have ha : raw38828step0 = (fun i j => raw38828 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38828step0 raw38828; decide +kernel
      have hl : raw38828step0Labels = raw38828Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38828 raw38828Labels permutation35 permutation7
    mixedMoment B raw38828step0 raw38828step0Labels = mixedMoment B raw38828step1 raw38828step1Labels := by
      have ha : raw38828step1 = -raw38828step0 := by apply Matrix.ext; change ∀ i j, raw38828step1 i j = -(raw38828step0 i j); unfold raw38828step1 raw38828step0; decide +kernel
      have hl : raw38828step1Labels = raw38828step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38828step1 raw38828step1Labels = mixedMoment B raw38828step2 raw38828step2Labels := by
      have ha : raw38828step2 = raw38828step1 := by apply Matrix.ext; unfold raw38828step2 raw38828step1; decide +kernel
      have hl : raw38828step1Labels = labelEmbedding4 ∘ raw38828step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38828step1 raw38828step1Labels raw38828step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1948 node1948Labels := by rfl

def raw38829 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw38829Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw38829step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38829 raw38829Labels = mixedMoment B node1928 node1928Labels := by
  calc
    mixedMoment B raw38829 raw38829Labels = mixedMoment B raw38829step0 raw38829step0Labels := by
      have ha : raw38829step0 = raw38829 := by apply Matrix.ext; unfold raw38829step0 raw38829; decide +kernel
      have hl : raw38829Labels = labelEmbedding2 ∘ raw38829step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38829 raw38829Labels raw38829step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1928 node1928Labels := by rfl

def raw38830 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw38830Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw38830step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw38830step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38830step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw38830step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38830 raw38830Labels = mixedMoment B node1928 node1928Labels := by
  calc
    mixedMoment B raw38830 raw38830Labels = mixedMoment B raw38830step0 raw38830step0Labels := by
      have ha : raw38830step0 = (fun i j => raw38830 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38830step0 raw38830; decide +kernel
      have hl : raw38830step0Labels = raw38830Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38830 raw38830Labels permutation34 permutation7
    mixedMoment B raw38830step0 raw38830step0Labels = mixedMoment B raw38830step1 raw38830step1Labels := by
      have ha : raw38830step1 = -raw38830step0 := by apply Matrix.ext; change ∀ i j, raw38830step1 i j = -(raw38830step0 i j); unfold raw38830step1 raw38830step0; decide +kernel
      have hl : raw38830step1Labels = raw38830step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38830step1 raw38830step1Labels = mixedMoment B raw38830step2 raw38830step2Labels := by
      have ha : raw38830step2 = raw38830step1 := by apply Matrix.ext; unfold raw38830step2 raw38830step1; decide +kernel
      have hl : raw38830step1Labels = labelEmbedding4 ∘ raw38830step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38830step1 raw38830step1Labels raw38830step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1928 node1928Labels := by rfl

def raw38831 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw38831Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw38831step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38831 raw38831Labels = mixedMoment B node1929 node1929Labels := by
  calc
    mixedMoment B raw38831 raw38831Labels = mixedMoment B raw38831step0 raw38831step0Labels := by
      have ha : raw38831step0 = raw38831 := by apply Matrix.ext; unfold raw38831step0 raw38831; decide +kernel
      have hl : raw38831Labels = labelEmbedding2 ∘ raw38831step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38831 raw38831Labels raw38831step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1929 node1929Labels := by rfl

def raw38832 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw38832Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw38832step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38832step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw38832step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38832step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw38832step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38832 raw38832Labels = mixedMoment B node1949 node1949Labels := by
  calc
    mixedMoment B raw38832 raw38832Labels = mixedMoment B raw38832step0 raw38832step0Labels := by
      have ha : raw38832step0 = (fun i j => raw38832 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38832step0 raw38832; decide +kernel
      have hl : raw38832step0Labels = raw38832Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38832 raw38832Labels permutation35 permutation7
    mixedMoment B raw38832step0 raw38832step0Labels = mixedMoment B raw38832step1 raw38832step1Labels := by
      have ha : raw38832step1 = -raw38832step0 := by apply Matrix.ext; change ∀ i j, raw38832step1 i j = -(raw38832step0 i j); unfold raw38832step1 raw38832step0; decide +kernel
      have hl : raw38832step1Labels = raw38832step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38832step1 raw38832step1Labels = mixedMoment B raw38832step2 raw38832step2Labels := by
      have ha : raw38832step2 = raw38832step1 := by apply Matrix.ext; unfold raw38832step2 raw38832step1; decide +kernel
      have hl : raw38832step1Labels = labelEmbedding4 ∘ raw38832step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38832step1 raw38832step1Labels raw38832step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1949 node1949Labels := by rfl

def raw38833 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw38833Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38833step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw38833step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38833 raw38833Labels = mixedMoment B node1951 node1951Labels := by
  calc
    mixedMoment B raw38833 raw38833Labels = mixedMoment B raw38833step0 raw38833step0Labels := by
      have ha : raw38833step0 = raw38833 := by apply Matrix.ext; unfold raw38833step0 raw38833; decide +kernel
      have hl : raw38833Labels = labelEmbedding2 ∘ raw38833step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38833 raw38833Labels raw38833step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1951 node1951Labels := by rfl

def raw38834 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw38834Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38834step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw38834step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38834step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw38834step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38834step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw38834step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38834 raw38834Labels = mixedMoment B node1951 node1951Labels := by
  calc
    mixedMoment B raw38834 raw38834Labels = mixedMoment B raw38834step0 raw38834step0Labels := by
      have ha : raw38834step0 = (fun i j => raw38834 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38834step0 raw38834; decide +kernel
      have hl : raw38834step0Labels = raw38834Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38834 raw38834Labels permutation9 permutation7
    mixedMoment B raw38834step0 raw38834step0Labels = mixedMoment B raw38834step1 raw38834step1Labels := by
      have ha : raw38834step1 = -raw38834step0 := by apply Matrix.ext; change ∀ i j, raw38834step1 i j = -(raw38834step0 i j); unfold raw38834step1 raw38834step0; decide +kernel
      have hl : raw38834step1Labels = raw38834step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38834step1 raw38834step1Labels = mixedMoment B raw38834step2 raw38834step2Labels := by
      have ha : raw38834step2 = raw38834step1 := by apply Matrix.ext; unfold raw38834step2 raw38834step1; decide +kernel
      have hl : raw38834step1Labels = labelEmbedding4 ∘ raw38834step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38834step1 raw38834step1Labels raw38834step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1951 node1951Labels := by rfl

def raw38835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw38835Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38835step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw38835step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38835 raw38835Labels = mixedMoment B node1954 node1954Labels := by
  calc
    mixedMoment B raw38835 raw38835Labels = mixedMoment B raw38835step0 raw38835step0Labels := by
      have ha : raw38835step0 = raw38835 := by apply Matrix.ext; unfold raw38835step0 raw38835; decide +kernel
      have hl : raw38835Labels = labelEmbedding2 ∘ raw38835step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38835 raw38835Labels raw38835step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1954 node1954Labels := by rfl

def raw38836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw38836Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38836step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 0, 2], ![-2, -1, 3]]
def raw38836step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38836step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw38836step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38836step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw38836step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38836 raw38836Labels = mixedMoment B node1985 node1985Labels := by
  calc
    mixedMoment B raw38836 raw38836Labels = mixedMoment B raw38836step0 raw38836step0Labels := by
      have ha : raw38836step0 = (fun i j => raw38836 (permutation200 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38836step0 raw38836; decide +kernel
      have hl : raw38836step0Labels = raw38836Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38836 raw38836Labels permutation200 permutation7
    mixedMoment B raw38836step0 raw38836step0Labels = mixedMoment B raw38836step1 raw38836step1Labels := by
      have ha : raw38836step1 = -raw38836step0 := by apply Matrix.ext; change ∀ i j, raw38836step1 i j = -(raw38836step0 i j); unfold raw38836step1 raw38836step0; decide +kernel
      have hl : raw38836step1Labels = raw38836step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38836step1 raw38836step1Labels = mixedMoment B raw38836step2 raw38836step2Labels := by
      have ha : raw38836step2 = raw38836step1 := by apply Matrix.ext; unfold raw38836step2 raw38836step1; decide +kernel
      have hl : raw38836step1Labels = labelEmbedding4 ∘ raw38836step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38836step1 raw38836step1Labels raw38836step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1985 node1985Labels := by rfl

def raw38837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw38837Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38837step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw38837step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38837 raw38837Labels = mixedMoment B node1958 node1958Labels := by
  calc
    mixedMoment B raw38837 raw38837Labels = mixedMoment B raw38837step0 raw38837step0Labels := by
      have ha : raw38837step0 = raw38837 := by apply Matrix.ext; unfold raw38837step0 raw38837; decide +kernel
      have hl : raw38837Labels = labelEmbedding2 ∘ raw38837step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38837 raw38837Labels raw38837step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1958 node1958Labels := by rfl

def raw38838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw38838Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38838step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw38838step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38838step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw38838step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38838step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw38838step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38838 raw38838Labels = mixedMoment B node2069 node2069Labels := by
  calc
    mixedMoment B raw38838 raw38838Labels = mixedMoment B raw38838step0 raw38838step0Labels := by
      have ha : raw38838step0 = (fun i j => raw38838 (permutation200 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38838step0 raw38838; decide +kernel
      have hl : raw38838step0Labels = raw38838Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38838 raw38838Labels permutation200 permutation7
    mixedMoment B raw38838step0 raw38838step0Labels = mixedMoment B raw38838step1 raw38838step1Labels := by
      have ha : raw38838step1 = -raw38838step0 := by apply Matrix.ext; change ∀ i j, raw38838step1 i j = -(raw38838step0 i j); unfold raw38838step1 raw38838step0; decide +kernel
      have hl : raw38838step1Labels = raw38838step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38838step1 raw38838step1Labels = mixedMoment B raw38838step2 raw38838step2Labels := by
      have ha : raw38838step2 = raw38838step1 := by apply Matrix.ext; unfold raw38838step2 raw38838step1; decide +kernel
      have hl : raw38838step1Labels = labelEmbedding4 ∘ raw38838step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38838step1 raw38838step1Labels raw38838step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2069 node2069Labels := by rfl

def raw38839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38839Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38839step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38839step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38839 raw38839Labels = mixedMoment B node1959 node1959Labels := by
  calc
    mixedMoment B raw38839 raw38839Labels = mixedMoment B raw38839step0 raw38839step0Labels := by
      have ha : raw38839step0 = raw38839 := by apply Matrix.ext; unfold raw38839step0 raw38839; decide +kernel
      have hl : raw38839Labels = labelEmbedding2 ∘ raw38839step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38839 raw38839Labels raw38839step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1959 node1959Labels := by rfl

def raw38840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38840Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38840step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw38840step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38840step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw38840step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38840 raw38840Labels = mixedMoment B node2170 node2170Labels := by
  calc
    mixedMoment B raw38840 raw38840Labels = mixedMoment B raw38840step0 raw38840step0Labels := by
      have ha : raw38840step0 = (fun i j => raw38840 (permutation662 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38840step0 raw38840; decide +kernel
      have hl : raw38840step0Labels = raw38840Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38840 raw38840Labels permutation662 permutation7
    mixedMoment B raw38840step0 raw38840step0Labels = mixedMoment B raw38840step1 raw38840step1Labels := by
      have ha : raw38840step1 = raw38840step0 := by apply Matrix.ext; unfold raw38840step1 raw38840step0; decide +kernel
      have hl : raw38840step0Labels = labelEmbedding4 ∘ raw38840step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38840step0 raw38840step0Labels raw38840step1Labels labelEmbedding4 hl
    _ = mixedMoment B node2170 node2170Labels := by rfl

def raw38841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38841Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38841step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38841step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38841 raw38841Labels = mixedMoment B node1960 node1960Labels := by
  calc
    mixedMoment B raw38841 raw38841Labels = mixedMoment B raw38841step0 raw38841step0Labels := by
      have ha : raw38841step0 = raw38841 := by apply Matrix.ext; unfold raw38841step0 raw38841; decide +kernel
      have hl : raw38841Labels = labelEmbedding2 ∘ raw38841step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38841 raw38841Labels raw38841step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1960 node1960Labels := by rfl

def raw38842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38842Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38842step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw38842step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38842step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw38842step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38842step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw38842step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38842 raw38842Labels = mixedMoment B node2173 node2173Labels := by
  calc
    mixedMoment B raw38842 raw38842Labels = mixedMoment B raw38842step0 raw38842step0Labels := by
      have ha : raw38842step0 = (fun i j => raw38842 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38842step0 raw38842; decide +kernel
      have hl : raw38842step0Labels = raw38842Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38842 raw38842Labels permutation152 permutation7
    mixedMoment B raw38842step0 raw38842step0Labels = mixedMoment B raw38842step1 raw38842step1Labels := by
      have ha : raw38842step1 = -raw38842step0 := by apply Matrix.ext; change ∀ i j, raw38842step1 i j = -(raw38842step0 i j); unfold raw38842step1 raw38842step0; decide +kernel
      have hl : raw38842step1Labels = raw38842step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38842step1 raw38842step1Labels = mixedMoment B raw38842step2 raw38842step2Labels := by
      have ha : raw38842step2 = raw38842step1 := by apply Matrix.ext; unfold raw38842step2 raw38842step1; decide +kernel
      have hl : raw38842step1Labels = labelEmbedding4 ∘ raw38842step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38842step1 raw38842step1Labels raw38842step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2173 node2173Labels := by rfl

def raw38843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38843Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38843 raw38843Labels = mixedMoment B node1963 node1963Labels := by
  calc
    mixedMoment B raw38843 raw38843Labels = mixedMoment B raw38843step0 raw38843step0Labels := by
      have ha : raw38843step0 = raw38843 := by apply Matrix.ext; unfold raw38843step0 raw38843; decide +kernel
      have hl : raw38843Labels = labelEmbedding2 ∘ raw38843step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38843 raw38843Labels raw38843step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1963 node1963Labels := by rfl

def raw38844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38844Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38844step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw38844step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38844step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw38844step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38844step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw38844step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38844 raw38844Labels = mixedMoment B node2174 node2174Labels := by
  calc
    mixedMoment B raw38844 raw38844Labels = mixedMoment B raw38844step0 raw38844step0Labels := by
      have ha : raw38844step0 = (fun i j => raw38844 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38844step0 raw38844; decide +kernel
      have hl : raw38844step0Labels = raw38844Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38844 raw38844Labels permutation152 permutation7
    mixedMoment B raw38844step0 raw38844step0Labels = mixedMoment B raw38844step1 raw38844step1Labels := by
      have ha : raw38844step1 = -raw38844step0 := by apply Matrix.ext; change ∀ i j, raw38844step1 i j = -(raw38844step0 i j); unfold raw38844step1 raw38844step0; decide +kernel
      have hl : raw38844step1Labels = raw38844step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38844step1 raw38844step1Labels = mixedMoment B raw38844step2 raw38844step2Labels := by
      have ha : raw38844step2 = raw38844step1 := by apply Matrix.ext; unfold raw38844step2 raw38844step1; decide +kernel
      have hl : raw38844step1Labels = labelEmbedding4 ∘ raw38844step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38844step1 raw38844step1Labels raw38844step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2174 node2174Labels := by rfl

def raw38845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38845Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38845step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38845step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38845 raw38845Labels = mixedMoment B node1964 node1964Labels := by
  calc
    mixedMoment B raw38845 raw38845Labels = mixedMoment B raw38845step0 raw38845step0Labels := by
      have ha : raw38845step0 = raw38845 := by apply Matrix.ext; unfold raw38845step0 raw38845; decide +kernel
      have hl : raw38845Labels = labelEmbedding2 ∘ raw38845step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38845 raw38845Labels raw38845step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1964 node1964Labels := by rfl

def raw38846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38846Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw38846step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38846step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw38846step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38846step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw38846step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38846 raw38846Labels = mixedMoment B node2182 node2182Labels := by
  calc
    mixedMoment B raw38846 raw38846Labels = mixedMoment B raw38846step0 raw38846step0Labels := by
      have ha : raw38846step0 = (fun i j => raw38846 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38846step0 raw38846; decide +kernel
      have hl : raw38846step0Labels = raw38846Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38846 raw38846Labels permutation152 permutation7
    mixedMoment B raw38846step0 raw38846step0Labels = mixedMoment B raw38846step1 raw38846step1Labels := by
      have ha : raw38846step1 = -raw38846step0 := by apply Matrix.ext; change ∀ i j, raw38846step1 i j = -(raw38846step0 i j); unfold raw38846step1 raw38846step0; decide +kernel
      have hl : raw38846step1Labels = raw38846step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38846step1 raw38846step1Labels = mixedMoment B raw38846step2 raw38846step2Labels := by
      have ha : raw38846step2 = raw38846step1 := by apply Matrix.ext; unfold raw38846step2 raw38846step1; decide +kernel
      have hl : raw38846step1Labels = labelEmbedding4 ∘ raw38846step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38846step1 raw38846step1Labels raw38846step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2182 node2182Labels := by rfl

def raw38847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38847Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38847step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38847step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38847 raw38847Labels = mixedMoment B node1966 node1966Labels := by
  calc
    mixedMoment B raw38847 raw38847Labels = mixedMoment B raw38847step0 raw38847step0Labels := by
      have ha : raw38847step0 = raw38847 := by apply Matrix.ext; unfold raw38847step0 raw38847; decide +kernel
      have hl : raw38847Labels = labelEmbedding2 ∘ raw38847step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38847 raw38847Labels raw38847step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1966 node1966Labels := by rfl

def raw38848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38848Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38848step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw38848step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38848step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw38848step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38848step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw38848step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38848 raw38848Labels = mixedMoment B node2177 node2177Labels := by
  calc
    mixedMoment B raw38848 raw38848Labels = mixedMoment B raw38848step0 raw38848step0Labels := by
      have ha : raw38848step0 = (fun i j => raw38848 (permutation154 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38848step0 raw38848; decide +kernel
      have hl : raw38848step0Labels = raw38848Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38848 raw38848Labels permutation154 permutation7
    mixedMoment B raw38848step0 raw38848step0Labels = mixedMoment B raw38848step1 raw38848step1Labels := by
      have ha : raw38848step1 = -raw38848step0 := by apply Matrix.ext; change ∀ i j, raw38848step1 i j = -(raw38848step0 i j); unfold raw38848step1 raw38848step0; decide +kernel
      have hl : raw38848step1Labels = raw38848step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38848step1 raw38848step1Labels = mixedMoment B raw38848step2 raw38848step2Labels := by
      have ha : raw38848step2 = raw38848step1 := by apply Matrix.ext; unfold raw38848step2 raw38848step1; decide +kernel
      have hl : raw38848step1Labels = labelEmbedding4 ∘ raw38848step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38848step1 raw38848step1Labels raw38848step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2177 node2177Labels := by rfl

def raw38849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38849Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38849step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38849 raw38849Labels = mixedMoment B node1967 node1967Labels := by
  calc
    mixedMoment B raw38849 raw38849Labels = mixedMoment B raw38849step0 raw38849step0Labels := by
      have ha : raw38849step0 = raw38849 := by apply Matrix.ext; unfold raw38849step0 raw38849; decide +kernel
      have hl : raw38849Labels = labelEmbedding2 ∘ raw38849step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38849 raw38849Labels raw38849step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1967 node1967Labels := by rfl

def raw38850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38850Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38850step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw38850step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38850step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw38850step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38850step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw38850step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38850 raw38850Labels = mixedMoment B node2183 node2183Labels := by
  calc
    mixedMoment B raw38850 raw38850Labels = mixedMoment B raw38850step0 raw38850step0Labels := by
      have ha : raw38850step0 = (fun i j => raw38850 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38850step0 raw38850; decide +kernel
      have hl : raw38850step0Labels = raw38850Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38850 raw38850Labels permutation152 permutation7
    mixedMoment B raw38850step0 raw38850step0Labels = mixedMoment B raw38850step1 raw38850step1Labels := by
      have ha : raw38850step1 = -raw38850step0 := by apply Matrix.ext; change ∀ i j, raw38850step1 i j = -(raw38850step0 i j); unfold raw38850step1 raw38850step0; decide +kernel
      have hl : raw38850step1Labels = raw38850step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38850step1 raw38850step1Labels = mixedMoment B raw38850step2 raw38850step2Labels := by
      have ha : raw38850step2 = raw38850step1 := by apply Matrix.ext; unfold raw38850step2 raw38850step1; decide +kernel
      have hl : raw38850step1Labels = labelEmbedding4 ∘ raw38850step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38850step1 raw38850step1Labels raw38850step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2183 node2183Labels := by rfl

def raw38851 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw38851Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw38851step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38851 raw38851Labels = mixedMoment B node1969 node1969Labels := by
  calc
    mixedMoment B raw38851 raw38851Labels = mixedMoment B raw38851step0 raw38851step0Labels := by
      have ha : raw38851step0 = raw38851 := by apply Matrix.ext; unfold raw38851step0 raw38851; decide +kernel
      have hl : raw38851Labels = labelEmbedding2 ∘ raw38851step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38851 raw38851Labels raw38851step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1969 node1969Labels := by rfl

def raw38852 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw38852Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw38852step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw38852step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38852step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw38852step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38852 raw38852Labels = mixedMoment B node2185 node2185Labels := by
  calc
    mixedMoment B raw38852 raw38852Labels = mixedMoment B raw38852step0 raw38852step0Labels := by
      have ha : raw38852step0 = (fun i j => raw38852 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38852step0 raw38852; decide +kernel
      have hl : raw38852step0Labels = raw38852Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38852 raw38852Labels permutation32 permutation7
    mixedMoment B raw38852step0 raw38852step0Labels = mixedMoment B raw38852step1 raw38852step1Labels := by
      have ha : raw38852step1 = -raw38852step0 := by apply Matrix.ext; change ∀ i j, raw38852step1 i j = -(raw38852step0 i j); unfold raw38852step1 raw38852step0; decide +kernel
      have hl : raw38852step1Labels = raw38852step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38852step1 raw38852step1Labels = mixedMoment B raw38852step2 raw38852step2Labels := by
      have ha : raw38852step2 = raw38852step1 := by apply Matrix.ext; unfold raw38852step2 raw38852step1; decide +kernel
      have hl : raw38852step1Labels = labelEmbedding4 ∘ raw38852step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38852step1 raw38852step1Labels raw38852step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2185 node2185Labels := by rfl

def raw38853 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw38853Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw38853step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38853 raw38853Labels = mixedMoment B node1970 node1970Labels := by
  calc
    mixedMoment B raw38853 raw38853Labels = mixedMoment B raw38853step0 raw38853step0Labels := by
      have ha : raw38853step0 = raw38853 := by apply Matrix.ext; unfold raw38853step0 raw38853; decide +kernel
      have hl : raw38853Labels = labelEmbedding2 ∘ raw38853step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38853 raw38853Labels raw38853step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1970 node1970Labels := by rfl

def raw38854 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw38854Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw38854step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38854step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw38854step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38854step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw38854step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38854 raw38854Labels = mixedMoment B node2186 node2186Labels := by
  calc
    mixedMoment B raw38854 raw38854Labels = mixedMoment B raw38854step0 raw38854step0Labels := by
      have ha : raw38854step0 = (fun i j => raw38854 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38854step0 raw38854; decide +kernel
      have hl : raw38854step0Labels = raw38854Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38854 raw38854Labels permutation33 permutation7
    mixedMoment B raw38854step0 raw38854step0Labels = mixedMoment B raw38854step1 raw38854step1Labels := by
      have ha : raw38854step1 = -raw38854step0 := by apply Matrix.ext; change ∀ i j, raw38854step1 i j = -(raw38854step0 i j); unfold raw38854step1 raw38854step0; decide +kernel
      have hl : raw38854step1Labels = raw38854step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38854step1 raw38854step1Labels = mixedMoment B raw38854step2 raw38854step2Labels := by
      have ha : raw38854step2 = raw38854step1 := by apply Matrix.ext; unfold raw38854step2 raw38854step1; decide +kernel
      have hl : raw38854step1Labels = labelEmbedding4 ∘ raw38854step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38854step1 raw38854step1Labels raw38854step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2186 node2186Labels := by rfl

def raw38855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw38855Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw38855step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38855 raw38855Labels = mixedMoment B node1986 node1986Labels := by
  calc
    mixedMoment B raw38855 raw38855Labels = mixedMoment B raw38855step0 raw38855step0Labels := by
      have ha : raw38855step0 = raw38855 := by apply Matrix.ext; unfold raw38855step0 raw38855; decide +kernel
      have hl : raw38855Labels = labelEmbedding2 ∘ raw38855step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38855 raw38855Labels raw38855step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1986 node1986Labels := by rfl

def raw38856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw38856Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw38856step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38856step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw38856step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38856 raw38856Labels = mixedMoment B node1986 node1986Labels := by
  calc
    mixedMoment B raw38856 raw38856Labels = mixedMoment B raw38856step0 raw38856step0Labels := by
      have ha : raw38856step0 = (fun i j => raw38856 (permutation662 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38856step0 raw38856; decide +kernel
      have hl : raw38856step0Labels = raw38856Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38856 raw38856Labels permutation662 permutation7
    mixedMoment B raw38856step0 raw38856step0Labels = mixedMoment B raw38856step1 raw38856step1Labels := by
      have ha : raw38856step1 = raw38856step0 := by apply Matrix.ext; unfold raw38856step1 raw38856step0; decide +kernel
      have hl : raw38856step0Labels = labelEmbedding4 ∘ raw38856step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38856step0 raw38856step0Labels raw38856step1Labels labelEmbedding4 hl
    _ = mixedMoment B node1986 node1986Labels := by rfl

def raw38857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38857Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38857step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38857 raw38857Labels = mixedMoment B node1987 node1987Labels := by
  calc
    mixedMoment B raw38857 raw38857Labels = mixedMoment B raw38857step0 raw38857step0Labels := by
      have ha : raw38857step0 = raw38857 := by apply Matrix.ext; unfold raw38857step0 raw38857; decide +kernel
      have hl : raw38857Labels = labelEmbedding2 ∘ raw38857step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38857 raw38857Labels raw38857step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1987 node1987Labels := by rfl

def raw38858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38858Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw38858step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38858step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38858step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38858step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38858step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38858 raw38858Labels = mixedMoment B node1996 node1996Labels := by
  calc
    mixedMoment B raw38858 raw38858Labels = mixedMoment B raw38858step0 raw38858step0Labels := by
      have ha : raw38858step0 = (fun i j => raw38858 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38858step0 raw38858; decide +kernel
      have hl : raw38858step0Labels = raw38858Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38858 raw38858Labels permutation176 permutation7
    mixedMoment B raw38858step0 raw38858step0Labels = mixedMoment B raw38858step1 raw38858step1Labels := by
      have ha : raw38858step1 = -raw38858step0 := by apply Matrix.ext; change ∀ i j, raw38858step1 i j = -(raw38858step0 i j); unfold raw38858step1 raw38858step0; decide +kernel
      have hl : raw38858step1Labels = raw38858step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38858step1 raw38858step1Labels = mixedMoment B raw38858step2 raw38858step2Labels := by
      have ha : raw38858step2 = raw38858step1 := by apply Matrix.ext; unfold raw38858step2 raw38858step1; decide +kernel
      have hl : raw38858step1Labels = labelEmbedding4 ∘ raw38858step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38858step1 raw38858step1Labels raw38858step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1996 node1996Labels := by rfl

def raw38859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38859Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38859step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38859 raw38859Labels = mixedMoment B node1990 node1990Labels := by
  calc
    mixedMoment B raw38859 raw38859Labels = mixedMoment B raw38859step0 raw38859step0Labels := by
      have ha : raw38859step0 = raw38859 := by apply Matrix.ext; unfold raw38859step0 raw38859; decide +kernel
      have hl : raw38859Labels = labelEmbedding2 ∘ raw38859step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38859 raw38859Labels raw38859step0Labels labelEmbedding2 hl
    _ = mixedMoment B node1990 node1990Labels := by rfl

def raw38860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38860Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw38860step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38860step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38860step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38860step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38860step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38860 raw38860Labels = mixedMoment B node1997 node1997Labels := by
  calc
    mixedMoment B raw38860 raw38860Labels = mixedMoment B raw38860step0 raw38860step0Labels := by
      have ha : raw38860step0 = (fun i j => raw38860 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38860step0 raw38860; decide +kernel
      have hl : raw38860step0Labels = raw38860Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38860 raw38860Labels permutation176 permutation7
    mixedMoment B raw38860step0 raw38860step0Labels = mixedMoment B raw38860step1 raw38860step1Labels := by
      have ha : raw38860step1 = -raw38860step0 := by apply Matrix.ext; change ∀ i j, raw38860step1 i j = -(raw38860step0 i j); unfold raw38860step1 raw38860step0; decide +kernel
      have hl : raw38860step1Labels = raw38860step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38860step1 raw38860step1Labels = mixedMoment B raw38860step2 raw38860step2Labels := by
      have ha : raw38860step2 = raw38860step1 := by apply Matrix.ext; unfold raw38860step2 raw38860step1; decide +kernel
      have hl : raw38860step1Labels = labelEmbedding4 ∘ raw38860step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38860step1 raw38860step1Labels raw38860step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1997 node1997Labels := by rfl

def raw38861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38861Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38861step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38861step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38861 raw38861Labels = mixedMoment B node2000 node2000Labels := by
  calc
    mixedMoment B raw38861 raw38861Labels = mixedMoment B raw38861step0 raw38861step0Labels := by
      have ha : raw38861step0 = raw38861 := by apply Matrix.ext; unfold raw38861step0 raw38861; decide +kernel
      have hl : raw38861Labels = labelEmbedding2 ∘ raw38861step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38861 raw38861Labels raw38861step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2000 node2000Labels := by rfl

def raw38862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38862Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38862step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw38862step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38862step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38862step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38862step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38862step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38862 raw38862Labels = mixedMoment B node2000 node2000Labels := by
  calc
    mixedMoment B raw38862 raw38862Labels = mixedMoment B raw38862step0 raw38862step0Labels := by
      have ha : raw38862step0 = (fun i j => raw38862 (permutation177 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38862step0 raw38862; decide +kernel
      have hl : raw38862step0Labels = raw38862Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38862 raw38862Labels permutation177 permutation7
    mixedMoment B raw38862step0 raw38862step0Labels = mixedMoment B raw38862step1 raw38862step1Labels := by
      have ha : raw38862step1 = -raw38862step0 := by apply Matrix.ext; change ∀ i j, raw38862step1 i j = -(raw38862step0 i j); unfold raw38862step1 raw38862step0; decide +kernel
      have hl : raw38862step1Labels = raw38862step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38862step1 raw38862step1Labels = mixedMoment B raw38862step2 raw38862step2Labels := by
      have ha : raw38862step2 = raw38862step1 := by apply Matrix.ext; unfold raw38862step2 raw38862step1; decide +kernel
      have hl : raw38862step1Labels = labelEmbedding4 ∘ raw38862step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38862step1 raw38862step1Labels raw38862step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2000 node2000Labels := by rfl

def raw38863 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw38863Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw38863step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38863 raw38863Labels = mixedMoment B node2003 node2003Labels := by
  calc
    mixedMoment B raw38863 raw38863Labels = mixedMoment B raw38863step0 raw38863step0Labels := by
      have ha : raw38863step0 = raw38863 := by apply Matrix.ext; unfold raw38863step0 raw38863; decide +kernel
      have hl : raw38863Labels = labelEmbedding2 ∘ raw38863step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38863 raw38863Labels raw38863step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2003 node2003Labels := by rfl

def raw38864 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw38864Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![-2, -1, 3]]
def raw38864step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38864step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw38864step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38864step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw38864step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38864 raw38864Labels = mixedMoment B node2006 node2006Labels := by
  calc
    mixedMoment B raw38864 raw38864Labels = mixedMoment B raw38864step0 raw38864step0Labels := by
      have ha : raw38864step0 = (fun i j => raw38864 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38864step0 raw38864; decide +kernel
      have hl : raw38864step0Labels = raw38864Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38864 raw38864Labels permutation38 permutation7
    mixedMoment B raw38864step0 raw38864step0Labels = mixedMoment B raw38864step1 raw38864step1Labels := by
      have ha : raw38864step1 = -raw38864step0 := by apply Matrix.ext; change ∀ i j, raw38864step1 i j = -(raw38864step0 i j); unfold raw38864step1 raw38864step0; decide +kernel
      have hl : raw38864step1Labels = raw38864step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38864step1 raw38864step1Labels = mixedMoment B raw38864step2 raw38864step2Labels := by
      have ha : raw38864step2 = raw38864step1 := by apply Matrix.ext; unfold raw38864step2 raw38864step1; decide +kernel
      have hl : raw38864step1Labels = labelEmbedding4 ∘ raw38864step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38864step1 raw38864step1Labels raw38864step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2006 node2006Labels := by rfl

def raw38865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw38865Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw38865step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38865 raw38865Labels = mixedMoment B node2016 node2016Labels := by
  calc
    mixedMoment B raw38865 raw38865Labels = mixedMoment B raw38865step0 raw38865step0Labels := by
      have ha : raw38865step0 = raw38865 := by apply Matrix.ext; unfold raw38865step0 raw38865; decide +kernel
      have hl : raw38865Labels = labelEmbedding2 ∘ raw38865step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38865 raw38865Labels raw38865step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2016 node2016Labels := by rfl

def raw38866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw38866Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38866step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw38866step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38866step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38866step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38866step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38866step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38866 raw38866Labels = mixedMoment B node2075 node2075Labels := by
  calc
    mixedMoment B raw38866 raw38866Labels = mixedMoment B raw38866step0 raw38866step0Labels := by
      have ha : raw38866step0 = (fun i j => raw38866 (permutation200 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38866step0 raw38866; decide +kernel
      have hl : raw38866step0Labels = raw38866Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38866 raw38866Labels permutation200 permutation7
    mixedMoment B raw38866step0 raw38866step0Labels = mixedMoment B raw38866step1 raw38866step1Labels := by
      have ha : raw38866step1 = -raw38866step0 := by apply Matrix.ext; change ∀ i j, raw38866step1 i j = -(raw38866step0 i j); unfold raw38866step1 raw38866step0; decide +kernel
      have hl : raw38866step1Labels = raw38866step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38866step1 raw38866step1Labels = mixedMoment B raw38866step2 raw38866step2Labels := by
      have ha : raw38866step2 = raw38866step1 := by apply Matrix.ext; unfold raw38866step2 raw38866step1; decide +kernel
      have hl : raw38866step1Labels = labelEmbedding4 ∘ raw38866step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38866step1 raw38866step1Labels raw38866step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2075 node2075Labels := by rfl

def raw38867 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw38867Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw38867step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38867 raw38867Labels = mixedMoment B node2018 node2018Labels := by
  calc
    mixedMoment B raw38867 raw38867Labels = mixedMoment B raw38867step0 raw38867step0Labels := by
      have ha : raw38867step0 = raw38867 := by apply Matrix.ext; unfold raw38867step0 raw38867; decide +kernel
      have hl : raw38867Labels = labelEmbedding2 ∘ raw38867step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38867 raw38867Labels raw38867step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2018 node2018Labels := by rfl

def raw38868 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw38868Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw38868step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38868step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw38868step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38868 raw38868Labels = mixedMoment B node2018 node2018Labels := by
  calc
    mixedMoment B raw38868 raw38868Labels = mixedMoment B raw38868step0 raw38868step0Labels := by
      have ha : raw38868step0 = (fun i j => raw38868 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38868step0 raw38868; decide +kernel
      have hl : raw38868step0Labels = raw38868Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38868 raw38868Labels permutation143 permutation7
    mixedMoment B raw38868step0 raw38868step0Labels = mixedMoment B raw38868step1 raw38868step1Labels := by
      have ha : raw38868step1 = raw38868step0 := by apply Matrix.ext; unfold raw38868step1 raw38868step0; decide +kernel
      have hl : raw38868step0Labels = labelEmbedding4 ∘ raw38868step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38868step0 raw38868step0Labels raw38868step1Labels labelEmbedding4 hl
    _ = mixedMoment B node2018 node2018Labels := by rfl

def raw38869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw38869Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw38869step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38869 raw38869Labels = mixedMoment B node2019 node2019Labels := by
  calc
    mixedMoment B raw38869 raw38869Labels = mixedMoment B raw38869step0 raw38869step0Labels := by
      have ha : raw38869step0 = raw38869 := by apply Matrix.ext; unfold raw38869step0 raw38869; decide +kernel
      have hl : raw38869Labels = labelEmbedding2 ∘ raw38869step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38869 raw38869Labels raw38869step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2019 node2019Labels := by rfl

def raw38870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw38870Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw38870step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38870step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw38870step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38870step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw38870step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38870 raw38870Labels = mixedMoment B node2190 node2190Labels := by
  calc
    mixedMoment B raw38870 raw38870Labels = mixedMoment B raw38870step0 raw38870step0Labels := by
      have ha : raw38870step0 = (fun i j => raw38870 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38870step0 raw38870; decide +kernel
      have hl : raw38870step0Labels = raw38870Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38870 raw38870Labels permutation160 permutation7
    mixedMoment B raw38870step0 raw38870step0Labels = mixedMoment B raw38870step1 raw38870step1Labels := by
      have ha : raw38870step1 = -raw38870step0 := by apply Matrix.ext; change ∀ i j, raw38870step1 i j = -(raw38870step0 i j); unfold raw38870step1 raw38870step0; decide +kernel
      have hl : raw38870step1Labels = raw38870step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38870step1 raw38870step1Labels = mixedMoment B raw38870step2 raw38870step2Labels := by
      have ha : raw38870step2 = raw38870step1 := by apply Matrix.ext; unfold raw38870step2 raw38870step1; decide +kernel
      have hl : raw38870step1Labels = labelEmbedding4 ∘ raw38870step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38870step1 raw38870step1Labels raw38870step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2190 node2190Labels := by rfl

def raw38871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw38871Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw38871step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38871 raw38871Labels = mixedMoment B node2020 node2020Labels := by
  calc
    mixedMoment B raw38871 raw38871Labels = mixedMoment B raw38871step0 raw38871step0Labels := by
      have ha : raw38871step0 = raw38871 := by apply Matrix.ext; unfold raw38871step0 raw38871; decide +kernel
      have hl : raw38871Labels = labelEmbedding2 ∘ raw38871step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38871 raw38871Labels raw38871step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2020 node2020Labels := by rfl

def raw38872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw38872Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw38872step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38872step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw38872step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38872step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw38872step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38872 raw38872Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw38872 raw38872Labels = mixedMoment B raw38872step0 raw38872step0Labels := by
      have ha : raw38872step0 = (fun i j => raw38872 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38872step0 raw38872; decide +kernel
      have hl : raw38872step0Labels = raw38872Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38872 raw38872Labels permutation158 permutation7
    mixedMoment B raw38872step0 raw38872step0Labels = mixedMoment B raw38872step1 raw38872step1Labels := by
      have ha : raw38872step1 = -raw38872step0 := by apply Matrix.ext; change ∀ i j, raw38872step1 i j = -(raw38872step0 i j); unfold raw38872step1 raw38872step0; decide +kernel
      have hl : raw38872step1Labels = raw38872step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38872step1 raw38872step1Labels = mixedMoment B raw38872step2 raw38872step2Labels := by
      have ha : raw38872step2 = raw38872step1 := by apply Matrix.ext; unfold raw38872step2 raw38872step1; decide +kernel
      have hl : raw38872step1Labels = labelEmbedding4 ∘ raw38872step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38872step1 raw38872step1Labels raw38872step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2202 node2202Labels := by rfl

def raw38873 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw38873Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw38873step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38873 raw38873Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw38873 raw38873Labels = mixedMoment B raw38873step0 raw38873step0Labels := by
      have ha : raw38873step0 = raw38873 := by apply Matrix.ext; unfold raw38873step0 raw38873; decide +kernel
      have hl : raw38873Labels = labelEmbedding2 ∘ raw38873step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38873 raw38873Labels raw38873step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2022 node2022Labels := by rfl

def raw38874 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw38874Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw38874step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38874step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw38874step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38874step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw38874step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38874 raw38874Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw38874 raw38874Labels = mixedMoment B raw38874step0 raw38874step0Labels := by
      have ha : raw38874step0 = (fun i j => raw38874 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38874step0 raw38874; decide +kernel
      have hl : raw38874step0Labels = raw38874Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38874 raw38874Labels permutation34 permutation7
    mixedMoment B raw38874step0 raw38874step0Labels = mixedMoment B raw38874step1 raw38874step1Labels := by
      have ha : raw38874step1 = -raw38874step0 := by apply Matrix.ext; change ∀ i j, raw38874step1 i j = -(raw38874step0 i j); unfold raw38874step1 raw38874step0; decide +kernel
      have hl : raw38874step1Labels = raw38874step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38874step1 raw38874step1Labels = mixedMoment B raw38874step2 raw38874step2Labels := by
      have ha : raw38874step2 = raw38874step1 := by apply Matrix.ext; unfold raw38874step2 raw38874step1; decide +kernel
      have hl : raw38874step1Labels = labelEmbedding4 ∘ raw38874step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38874step1 raw38874step1Labels raw38874step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

def raw38875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38875Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38875step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38875 raw38875Labels = mixedMoment B node2023 node2023Labels := by
  calc
    mixedMoment B raw38875 raw38875Labels = mixedMoment B raw38875step0 raw38875step0Labels := by
      have ha : raw38875step0 = raw38875 := by apply Matrix.ext; unfold raw38875step0 raw38875; decide +kernel
      have hl : raw38875Labels = labelEmbedding2 ∘ raw38875step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38875 raw38875Labels raw38875step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2023 node2023Labels := by rfl

def raw38876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38876Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw38876step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38876step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw38876step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38876step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw38876step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38876 raw38876Labels = mixedMoment B node2214 node2214Labels := by
  calc
    mixedMoment B raw38876 raw38876Labels = mixedMoment B raw38876step0 raw38876step0Labels := by
      have ha : raw38876step0 = (fun i j => raw38876 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38876step0 raw38876; decide +kernel
      have hl : raw38876step0Labels = raw38876Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38876 raw38876Labels permutation170 permutation7
    mixedMoment B raw38876step0 raw38876step0Labels = mixedMoment B raw38876step1 raw38876step1Labels := by
      have ha : raw38876step1 = -raw38876step0 := by apply Matrix.ext; change ∀ i j, raw38876step1 i j = -(raw38876step0 i j); unfold raw38876step1 raw38876step0; decide +kernel
      have hl : raw38876step1Labels = raw38876step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38876step1 raw38876step1Labels = mixedMoment B raw38876step2 raw38876step2Labels := by
      have ha : raw38876step2 = raw38876step1 := by apply Matrix.ext; unfold raw38876step2 raw38876step1; decide +kernel
      have hl : raw38876step1Labels = labelEmbedding4 ∘ raw38876step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38876step1 raw38876step1Labels raw38876step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2214 node2214Labels := by rfl

def raw38877 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38877Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38877step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38877 raw38877Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw38877 raw38877Labels = mixedMoment B raw38877step0 raw38877step0Labels := by
      have ha : raw38877step0 = raw38877 := by apply Matrix.ext; unfold raw38877step0 raw38877; decide +kernel
      have hl : raw38877Labels = labelEmbedding2 ∘ raw38877step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38877 raw38877Labels raw38877step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2025 node2025Labels := by rfl

def raw38878 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38878Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw38878step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw38878step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38878step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw38878step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38878 raw38878Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw38878 raw38878Labels = mixedMoment B raw38878step0 raw38878step0Labels := by
      have ha : raw38878step0 = (fun i j => raw38878 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38878step0 raw38878; decide +kernel
      have hl : raw38878step0Labels = raw38878Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38878 raw38878Labels permutation32 permutation7
    mixedMoment B raw38878step0 raw38878step0Labels = mixedMoment B raw38878step1 raw38878step1Labels := by
      have ha : raw38878step1 = -raw38878step0 := by apply Matrix.ext; change ∀ i j, raw38878step1 i j = -(raw38878step0 i j); unfold raw38878step1 raw38878step0; decide +kernel
      have hl : raw38878step1Labels = raw38878step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38878step1 raw38878step1Labels = mixedMoment B raw38878step2 raw38878step2Labels := by
      have ha : raw38878step2 = raw38878step1 := by apply Matrix.ext; unfold raw38878step2 raw38878step1; decide +kernel
      have hl : raw38878step1Labels = labelEmbedding4 ∘ raw38878step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38878step1 raw38878step1Labels raw38878step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

def raw38879 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38879Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38879step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38879 raw38879Labels = mixedMoment B node2028 node2028Labels := by
  calc
    mixedMoment B raw38879 raw38879Labels = mixedMoment B raw38879step0 raw38879step0Labels := by
      have ha : raw38879step0 = raw38879 := by apply Matrix.ext; unfold raw38879step0 raw38879; decide +kernel
      have hl : raw38879Labels = labelEmbedding2 ∘ raw38879step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38879 raw38879Labels raw38879step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2028 node2028Labels := by rfl

def raw38880 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38880Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw38880step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw38880step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38880step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw38880step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38880 raw38880Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw38880 raw38880Labels = mixedMoment B raw38880step0 raw38880step0Labels := by
      have ha : raw38880step0 = (fun i j => raw38880 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38880step0 raw38880; decide +kernel
      have hl : raw38880step0Labels = raw38880Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38880 raw38880Labels permutation34 permutation7
    mixedMoment B raw38880step0 raw38880step0Labels = mixedMoment B raw38880step1 raw38880step1Labels := by
      have ha : raw38880step1 = -raw38880step0 := by apply Matrix.ext; change ∀ i j, raw38880step1 i j = -(raw38880step0 i j); unfold raw38880step1 raw38880step0; decide +kernel
      have hl : raw38880step1Labels = raw38880step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38880step1 raw38880step1Labels = mixedMoment B raw38880step2 raw38880step2Labels := by
      have ha : raw38880step2 = raw38880step1 := by apply Matrix.ext; unfold raw38880step2 raw38880step1; decide +kernel
      have hl : raw38880step1Labels = labelEmbedding4 ∘ raw38880step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38880step1 raw38880step1Labels raw38880step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2215 node2215Labels := by rfl

def raw38881 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38881Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38881step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38881 raw38881Labels = mixedMoment B node2029 node2029Labels := by
  calc
    mixedMoment B raw38881 raw38881Labels = mixedMoment B raw38881step0 raw38881step0Labels := by
      have ha : raw38881step0 = raw38881 := by apply Matrix.ext; unfold raw38881step0 raw38881; decide +kernel
      have hl : raw38881Labels = labelEmbedding2 ∘ raw38881step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38881 raw38881Labels raw38881step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2029 node2029Labels := by rfl

def raw38882 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38882Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw38882step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw38882step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38882step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw38882step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38882 raw38882Labels = mixedMoment B node2225 node2225Labels := by
  calc
    mixedMoment B raw38882 raw38882Labels = mixedMoment B raw38882step0 raw38882step0Labels := by
      have ha : raw38882step0 = (fun i j => raw38882 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38882step0 raw38882; decide +kernel
      have hl : raw38882step0Labels = raw38882Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38882 raw38882Labels permutation32 permutation7
    mixedMoment B raw38882step0 raw38882step0Labels = mixedMoment B raw38882step1 raw38882step1Labels := by
      have ha : raw38882step1 = -raw38882step0 := by apply Matrix.ext; change ∀ i j, raw38882step1 i j = -(raw38882step0 i j); unfold raw38882step1 raw38882step0; decide +kernel
      have hl : raw38882step1Labels = raw38882step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38882step1 raw38882step1Labels = mixedMoment B raw38882step2 raw38882step2Labels := by
      have ha : raw38882step2 = raw38882step1 := by apply Matrix.ext; unfold raw38882step2 raw38882step1; decide +kernel
      have hl : raw38882step1Labels = labelEmbedding4 ∘ raw38882step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38882step1 raw38882step1Labels raw38882step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2225 node2225Labels := by rfl

def raw38883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38883Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38883step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38883step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38883 raw38883Labels = mixedMoment B node2046 node2046Labels := by
  calc
    mixedMoment B raw38883 raw38883Labels = mixedMoment B raw38883step0 raw38883step0Labels := by
      have ha : raw38883step0 = raw38883 := by apply Matrix.ext; unfold raw38883step0 raw38883; decide +kernel
      have hl : raw38883Labels = labelEmbedding2 ∘ raw38883step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38883 raw38883Labels raw38883step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2046 node2046Labels := by rfl

def raw38884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38884Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw38884step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38884step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38884step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38884step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38884step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38884 raw38884Labels = mixedMoment B node2077 node2077Labels := by
  calc
    mixedMoment B raw38884 raw38884Labels = mixedMoment B raw38884step0 raw38884step0Labels := by
      have ha : raw38884step0 = (fun i j => raw38884 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38884step0 raw38884; decide +kernel
      have hl : raw38884step0Labels = raw38884Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38884 raw38884Labels permutation176 permutation7
    mixedMoment B raw38884step0 raw38884step0Labels = mixedMoment B raw38884step1 raw38884step1Labels := by
      have ha : raw38884step1 = -raw38884step0 := by apply Matrix.ext; change ∀ i j, raw38884step1 i j = -(raw38884step0 i j); unfold raw38884step1 raw38884step0; decide +kernel
      have hl : raw38884step1Labels = raw38884step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38884step1 raw38884step1Labels = mixedMoment B raw38884step2 raw38884step2Labels := by
      have ha : raw38884step2 = raw38884step1 := by apply Matrix.ext; unfold raw38884step2 raw38884step1; decide +kernel
      have hl : raw38884step1Labels = labelEmbedding4 ∘ raw38884step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38884step1 raw38884step1Labels raw38884step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2077 node2077Labels := by rfl

def raw38885 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw38885Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw38885step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38885 raw38885Labels = mixedMoment B node2047 node2047Labels := by
  calc
    mixedMoment B raw38885 raw38885Labels = mixedMoment B raw38885step0 raw38885step0Labels := by
      have ha : raw38885step0 = raw38885 := by apply Matrix.ext; unfold raw38885step0 raw38885; decide +kernel
      have hl : raw38885Labels = labelEmbedding2 ∘ raw38885step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38885 raw38885Labels raw38885step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2047 node2047Labels := by rfl

def raw38886 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw38886Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw38886step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38886step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw38886step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38886step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw38886step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38886 raw38886Labels = mixedMoment B node2079 node2079Labels := by
  calc
    mixedMoment B raw38886 raw38886Labels = mixedMoment B raw38886step0 raw38886step0Labels := by
      have ha : raw38886step0 = (fun i j => raw38886 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38886step0 raw38886; decide +kernel
      have hl : raw38886step0Labels = raw38886Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38886 raw38886Labels permutation38 permutation7
    mixedMoment B raw38886step0 raw38886step0Labels = mixedMoment B raw38886step1 raw38886step1Labels := by
      have ha : raw38886step1 = -raw38886step0 := by apply Matrix.ext; change ∀ i j, raw38886step1 i j = -(raw38886step0 i j); unfold raw38886step1 raw38886step0; decide +kernel
      have hl : raw38886step1Labels = raw38886step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38886step1 raw38886step1Labels = mixedMoment B raw38886step2 raw38886step2Labels := by
      have ha : raw38886step2 = raw38886step1 := by apply Matrix.ext; unfold raw38886step2 raw38886step1; decide +kernel
      have hl : raw38886step1Labels = labelEmbedding4 ∘ raw38886step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38886step1 raw38886step1Labels raw38886step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2079 node2079Labels := by rfl

def raw38887 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw38887Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw38887step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38887 raw38887Labels = mixedMoment B node2048 node2048Labels := by
  calc
    mixedMoment B raw38887 raw38887Labels = mixedMoment B raw38887step0 raw38887step0Labels := by
      have ha : raw38887step0 = raw38887 := by apply Matrix.ext; unfold raw38887step0 raw38887; decide +kernel
      have hl : raw38887Labels = labelEmbedding2 ∘ raw38887step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38887 raw38887Labels raw38887step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2048 node2048Labels := by rfl

def raw38888 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw38888Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw38888step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw38888step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38888step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw38888step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38888 raw38888Labels = mixedMoment B node2082 node2082Labels := by
  calc
    mixedMoment B raw38888 raw38888Labels = mixedMoment B raw38888step0 raw38888step0Labels := by
      have ha : raw38888step0 = (fun i j => raw38888 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38888step0 raw38888; decide +kernel
      have hl : raw38888step0Labels = raw38888Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38888 raw38888Labels permutation38 permutation7
    mixedMoment B raw38888step0 raw38888step0Labels = mixedMoment B raw38888step1 raw38888step1Labels := by
      have ha : raw38888step1 = -raw38888step0 := by apply Matrix.ext; change ∀ i j, raw38888step1 i j = -(raw38888step0 i j); unfold raw38888step1 raw38888step0; decide +kernel
      have hl : raw38888step1Labels = raw38888step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38888step1 raw38888step1Labels = mixedMoment B raw38888step2 raw38888step2Labels := by
      have ha : raw38888step2 = raw38888step1 := by apply Matrix.ext; unfold raw38888step2 raw38888step1; decide +kernel
      have hl : raw38888step1Labels = labelEmbedding4 ∘ raw38888step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38888step1 raw38888step1Labels raw38888step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2082 node2082Labels := by rfl

def raw38889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw38889Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw38889step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38889 raw38889Labels = mixedMoment B node2051 node2051Labels := by
  calc
    mixedMoment B raw38889 raw38889Labels = mixedMoment B raw38889step0 raw38889step0Labels := by
      have ha : raw38889step0 = raw38889 := by apply Matrix.ext; unfold raw38889step0 raw38889; decide +kernel
      have hl : raw38889Labels = labelEmbedding2 ∘ raw38889step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38889 raw38889Labels raw38889step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2051 node2051Labels := by rfl

def raw38890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw38890Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw38890step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38890step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38890step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38890step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38890 raw38890Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw38890 raw38890Labels = mixedMoment B raw38890step0 raw38890step0Labels := by
      have ha : raw38890step0 = (fun i j => raw38890 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38890step0 raw38890; decide +kernel
      have hl : raw38890step0Labels = raw38890Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38890 raw38890Labels permutation152 permutation7
    mixedMoment B raw38890step0 raw38890step0Labels = mixedMoment B raw38890step1 raw38890step1Labels := by
      have ha : raw38890step1 = -raw38890step0 := by apply Matrix.ext; change ∀ i j, raw38890step1 i j = -(raw38890step0 i j); unfold raw38890step1 raw38890step0; decide +kernel
      have hl : raw38890step1Labels = raw38890step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38890step1 raw38890step1Labels = mixedMoment B raw38890step2 raw38890step2Labels := by
      have ha : raw38890step2 = raw38890step1 := by apply Matrix.ext; unfold raw38890step2 raw38890step1; decide +kernel
      have hl : raw38890step1Labels = labelEmbedding4 ∘ raw38890step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38890step1 raw38890step1Labels raw38890step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2191 node2191Labels := by rfl

def raw38891 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw38891Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw38891step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38891 raw38891Labels = mixedMoment B node2052 node2052Labels := by
  calc
    mixedMoment B raw38891 raw38891Labels = mixedMoment B raw38891step0 raw38891step0Labels := by
      have ha : raw38891step0 = raw38891 := by apply Matrix.ext; unfold raw38891step0 raw38891; decide +kernel
      have hl : raw38891Labels = labelEmbedding2 ∘ raw38891step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38891 raw38891Labels raw38891step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2052 node2052Labels := by rfl

def raw38892 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw38892Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw38892step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw38892step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38892step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw38892step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38892 raw38892Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw38892 raw38892Labels = mixedMoment B raw38892step0 raw38892step0Labels := by
      have ha : raw38892step0 = (fun i j => raw38892 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38892step0 raw38892; decide +kernel
      have hl : raw38892step0Labels = raw38892Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38892 raw38892Labels permutation32 permutation7
    mixedMoment B raw38892step0 raw38892step0Labels = mixedMoment B raw38892step1 raw38892step1Labels := by
      have ha : raw38892step1 = -raw38892step0 := by apply Matrix.ext; change ∀ i j, raw38892step1 i j = -(raw38892step0 i j); unfold raw38892step1 raw38892step0; decide +kernel
      have hl : raw38892step1Labels = raw38892step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38892step1 raw38892step1Labels = mixedMoment B raw38892step2 raw38892step2Labels := by
      have ha : raw38892step2 = raw38892step1 := by apply Matrix.ext; unfold raw38892step2 raw38892step1; decide +kernel
      have hl : raw38892step1Labels = labelEmbedding4 ∘ raw38892step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38892step1 raw38892step1Labels raw38892step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2193 node2193Labels := by rfl

def raw38893 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw38893Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw38893step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38893 raw38893Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw38893 raw38893Labels = mixedMoment B raw38893step0 raw38893step0Labels := by
      have ha : raw38893step0 = raw38893 := by apply Matrix.ext; unfold raw38893step0 raw38893; decide +kernel
      have hl : raw38893Labels = labelEmbedding2 ∘ raw38893step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38893 raw38893Labels raw38893step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2054 node2054Labels := by rfl

def raw38894 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw38894Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw38894step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38894step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38894step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38894step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38894 raw38894Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw38894 raw38894Labels = mixedMoment B raw38894step0 raw38894step0Labels := by
      have ha : raw38894step0 = (fun i j => raw38894 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38894step0 raw38894; decide +kernel
      have hl : raw38894step0Labels = raw38894Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38894 raw38894Labels permutation33 permutation7
    mixedMoment B raw38894step0 raw38894step0Labels = mixedMoment B raw38894step1 raw38894step1Labels := by
      have ha : raw38894step1 = -raw38894step0 := by apply Matrix.ext; change ∀ i j, raw38894step1 i j = -(raw38894step0 i j); unfold raw38894step1 raw38894step0; decide +kernel
      have hl : raw38894step1Labels = raw38894step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38894step1 raw38894step1Labels = mixedMoment B raw38894step2 raw38894step2Labels := by
      have ha : raw38894step2 = raw38894step1 := by apply Matrix.ext; unfold raw38894step2 raw38894step1; decide +kernel
      have hl : raw38894step1Labels = labelEmbedding4 ∘ raw38894step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38894step1 raw38894step1Labels raw38894step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2206 node2206Labels := by rfl

def raw38895 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38895Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38895step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38895 raw38895Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw38895 raw38895Labels = mixedMoment B raw38895step0 raw38895step0Labels := by
      have ha : raw38895step0 = raw38895 := by apply Matrix.ext; unfold raw38895step0 raw38895; decide +kernel
      have hl : raw38895Labels = labelEmbedding2 ∘ raw38895step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38895 raw38895Labels raw38895step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2058 node2058Labels := by rfl

def raw38896 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38896Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw38896step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw38896step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38896step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw38896step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38896 raw38896Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw38896 raw38896Labels = mixedMoment B raw38896step0 raw38896step0Labels := by
      have ha : raw38896step0 = (fun i j => raw38896 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38896step0 raw38896; decide +kernel
      have hl : raw38896step0Labels = raw38896Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38896 raw38896Labels permutation36 permutation7
    mixedMoment B raw38896step0 raw38896step0Labels = mixedMoment B raw38896step1 raw38896step1Labels := by
      have ha : raw38896step1 = -raw38896step0 := by apply Matrix.ext; change ∀ i j, raw38896step1 i j = -(raw38896step0 i j); unfold raw38896step1 raw38896step0; decide +kernel
      have hl : raw38896step1Labels = raw38896step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38896step1 raw38896step1Labels = mixedMoment B raw38896step2 raw38896step2Labels := by
      have ha : raw38896step2 = raw38896step1 := by apply Matrix.ext; unfold raw38896step2 raw38896step1; decide +kernel
      have hl : raw38896step1Labels = labelEmbedding4 ∘ raw38896step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38896step1 raw38896step1Labels raw38896step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2216 node2216Labels := by rfl

def raw38897 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw38897Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38897step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw38897step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38897 raw38897Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw38897 raw38897Labels = mixedMoment B raw38897step0 raw38897step0Labels := by
      have ha : raw38897step0 = raw38897 := by apply Matrix.ext; unfold raw38897step0 raw38897; decide +kernel
      have hl : raw38897Labels = labelEmbedding2 ∘ raw38897step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38897 raw38897Labels raw38897step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2062 node2062Labels := by rfl

def raw38898 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw38898Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38898step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw38898step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38898step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw38898step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38898step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw38898step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38898 raw38898Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw38898 raw38898Labels = mixedMoment B raw38898step0 raw38898step0Labels := by
      have ha : raw38898step0 = (fun i j => raw38898 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38898step0 raw38898; decide +kernel
      have hl : raw38898step0Labels = raw38898Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38898 raw38898Labels permutation9 permutation7
    mixedMoment B raw38898step0 raw38898step0Labels = mixedMoment B raw38898step1 raw38898step1Labels := by
      have ha : raw38898step1 = -raw38898step0 := by apply Matrix.ext; change ∀ i j, raw38898step1 i j = -(raw38898step0 i j); unfold raw38898step1 raw38898step0; decide +kernel
      have hl : raw38898step1Labels = raw38898step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38898step1 raw38898step1Labels = mixedMoment B raw38898step2 raw38898step2Labels := by
      have ha : raw38898step2 = raw38898step1 := by apply Matrix.ext; unfold raw38898step2 raw38898step1; decide +kernel
      have hl : raw38898step1Labels = labelEmbedding4 ∘ raw38898step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38898step1 raw38898step1Labels raw38898step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2230 node2230Labels := by rfl

def raw38899 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw38899Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38899step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw38899step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38899 raw38899Labels = mixedMoment B node2065 node2065Labels := by
  calc
    mixedMoment B raw38899 raw38899Labels = mixedMoment B raw38899step0 raw38899step0Labels := by
      have ha : raw38899step0 = raw38899 := by apply Matrix.ext; unfold raw38899step0 raw38899; decide +kernel
      have hl : raw38899Labels = labelEmbedding2 ∘ raw38899step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38899 raw38899Labels raw38899step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2065 node2065Labels := by rfl

def raw38900 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw38900Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38900step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw38900step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38900step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw38900step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38900step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw38900step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38900 raw38900Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw38900 raw38900Labels = mixedMoment B raw38900step0 raw38900step0Labels := by
      have ha : raw38900step0 = (fun i j => raw38900 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38900step0 raw38900; decide +kernel
      have hl : raw38900step0Labels = raw38900Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38900 raw38900Labels permutation8 permutation7
    mixedMoment B raw38900step0 raw38900step0Labels = mixedMoment B raw38900step1 raw38900step1Labels := by
      have ha : raw38900step1 = -raw38900step0 := by apply Matrix.ext; change ∀ i j, raw38900step1 i j = -(raw38900step0 i j); unfold raw38900step1 raw38900step0; decide +kernel
      have hl : raw38900step1Labels = raw38900step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38900step1 raw38900step1Labels = mixedMoment B raw38900step2 raw38900step2Labels := by
      have ha : raw38900step2 = raw38900step1 := by apply Matrix.ext; unfold raw38900step2 raw38900step1; decide +kernel
      have hl : raw38900step1Labels = labelEmbedding4 ∘ raw38900step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38900step1 raw38900step1Labels raw38900step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2218 node2218Labels := by rfl

def raw38901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38901Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38901step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38901 raw38901Labels = mixedMoment B node2100 node2100Labels := by
  calc
    mixedMoment B raw38901 raw38901Labels = mixedMoment B raw38901step0 raw38901step0Labels := by
      have ha : raw38901step0 = raw38901 := by apply Matrix.ext; unfold raw38901step0 raw38901; decide +kernel
      have hl : raw38901Labels = labelEmbedding2 ∘ raw38901step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38901 raw38901Labels raw38901step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2100 node2100Labels := by rfl

def raw38902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38902Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38902step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw38902step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38902step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38902step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38902step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38902step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38902 raw38902Labels = mixedMoment B node2100 node2100Labels := by
  calc
    mixedMoment B raw38902 raw38902Labels = mixedMoment B raw38902step0 raw38902step0Labels := by
      have ha : raw38902step0 = (fun i j => raw38902 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38902step0 raw38902; decide +kernel
      have hl : raw38902step0Labels = raw38902Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38902 raw38902Labels permutation176 permutation7
    mixedMoment B raw38902step0 raw38902step0Labels = mixedMoment B raw38902step1 raw38902step1Labels := by
      have ha : raw38902step1 = -raw38902step0 := by apply Matrix.ext; change ∀ i j, raw38902step1 i j = -(raw38902step0 i j); unfold raw38902step1 raw38902step0; decide +kernel
      have hl : raw38902step1Labels = raw38902step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38902step1 raw38902step1Labels = mixedMoment B raw38902step2 raw38902step2Labels := by
      have ha : raw38902step2 = raw38902step1 := by apply Matrix.ext; unfold raw38902step2 raw38902step1; decide +kernel
      have hl : raw38902step1Labels = labelEmbedding4 ∘ raw38902step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38902step1 raw38902step1Labels raw38902step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2100 node2100Labels := by rfl

def raw38903 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw38903Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw38903step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38903 raw38903Labels = mixedMoment B node2101 node2101Labels := by
  calc
    mixedMoment B raw38903 raw38903Labels = mixedMoment B raw38903step0 raw38903step0Labels := by
      have ha : raw38903step0 = raw38903 := by apply Matrix.ext; unfold raw38903step0 raw38903; decide +kernel
      have hl : raw38903Labels = labelEmbedding2 ∘ raw38903step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38903 raw38903Labels raw38903step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2101 node2101Labels := by rfl

def raw38904 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw38904Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw38904step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38904step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw38904step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38904step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw38904step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38904 raw38904Labels = mixedMoment B node2101 node2101Labels := by
  calc
    mixedMoment B raw38904 raw38904Labels = mixedMoment B raw38904step0 raw38904step0Labels := by
      have ha : raw38904step0 = (fun i j => raw38904 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38904step0 raw38904; decide +kernel
      have hl : raw38904step0Labels = raw38904Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38904 raw38904Labels permutation38 permutation7
    mixedMoment B raw38904step0 raw38904step0Labels = mixedMoment B raw38904step1 raw38904step1Labels := by
      have ha : raw38904step1 = -raw38904step0 := by apply Matrix.ext; change ∀ i j, raw38904step1 i j = -(raw38904step0 i j); unfold raw38904step1 raw38904step0; decide +kernel
      have hl : raw38904step1Labels = raw38904step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38904step1 raw38904step1Labels = mixedMoment B raw38904step2 raw38904step2Labels := by
      have ha : raw38904step2 = raw38904step1 := by apply Matrix.ext; unfold raw38904step2 raw38904step1; decide +kernel
      have hl : raw38904step1Labels = labelEmbedding4 ∘ raw38904step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38904step1 raw38904step1Labels raw38904step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2101 node2101Labels := by rfl

def raw38905 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw38905Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38905step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw38905step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38905 raw38905Labels = mixedMoment B node2103 node2103Labels := by
  calc
    mixedMoment B raw38905 raw38905Labels = mixedMoment B raw38905step0 raw38905step0Labels := by
      have ha : raw38905step0 = raw38905 := by apply Matrix.ext; unfold raw38905step0 raw38905; decide +kernel
      have hl : raw38905Labels = labelEmbedding2 ∘ raw38905step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38905 raw38905Labels raw38905step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2103 node2103Labels := by rfl

def raw38906 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw38906Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38906step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw38906step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38906step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw38906step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38906 raw38906Labels = mixedMoment B node2103 node2103Labels := by
  calc
    mixedMoment B raw38906 raw38906Labels = mixedMoment B raw38906step0 raw38906step0Labels := by
      have ha : raw38906step0 = (fun i j => raw38906 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38906step0 raw38906; decide +kernel
      have hl : raw38906step0Labels = raw38906Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38906 raw38906Labels permutation29 permutation7
    mixedMoment B raw38906step0 raw38906step0Labels = mixedMoment B raw38906step1 raw38906step1Labels := by
      have ha : raw38906step1 = raw38906step0 := by apply Matrix.ext; unfold raw38906step1 raw38906step0; decide +kernel
      have hl : raw38906step0Labels = labelEmbedding4 ∘ raw38906step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38906step0 raw38906step0Labels raw38906step1Labels labelEmbedding4 hl
    _ = mixedMoment B node2103 node2103Labels := by rfl

def raw38907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw38907Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38907step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw38907step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38907 raw38907Labels = mixedMoment B node2105 node2105Labels := by
  calc
    mixedMoment B raw38907 raw38907Labels = mixedMoment B raw38907step0 raw38907step0Labels := by
      have ha : raw38907step0 = raw38907 := by apply Matrix.ext; unfold raw38907step0 raw38907; decide +kernel
      have hl : raw38907Labels = labelEmbedding2 ∘ raw38907step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38907 raw38907Labels raw38907step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2105 node2105Labels := by rfl

def raw38908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw38908Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38908step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw38908step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38908step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw38908step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38908step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw38908step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38908 raw38908Labels = mixedMoment B node2241 node2241Labels := by
  calc
    mixedMoment B raw38908 raw38908Labels = mixedMoment B raw38908step0 raw38908step0Labels := by
      have ha : raw38908step0 = (fun i j => raw38908 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38908step0 raw38908; decide +kernel
      have hl : raw38908step0Labels = raw38908Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38908 raw38908Labels permutation182 permutation7
    mixedMoment B raw38908step0 raw38908step0Labels = mixedMoment B raw38908step1 raw38908step1Labels := by
      have ha : raw38908step1 = -raw38908step0 := by apply Matrix.ext; change ∀ i j, raw38908step1 i j = -(raw38908step0 i j); unfold raw38908step1 raw38908step0; decide +kernel
      have hl : raw38908step1Labels = raw38908step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38908step1 raw38908step1Labels = mixedMoment B raw38908step2 raw38908step2Labels := by
      have ha : raw38908step2 = raw38908step1 := by apply Matrix.ext; unfold raw38908step2 raw38908step1; decide +kernel
      have hl : raw38908step1Labels = labelEmbedding4 ∘ raw38908step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38908step1 raw38908step1Labels raw38908step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2241 node2241Labels := by rfl

def raw38909 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw38909Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw38909step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38909 raw38909Labels = mixedMoment B node2106 node2106Labels := by
  calc
    mixedMoment B raw38909 raw38909Labels = mixedMoment B raw38909step0 raw38909step0Labels := by
      have ha : raw38909step0 = raw38909 := by apply Matrix.ext; unfold raw38909step0 raw38909; decide +kernel
      have hl : raw38909Labels = labelEmbedding2 ∘ raw38909step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38909 raw38909Labels raw38909step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2106 node2106Labels := by rfl

def raw38910 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw38910Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw38910step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw38910step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38910step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw38910step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38910 raw38910Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw38910 raw38910Labels = mixedMoment B raw38910step0 raw38910step0Labels := by
      have ha : raw38910step0 = (fun i j => raw38910 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38910step0 raw38910; decide +kernel
      have hl : raw38910step0Labels = raw38910Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38910 raw38910Labels permutation40 permutation7
    mixedMoment B raw38910step0 raw38910step0Labels = mixedMoment B raw38910step1 raw38910step1Labels := by
      have ha : raw38910step1 = -raw38910step0 := by apply Matrix.ext; change ∀ i j, raw38910step1 i j = -(raw38910step0 i j); unfold raw38910step1 raw38910step0; decide +kernel
      have hl : raw38910step1Labels = raw38910step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38910step1 raw38910step1Labels = mixedMoment B raw38910step2 raw38910step2Labels := by
      have ha : raw38910step2 = raw38910step1 := by apply Matrix.ext; unfold raw38910step2 raw38910step1; decide +kernel
      have hl : raw38910step1Labels = labelEmbedding4 ∘ raw38910step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38910step1 raw38910step1Labels raw38910step2Labels labelEmbedding4 hl
    _ = mixedMoment B node2242 node2242Labels := by rfl

def raw38911 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw38911Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw38911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38911 raw38911Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw38911 raw38911Labels = mixedMoment B raw38911step0 raw38911step0Labels := by
      have ha : raw38911step0 = raw38911 := by apply Matrix.ext; unfold raw38911step0 raw38911; decide +kernel
      have hl : raw38911Labels = labelEmbedding2 ∘ raw38911step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38911 raw38911Labels raw38911step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2107 node2107Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
