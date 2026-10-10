import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw1792 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1792Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1792step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1792 raw1792Labels = mixedMoment B node2106 node2106Labels := by
  calc
    mixedMoment B raw1792 raw1792Labels = mixedMoment B raw1792step0 raw1792step0Labels := by
      have ha : raw1792step0 = (fun i j => raw1792 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1792step0 raw1792; decide +kernel
      have hl : raw1792step0Labels = raw1792Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1792 raw1792Labels permutation32 permutation4
    _ = mixedMoment B node2106 node2106Labels := by rfl

def raw1793 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1793Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw1793step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw1793step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1793step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw1793step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1793 raw1793Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw1793 raw1793Labels = mixedMoment B raw1793step0 raw1793step0Labels := by
      have ha : raw1793step0 = (fun i j => raw1793 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1793step0 raw1793; decide +kernel
      have hl : raw1793step0Labels = raw1793Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1793 raw1793Labels permutation40 permutation6
    mixedMoment B raw1793step0 raw1793step0Labels = mixedMoment B raw1793step1 raw1793step1Labels := by
      have ha : raw1793step1 = -raw1793step0 := by apply Matrix.ext; change ∀ i j, raw1793step1 i j = -(raw1793step0 i j); unfold raw1793step1 raw1793step0; decide +kernel
      have hl : raw1793step1Labels = raw1793step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1793step1 raw1793step1Labels = mixedMoment B raw1793step2 raw1793step2Labels := by
      have ha : raw1793step2 = raw1793step1 := by apply Matrix.ext; unfold raw1793step2 raw1793step1; decide +kernel
      have hl : raw1793step1Labels = labelEmbedding1 ∘ raw1793step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1793step1 raw1793step1Labels raw1793step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2242 node2242Labels := by rfl

def raw1794 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw1794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1794step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1794step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1794 raw1794Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw1794 raw1794Labels = mixedMoment B raw1794step0 raw1794step0Labels := by
      have ha : raw1794step0 = (fun i j => raw1794 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1794step0 raw1794; decide +kernel
      have hl : raw1794step0Labels = raw1794Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1794 raw1794Labels permutation32 permutation4
    mixedMoment B raw1794step0 raw1794step0Labels = mixedMoment B raw1794step1 raw1794step1Labels := by
      have ha : raw1794step1 = raw1794step0 := by apply Matrix.ext; unfold raw1794step1 raw1794step0; decide +kernel
      have hl : raw1794step0Labels = labelEmbedding7 ∘ raw1794step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1794step0 raw1794step0Labels raw1794step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw1795 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw1795Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1795step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1795 raw1795Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw1795 raw1795Labels = mixedMoment B raw1795step0 raw1795step0Labels := by
      have ha : raw1795step0 = (fun i j => raw1795 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1795step0 raw1795; decide +kernel
      have hl : raw1795step0Labels = raw1795Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1795 raw1795Labels permutation32 permutation4
    _ = mixedMoment B node2107 node2107Labels := by rfl

def raw1796 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw1796Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw1796step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1796step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw1796step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1796step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw1796step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1796 raw1796Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw1796 raw1796Labels = mixedMoment B raw1796step0 raw1796step0Labels := by
      have ha : raw1796step0 = (fun i j => raw1796 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1796step0 raw1796; decide +kernel
      have hl : raw1796step0Labels = raw1796Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1796 raw1796Labels permutation38 permutation6
    mixedMoment B raw1796step0 raw1796step0Labels = mixedMoment B raw1796step1 raw1796step1Labels := by
      have ha : raw1796step1 = -raw1796step0 := by apply Matrix.ext; change ∀ i j, raw1796step1 i j = -(raw1796step0 i j); unfold raw1796step1 raw1796step0; decide +kernel
      have hl : raw1796step1Labels = raw1796step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1796step1 raw1796step1Labels = mixedMoment B raw1796step2 raw1796step2Labels := by
      have ha : raw1796step2 = raw1796step1 := by apply Matrix.ext; unfold raw1796step2 raw1796step1; decide +kernel
      have hl : raw1796step1Labels = labelEmbedding1 ∘ raw1796step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1796step1 raw1796step1Labels raw1796step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

def raw1797 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1797step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw1797step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1797step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw1797step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1797 raw1797Labels = mixedMoment B node4868 node4868Labels := by
  calc
    mixedMoment B raw1797 raw1797Labels = mixedMoment B raw1797step0 raw1797step0Labels := by
      have ha : raw1797step0 = (fun i j => raw1797 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1797step0 raw1797; decide +kernel
      have hl : raw1797step0Labels = raw1797Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1797 raw1797Labels permutation8 permutation4
    mixedMoment B raw1797step0 raw1797step0Labels = mixedMoment B raw1797step1 raw1797step1Labels := by
      have ha : raw1797step1 = raw1797step0 := by apply Matrix.ext; unfold raw1797step1 raw1797step0; decide +kernel
      have hl : raw1797step0Labels = labelEmbedding7 ∘ raw1797step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1797step0 raw1797step0Labels raw1797step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4868 node4868Labels := by rfl

def raw1798 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1798Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1798step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw1798step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1798 raw1798Labels = mixedMoment B node2109 node2109Labels := by
  calc
    mixedMoment B raw1798 raw1798Labels = mixedMoment B raw1798step0 raw1798step0Labels := by
      have ha : raw1798step0 = (fun i j => raw1798 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1798step0 raw1798; decide +kernel
      have hl : raw1798step0Labels = raw1798Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1798 raw1798Labels permutation8 permutation4
    _ = mixedMoment B node2109 node2109Labels := by rfl

def raw1799 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw1799Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1799step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw1799step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1799step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw1799step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1799step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw1799step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1799 raw1799Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw1799 raw1799Labels = mixedMoment B raw1799step0 raw1799step0Labels := by
      have ha : raw1799step0 = (fun i j => raw1799 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1799step0 raw1799; decide +kernel
      have hl : raw1799step0Labels = raw1799Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1799 raw1799Labels permutation10 permutation6
    mixedMoment B raw1799step0 raw1799step0Labels = mixedMoment B raw1799step1 raw1799step1Labels := by
      have ha : raw1799step1 = -raw1799step0 := by apply Matrix.ext; change ∀ i j, raw1799step1 i j = -(raw1799step0 i j); unfold raw1799step1 raw1799step0; decide +kernel
      have hl : raw1799step1Labels = raw1799step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1799step1 raw1799step1Labels = mixedMoment B raw1799step2 raw1799step2Labels := by
      have ha : raw1799step2 = raw1799step1 := by apply Matrix.ext; unfold raw1799step2 raw1799step1; decide +kernel
      have hl : raw1799step1Labels = labelEmbedding1 ∘ raw1799step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1799step1 raw1799step1Labels raw1799step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2261 node2261Labels := by rfl

def raw1800 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1800Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1800step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1800step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1800 raw1800Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw1800 raw1800Labels = mixedMoment B raw1800step0 raw1800step0Labels := by
      have ha : raw1800step0 = (fun i j => raw1800 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1800step0 raw1800; decide +kernel
      have hl : raw1800step0Labels = raw1800Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1800 raw1800Labels permutation32 permutation4
    mixedMoment B raw1800step0 raw1800step0Labels = mixedMoment B raw1800step1 raw1800step1Labels := by
      have ha : raw1800step1 = raw1800step0 := by apply Matrix.ext; unfold raw1800step1 raw1800step0; decide +kernel
      have hl : raw1800step0Labels = labelEmbedding7 ∘ raw1800step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1800step0 raw1800step0Labels raw1800step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4869 node4869Labels := by rfl

def raw1801 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1801Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1801step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1801 raw1801Labels = mixedMoment B node2110 node2110Labels := by
  calc
    mixedMoment B raw1801 raw1801Labels = mixedMoment B raw1801step0 raw1801step0Labels := by
      have ha : raw1801step0 = (fun i j => raw1801 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1801step0 raw1801; decide +kernel
      have hl : raw1801step0Labels = raw1801Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1801 raw1801Labels permutation32 permutation4
    _ = mixedMoment B node2110 node2110Labels := by rfl

def raw1802 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1802Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw1802step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1802step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw1802step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1802step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw1802step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1802 raw1802Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw1802 raw1802Labels = mixedMoment B raw1802step0 raw1802step0Labels := by
      have ha : raw1802step0 = (fun i j => raw1802 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1802step0 raw1802; decide +kernel
      have hl : raw1802step0Labels = raw1802Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1802 raw1802Labels permutation50 permutation6
    mixedMoment B raw1802step0 raw1802step0Labels = mixedMoment B raw1802step1 raw1802step1Labels := by
      have ha : raw1802step1 = -raw1802step0 := by apply Matrix.ext; change ∀ i j, raw1802step1 i j = -(raw1802step0 i j); unfold raw1802step1 raw1802step0; decide +kernel
      have hl : raw1802step1Labels = raw1802step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1802step1 raw1802step1Labels = mixedMoment B raw1802step2 raw1802step2Labels := by
      have ha : raw1802step2 = raw1802step1 := by apply Matrix.ext; unfold raw1802step2 raw1802step1; decide +kernel
      have hl : raw1802step1Labels = labelEmbedding1 ∘ raw1802step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1802step1 raw1802step1Labels raw1802step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2275 node2275Labels := by rfl

def raw1803 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1803Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1803step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1803step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1803step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1803step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1803 raw1803Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw1803 raw1803Labels = mixedMoment B raw1803step0 raw1803step0Labels := by
      have ha : raw1803step0 = (fun i j => raw1803 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1803step0 raw1803; decide +kernel
      have hl : raw1803step0Labels = raw1803Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1803 raw1803Labels permutation8 permutation4
    mixedMoment B raw1803step0 raw1803step0Labels = mixedMoment B raw1803step1 raw1803step1Labels := by
      have ha : raw1803step1 = raw1803step0 := by apply Matrix.ext; unfold raw1803step1 raw1803step0; decide +kernel
      have hl : raw1803step0Labels = labelEmbedding7 ∘ raw1803step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1803step0 raw1803step0Labels raw1803step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4871 node4871Labels := by rfl

def raw1804 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1804Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1804step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1804step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1804 raw1804Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw1804 raw1804Labels = mixedMoment B raw1804step0 raw1804step0Labels := by
      have ha : raw1804step0 = (fun i j => raw1804 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1804step0 raw1804; decide +kernel
      have hl : raw1804step0Labels = raw1804Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1804 raw1804Labels permutation8 permutation4
    _ = mixedMoment B node2112 node2112Labels := by rfl

def raw1805 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1805Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1805step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw1805step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1805step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw1805step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1805step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw1805step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1805 raw1805Labels = mixedMoment B node2287 node2287Labels := by
  calc
    mixedMoment B raw1805 raw1805Labels = mixedMoment B raw1805step0 raw1805step0Labels := by
      have ha : raw1805step0 = (fun i j => raw1805 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1805step0 raw1805; decide +kernel
      have hl : raw1805step0Labels = raw1805Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1805 raw1805Labels permutation8 permutation6
    mixedMoment B raw1805step0 raw1805step0Labels = mixedMoment B raw1805step1 raw1805step1Labels := by
      have ha : raw1805step1 = -raw1805step0 := by apply Matrix.ext; change ∀ i j, raw1805step1 i j = -(raw1805step0 i j); unfold raw1805step1 raw1805step0; decide +kernel
      have hl : raw1805step1Labels = raw1805step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1805step1 raw1805step1Labels = mixedMoment B raw1805step2 raw1805step2Labels := by
      have ha : raw1805step2 = raw1805step1 := by apply Matrix.ext; unfold raw1805step2 raw1805step1; decide +kernel
      have hl : raw1805step1Labels = labelEmbedding1 ∘ raw1805step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1805step1 raw1805step1Labels raw1805step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2287 node2287Labels := by rfl

def raw1806 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1806Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1806step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1806step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1806step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1806step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1806 raw1806Labels = mixedMoment B node4874 node4874Labels := by
  calc
    mixedMoment B raw1806 raw1806Labels = mixedMoment B raw1806step0 raw1806step0Labels := by
      have ha : raw1806step0 = (fun i j => raw1806 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1806step0 raw1806; decide +kernel
      have hl : raw1806step0Labels = raw1806Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1806 raw1806Labels permutation8 permutation4
    mixedMoment B raw1806step0 raw1806step0Labels = mixedMoment B raw1806step1 raw1806step1Labels := by
      have ha : raw1806step1 = raw1806step0 := by apply Matrix.ext; unfold raw1806step1 raw1806step0; decide +kernel
      have hl : raw1806step0Labels = labelEmbedding7 ∘ raw1806step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1806step0 raw1806step0Labels raw1806step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4874 node4874Labels := by rfl

def raw1807 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1807Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1807step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1807step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1807 raw1807Labels = mixedMoment B node2115 node2115Labels := by
  calc
    mixedMoment B raw1807 raw1807Labels = mixedMoment B raw1807step0 raw1807step0Labels := by
      have ha : raw1807step0 = (fun i j => raw1807 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1807step0 raw1807; decide +kernel
      have hl : raw1807step0Labels = raw1807Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1807 raw1807Labels permutation8 permutation4
    _ = mixedMoment B node2115 node2115Labels := by rfl

def raw1808 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1808Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1808step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw1808step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1808step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw1808step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1808step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw1808step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1808 raw1808Labels = mixedMoment B node2276 node2276Labels := by
  calc
    mixedMoment B raw1808 raw1808Labels = mixedMoment B raw1808step0 raw1808step0Labels := by
      have ha : raw1808step0 = (fun i j => raw1808 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1808step0 raw1808; decide +kernel
      have hl : raw1808step0Labels = raw1808Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1808 raw1808Labels permutation10 permutation6
    mixedMoment B raw1808step0 raw1808step0Labels = mixedMoment B raw1808step1 raw1808step1Labels := by
      have ha : raw1808step1 = -raw1808step0 := by apply Matrix.ext; change ∀ i j, raw1808step1 i j = -(raw1808step0 i j); unfold raw1808step1 raw1808step0; decide +kernel
      have hl : raw1808step1Labels = raw1808step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1808step1 raw1808step1Labels = mixedMoment B raw1808step2 raw1808step2Labels := by
      have ha : raw1808step2 = raw1808step1 := by apply Matrix.ext; unfold raw1808step2 raw1808step1; decide +kernel
      have hl : raw1808step1Labels = labelEmbedding1 ∘ raw1808step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1808step1 raw1808step1Labels raw1808step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2276 node2276Labels := by rfl

def raw1809 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1809Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1809step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1809step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1809step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1809step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1809 raw1809Labels = mixedMoment B node4875 node4875Labels := by
  calc
    mixedMoment B raw1809 raw1809Labels = mixedMoment B raw1809step0 raw1809step0Labels := by
      have ha : raw1809step0 = (fun i j => raw1809 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1809step0 raw1809; decide +kernel
      have hl : raw1809step0Labels = raw1809Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1809 raw1809Labels permutation8 permutation4
    mixedMoment B raw1809step0 raw1809step0Labels = mixedMoment B raw1809step1 raw1809step1Labels := by
      have ha : raw1809step1 = raw1809step0 := by apply Matrix.ext; unfold raw1809step1 raw1809step0; decide +kernel
      have hl : raw1809step0Labels = labelEmbedding7 ∘ raw1809step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1809step0 raw1809step0Labels raw1809step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4875 node4875Labels := by rfl

def raw1810 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1810Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1810step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1810step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1810 raw1810Labels = mixedMoment B node2116 node2116Labels := by
  calc
    mixedMoment B raw1810 raw1810Labels = mixedMoment B raw1810step0 raw1810step0Labels := by
      have ha : raw1810step0 = (fun i j => raw1810 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1810step0 raw1810; decide +kernel
      have hl : raw1810step0Labels = raw1810Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1810 raw1810Labels permutation8 permutation4
    _ = mixedMoment B node2116 node2116Labels := by rfl

def raw1811 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, -1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1811Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1811step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw1811step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1811step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw1811step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1811step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw1811step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1811 raw1811Labels = mixedMoment B node2288 node2288Labels := by
  calc
    mixedMoment B raw1811 raw1811Labels = mixedMoment B raw1811step0 raw1811step0Labels := by
      have ha : raw1811step0 = (fun i j => raw1811 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1811step0 raw1811; decide +kernel
      have hl : raw1811step0Labels = raw1811Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1811 raw1811Labels permutation8 permutation6
    mixedMoment B raw1811step0 raw1811step0Labels = mixedMoment B raw1811step1 raw1811step1Labels := by
      have ha : raw1811step1 = -raw1811step0 := by apply Matrix.ext; change ∀ i j, raw1811step1 i j = -(raw1811step0 i j); unfold raw1811step1 raw1811step0; decide +kernel
      have hl : raw1811step1Labels = raw1811step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1811step1 raw1811step1Labels = mixedMoment B raw1811step2 raw1811step2Labels := by
      have ha : raw1811step2 = raw1811step1 := by apply Matrix.ext; unfold raw1811step2 raw1811step1; decide +kernel
      have hl : raw1811step1Labels = labelEmbedding1 ∘ raw1811step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1811step1 raw1811step1Labels raw1811step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2288 node2288Labels := by rfl

def raw1812 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw1812Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw1812step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1812step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw1812step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1812 raw1812Labels = mixedMoment B node4887 node4887Labels := by
  calc
    mixedMoment B raw1812 raw1812Labels = mixedMoment B raw1812step0 raw1812step0Labels := by
      have ha : raw1812step0 = (fun i j => raw1812 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1812step0 raw1812; decide +kernel
      have hl : raw1812step0Labels = raw1812Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1812 raw1812Labels permutation152 permutation4
    mixedMoment B raw1812step0 raw1812step0Labels = mixedMoment B raw1812step1 raw1812step1Labels := by
      have ha : raw1812step1 = raw1812step0 := by apply Matrix.ext; unfold raw1812step1 raw1812step0; decide +kernel
      have hl : raw1812step0Labels = labelEmbedding7 ∘ raw1812step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1812step0 raw1812step0Labels raw1812step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4887 node4887Labels := by rfl

def raw1813 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw1813Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1813step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw1813step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1813 raw1813Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw1813 raw1813Labels = mixedMoment B raw1813step0 raw1813step0Labels := by
      have ha : raw1813step0 = (fun i j => raw1813 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1813step0 raw1813; decide +kernel
      have hl : raw1813step0Labels = raw1813Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1813 raw1813Labels permutation152 permutation4
    _ = mixedMoment B node2243 node2243Labels := by rfl

def raw1814 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw1814Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1814step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw1814step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1814step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw1814step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1814step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw1814step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1814 raw1814Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw1814 raw1814Labels = mixedMoment B raw1814step0 raw1814step0Labels := by
      have ha : raw1814step0 = (fun i j => raw1814 (permutation212 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1814step0 raw1814; decide +kernel
      have hl : raw1814step0Labels = raw1814Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1814 raw1814Labels permutation212 permutation6
    mixedMoment B raw1814step0 raw1814step0Labels = mixedMoment B raw1814step1 raw1814step1Labels := by
      have ha : raw1814step1 = -raw1814step0 := by apply Matrix.ext; change ∀ i j, raw1814step1 i j = -(raw1814step0 i j); unfold raw1814step1 raw1814step0; decide +kernel
      have hl : raw1814step1Labels = raw1814step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1814step1 raw1814step1Labels = mixedMoment B raw1814step2 raw1814step2Labels := by
      have ha : raw1814step2 = raw1814step1 := by apply Matrix.ext; unfold raw1814step2 raw1814step1; decide +kernel
      have hl : raw1814step1Labels = labelEmbedding1 ∘ raw1814step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1814step1 raw1814step1Labels raw1814step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2243 node2243Labels := by rfl

def raw1815 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw1815Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw1815step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw1815step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1815 raw1815Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw1815 raw1815Labels = mixedMoment B raw1815step0 raw1815step0Labels := by
      have ha : raw1815step0 = (fun i j => raw1815 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1815step0 raw1815; decide +kernel
      have hl : raw1815step0Labels = raw1815Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1815 raw1815Labels permutation32 permutation4
    mixedMoment B raw1815step0 raw1815step0Labels = mixedMoment B raw1815step1 raw1815step1Labels := by
      have ha : raw1815step1 = raw1815step0 := by apply Matrix.ext; unfold raw1815step1 raw1815step0; decide +kernel
      have hl : raw1815step0Labels = labelEmbedding7 ∘ raw1815step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1815step0 raw1815step0Labels raw1815step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw1816 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw1816Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw1816step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1816 raw1816Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw1816 raw1816Labels = mixedMoment B raw1816step0 raw1816step0Labels := by
      have ha : raw1816step0 = (fun i j => raw1816 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1816step0 raw1816; decide +kernel
      have hl : raw1816step0Labels = raw1816Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1816 raw1816Labels permutation32 permutation4
    _ = mixedMoment B node2244 node2244Labels := by rfl

def raw1817 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw1817Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw1817step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw1817step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1817step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw1817step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1817 raw1817Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw1817 raw1817Labels = mixedMoment B raw1817step0 raw1817step0Labels := by
      have ha : raw1817step0 = (fun i j => raw1817 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1817step0 raw1817; decide +kernel
      have hl : raw1817step0Labels = raw1817Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1817 raw1817Labels permutation44 permutation6
    mixedMoment B raw1817step0 raw1817step0Labels = mixedMoment B raw1817step1 raw1817step1Labels := by
      have ha : raw1817step1 = -raw1817step0 := by apply Matrix.ext; change ∀ i j, raw1817step1 i j = -(raw1817step0 i j); unfold raw1817step1 raw1817step0; decide +kernel
      have hl : raw1817step1Labels = raw1817step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1817step1 raw1817step1Labels = mixedMoment B raw1817step2 raw1817step2Labels := by
      have ha : raw1817step2 = raw1817step1 := by apply Matrix.ext; unfold raw1817step2 raw1817step1; decide +kernel
      have hl : raw1817step1Labels = labelEmbedding1 ∘ raw1817step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1817step1 raw1817step1Labels raw1817step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2262 node2262Labels := by rfl

def raw1818 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1818step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1818step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1818 raw1818Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw1818 raw1818Labels = mixedMoment B raw1818step0 raw1818step0Labels := by
      have ha : raw1818step0 = (fun i j => raw1818 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1818step0 raw1818; decide +kernel
      have hl : raw1818step0Labels = raw1818Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1818 raw1818Labels permutation32 permutation4
    mixedMoment B raw1818step0 raw1818step0Labels = mixedMoment B raw1818step1 raw1818step1Labels := by
      have ha : raw1818step1 = raw1818step0 := by apply Matrix.ext; unfold raw1818step1 raw1818step0; decide +kernel
      have hl : raw1818step0Labels = labelEmbedding7 ∘ raw1818step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1818step0 raw1818step0Labels raw1818step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw1819 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1819Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1819step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1819 raw1819Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw1819 raw1819Labels = mixedMoment B raw1819step0 raw1819step0Labels := by
      have ha : raw1819step0 = (fun i j => raw1819 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1819step0 raw1819; decide +kernel
      have hl : raw1819step0Labels = raw1819Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1819 raw1819Labels permutation32 permutation4
    _ = mixedMoment B node2245 node2245Labels := by rfl

def raw1820 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1820Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw1820step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw1820step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1820step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw1820step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1820 raw1820Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw1820 raw1820Labels = mixedMoment B raw1820step0 raw1820step0Labels := by
      have ha : raw1820step0 = (fun i j => raw1820 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1820step0 raw1820; decide +kernel
      have hl : raw1820step0Labels = raw1820Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1820 raw1820Labels permutation50 permutation6
    mixedMoment B raw1820step0 raw1820step0Labels = mixedMoment B raw1820step1 raw1820step1Labels := by
      have ha : raw1820step1 = -raw1820step0 := by apply Matrix.ext; change ∀ i j, raw1820step1 i j = -(raw1820step0 i j); unfold raw1820step1 raw1820step0; decide +kernel
      have hl : raw1820step1Labels = raw1820step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1820step1 raw1820step1Labels = mixedMoment B raw1820step2 raw1820step2Labels := by
      have ha : raw1820step2 = raw1820step1 := by apply Matrix.ext; unfold raw1820step2 raw1820step1; decide +kernel
      have hl : raw1820step1Labels = labelEmbedding1 ∘ raw1820step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1820step1 raw1820step1Labels raw1820step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2277 node2277Labels := by rfl

def raw1821 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![-2, 3, -1]]
def raw1821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1821step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw1821step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1821step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw1821step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1821 raw1821Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw1821 raw1821Labels = mixedMoment B raw1821step0 raw1821step0Labels := by
      have ha : raw1821step0 = (fun i j => raw1821 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1821step0 raw1821; decide +kernel
      have hl : raw1821step0Labels = raw1821Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1821 raw1821Labels permutation8 permutation4
    mixedMoment B raw1821step0 raw1821step0Labels = mixedMoment B raw1821step1 raw1821step1Labels := by
      have ha : raw1821step1 = raw1821step0 := by apply Matrix.ext; unfold raw1821step1 raw1821step0; decide +kernel
      have hl : raw1821step0Labels = labelEmbedding7 ∘ raw1821step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1821step0 raw1821step0Labels raw1821step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

def raw1822 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![-2, 3, -1]]
def raw1822Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1822step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw1822step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1822 raw1822Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw1822 raw1822Labels = mixedMoment B raw1822step0 raw1822step0Labels := by
      have ha : raw1822step0 = (fun i j => raw1822 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1822step0 raw1822; decide +kernel
      have hl : raw1822step0Labels = raw1822Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1822 raw1822Labels permutation8 permutation4
    _ = mixedMoment B node2247 node2247Labels := by rfl

def raw1823 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 0, -1], ![-2, 3, -1]]
def raw1823Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1823step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw1823step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1823step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw1823step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1823step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw1823step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1823 raw1823Labels = mixedMoment B node2290 node2290Labels := by
  calc
    mixedMoment B raw1823 raw1823Labels = mixedMoment B raw1823step0 raw1823step0Labels := by
      have ha : raw1823step0 = (fun i j => raw1823 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1823step0 raw1823; decide +kernel
      have hl : raw1823step0Labels = raw1823Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1823 raw1823Labels permutation8 permutation6
    mixedMoment B raw1823step0 raw1823step0Labels = mixedMoment B raw1823step1 raw1823step1Labels := by
      have ha : raw1823step1 = -raw1823step0 := by apply Matrix.ext; change ∀ i j, raw1823step1 i j = -(raw1823step0 i j); unfold raw1823step1 raw1823step0; decide +kernel
      have hl : raw1823step1Labels = raw1823step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1823step1 raw1823step1Labels = mixedMoment B raw1823step2 raw1823step2Labels := by
      have ha : raw1823step2 = raw1823step1 := by apply Matrix.ext; unfold raw1823step2 raw1823step1; decide +kernel
      have hl : raw1823step1Labels = labelEmbedding1 ∘ raw1823step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1823step1 raw1823step1Labels raw1823step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2290 node2290Labels := by rfl

def raw1824 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1824Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1824step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1824step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1824step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1824step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1824 raw1824Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw1824 raw1824Labels = mixedMoment B raw1824step0 raw1824step0Labels := by
      have ha : raw1824step0 = (fun i j => raw1824 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1824step0 raw1824; decide +kernel
      have hl : raw1824step0Labels = raw1824Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1824 raw1824Labels permutation8 permutation4
    mixedMoment B raw1824step0 raw1824step0Labels = mixedMoment B raw1824step1 raw1824step1Labels := by
      have ha : raw1824step1 = raw1824step0 := by apply Matrix.ext; unfold raw1824step1 raw1824step0; decide +kernel
      have hl : raw1824step0Labels = labelEmbedding7 ∘ raw1824step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1824step0 raw1824step0Labels raw1824step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw1825 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1825Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1825step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1825step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1825 raw1825Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw1825 raw1825Labels = mixedMoment B raw1825step0 raw1825step0Labels := by
      have ha : raw1825step0 = (fun i j => raw1825 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1825step0 raw1825; decide +kernel
      have hl : raw1825step0Labels = raw1825Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1825 raw1825Labels permutation8 permutation4
    _ = mixedMoment B node2266 node2266Labels := by rfl

def raw1826 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, 0, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1826Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1826step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw1826step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1826step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw1826step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1826step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw1826step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1826 raw1826Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw1826 raw1826Labels = mixedMoment B raw1826step0 raw1826step0Labels := by
      have ha : raw1826step0 = (fun i j => raw1826 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1826step0 raw1826; decide +kernel
      have hl : raw1826step0Labels = raw1826Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1826 raw1826Labels permutation12 permutation6
    mixedMoment B raw1826step0 raw1826step0Labels = mixedMoment B raw1826step1 raw1826step1Labels := by
      have ha : raw1826step1 = -raw1826step0 := by apply Matrix.ext; change ∀ i j, raw1826step1 i j = -(raw1826step0 i j); unfold raw1826step1 raw1826step0; decide +kernel
      have hl : raw1826step1Labels = raw1826step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1826step1 raw1826step1Labels = mixedMoment B raw1826step2 raw1826step2Labels := by
      have ha : raw1826step2 = raw1826step1 := by apply Matrix.ext; unfold raw1826step2 raw1826step1; decide +kernel
      have hl : raw1826step1Labels = labelEmbedding1 ∘ raw1826step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1826step1 raw1826step1Labels raw1826step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2278 node2278Labels := by rfl

def raw1827 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw1827Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1827step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw1827step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1827step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw1827step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1827 raw1827Labels = mixedMoment B node4898 node4898Labels := by
  calc
    mixedMoment B raw1827 raw1827Labels = mixedMoment B raw1827step0 raw1827step0Labels := by
      have ha : raw1827step0 = (fun i j => raw1827 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1827step0 raw1827; decide +kernel
      have hl : raw1827step0Labels = raw1827Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1827 raw1827Labels permutation8 permutation4
    mixedMoment B raw1827step0 raw1827step0Labels = mixedMoment B raw1827step1 raw1827step1Labels := by
      have ha : raw1827step1 = raw1827step0 := by apply Matrix.ext; unfold raw1827step1 raw1827step0; decide +kernel
      have hl : raw1827step0Labels = labelEmbedding7 ∘ raw1827step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1827step0 raw1827step0Labels raw1827step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4898 node4898Labels := by rfl

def raw1828 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw1828Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1828step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw1828step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1828 raw1828Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw1828 raw1828Labels = mixedMoment B raw1828step0 raw1828step0Labels := by
      have ha : raw1828step0 = (fun i j => raw1828 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1828step0 raw1828; decide +kernel
      have hl : raw1828step0Labels = raw1828Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1828 raw1828Labels permutation8 permutation4
    _ = mixedMoment B node2279 node2279Labels := by rfl

def raw1829 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw1829Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1829step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw1829step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1829step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw1829step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1829step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw1829step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1829 raw1829Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw1829 raw1829Labels = mixedMoment B raw1829step0 raw1829step0Labels := by
      have ha : raw1829step0 = (fun i j => raw1829 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1829step0 raw1829; decide +kernel
      have hl : raw1829step0Labels = raw1829Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1829 raw1829Labels permutation13 permutation6
    mixedMoment B raw1829step0 raw1829step0Labels = mixedMoment B raw1829step1 raw1829step1Labels := by
      have ha : raw1829step1 = -raw1829step0 := by apply Matrix.ext; change ∀ i j, raw1829step1 i j = -(raw1829step0 i j); unfold raw1829step1 raw1829step0; decide +kernel
      have hl : raw1829step1Labels = raw1829step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1829step1 raw1829step1Labels = mixedMoment B raw1829step2 raw1829step2Labels := by
      have ha : raw1829step2 = raw1829step1 := by apply Matrix.ext; unfold raw1829step2 raw1829step1; decide +kernel
      have hl : raw1829step1Labels = labelEmbedding1 ∘ raw1829step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1829step1 raw1829step1Labels raw1829step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2279 node2279Labels := by rfl

def raw1830 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![-2, 3, -1]]
def raw1830Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1830step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw1830step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1830step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw1830step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1830 raw1830Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw1830 raw1830Labels = mixedMoment B raw1830step0 raw1830step0Labels := by
      have ha : raw1830step0 = (fun i j => raw1830 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1830step0 raw1830; decide +kernel
      have hl : raw1830step0Labels = raw1830Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1830 raw1830Labels permutation2 permutation4
    mixedMoment B raw1830step0 raw1830step0Labels = mixedMoment B raw1830step1 raw1830step1Labels := by
      have ha : raw1830step1 = raw1830step0 := by apply Matrix.ext; unfold raw1830step1 raw1830step0; decide +kernel
      have hl : raw1830step0Labels = labelEmbedding7 ∘ raw1830step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1830step0 raw1830step0Labels raw1830step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4899 node4899Labels := by rfl

def raw1831 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![-2, 3, -1]]
def raw1831Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1831step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw1831step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1831 raw1831Labels = mixedMoment B node2281 node2281Labels := by
  calc
    mixedMoment B raw1831 raw1831Labels = mixedMoment B raw1831step0 raw1831step0Labels := by
      have ha : raw1831step0 = (fun i j => raw1831 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1831step0 raw1831; decide +kernel
      have hl : raw1831step0Labels = raw1831Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1831 raw1831Labels permutation2 permutation4
    _ = mixedMoment B node2281 node2281Labels := by rfl

def raw1832 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -3, 3], ![2, 0, -2], ![-2, 3, -1]]
def raw1832Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1832step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -2, 3], ![-2, 2, 0]]
def raw1832step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1832step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw1832step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1832step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw1832step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1832 raw1832Labels = mixedMoment B node2294 node2294Labels := by
  calc
    mixedMoment B raw1832 raw1832Labels = mixedMoment B raw1832step0 raw1832step0Labels := by
      have ha : raw1832step0 = (fun i j => raw1832 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1832step0 raw1832; decide +kernel
      have hl : raw1832step0Labels = raw1832Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1832 raw1832Labels permutation3 permutation6
    mixedMoment B raw1832step0 raw1832step0Labels = mixedMoment B raw1832step1 raw1832step1Labels := by
      have ha : raw1832step1 = -raw1832step0 := by apply Matrix.ext; change ∀ i j, raw1832step1 i j = -(raw1832step0 i j); unfold raw1832step1 raw1832step0; decide +kernel
      have hl : raw1832step1Labels = raw1832step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1832step1 raw1832step1Labels = mixedMoment B raw1832step2 raw1832step2Labels := by
      have ha : raw1832step2 = raw1832step1 := by apply Matrix.ext; unfold raw1832step2 raw1832step1; decide +kernel
      have hl : raw1832step1Labels = labelEmbedding1 ∘ raw1832step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1832step1 raw1832step1Labels raw1832step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2294 node2294Labels := by rfl

def raw1833 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1833Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1833step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1833step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1833step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1833 raw1833Labels = mixedMoment B node4902 node4902Labels := by
  calc
    mixedMoment B raw1833 raw1833Labels = mixedMoment B raw1833step0 raw1833step0Labels := by
      have ha : raw1833step0 = (fun i j => raw1833 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1833step0 raw1833; decide +kernel
      have hl : raw1833step0Labels = raw1833Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1833 raw1833Labels permutation152 permutation4
    mixedMoment B raw1833step0 raw1833step0Labels = mixedMoment B raw1833step1 raw1833step1Labels := by
      have ha : raw1833step1 = raw1833step0 := by apply Matrix.ext; unfold raw1833step1 raw1833step0; decide +kernel
      have hl : raw1833step0Labels = labelEmbedding7 ∘ raw1833step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1833step0 raw1833step0Labels raw1833step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4902 node4902Labels := by rfl

def raw1834 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1834Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1834step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1834step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1834 raw1834Labels = mixedMoment B node2295 node2295Labels := by
  calc
    mixedMoment B raw1834 raw1834Labels = mixedMoment B raw1834step0 raw1834step0Labels := by
      have ha : raw1834step0 = (fun i j => raw1834 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1834step0 raw1834; decide +kernel
      have hl : raw1834step0Labels = raw1834Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1834 raw1834Labels permutation152 permutation4
    _ = mixedMoment B node2295 node2295Labels := by rfl

def raw1835 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1835Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1835step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw1835step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1835step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1835step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1835step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1835step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1835 raw1835Labels = mixedMoment B node3315 node3315Labels := by
  calc
    mixedMoment B raw1835 raw1835Labels = mixedMoment B raw1835step0 raw1835step0Labels := by
      have ha : raw1835step0 = (fun i j => raw1835 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1835step0 raw1835; decide +kernel
      have hl : raw1835step0Labels = raw1835Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1835 raw1835Labels permutation158 permutation6
    mixedMoment B raw1835step0 raw1835step0Labels = mixedMoment B raw1835step1 raw1835step1Labels := by
      have ha : raw1835step1 = -raw1835step0 := by apply Matrix.ext; change ∀ i j, raw1835step1 i j = -(raw1835step0 i j); unfold raw1835step1 raw1835step0; decide +kernel
      have hl : raw1835step1Labels = raw1835step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1835step1 raw1835step1Labels = mixedMoment B raw1835step2 raw1835step2Labels := by
      have ha : raw1835step2 = raw1835step1 := by apply Matrix.ext; unfold raw1835step2 raw1835step1; decide +kernel
      have hl : raw1835step1Labels = labelEmbedding1 ∘ raw1835step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1835step1 raw1835step1Labels raw1835step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3315 node3315Labels := by rfl

def raw1836 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1836Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1836step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1836step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1836step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1836step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1836 raw1836Labels = mixedMoment B node4903 node4903Labels := by
  calc
    mixedMoment B raw1836 raw1836Labels = mixedMoment B raw1836step0 raw1836step0Labels := by
      have ha : raw1836step0 = (fun i j => raw1836 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1836step0 raw1836; decide +kernel
      have hl : raw1836step0Labels = raw1836Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1836 raw1836Labels permutation152 permutation4
    mixedMoment B raw1836step0 raw1836step0Labels = mixedMoment B raw1836step1 raw1836step1Labels := by
      have ha : raw1836step1 = raw1836step0 := by apply Matrix.ext; unfold raw1836step1 raw1836step0; decide +kernel
      have hl : raw1836step0Labels = labelEmbedding7 ∘ raw1836step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1836step0 raw1836step0Labels raw1836step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4903 node4903Labels := by rfl

def raw1837 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1837Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1837step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1837step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1837 raw1837Labels = mixedMoment B node2296 node2296Labels := by
  calc
    mixedMoment B raw1837 raw1837Labels = mixedMoment B raw1837step0 raw1837step0Labels := by
      have ha : raw1837step0 = (fun i j => raw1837 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1837step0 raw1837; decide +kernel
      have hl : raw1837step0Labels = raw1837Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1837 raw1837Labels permutation152 permutation4
    _ = mixedMoment B node2296 node2296Labels := by rfl

def raw1838 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1838Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1838step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw1838step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1838step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1838step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1838step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1838step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1838 raw1838Labels = mixedMoment B node3316 node3316Labels := by
  calc
    mixedMoment B raw1838 raw1838Labels = mixedMoment B raw1838step0 raw1838step0Labels := by
      have ha : raw1838step0 = (fun i j => raw1838 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1838step0 raw1838; decide +kernel
      have hl : raw1838step0Labels = raw1838Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1838 raw1838Labels permutation158 permutation6
    mixedMoment B raw1838step0 raw1838step0Labels = mixedMoment B raw1838step1 raw1838step1Labels := by
      have ha : raw1838step1 = -raw1838step0 := by apply Matrix.ext; change ∀ i j, raw1838step1 i j = -(raw1838step0 i j); unfold raw1838step1 raw1838step0; decide +kernel
      have hl : raw1838step1Labels = raw1838step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1838step1 raw1838step1Labels = mixedMoment B raw1838step2 raw1838step2Labels := by
      have ha : raw1838step2 = raw1838step1 := by apply Matrix.ext; unfold raw1838step2 raw1838step1; decide +kernel
      have hl : raw1838step1Labels = labelEmbedding1 ∘ raw1838step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1838step1 raw1838step1Labels raw1838step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3316 node3316Labels := by rfl

def raw1839 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1839Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1839step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1839step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1839step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1839step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1839 raw1839Labels = mixedMoment B node4904 node4904Labels := by
  calc
    mixedMoment B raw1839 raw1839Labels = mixedMoment B raw1839step0 raw1839step0Labels := by
      have ha : raw1839step0 = (fun i j => raw1839 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1839step0 raw1839; decide +kernel
      have hl : raw1839step0Labels = raw1839Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1839 raw1839Labels permutation152 permutation4
    mixedMoment B raw1839step0 raw1839step0Labels = mixedMoment B raw1839step1 raw1839step1Labels := by
      have ha : raw1839step1 = raw1839step0 := by apply Matrix.ext; unfold raw1839step1 raw1839step0; decide +kernel
      have hl : raw1839step0Labels = labelEmbedding7 ∘ raw1839step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1839step0 raw1839step0Labels raw1839step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4904 node4904Labels := by rfl

def raw1840 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1840Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1840step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1840step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1840 raw1840Labels = mixedMoment B node2297 node2297Labels := by
  calc
    mixedMoment B raw1840 raw1840Labels = mixedMoment B raw1840step0 raw1840step0Labels := by
      have ha : raw1840step0 = (fun i j => raw1840 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1840step0 raw1840; decide +kernel
      have hl : raw1840step0Labels = raw1840Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1840 raw1840Labels permutation152 permutation4
    _ = mixedMoment B node2297 node2297Labels := by rfl

def raw1841 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1841Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1841step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw1841step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1841step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1841step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1841step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1841step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1841 raw1841Labels = mixedMoment B node3323 node3323Labels := by
  calc
    mixedMoment B raw1841 raw1841Labels = mixedMoment B raw1841step0 raw1841step0Labels := by
      have ha : raw1841step0 = (fun i j => raw1841 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1841step0 raw1841; decide +kernel
      have hl : raw1841step0Labels = raw1841Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1841 raw1841Labels permutation152 permutation6
    mixedMoment B raw1841step0 raw1841step0Labels = mixedMoment B raw1841step1 raw1841step1Labels := by
      have ha : raw1841step1 = -raw1841step0 := by apply Matrix.ext; change ∀ i j, raw1841step1 i j = -(raw1841step0 i j); unfold raw1841step1 raw1841step0; decide +kernel
      have hl : raw1841step1Labels = raw1841step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1841step1 raw1841step1Labels = mixedMoment B raw1841step2 raw1841step2Labels := by
      have ha : raw1841step2 = raw1841step1 := by apply Matrix.ext; unfold raw1841step2 raw1841step1; decide +kernel
      have hl : raw1841step1Labels = labelEmbedding1 ∘ raw1841step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1841step1 raw1841step1Labels raw1841step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3323 node3323Labels := by rfl

def raw1842 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1842Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1842step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1842step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1842step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1842step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1842 raw1842Labels = mixedMoment B node4905 node4905Labels := by
  calc
    mixedMoment B raw1842 raw1842Labels = mixedMoment B raw1842step0 raw1842step0Labels := by
      have ha : raw1842step0 = (fun i j => raw1842 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1842step0 raw1842; decide +kernel
      have hl : raw1842step0Labels = raw1842Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1842 raw1842Labels permutation152 permutation4
    mixedMoment B raw1842step0 raw1842step0Labels = mixedMoment B raw1842step1 raw1842step1Labels := by
      have ha : raw1842step1 = raw1842step0 := by apply Matrix.ext; unfold raw1842step1 raw1842step0; decide +kernel
      have hl : raw1842step0Labels = labelEmbedding7 ∘ raw1842step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1842step0 raw1842step0Labels raw1842step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4905 node4905Labels := by rfl

def raw1843 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1843Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1843 raw1843Labels = mixedMoment B node2298 node2298Labels := by
  calc
    mixedMoment B raw1843 raw1843Labels = mixedMoment B raw1843step0 raw1843step0Labels := by
      have ha : raw1843step0 = (fun i j => raw1843 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1843step0 raw1843; decide +kernel
      have hl : raw1843step0Labels = raw1843Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1843 raw1843Labels permutation152 permutation4
    _ = mixedMoment B node2298 node2298Labels := by rfl

def raw1844 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1844Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1844step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw1844step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1844step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1844step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1844step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1844step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1844 raw1844Labels = mixedMoment B node3320 node3320Labels := by
  calc
    mixedMoment B raw1844 raw1844Labels = mixedMoment B raw1844step0 raw1844step0Labels := by
      have ha : raw1844step0 = (fun i j => raw1844 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1844step0 raw1844; decide +kernel
      have hl : raw1844step0Labels = raw1844Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1844 raw1844Labels permutation164 permutation6
    mixedMoment B raw1844step0 raw1844step0Labels = mixedMoment B raw1844step1 raw1844step1Labels := by
      have ha : raw1844step1 = -raw1844step0 := by apply Matrix.ext; change ∀ i j, raw1844step1 i j = -(raw1844step0 i j); unfold raw1844step1 raw1844step0; decide +kernel
      have hl : raw1844step1Labels = raw1844step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1844step1 raw1844step1Labels = mixedMoment B raw1844step2 raw1844step2Labels := by
      have ha : raw1844step2 = raw1844step1 := by apply Matrix.ext; unfold raw1844step2 raw1844step1; decide +kernel
      have hl : raw1844step1Labels = labelEmbedding1 ∘ raw1844step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1844step1 raw1844step1Labels raw1844step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3320 node3320Labels := by rfl

def raw1845 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1845Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1845step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1845step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1845step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1845step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1845 raw1845Labels = mixedMoment B node4906 node4906Labels := by
  calc
    mixedMoment B raw1845 raw1845Labels = mixedMoment B raw1845step0 raw1845step0Labels := by
      have ha : raw1845step0 = (fun i j => raw1845 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1845step0 raw1845; decide +kernel
      have hl : raw1845step0Labels = raw1845Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1845 raw1845Labels permutation152 permutation4
    mixedMoment B raw1845step0 raw1845step0Labels = mixedMoment B raw1845step1 raw1845step1Labels := by
      have ha : raw1845step1 = raw1845step0 := by apply Matrix.ext; unfold raw1845step1 raw1845step0; decide +kernel
      have hl : raw1845step0Labels = labelEmbedding7 ∘ raw1845step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1845step0 raw1845step0Labels raw1845step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4906 node4906Labels := by rfl

def raw1846 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1846Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1846step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1846 raw1846Labels = mixedMoment B node2299 node2299Labels := by
  calc
    mixedMoment B raw1846 raw1846Labels = mixedMoment B raw1846step0 raw1846step0Labels := by
      have ha : raw1846step0 = (fun i j => raw1846 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1846step0 raw1846; decide +kernel
      have hl : raw1846step0Labels = raw1846Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1846 raw1846Labels permutation152 permutation4
    _ = mixedMoment B node2299 node2299Labels := by rfl

def raw1847 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1847Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1847step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw1847step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1847step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1847step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1847step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1847step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1847 raw1847Labels = mixedMoment B node3324 node3324Labels := by
  calc
    mixedMoment B raw1847 raw1847Labels = mixedMoment B raw1847step0 raw1847step0Labels := by
      have ha : raw1847step0 = (fun i j => raw1847 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1847step0 raw1847; decide +kernel
      have hl : raw1847step0Labels = raw1847Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1847 raw1847Labels permutation152 permutation6
    mixedMoment B raw1847step0 raw1847step0Labels = mixedMoment B raw1847step1 raw1847step1Labels := by
      have ha : raw1847step1 = -raw1847step0 := by apply Matrix.ext; change ∀ i j, raw1847step1 i j = -(raw1847step0 i j); unfold raw1847step1 raw1847step0; decide +kernel
      have hl : raw1847step1Labels = raw1847step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1847step1 raw1847step1Labels = mixedMoment B raw1847step2 raw1847step2Labels := by
      have ha : raw1847step2 = raw1847step1 := by apply Matrix.ext; unfold raw1847step2 raw1847step1; decide +kernel
      have hl : raw1847step1Labels = labelEmbedding1 ∘ raw1847step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1847step1 raw1847step1Labels raw1847step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3324 node3324Labels := by rfl

def raw1848 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1848Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw1848step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw1848step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1848 raw1848Labels = mixedMoment B node4907 node4907Labels := by
  calc
    mixedMoment B raw1848 raw1848Labels = mixedMoment B raw1848step0 raw1848step0Labels := by
      have ha : raw1848step0 = (fun i j => raw1848 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1848step0 raw1848; decide +kernel
      have hl : raw1848step0Labels = raw1848Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1848 raw1848Labels permutation32 permutation4
    mixedMoment B raw1848step0 raw1848step0Labels = mixedMoment B raw1848step1 raw1848step1Labels := by
      have ha : raw1848step1 = raw1848step0 := by apply Matrix.ext; unfold raw1848step1 raw1848step0; decide +kernel
      have hl : raw1848step0Labels = labelEmbedding7 ∘ raw1848step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1848step0 raw1848step0Labels raw1848step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4907 node4907Labels := by rfl

def raw1849 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1849Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw1849step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1849 raw1849Labels = mixedMoment B node2300 node2300Labels := by
  calc
    mixedMoment B raw1849 raw1849Labels = mixedMoment B raw1849step0 raw1849step0Labels := by
      have ha : raw1849step0 = (fun i j => raw1849 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1849step0 raw1849; decide +kernel
      have hl : raw1849step0Labels = raw1849Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1849 raw1849Labels permutation32 permutation4
    _ = mixedMoment B node2300 node2300Labels := by rfl

def raw1850 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1850Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw1850step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw1850step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1850step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw1850step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1850 raw1850Labels = mixedMoment B node3325 node3325Labels := by
  calc
    mixedMoment B raw1850 raw1850Labels = mixedMoment B raw1850step0 raw1850step0Labels := by
      have ha : raw1850step0 = (fun i j => raw1850 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1850step0 raw1850; decide +kernel
      have hl : raw1850step0Labels = raw1850Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1850 raw1850Labels permutation32 permutation6
    mixedMoment B raw1850step0 raw1850step0Labels = mixedMoment B raw1850step1 raw1850step1Labels := by
      have ha : raw1850step1 = -raw1850step0 := by apply Matrix.ext; change ∀ i j, raw1850step1 i j = -(raw1850step0 i j); unfold raw1850step1 raw1850step0; decide +kernel
      have hl : raw1850step1Labels = raw1850step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1850step1 raw1850step1Labels = mixedMoment B raw1850step2 raw1850step2Labels := by
      have ha : raw1850step2 = raw1850step1 := by apply Matrix.ext; unfold raw1850step2 raw1850step1; decide +kernel
      have hl : raw1850step1Labels = labelEmbedding1 ∘ raw1850step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1850step1 raw1850step1Labels raw1850step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3325 node3325Labels := by rfl

def raw1851 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 0, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw1851Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw1851step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1851step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw1851step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1851 raw1851Labels = mixedMoment B node4908 node4908Labels := by
  calc
    mixedMoment B raw1851 raw1851Labels = mixedMoment B raw1851step0 raw1851step0Labels := by
      have ha : raw1851step0 = (fun i j => raw1851 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1851step0 raw1851; decide +kernel
      have hl : raw1851step0Labels = raw1851Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1851 raw1851Labels permutation32 permutation4
    mixedMoment B raw1851step0 raw1851step0Labels = mixedMoment B raw1851step1 raw1851step1Labels := by
      have ha : raw1851step1 = raw1851step0 := by apply Matrix.ext; unfold raw1851step1 raw1851step0; decide +kernel
      have hl : raw1851step0Labels = labelEmbedding7 ∘ raw1851step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1851step0 raw1851step0Labels raw1851step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4908 node4908Labels := by rfl

def raw1852 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 0, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw1852Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw1852step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1852 raw1852Labels = mixedMoment B node2301 node2301Labels := by
  calc
    mixedMoment B raw1852 raw1852Labels = mixedMoment B raw1852step0 raw1852step0Labels := by
      have ha : raw1852step0 = (fun i j => raw1852 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1852step0 raw1852; decide +kernel
      have hl : raw1852step0Labels = raw1852Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1852 raw1852Labels permutation32 permutation4
    _ = mixedMoment B node2301 node2301Labels := by rfl

def raw1853 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 0, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw1853Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw1853step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1853step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw1853step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1853step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw1853step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1853 raw1853Labels = mixedMoment B node3326 node3326Labels := by
  calc
    mixedMoment B raw1853 raw1853Labels = mixedMoment B raw1853step0 raw1853step0Labels := by
      have ha : raw1853step0 = (fun i j => raw1853 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1853step0 raw1853; decide +kernel
      have hl : raw1853step0Labels = raw1853Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1853 raw1853Labels permutation33 permutation6
    mixedMoment B raw1853step0 raw1853step0Labels = mixedMoment B raw1853step1 raw1853step1Labels := by
      have ha : raw1853step1 = -raw1853step0 := by apply Matrix.ext; change ∀ i j, raw1853step1 i j = -(raw1853step0 i j); unfold raw1853step1 raw1853step0; decide +kernel
      have hl : raw1853step1Labels = raw1853step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1853step1 raw1853step1Labels = mixedMoment B raw1853step2 raw1853step2Labels := by
      have ha : raw1853step2 = raw1853step1 := by apply Matrix.ext; unfold raw1853step2 raw1853step1; decide +kernel
      have hl : raw1853step1Labels = labelEmbedding1 ∘ raw1853step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1853step1 raw1853step1Labels raw1853step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3326 node3326Labels := by rfl

def raw1854 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw1854Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1854step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1854step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1854step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1854step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1854 raw1854Labels = mixedMoment B node4909 node4909Labels := by
  calc
    mixedMoment B raw1854 raw1854Labels = mixedMoment B raw1854step0 raw1854step0Labels := by
      have ha : raw1854step0 = (fun i j => raw1854 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1854step0 raw1854; decide +kernel
      have hl : raw1854step0Labels = raw1854Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1854 raw1854Labels permutation152 permutation4
    mixedMoment B raw1854step0 raw1854step0Labels = mixedMoment B raw1854step1 raw1854step1Labels := by
      have ha : raw1854step1 = raw1854step0 := by apply Matrix.ext; unfold raw1854step1 raw1854step0; decide +kernel
      have hl : raw1854step0Labels = labelEmbedding7 ∘ raw1854step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1854step0 raw1854step0Labels raw1854step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4909 node4909Labels := by rfl

def raw1855 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw1855Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1855step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1855 raw1855Labels = mixedMoment B node2302 node2302Labels := by
  calc
    mixedMoment B raw1855 raw1855Labels = mixedMoment B raw1855step0 raw1855step0Labels := by
      have ha : raw1855step0 = (fun i j => raw1855 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1855step0 raw1855; decide +kernel
      have hl : raw1855step0Labels = raw1855Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1855 raw1855Labels permutation152 permutation4
    _ = mixedMoment B node2302 node2302Labels := by rfl

def raw1856 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw1856Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw1856step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1856step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw1856step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1856 raw1856Labels = mixedMoment B node2448 node2448Labels := by
  calc
    mixedMoment B raw1856 raw1856Labels = mixedMoment B raw1856step0 raw1856step0Labels := by
      have ha : raw1856step0 = (fun i j => raw1856 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1856step0 raw1856; decide +kernel
      have hl : raw1856step0Labels = raw1856Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1856 raw1856Labels permutation682 permutation6
    mixedMoment B raw1856step0 raw1856step0Labels = mixedMoment B raw1856step1 raw1856step1Labels := by
      have ha : raw1856step1 = raw1856step0 := by apply Matrix.ext; unfold raw1856step1 raw1856step0; decide +kernel
      have hl : raw1856step0Labels = labelEmbedding1 ∘ raw1856step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1856step0 raw1856step0Labels raw1856step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2448 node2448Labels := by rfl

def raw1857 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw1857Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1857step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1857step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1857step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1857 raw1857Labels = mixedMoment B node4910 node4910Labels := by
  calc
    mixedMoment B raw1857 raw1857Labels = mixedMoment B raw1857step0 raw1857step0Labels := by
      have ha : raw1857step0 = (fun i j => raw1857 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1857step0 raw1857; decide +kernel
      have hl : raw1857step0Labels = raw1857Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1857 raw1857Labels permutation152 permutation4
    mixedMoment B raw1857step0 raw1857step0Labels = mixedMoment B raw1857step1 raw1857step1Labels := by
      have ha : raw1857step1 = raw1857step0 := by apply Matrix.ext; unfold raw1857step1 raw1857step0; decide +kernel
      have hl : raw1857step0Labels = labelEmbedding7 ∘ raw1857step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1857step0 raw1857step0Labels raw1857step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4910 node4910Labels := by rfl

def raw1858 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw1858Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1858step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1858 raw1858Labels = mixedMoment B node2303 node2303Labels := by
  calc
    mixedMoment B raw1858 raw1858Labels = mixedMoment B raw1858step0 raw1858step0Labels := by
      have ha : raw1858step0 = (fun i j => raw1858 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1858step0 raw1858; decide +kernel
      have hl : raw1858step0Labels = raw1858Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1858 raw1858Labels permutation152 permutation4
    _ = mixedMoment B node2303 node2303Labels := by rfl

def raw1859 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw1859Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw1859step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1859step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1859step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1859step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1859step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1859 raw1859Labels = mixedMoment B node3314 node3314Labels := by
  calc
    mixedMoment B raw1859 raw1859Labels = mixedMoment B raw1859step0 raw1859step0Labels := by
      have ha : raw1859step0 = (fun i j => raw1859 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1859step0 raw1859; decide +kernel
      have hl : raw1859step0Labels = raw1859Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1859 raw1859Labels permutation152 permutation6
    mixedMoment B raw1859step0 raw1859step0Labels = mixedMoment B raw1859step1 raw1859step1Labels := by
      have ha : raw1859step1 = -raw1859step0 := by apply Matrix.ext; change ∀ i j, raw1859step1 i j = -(raw1859step0 i j); unfold raw1859step1 raw1859step0; decide +kernel
      have hl : raw1859step1Labels = raw1859step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1859step1 raw1859step1Labels = mixedMoment B raw1859step2 raw1859step2Labels := by
      have ha : raw1859step2 = raw1859step1 := by apply Matrix.ext; unfold raw1859step2 raw1859step1; decide +kernel
      have hl : raw1859step1Labels = labelEmbedding1 ∘ raw1859step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1859step1 raw1859step1Labels raw1859step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3314 node3314Labels := by rfl

def raw1860 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw1860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1860step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1860step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1860step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1860 raw1860Labels = mixedMoment B node4912 node4912Labels := by
  calc
    mixedMoment B raw1860 raw1860Labels = mixedMoment B raw1860step0 raw1860step0Labels := by
      have ha : raw1860step0 = (fun i j => raw1860 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1860step0 raw1860; decide +kernel
      have hl : raw1860step0Labels = raw1860Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1860 raw1860Labels permutation152 permutation4
    mixedMoment B raw1860step0 raw1860step0Labels = mixedMoment B raw1860step1 raw1860step1Labels := by
      have ha : raw1860step1 = raw1860step0 := by apply Matrix.ext; unfold raw1860step1 raw1860step0; decide +kernel
      have hl : raw1860step0Labels = labelEmbedding7 ∘ raw1860step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1860step0 raw1860step0Labels raw1860step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4912 node4912Labels := by rfl

def raw1861 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw1861Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1861step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1861step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1861 raw1861Labels = mixedMoment B node2305 node2305Labels := by
  calc
    mixedMoment B raw1861 raw1861Labels = mixedMoment B raw1861step0 raw1861step0Labels := by
      have ha : raw1861step0 = (fun i j => raw1861 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1861step0 raw1861; decide +kernel
      have hl : raw1861step0Labels = raw1861Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1861 raw1861Labels permutation152 permutation4
    _ = mixedMoment B node2305 node2305Labels := by rfl

def raw1862 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw1862Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1862step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw1862step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1862step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1862step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1862step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1862step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1862 raw1862Labels = mixedMoment B node3317 node3317Labels := by
  calc
    mixedMoment B raw1862 raw1862Labels = mixedMoment B raw1862step0 raw1862step0Labels := by
      have ha : raw1862step0 = (fun i j => raw1862 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1862step0 raw1862; decide +kernel
      have hl : raw1862step0Labels = raw1862Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1862 raw1862Labels permutation153 permutation6
    mixedMoment B raw1862step0 raw1862step0Labels = mixedMoment B raw1862step1 raw1862step1Labels := by
      have ha : raw1862step1 = -raw1862step0 := by apply Matrix.ext; change ∀ i j, raw1862step1 i j = -(raw1862step0 i j); unfold raw1862step1 raw1862step0; decide +kernel
      have hl : raw1862step1Labels = raw1862step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1862step1 raw1862step1Labels = mixedMoment B raw1862step2 raw1862step2Labels := by
      have ha : raw1862step2 = raw1862step1 := by apply Matrix.ext; unfold raw1862step2 raw1862step1; decide +kernel
      have hl : raw1862step1Labels = labelEmbedding1 ∘ raw1862step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1862step1 raw1862step1Labels raw1862step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3317 node3317Labels := by rfl

def raw1863 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw1863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw1863step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw1863step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1863 raw1863Labels = mixedMoment B node4913 node4913Labels := by
  calc
    mixedMoment B raw1863 raw1863Labels = mixedMoment B raw1863step0 raw1863step0Labels := by
      have ha : raw1863step0 = (fun i j => raw1863 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1863step0 raw1863; decide +kernel
      have hl : raw1863step0Labels = raw1863Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1863 raw1863Labels permutation32 permutation4
    mixedMoment B raw1863step0 raw1863step0Labels = mixedMoment B raw1863step1 raw1863step1Labels := by
      have ha : raw1863step1 = raw1863step0 := by apply Matrix.ext; unfold raw1863step1 raw1863step0; decide +kernel
      have hl : raw1863step0Labels = labelEmbedding7 ∘ raw1863step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1863step0 raw1863step0Labels raw1863step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4913 node4913Labels := by rfl

def raw1864 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw1864Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw1864step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1864 raw1864Labels = mixedMoment B node2306 node2306Labels := by
  calc
    mixedMoment B raw1864 raw1864Labels = mixedMoment B raw1864step0 raw1864step0Labels := by
      have ha : raw1864step0 = (fun i j => raw1864 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1864step0 raw1864; decide +kernel
      have hl : raw1864step0Labels = raw1864Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1864 raw1864Labels permutation32 permutation4
    _ = mixedMoment B node2306 node2306Labels := by rfl

def raw1865 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw1865Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, -1, 3]]
def raw1865step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw1865step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1865step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw1865step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1865 raw1865Labels = mixedMoment B node3318 node3318Labels := by
  calc
    mixedMoment B raw1865 raw1865Labels = mixedMoment B raw1865step0 raw1865step0Labels := by
      have ha : raw1865step0 = (fun i j => raw1865 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1865step0 raw1865; decide +kernel
      have hl : raw1865step0Labels = raw1865Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1865 raw1865Labels permutation32 permutation6
    mixedMoment B raw1865step0 raw1865step0Labels = mixedMoment B raw1865step1 raw1865step1Labels := by
      have ha : raw1865step1 = -raw1865step0 := by apply Matrix.ext; change ∀ i j, raw1865step1 i j = -(raw1865step0 i j); unfold raw1865step1 raw1865step0; decide +kernel
      have hl : raw1865step1Labels = raw1865step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1865step1 raw1865step1Labels = mixedMoment B raw1865step2 raw1865step2Labels := by
      have ha : raw1865step2 = raw1865step1 := by apply Matrix.ext; unfold raw1865step2 raw1865step1; decide +kernel
      have hl : raw1865step1Labels = labelEmbedding1 ∘ raw1865step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1865step1 raw1865step1Labels raw1865step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3318 node3318Labels := by rfl

def raw1866 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, 2, -3]]
def raw1866Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw1866step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw1866step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1866 raw1866Labels = mixedMoment B node4914 node4914Labels := by
  calc
    mixedMoment B raw1866 raw1866Labels = mixedMoment B raw1866step0 raw1866step0Labels := by
      have ha : raw1866step0 = (fun i j => raw1866 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1866step0 raw1866; decide +kernel
      have hl : raw1866step0Labels = raw1866Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1866 raw1866Labels permutation32 permutation4
    mixedMoment B raw1866step0 raw1866step0Labels = mixedMoment B raw1866step1 raw1866step1Labels := by
      have ha : raw1866step1 = raw1866step0 := by apply Matrix.ext; unfold raw1866step1 raw1866step0; decide +kernel
      have hl : raw1866step0Labels = labelEmbedding7 ∘ raw1866step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1866step0 raw1866step0Labels raw1866step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4914 node4914Labels := by rfl

def raw1867 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, 2, -3]]
def raw1867Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw1867step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1867 raw1867Labels = mixedMoment B node2307 node2307Labels := by
  calc
    mixedMoment B raw1867 raw1867Labels = mixedMoment B raw1867step0 raw1867step0Labels := by
      have ha : raw1867step0 = (fun i j => raw1867 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1867step0 raw1867; decide +kernel
      have hl : raw1867step0Labels = raw1867Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1867 raw1867Labels permutation32 permutation4
    _ = mixedMoment B node2307 node2307Labels := by rfl

def raw1868 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, 2, -3]]
def raw1868Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw1868step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1868step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw1868step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1868 raw1868Labels = mixedMoment B node2376 node2376Labels := by
  calc
    mixedMoment B raw1868 raw1868Labels = mixedMoment B raw1868step0 raw1868step0Labels := by
      have ha : raw1868step0 = (fun i j => raw1868 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1868step0 raw1868; decide +kernel
      have hl : raw1868step0Labels = raw1868Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1868 raw1868Labels permutation151 permutation6
    mixedMoment B raw1868step0 raw1868step0Labels = mixedMoment B raw1868step1 raw1868step1Labels := by
      have ha : raw1868step1 = raw1868step0 := by apply Matrix.ext; unfold raw1868step1 raw1868step0; decide +kernel
      have hl : raw1868step0Labels = labelEmbedding1 ∘ raw1868step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1868step0 raw1868step0Labels raw1868step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2376 node2376Labels := by rfl

def raw1869 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1869Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1869step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1869step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1869step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1869 raw1869Labels = mixedMoment B node4917 node4917Labels := by
  calc
    mixedMoment B raw1869 raw1869Labels = mixedMoment B raw1869step0 raw1869step0Labels := by
      have ha : raw1869step0 = (fun i j => raw1869 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1869step0 raw1869; decide +kernel
      have hl : raw1869step0Labels = raw1869Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1869 raw1869Labels permutation152 permutation4
    mixedMoment B raw1869step0 raw1869step0Labels = mixedMoment B raw1869step1 raw1869step1Labels := by
      have ha : raw1869step1 = raw1869step0 := by apply Matrix.ext; unfold raw1869step1 raw1869step0; decide +kernel
      have hl : raw1869step0Labels = labelEmbedding7 ∘ raw1869step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1869step0 raw1869step0Labels raw1869step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4917 node4917Labels := by rfl

def raw1870 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1870Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1870step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1870 raw1870Labels = mixedMoment B node2308 node2308Labels := by
  calc
    mixedMoment B raw1870 raw1870Labels = mixedMoment B raw1870step0 raw1870step0Labels := by
      have ha : raw1870step0 = (fun i j => raw1870 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1870step0 raw1870; decide +kernel
      have hl : raw1870step0Labels = raw1870Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1870 raw1870Labels permutation152 permutation4
    _ = mixedMoment B node2308 node2308Labels := by rfl

def raw1871 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1871Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw1871step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1871step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1871step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1871step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1871step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1871 raw1871Labels = mixedMoment B node3321 node3321Labels := by
  calc
    mixedMoment B raw1871 raw1871Labels = mixedMoment B raw1871step0 raw1871step0Labels := by
      have ha : raw1871step0 = (fun i j => raw1871 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1871step0 raw1871; decide +kernel
      have hl : raw1871step0Labels = raw1871Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1871 raw1871Labels permutation170 permutation6
    mixedMoment B raw1871step0 raw1871step0Labels = mixedMoment B raw1871step1 raw1871step1Labels := by
      have ha : raw1871step1 = -raw1871step0 := by apply Matrix.ext; change ∀ i j, raw1871step1 i j = -(raw1871step0 i j); unfold raw1871step1 raw1871step0; decide +kernel
      have hl : raw1871step1Labels = raw1871step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1871step1 raw1871step1Labels = mixedMoment B raw1871step2 raw1871step2Labels := by
      have ha : raw1871step2 = raw1871step1 := by apply Matrix.ext; unfold raw1871step2 raw1871step1; decide +kernel
      have hl : raw1871step1Labels = labelEmbedding1 ∘ raw1871step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1871step1 raw1871step1Labels raw1871step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3321 node3321Labels := by rfl

def raw1872 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw1872Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw1872step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1872step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw1872step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1872 raw1872Labels = mixedMoment B node4919 node4919Labels := by
  calc
    mixedMoment B raw1872 raw1872Labels = mixedMoment B raw1872step0 raw1872step0Labels := by
      have ha : raw1872step0 = (fun i j => raw1872 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1872step0 raw1872; decide +kernel
      have hl : raw1872step0Labels = raw1872Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1872 raw1872Labels permutation32 permutation4
    mixedMoment B raw1872step0 raw1872step0Labels = mixedMoment B raw1872step1 raw1872step1Labels := by
      have ha : raw1872step1 = raw1872step0 := by apply Matrix.ext; unfold raw1872step1 raw1872step0; decide +kernel
      have hl : raw1872step0Labels = labelEmbedding7 ∘ raw1872step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1872step0 raw1872step0Labels raw1872step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4919 node4919Labels := by rfl

def raw1873 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw1873Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw1873step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1873 raw1873Labels = mixedMoment B node2310 node2310Labels := by
  calc
    mixedMoment B raw1873 raw1873Labels = mixedMoment B raw1873step0 raw1873step0Labels := by
      have ha : raw1873step0 = (fun i j => raw1873 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1873step0 raw1873; decide +kernel
      have hl : raw1873step0Labels = raw1873Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1873 raw1873Labels permutation32 permutation4
    _ = mixedMoment B node2310 node2310Labels := by rfl

def raw1874 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw1874Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, 0, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw1874step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1874step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw1874step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1874step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw1874step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1874 raw1874Labels = mixedMoment B node3329 node3329Labels := by
  calc
    mixedMoment B raw1874 raw1874Labels = mixedMoment B raw1874step0 raw1874step0Labels := by
      have ha : raw1874step0 = (fun i j => raw1874 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1874step0 raw1874; decide +kernel
      have hl : raw1874step0Labels = raw1874Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1874 raw1874Labels permutation33 permutation6
    mixedMoment B raw1874step0 raw1874step0Labels = mixedMoment B raw1874step1 raw1874step1Labels := by
      have ha : raw1874step1 = -raw1874step0 := by apply Matrix.ext; change ∀ i j, raw1874step1 i j = -(raw1874step0 i j); unfold raw1874step1 raw1874step0; decide +kernel
      have hl : raw1874step1Labels = raw1874step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1874step1 raw1874step1Labels = mixedMoment B raw1874step2 raw1874step2Labels := by
      have ha : raw1874step2 = raw1874step1 := by apply Matrix.ext; unfold raw1874step2 raw1874step1; decide +kernel
      have hl : raw1874step1Labels = labelEmbedding1 ∘ raw1874step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1874step1 raw1874step1Labels raw1874step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3329 node3329Labels := by rfl

def raw1875 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![0, 1, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw1875Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw1875step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1875step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw1875step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1875 raw1875Labels = mixedMoment B node4920 node4920Labels := by
  calc
    mixedMoment B raw1875 raw1875Labels = mixedMoment B raw1875step0 raw1875step0Labels := by
      have ha : raw1875step0 = (fun i j => raw1875 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1875step0 raw1875; decide +kernel
      have hl : raw1875step0Labels = raw1875Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1875 raw1875Labels permutation32 permutation4
    mixedMoment B raw1875step0 raw1875step0Labels = mixedMoment B raw1875step1 raw1875step1Labels := by
      have ha : raw1875step1 = raw1875step0 := by apply Matrix.ext; unfold raw1875step1 raw1875step0; decide +kernel
      have hl : raw1875step0Labels = labelEmbedding7 ∘ raw1875step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1875step0 raw1875step0Labels raw1875step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4920 node4920Labels := by rfl

def raw1876 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![0, 1, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw1876Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw1876step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1876 raw1876Labels = mixedMoment B node2311 node2311Labels := by
  calc
    mixedMoment B raw1876 raw1876Labels = mixedMoment B raw1876step0 raw1876step0Labels := by
      have ha : raw1876step0 = (fun i j => raw1876 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1876step0 raw1876; decide +kernel
      have hl : raw1876step0Labels = raw1876Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1876 raw1876Labels permutation32 permutation4
    _ = mixedMoment B node2311 node2311Labels := by rfl

def raw1877 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![0, 1, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw1877Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, 1, -3]]
def raw1877step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, 1, -3]]
def raw1877step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1877 raw1877Labels = mixedMoment B node2447 node2447Labels := by
  calc
    mixedMoment B raw1877 raw1877Labels = mixedMoment B raw1877step0 raw1877step0Labels := by
      have ha : raw1877step0 = (fun i j => raw1877 (permutation145 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1877step0 raw1877; decide +kernel
      have hl : raw1877step0Labels = raw1877Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1877 raw1877Labels permutation145 permutation6
    mixedMoment B raw1877step0 raw1877step0Labels = mixedMoment B raw1877step1 raw1877step1Labels := by
      have ha : raw1877step1 = raw1877step0 := by apply Matrix.ext; unfold raw1877step1 raw1877step0; decide +kernel
      have hl : raw1877step0Labels = labelEmbedding1 ∘ raw1877step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1877step0 raw1877step0Labels raw1877step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2447 node2447Labels := by rfl

def raw1878 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1878Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1878step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1878step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1878 raw1878Labels = mixedMoment B node4922 node4922Labels := by
  calc
    mixedMoment B raw1878 raw1878Labels = mixedMoment B raw1878step0 raw1878step0Labels := by
      have ha : raw1878step0 = (fun i j => raw1878 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1878step0 raw1878; decide +kernel
      have hl : raw1878step0Labels = raw1878Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1878 raw1878Labels permutation32 permutation4
    mixedMoment B raw1878step0 raw1878step0Labels = mixedMoment B raw1878step1 raw1878step1Labels := by
      have ha : raw1878step1 = raw1878step0 := by apply Matrix.ext; unfold raw1878step1 raw1878step0; decide +kernel
      have hl : raw1878step0Labels = labelEmbedding7 ∘ raw1878step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1878step0 raw1878step0Labels raw1878step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4922 node4922Labels := by rfl

def raw1879 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1879Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1879step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1879 raw1879Labels = mixedMoment B node2313 node2313Labels := by
  calc
    mixedMoment B raw1879 raw1879Labels = mixedMoment B raw1879step0 raw1879step0Labels := by
      have ha : raw1879step0 = (fun i j => raw1879 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1879step0 raw1879; decide +kernel
      have hl : raw1879step0Labels = raw1879Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1879 raw1879Labels permutation32 permutation4
    _ = mixedMoment B node2313 node2313Labels := by rfl

def raw1880 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1880Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![0, -2, 2], ![-2, 1, 1], ![-2, 0, 2]]
def raw1880step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw1880step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1880step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw1880step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1880 raw1880Labels = mixedMoment B node3322 node3322Labels := by
  calc
    mixedMoment B raw1880 raw1880Labels = mixedMoment B raw1880step0 raw1880step0Labels := by
      have ha : raw1880step0 = (fun i j => raw1880 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1880step0 raw1880; decide +kernel
      have hl : raw1880step0Labels = raw1880Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1880 raw1880Labels permutation34 permutation6
    mixedMoment B raw1880step0 raw1880step0Labels = mixedMoment B raw1880step1 raw1880step1Labels := by
      have ha : raw1880step1 = -raw1880step0 := by apply Matrix.ext; change ∀ i j, raw1880step1 i j = -(raw1880step0 i j); unfold raw1880step1 raw1880step0; decide +kernel
      have hl : raw1880step1Labels = raw1880step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1880step1 raw1880step1Labels = mixedMoment B raw1880step2 raw1880step2Labels := by
      have ha : raw1880step2 = raw1880step1 := by apply Matrix.ext; unfold raw1880step2 raw1880step1; decide +kernel
      have hl : raw1880step1Labels = labelEmbedding1 ∘ raw1880step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1880step1 raw1880step1Labels raw1880step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3322 node3322Labels := by rfl

def raw1881 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1881Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1881step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1881step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1881step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1881 raw1881Labels = mixedMoment B node4923 node4923Labels := by
  calc
    mixedMoment B raw1881 raw1881Labels = mixedMoment B raw1881step0 raw1881step0Labels := by
      have ha : raw1881step0 = (fun i j => raw1881 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1881step0 raw1881; decide +kernel
      have hl : raw1881step0Labels = raw1881Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1881 raw1881Labels permutation32 permutation4
    mixedMoment B raw1881step0 raw1881step0Labels = mixedMoment B raw1881step1 raw1881step1Labels := by
      have ha : raw1881step1 = raw1881step0 := by apply Matrix.ext; unfold raw1881step1 raw1881step0; decide +kernel
      have hl : raw1881step0Labels = labelEmbedding7 ∘ raw1881step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1881step0 raw1881step0Labels raw1881step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4923 node4923Labels := by rfl

def raw1882 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1882Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1882step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1882 raw1882Labels = mixedMoment B node2314 node2314Labels := by
  calc
    mixedMoment B raw1882 raw1882Labels = mixedMoment B raw1882step0 raw1882step0Labels := by
      have ha : raw1882step0 = (fun i j => raw1882 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1882step0 raw1882; decide +kernel
      have hl : raw1882step0Labels = raw1882Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1882 raw1882Labels permutation32 permutation4
    _ = mixedMoment B node2314 node2314Labels := by rfl

def raw1883 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1883Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, 0, -2], ![-1, -1, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw1883step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw1883step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1883step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw1883step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1883 raw1883Labels = mixedMoment B node3330 node3330Labels := by
  calc
    mixedMoment B raw1883 raw1883Labels = mixedMoment B raw1883step0 raw1883step0Labels := by
      have ha : raw1883step0 = (fun i j => raw1883 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1883step0 raw1883; decide +kernel
      have hl : raw1883step0Labels = raw1883Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1883 raw1883Labels permutation35 permutation6
    mixedMoment B raw1883step0 raw1883step0Labels = mixedMoment B raw1883step1 raw1883step1Labels := by
      have ha : raw1883step1 = -raw1883step0 := by apply Matrix.ext; change ∀ i j, raw1883step1 i j = -(raw1883step0 i j); unfold raw1883step1 raw1883step0; decide +kernel
      have hl : raw1883step1Labels = raw1883step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1883step1 raw1883step1Labels = mixedMoment B raw1883step2 raw1883step2Labels := by
      have ha : raw1883step2 = raw1883step1 := by apply Matrix.ext; unfold raw1883step2 raw1883step1; decide +kernel
      have hl : raw1883step1Labels = labelEmbedding1 ∘ raw1883step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1883step1 raw1883step1Labels raw1883step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3330 node3330Labels := by rfl

def raw1884 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 2, -3], ![-2, 3, -1]]
def raw1884Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1884step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![2, 1, -3], ![3, -2, -1]]
def raw1884step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1884step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![2, 1, -3], ![3, -2, -1]]
def raw1884step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1884 raw1884Labels = mixedMoment B node4925 node4925Labels := by
  calc
    mixedMoment B raw1884 raw1884Labels = mixedMoment B raw1884step0 raw1884step0Labels := by
      have ha : raw1884step0 = (fun i j => raw1884 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1884step0 raw1884; decide +kernel
      have hl : raw1884step0Labels = raw1884Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1884 raw1884Labels permutation8 permutation4
    mixedMoment B raw1884step0 raw1884step0Labels = mixedMoment B raw1884step1 raw1884step1Labels := by
      have ha : raw1884step1 = raw1884step0 := by apply Matrix.ext; unfold raw1884step1 raw1884step0; decide +kernel
      have hl : raw1884step0Labels = labelEmbedding7 ∘ raw1884step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1884step0 raw1884step0Labels raw1884step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4925 node4925Labels := by rfl

def raw1885 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 2, -3], ![-2, 3, -1]]
def raw1885Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1885step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![2, 1, -3], ![3, -2, -1]]
def raw1885step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1885 raw1885Labels = mixedMoment B node2315 node2315Labels := by
  calc
    mixedMoment B raw1885 raw1885Labels = mixedMoment B raw1885step0 raw1885step0Labels := by
      have ha : raw1885step0 = (fun i j => raw1885 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1885step0 raw1885; decide +kernel
      have hl : raw1885step0Labels = raw1885Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1885 raw1885Labels permutation8 permutation4
    _ = mixedMoment B node2315 node2315Labels := by rfl

def raw1886 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![0, -2, 2], ![1, 2, -3], ![-2, 3, -1]]
def raw1886Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1886step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![2, 0, -2], ![2, 1, -3]]
def raw1886step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1886step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -2, 3], ![2, 0, -2], ![2, 1, -3]]
def raw1886step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1886 raw1886Labels = mixedMoment B node2369 node2369Labels := by
  calc
    mixedMoment B raw1886 raw1886Labels = mixedMoment B raw1886step0 raw1886step0Labels := by
      have ha : raw1886step0 = (fun i j => raw1886 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1886step0 raw1886; decide +kernel
      have hl : raw1886step0Labels = raw1886Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1886 raw1886Labels permutation25 permutation6
    mixedMoment B raw1886step0 raw1886step0Labels = mixedMoment B raw1886step1 raw1886step1Labels := by
      have ha : raw1886step1 = raw1886step0 := by apply Matrix.ext; unfold raw1886step1 raw1886step0; decide +kernel
      have hl : raw1886step0Labels = labelEmbedding1 ∘ raw1886step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1886step0 raw1886step0Labels raw1886step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2369 node2369Labels := by rfl

def raw1887 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1887step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1887step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1887step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1887 raw1887Labels = mixedMoment B node4926 node4926Labels := by
  calc
    mixedMoment B raw1887 raw1887Labels = mixedMoment B raw1887step0 raw1887step0Labels := by
      have ha : raw1887step0 = (fun i j => raw1887 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1887step0 raw1887; decide +kernel
      have hl : raw1887step0Labels = raw1887Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1887 raw1887Labels permutation152 permutation4
    mixedMoment B raw1887step0 raw1887step0Labels = mixedMoment B raw1887step1 raw1887step1Labels := by
      have ha : raw1887step1 = raw1887step0 := by apply Matrix.ext; unfold raw1887step1 raw1887step0; decide +kernel
      have hl : raw1887step0Labels = labelEmbedding7 ∘ raw1887step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1887step0 raw1887step0Labels raw1887step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4926 node4926Labels := by rfl

def raw1888 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1888Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1888step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1888 raw1888Labels = mixedMoment B node2316 node2316Labels := by
  calc
    mixedMoment B raw1888 raw1888Labels = mixedMoment B raw1888step0 raw1888step0Labels := by
      have ha : raw1888step0 = (fun i j => raw1888 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1888step0 raw1888; decide +kernel
      have hl : raw1888step0Labels = raw1888Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1888 raw1888Labels permutation152 permutation4
    _ = mixedMoment B node2316 node2316Labels := by rfl

def raw1889 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1889Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw1889step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1889step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1889step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1889step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1889step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1889 raw1889Labels = mixedMoment B node3398 node3398Labels := by
  calc
    mixedMoment B raw1889 raw1889Labels = mixedMoment B raw1889step0 raw1889step0Labels := by
      have ha : raw1889step0 = (fun i j => raw1889 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1889step0 raw1889; decide +kernel
      have hl : raw1889step0Labels = raw1889Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1889 raw1889Labels permutation152 permutation6
    mixedMoment B raw1889step0 raw1889step0Labels = mixedMoment B raw1889step1 raw1889step1Labels := by
      have ha : raw1889step1 = -raw1889step0 := by apply Matrix.ext; change ∀ i j, raw1889step1 i j = -(raw1889step0 i j); unfold raw1889step1 raw1889step0; decide +kernel
      have hl : raw1889step1Labels = raw1889step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1889step1 raw1889step1Labels = mixedMoment B raw1889step2 raw1889step2Labels := by
      have ha : raw1889step2 = raw1889step1 := by apply Matrix.ext; unfold raw1889step2 raw1889step1; decide +kernel
      have hl : raw1889step1Labels = labelEmbedding1 ∘ raw1889step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1889step1 raw1889step1Labels raw1889step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3398 node3398Labels := by rfl

def raw1890 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1890step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1890step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1890 raw1890Labels = mixedMoment B node4927 node4927Labels := by
  calc
    mixedMoment B raw1890 raw1890Labels = mixedMoment B raw1890step0 raw1890step0Labels := by
      have ha : raw1890step0 = (fun i j => raw1890 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1890step0 raw1890; decide +kernel
      have hl : raw1890step0Labels = raw1890Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1890 raw1890Labels permutation152 permutation4
    mixedMoment B raw1890step0 raw1890step0Labels = mixedMoment B raw1890step1 raw1890step1Labels := by
      have ha : raw1890step1 = raw1890step0 := by apply Matrix.ext; unfold raw1890step1 raw1890step0; decide +kernel
      have hl : raw1890step0Labels = labelEmbedding7 ∘ raw1890step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1890step0 raw1890step0Labels raw1890step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4927 node4927Labels := by rfl

def raw1891 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1891Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1891step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1891 raw1891Labels = mixedMoment B node2317 node2317Labels := by
  calc
    mixedMoment B raw1891 raw1891Labels = mixedMoment B raw1891step0 raw1891step0Labels := by
      have ha : raw1891step0 = (fun i j => raw1891 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1891step0 raw1891; decide +kernel
      have hl : raw1891step0Labels = raw1891Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1891 raw1891Labels permutation152 permutation4
    _ = mixedMoment B node2317 node2317Labels := by rfl

def raw1892 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1892Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1892step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw1892step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1892step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1892step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1892step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1892step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1892 raw1892Labels = mixedMoment B node3399 node3399Labels := by
  calc
    mixedMoment B raw1892 raw1892Labels = mixedMoment B raw1892step0 raw1892step0Labels := by
      have ha : raw1892step0 = (fun i j => raw1892 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1892step0 raw1892; decide +kernel
      have hl : raw1892step0Labels = raw1892Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1892 raw1892Labels permutation152 permutation6
    mixedMoment B raw1892step0 raw1892step0Labels = mixedMoment B raw1892step1 raw1892step1Labels := by
      have ha : raw1892step1 = -raw1892step0 := by apply Matrix.ext; change ∀ i j, raw1892step1 i j = -(raw1892step0 i j); unfold raw1892step1 raw1892step0; decide +kernel
      have hl : raw1892step1Labels = raw1892step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1892step1 raw1892step1Labels = mixedMoment B raw1892step2 raw1892step2Labels := by
      have ha : raw1892step2 = raw1892step1 := by apply Matrix.ext; unfold raw1892step2 raw1892step1; decide +kernel
      have hl : raw1892step1Labels = labelEmbedding1 ∘ raw1892step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1892step1 raw1892step1Labels raw1892step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3399 node3399Labels := by rfl

def raw1893 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1893step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1893step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1893step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1893step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1893 raw1893Labels = mixedMoment B node4928 node4928Labels := by
  calc
    mixedMoment B raw1893 raw1893Labels = mixedMoment B raw1893step0 raw1893step0Labels := by
      have ha : raw1893step0 = (fun i j => raw1893 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1893step0 raw1893; decide +kernel
      have hl : raw1893step0Labels = raw1893Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1893 raw1893Labels permutation152 permutation4
    mixedMoment B raw1893step0 raw1893step0Labels = mixedMoment B raw1893step1 raw1893step1Labels := by
      have ha : raw1893step1 = raw1893step0 := by apply Matrix.ext; unfold raw1893step1 raw1893step0; decide +kernel
      have hl : raw1893step0Labels = labelEmbedding7 ∘ raw1893step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1893step0 raw1893step0Labels raw1893step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4928 node4928Labels := by rfl

def raw1894 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1894Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1894step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1894 raw1894Labels = mixedMoment B node2318 node2318Labels := by
  calc
    mixedMoment B raw1894 raw1894Labels = mixedMoment B raw1894step0 raw1894step0Labels := by
      have ha : raw1894step0 = (fun i j => raw1894 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1894step0 raw1894; decide +kernel
      have hl : raw1894step0Labels = raw1894Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1894 raw1894Labels permutation152 permutation4
    _ = mixedMoment B node2318 node2318Labels := by rfl

def raw1895 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1895Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw1895step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1895step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1895step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1895step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1895step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1895 raw1895Labels = mixedMoment B node3400 node3400Labels := by
  calc
    mixedMoment B raw1895 raw1895Labels = mixedMoment B raw1895step0 raw1895step0Labels := by
      have ha : raw1895step0 = (fun i j => raw1895 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1895step0 raw1895; decide +kernel
      have hl : raw1895step0Labels = raw1895Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1895 raw1895Labels permutation152 permutation6
    mixedMoment B raw1895step0 raw1895step0Labels = mixedMoment B raw1895step1 raw1895step1Labels := by
      have ha : raw1895step1 = -raw1895step0 := by apply Matrix.ext; change ∀ i j, raw1895step1 i j = -(raw1895step0 i j); unfold raw1895step1 raw1895step0; decide +kernel
      have hl : raw1895step1Labels = raw1895step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1895step1 raw1895step1Labels = mixedMoment B raw1895step2 raw1895step2Labels := by
      have ha : raw1895step2 = raw1895step1 := by apply Matrix.ext; unfold raw1895step2 raw1895step1; decide +kernel
      have hl : raw1895step1Labels = labelEmbedding1 ∘ raw1895step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1895step1 raw1895step1Labels raw1895step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3400 node3400Labels := by rfl

def raw1896 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1896step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1896step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1896step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1896step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1896 raw1896Labels = mixedMoment B node4936 node4936Labels := by
  calc
    mixedMoment B raw1896 raw1896Labels = mixedMoment B raw1896step0 raw1896step0Labels := by
      have ha : raw1896step0 = (fun i j => raw1896 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1896step0 raw1896; decide +kernel
      have hl : raw1896step0Labels = raw1896Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1896 raw1896Labels permutation152 permutation4
    mixedMoment B raw1896step0 raw1896step0Labels = mixedMoment B raw1896step1 raw1896step1Labels := by
      have ha : raw1896step1 = raw1896step0 := by apply Matrix.ext; unfold raw1896step1 raw1896step0; decide +kernel
      have hl : raw1896step0Labels = labelEmbedding7 ∘ raw1896step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1896step0 raw1896step0Labels raw1896step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4936 node4936Labels := by rfl

def raw1897 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1897Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1897step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1897 raw1897Labels = mixedMoment B node2328 node2328Labels := by
  calc
    mixedMoment B raw1897 raw1897Labels = mixedMoment B raw1897step0 raw1897step0Labels := by
      have ha : raw1897step0 = (fun i j => raw1897 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1897step0 raw1897; decide +kernel
      have hl : raw1897step0Labels = raw1897Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1897 raw1897Labels permutation152 permutation4
    _ = mixedMoment B node2328 node2328Labels := by rfl

def raw1898 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1898Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1898step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1898step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1898step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1898step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1898step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1898 raw1898Labels = mixedMoment B node3401 node3401Labels := by
  calc
    mixedMoment B raw1898 raw1898Labels = mixedMoment B raw1898step0 raw1898step0Labels := by
      have ha : raw1898step0 = (fun i j => raw1898 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1898step0 raw1898; decide +kernel
      have hl : raw1898step0Labels = raw1898Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1898 raw1898Labels permutation152 permutation6
    mixedMoment B raw1898step0 raw1898step0Labels = mixedMoment B raw1898step1 raw1898step1Labels := by
      have ha : raw1898step1 = -raw1898step0 := by apply Matrix.ext; change ∀ i j, raw1898step1 i j = -(raw1898step0 i j); unfold raw1898step1 raw1898step0; decide +kernel
      have hl : raw1898step1Labels = raw1898step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1898step1 raw1898step1Labels = mixedMoment B raw1898step2 raw1898step2Labels := by
      have ha : raw1898step2 = raw1898step1 := by apply Matrix.ext; unfold raw1898step2 raw1898step1; decide +kernel
      have hl : raw1898step1Labels = labelEmbedding1 ∘ raw1898step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1898step1 raw1898step1Labels raw1898step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3401 node3401Labels := by rfl

def raw1899 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw1899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1899step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1899step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1899 raw1899Labels = mixedMoment B node4937 node4937Labels := by
  calc
    mixedMoment B raw1899 raw1899Labels = mixedMoment B raw1899step0 raw1899step0Labels := by
      have ha : raw1899step0 = (fun i j => raw1899 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1899step0 raw1899; decide +kernel
      have hl : raw1899step0Labels = raw1899Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1899 raw1899Labels permutation32 permutation4
    mixedMoment B raw1899step0 raw1899step0Labels = mixedMoment B raw1899step1 raw1899step1Labels := by
      have ha : raw1899step1 = raw1899step0 := by apply Matrix.ext; unfold raw1899step1 raw1899step0; decide +kernel
      have hl : raw1899step0Labels = labelEmbedding7 ∘ raw1899step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1899step0 raw1899step0Labels raw1899step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4937 node4937Labels := by rfl

def raw1900 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw1900Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1900step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1900 raw1900Labels = mixedMoment B node2329 node2329Labels := by
  calc
    mixedMoment B raw1900 raw1900Labels = mixedMoment B raw1900step0 raw1900step0Labels := by
      have ha : raw1900step0 = (fun i j => raw1900 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1900step0 raw1900; decide +kernel
      have hl : raw1900step0Labels = raw1900Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1900 raw1900Labels permutation32 permutation4
    _ = mixedMoment B node2329 node2329Labels := by rfl

def raw1901 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw1901Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![1, -2, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw1901step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 2, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1901step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1901step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 2, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1901step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1901 raw1901Labels = mixedMoment B node3402 node3402Labels := by
  calc
    mixedMoment B raw1901 raw1901Labels = mixedMoment B raw1901step0 raw1901step0Labels := by
      have ha : raw1901step0 = (fun i j => raw1901 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1901step0 raw1901; decide +kernel
      have hl : raw1901step0Labels = raw1901Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1901 raw1901Labels permutation32 permutation6
    mixedMoment B raw1901step0 raw1901step0Labels = mixedMoment B raw1901step1 raw1901step1Labels := by
      have ha : raw1901step1 = -raw1901step0 := by apply Matrix.ext; change ∀ i j, raw1901step1 i j = -(raw1901step0 i j); unfold raw1901step1 raw1901step0; decide +kernel
      have hl : raw1901step1Labels = raw1901step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1901step1 raw1901step1Labels = mixedMoment B raw1901step2 raw1901step2Labels := by
      have ha : raw1901step2 = raw1901step1 := by apply Matrix.ext; unfold raw1901step2 raw1901step1; decide +kernel
      have hl : raw1901step1Labels = labelEmbedding1 ∘ raw1901step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1901step1 raw1901step1Labels raw1901step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3402 node3402Labels := by rfl

def raw1902 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1902step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1902step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1902step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1902step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1902 raw1902Labels = mixedMoment B node4939 node4939Labels := by
  calc
    mixedMoment B raw1902 raw1902Labels = mixedMoment B raw1902step0 raw1902step0Labels := by
      have ha : raw1902step0 = (fun i j => raw1902 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1902step0 raw1902; decide +kernel
      have hl : raw1902step0Labels = raw1902Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1902 raw1902Labels permutation152 permutation4
    mixedMoment B raw1902step0 raw1902step0Labels = mixedMoment B raw1902step1 raw1902step1Labels := by
      have ha : raw1902step1 = raw1902step0 := by apply Matrix.ext; unfold raw1902step1 raw1902step0; decide +kernel
      have hl : raw1902step0Labels = labelEmbedding7 ∘ raw1902step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1902step0 raw1902step0Labels raw1902step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4939 node4939Labels := by rfl

def raw1903 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1903Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1903step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1903 raw1903Labels = mixedMoment B node2330 node2330Labels := by
  calc
    mixedMoment B raw1903 raw1903Labels = mixedMoment B raw1903step0 raw1903step0Labels := by
      have ha : raw1903step0 = (fun i j => raw1903 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1903step0 raw1903; decide +kernel
      have hl : raw1903step0Labels = raw1903Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1903 raw1903Labels permutation152 permutation4
    _ = mixedMoment B node2330 node2330Labels := by rfl

def raw1904 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1904Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1904step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1904step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1904step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1904step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1904step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1904 raw1904Labels = mixedMoment B node3404 node3404Labels := by
  calc
    mixedMoment B raw1904 raw1904Labels = mixedMoment B raw1904step0 raw1904step0Labels := by
      have ha : raw1904step0 = (fun i j => raw1904 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1904step0 raw1904; decide +kernel
      have hl : raw1904step0Labels = raw1904Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1904 raw1904Labels permutation152 permutation6
    mixedMoment B raw1904step0 raw1904step0Labels = mixedMoment B raw1904step1 raw1904step1Labels := by
      have ha : raw1904step1 = -raw1904step0 := by apply Matrix.ext; change ∀ i j, raw1904step1 i j = -(raw1904step0 i j); unfold raw1904step1 raw1904step0; decide +kernel
      have hl : raw1904step1Labels = raw1904step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1904step1 raw1904step1Labels = mixedMoment B raw1904step2 raw1904step2Labels := by
      have ha : raw1904step2 = raw1904step1 := by apply Matrix.ext; unfold raw1904step2 raw1904step1; decide +kernel
      have hl : raw1904step1Labels = labelEmbedding1 ∘ raw1904step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1904step1 raw1904step1Labels raw1904step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3404 node3404Labels := by rfl

def raw1905 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1905Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1905step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1905step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1905step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1905 raw1905Labels = mixedMoment B node4941 node4941Labels := by
  calc
    mixedMoment B raw1905 raw1905Labels = mixedMoment B raw1905step0 raw1905step0Labels := by
      have ha : raw1905step0 = (fun i j => raw1905 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1905step0 raw1905; decide +kernel
      have hl : raw1905step0Labels = raw1905Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1905 raw1905Labels permutation152 permutation4
    mixedMoment B raw1905step0 raw1905step0Labels = mixedMoment B raw1905step1 raw1905step1Labels := by
      have ha : raw1905step1 = raw1905step0 := by apply Matrix.ext; unfold raw1905step1 raw1905step0; decide +kernel
      have hl : raw1905step0Labels = labelEmbedding7 ∘ raw1905step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1905step0 raw1905step0Labels raw1905step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4941 node4941Labels := by rfl

def raw1906 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1906Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1906step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1906 raw1906Labels = mixedMoment B node2332 node2332Labels := by
  calc
    mixedMoment B raw1906 raw1906Labels = mixedMoment B raw1906step0 raw1906step0Labels := by
      have ha : raw1906step0 = (fun i j => raw1906 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1906step0 raw1906; decide +kernel
      have hl : raw1906step0Labels = raw1906Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1906 raw1906Labels permutation152 permutation4
    _ = mixedMoment B node2332 node2332Labels := by rfl

def raw1907 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1907Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1907step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw1907step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1907step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1907step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1907step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1907step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1907 raw1907Labels = mixedMoment B node3410 node3410Labels := by
  calc
    mixedMoment B raw1907 raw1907Labels = mixedMoment B raw1907step0 raw1907step0Labels := by
      have ha : raw1907step0 = (fun i j => raw1907 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1907step0 raw1907; decide +kernel
      have hl : raw1907step0Labels = raw1907Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1907 raw1907Labels permutation152 permutation6
    mixedMoment B raw1907step0 raw1907step0Labels = mixedMoment B raw1907step1 raw1907step1Labels := by
      have ha : raw1907step1 = -raw1907step0 := by apply Matrix.ext; change ∀ i j, raw1907step1 i j = -(raw1907step0 i j); unfold raw1907step1 raw1907step0; decide +kernel
      have hl : raw1907step1Labels = raw1907step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1907step1 raw1907step1Labels = mixedMoment B raw1907step2 raw1907step2Labels := by
      have ha : raw1907step2 = raw1907step1 := by apply Matrix.ext; unfold raw1907step2 raw1907step1; decide +kernel
      have hl : raw1907step1Labels = labelEmbedding1 ∘ raw1907step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1907step1 raw1907step1Labels raw1907step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3410 node3410Labels := by rfl

def raw1908 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1908Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1908step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1908step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1908step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1908 raw1908Labels = mixedMoment B node4943 node4943Labels := by
  calc
    mixedMoment B raw1908 raw1908Labels = mixedMoment B raw1908step0 raw1908step0Labels := by
      have ha : raw1908step0 = (fun i j => raw1908 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1908step0 raw1908; decide +kernel
      have hl : raw1908step0Labels = raw1908Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1908 raw1908Labels permutation32 permutation4
    mixedMoment B raw1908step0 raw1908step0Labels = mixedMoment B raw1908step1 raw1908step1Labels := by
      have ha : raw1908step1 = raw1908step0 := by apply Matrix.ext; unfold raw1908step1 raw1908step0; decide +kernel
      have hl : raw1908step0Labels = labelEmbedding7 ∘ raw1908step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1908step0 raw1908step0Labels raw1908step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4943 node4943Labels := by rfl

def raw1909 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1909step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1909 raw1909Labels = mixedMoment B node2334 node2334Labels := by
  calc
    mixedMoment B raw1909 raw1909Labels = mixedMoment B raw1909step0 raw1909step0Labels := by
      have ha : raw1909step0 = (fun i j => raw1909 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1909step0 raw1909; decide +kernel
      have hl : raw1909step0Labels = raw1909Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1909 raw1909Labels permutation32 permutation4
    _ = mixedMoment B node2334 node2334Labels := by rfl

def raw1910 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1910Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw1910step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1910step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1910step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1910step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1910 raw1910Labels = mixedMoment B node3411 node3411Labels := by
  calc
    mixedMoment B raw1910 raw1910Labels = mixedMoment B raw1910step0 raw1910step0Labels := by
      have ha : raw1910step0 = (fun i j => raw1910 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1910step0 raw1910; decide +kernel
      have hl : raw1910step0Labels = raw1910Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1910 raw1910Labels permutation32 permutation6
    mixedMoment B raw1910step0 raw1910step0Labels = mixedMoment B raw1910step1 raw1910step1Labels := by
      have ha : raw1910step1 = -raw1910step0 := by apply Matrix.ext; change ∀ i j, raw1910step1 i j = -(raw1910step0 i j); unfold raw1910step1 raw1910step0; decide +kernel
      have hl : raw1910step1Labels = raw1910step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1910step1 raw1910step1Labels = mixedMoment B raw1910step2 raw1910step2Labels := by
      have ha : raw1910step2 = raw1910step1 := by apply Matrix.ext; unfold raw1910step2 raw1910step1; decide +kernel
      have hl : raw1910step1Labels = labelEmbedding1 ∘ raw1910step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1910step1 raw1910step1Labels raw1910step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3411 node3411Labels := by rfl

def raw1911 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1911Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1911step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1911step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1911 raw1911Labels = mixedMoment B node4946 node4946Labels := by
  calc
    mixedMoment B raw1911 raw1911Labels = mixedMoment B raw1911step0 raw1911step0Labels := by
      have ha : raw1911step0 = (fun i j => raw1911 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1911step0 raw1911; decide +kernel
      have hl : raw1911step0Labels = raw1911Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1911 raw1911Labels permutation32 permutation4
    mixedMoment B raw1911step0 raw1911step0Labels = mixedMoment B raw1911step1 raw1911step1Labels := by
      have ha : raw1911step1 = raw1911step0 := by apply Matrix.ext; unfold raw1911step1 raw1911step0; decide +kernel
      have hl : raw1911step0Labels = labelEmbedding7 ∘ raw1911step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1911step0 raw1911step0Labels raw1911step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4946 node4946Labels := by rfl

def raw1912 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1912 raw1912Labels = mixedMoment B node2337 node2337Labels := by
  calc
    mixedMoment B raw1912 raw1912Labels = mixedMoment B raw1912step0 raw1912step0Labels := by
      have ha : raw1912step0 = (fun i j => raw1912 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1912step0 raw1912; decide +kernel
      have hl : raw1912step0Labels = raw1912Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1912 raw1912Labels permutation32 permutation4
    _ = mixedMoment B node2337 node2337Labels := by rfl

def raw1913 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1913Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw1913step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1913step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1913step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1913step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1913step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1913 raw1913Labels = mixedMoment B node3412 node3412Labels := by
  calc
    mixedMoment B raw1913 raw1913Labels = mixedMoment B raw1913step0 raw1913step0Labels := by
      have ha : raw1913step0 = (fun i j => raw1913 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1913step0 raw1913; decide +kernel
      have hl : raw1913step0Labels = raw1913Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1913 raw1913Labels permutation32 permutation6
    mixedMoment B raw1913step0 raw1913step0Labels = mixedMoment B raw1913step1 raw1913step1Labels := by
      have ha : raw1913step1 = -raw1913step0 := by apply Matrix.ext; change ∀ i j, raw1913step1 i j = -(raw1913step0 i j); unfold raw1913step1 raw1913step0; decide +kernel
      have hl : raw1913step1Labels = raw1913step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1913step1 raw1913step1Labels = mixedMoment B raw1913step2 raw1913step2Labels := by
      have ha : raw1913step2 = raw1913step1 := by apply Matrix.ext; unfold raw1913step2 raw1913step1; decide +kernel
      have hl : raw1913step1Labels = labelEmbedding1 ∘ raw1913step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1913step1 raw1913step1Labels raw1913step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3412 node3412Labels := by rfl

def raw1914 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1914Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1914step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1914step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1914step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1914 raw1914Labels = mixedMoment B node4947 node4947Labels := by
  calc
    mixedMoment B raw1914 raw1914Labels = mixedMoment B raw1914step0 raw1914step0Labels := by
      have ha : raw1914step0 = (fun i j => raw1914 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1914step0 raw1914; decide +kernel
      have hl : raw1914step0Labels = raw1914Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1914 raw1914Labels permutation152 permutation4
    mixedMoment B raw1914step0 raw1914step0Labels = mixedMoment B raw1914step1 raw1914step1Labels := by
      have ha : raw1914step1 = raw1914step0 := by apply Matrix.ext; unfold raw1914step1 raw1914step0; decide +kernel
      have hl : raw1914step0Labels = labelEmbedding7 ∘ raw1914step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1914step0 raw1914step0Labels raw1914step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4947 node4947Labels := by rfl

def raw1915 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1915Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1915step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1915step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1915 raw1915Labels = mixedMoment B node2338 node2338Labels := by
  calc
    mixedMoment B raw1915 raw1915Labels = mixedMoment B raw1915step0 raw1915step0Labels := by
      have ha : raw1915step0 = (fun i j => raw1915 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1915step0 raw1915; decide +kernel
      have hl : raw1915step0Labels = raw1915Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1915 raw1915Labels permutation152 permutation4
    _ = mixedMoment B node2338 node2338Labels := by rfl

def raw1916 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1916Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw1916step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1916step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1916step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1916step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1916step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1916 raw1916Labels = mixedMoment B node3416 node3416Labels := by
  calc
    mixedMoment B raw1916 raw1916Labels = mixedMoment B raw1916step0 raw1916step0Labels := by
      have ha : raw1916step0 = (fun i j => raw1916 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1916step0 raw1916; decide +kernel
      have hl : raw1916step0Labels = raw1916Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1916 raw1916Labels permutation170 permutation6
    mixedMoment B raw1916step0 raw1916step0Labels = mixedMoment B raw1916step1 raw1916step1Labels := by
      have ha : raw1916step1 = -raw1916step0 := by apply Matrix.ext; change ∀ i j, raw1916step1 i j = -(raw1916step0 i j); unfold raw1916step1 raw1916step0; decide +kernel
      have hl : raw1916step1Labels = raw1916step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1916step1 raw1916step1Labels = mixedMoment B raw1916step2 raw1916step2Labels := by
      have ha : raw1916step2 = raw1916step1 := by apply Matrix.ext; unfold raw1916step2 raw1916step1; decide +kernel
      have hl : raw1916step1Labels = labelEmbedding1 ∘ raw1916step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1916step1 raw1916step1Labels raw1916step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3416 node3416Labels := by rfl

def raw1917 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1917Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1917step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1917step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1917step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1917 raw1917Labels = mixedMoment B node4948 node4948Labels := by
  calc
    mixedMoment B raw1917 raw1917Labels = mixedMoment B raw1917step0 raw1917step0Labels := by
      have ha : raw1917step0 = (fun i j => raw1917 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1917step0 raw1917; decide +kernel
      have hl : raw1917step0Labels = raw1917Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1917 raw1917Labels permutation32 permutation4
    mixedMoment B raw1917step0 raw1917step0Labels = mixedMoment B raw1917step1 raw1917step1Labels := by
      have ha : raw1917step1 = raw1917step0 := by apply Matrix.ext; unfold raw1917step1 raw1917step0; decide +kernel
      have hl : raw1917step0Labels = labelEmbedding7 ∘ raw1917step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1917step0 raw1917step0Labels raw1917step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4948 node4948Labels := by rfl

def raw1918 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1918Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1918 raw1918Labels = mixedMoment B node2339 node2339Labels := by
  calc
    mixedMoment B raw1918 raw1918Labels = mixedMoment B raw1918step0 raw1918step0Labels := by
      have ha : raw1918step0 = (fun i j => raw1918 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1918step0 raw1918; decide +kernel
      have hl : raw1918step0Labels = raw1918Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1918 raw1918Labels permutation32 permutation4
    _ = mixedMoment B node2339 node2339Labels := by rfl

def raw1919 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1919Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw1919step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1919step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1919step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1919step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1919 raw1919Labels = mixedMoment B node3420 node3420Labels := by
  calc
    mixedMoment B raw1919 raw1919Labels = mixedMoment B raw1919step0 raw1919step0Labels := by
      have ha : raw1919step0 = (fun i j => raw1919 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1919step0 raw1919; decide +kernel
      have hl : raw1919step0Labels = raw1919Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1919 raw1919Labels permutation32 permutation6
    mixedMoment B raw1919step0 raw1919step0Labels = mixedMoment B raw1919step1 raw1919step1Labels := by
      have ha : raw1919step1 = -raw1919step0 := by apply Matrix.ext; change ∀ i j, raw1919step1 i j = -(raw1919step0 i j); unfold raw1919step1 raw1919step0; decide +kernel
      have hl : raw1919step1Labels = raw1919step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1919step1 raw1919step1Labels = mixedMoment B raw1919step2 raw1919step2Labels := by
      have ha : raw1919step2 = raw1919step1 := by apply Matrix.ext; unfold raw1919step2 raw1919step1; decide +kernel
      have hl : raw1919step1Labels = labelEmbedding1 ∘ raw1919step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1919step1 raw1919step1Labels raw1919step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3420 node3420Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
