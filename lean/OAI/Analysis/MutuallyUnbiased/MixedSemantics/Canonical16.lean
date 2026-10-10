import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw2048 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw2048Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw2048step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2048step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw2048step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2048step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw2048step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2048 raw2048Labels = mixedMoment B node3428 node3428Labels := by
  calc
    mixedMoment B raw2048 raw2048Labels = mixedMoment B raw2048step0 raw2048step0Labels := by
      have ha : raw2048step0 = (fun i j => raw2048 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2048step0 raw2048; decide +kernel
      have hl : raw2048step0Labels = raw2048Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2048 raw2048Labels permutation155 permutation6
    mixedMoment B raw2048step0 raw2048step0Labels = mixedMoment B raw2048step1 raw2048step1Labels := by
      have ha : raw2048step1 = -raw2048step0 := by apply Matrix.ext; change ∀ i j, raw2048step1 i j = -(raw2048step0 i j); unfold raw2048step1 raw2048step0; decide +kernel
      have hl : raw2048step1Labels = raw2048step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2048step1 raw2048step1Labels = mixedMoment B raw2048step2 raw2048step2Labels := by
      have ha : raw2048step2 = raw2048step1 := by apply Matrix.ext; unfold raw2048step2 raw2048step1; decide +kernel
      have hl : raw2048step1Labels = labelEmbedding1 ∘ raw2048step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2048step1 raw2048step1Labels raw2048step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3428 node3428Labels := by rfl

def raw2049 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw2049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2049step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2049step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2049step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2049step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2049 raw2049Labels = mixedMoment B node5032 node5032Labels := by
  calc
    mixedMoment B raw2049 raw2049Labels = mixedMoment B raw2049step0 raw2049step0Labels := by
      have ha : raw2049step0 = (fun i j => raw2049 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2049step0 raw2049; decide +kernel
      have hl : raw2049step0Labels = raw2049Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2049 raw2049Labels permutation152 permutation4
    mixedMoment B raw2049step0 raw2049step0Labels = mixedMoment B raw2049step1 raw2049step1Labels := by
      have ha : raw2049step1 = raw2049step0 := by apply Matrix.ext; unfold raw2049step1 raw2049step0; decide +kernel
      have hl : raw2049step0Labels = labelEmbedding7 ∘ raw2049step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2049step0 raw2049step0Labels raw2049step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5032 node5032Labels := by rfl

def raw2050 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw2050Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2050step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2050step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2050 raw2050Labels = mixedMoment B node2424 node2424Labels := by
  calc
    mixedMoment B raw2050 raw2050Labels = mixedMoment B raw2050step0 raw2050step0Labels := by
      have ha : raw2050step0 = (fun i j => raw2050 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2050step0 raw2050; decide +kernel
      have hl : raw2050step0Labels = raw2050Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2050 raw2050Labels permutation152 permutation4
    _ = mixedMoment B node2424 node2424Labels := by rfl

def raw2051 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw2051Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw2051step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2051step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2051step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2051step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2051step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2051 raw2051Labels = mixedMoment B node3440 node3440Labels := by
  calc
    mixedMoment B raw2051 raw2051Labels = mixedMoment B raw2051step0 raw2051step0Labels := by
      have ha : raw2051step0 = (fun i j => raw2051 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2051step0 raw2051; decide +kernel
      have hl : raw2051step0Labels = raw2051Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2051 raw2051Labels permutation158 permutation6
    mixedMoment B raw2051step0 raw2051step0Labels = mixedMoment B raw2051step1 raw2051step1Labels := by
      have ha : raw2051step1 = -raw2051step0 := by apply Matrix.ext; change ∀ i j, raw2051step1 i j = -(raw2051step0 i j); unfold raw2051step1 raw2051step0; decide +kernel
      have hl : raw2051step1Labels = raw2051step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2051step1 raw2051step1Labels = mixedMoment B raw2051step2 raw2051step2Labels := by
      have ha : raw2051step2 = raw2051step1 := by apply Matrix.ext; unfold raw2051step2 raw2051step1; decide +kernel
      have hl : raw2051step1Labels = labelEmbedding1 ∘ raw2051step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2051step1 raw2051step1Labels raw2051step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3440 node3440Labels := by rfl

def raw2052 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw2052Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2052step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw2052step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2052step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw2052step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2052 raw2052Labels = mixedMoment B node5033 node5033Labels := by
  calc
    mixedMoment B raw2052 raw2052Labels = mixedMoment B raw2052step0 raw2052step0Labels := by
      have ha : raw2052step0 = (fun i j => raw2052 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2052step0 raw2052; decide +kernel
      have hl : raw2052step0Labels = raw2052Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2052 raw2052Labels permutation152 permutation4
    mixedMoment B raw2052step0 raw2052step0Labels = mixedMoment B raw2052step1 raw2052step1Labels := by
      have ha : raw2052step1 = raw2052step0 := by apply Matrix.ext; unfold raw2052step1 raw2052step0; decide +kernel
      have hl : raw2052step0Labels = labelEmbedding7 ∘ raw2052step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2052step0 raw2052step0Labels raw2052step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5033 node5033Labels := by rfl

def raw2053 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw2053Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2053step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw2053step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2053 raw2053Labels = mixedMoment B node2425 node2425Labels := by
  calc
    mixedMoment B raw2053 raw2053Labels = mixedMoment B raw2053step0 raw2053step0Labels := by
      have ha : raw2053step0 = (fun i j => raw2053 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2053step0 raw2053; decide +kernel
      have hl : raw2053step0Labels = raw2053Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2053 raw2053Labels permutation152 permutation4
    _ = mixedMoment B node2425 node2425Labels := by rfl

def raw2054 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw2054Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2054step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw2054step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2054step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw2054step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2054 raw2054Labels = mixedMoment B node3449 node3449Labels := by
  calc
    mixedMoment B raw2054 raw2054Labels = mixedMoment B raw2054step0 raw2054step0Labels := by
      have ha : raw2054step0 = (fun i j => raw2054 (permutation688 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2054step0 raw2054; decide +kernel
      have hl : raw2054step0Labels = raw2054Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2054 raw2054Labels permutation688 permutation6
    mixedMoment B raw2054step0 raw2054step0Labels = mixedMoment B raw2054step1 raw2054step1Labels := by
      have ha : raw2054step1 = raw2054step0 := by apply Matrix.ext; unfold raw2054step1 raw2054step0; decide +kernel
      have hl : raw2054step0Labels = labelEmbedding1 ∘ raw2054step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2054step0 raw2054step0Labels raw2054step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3449 node3449Labels := by rfl

def raw2055 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw2055Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2055step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw2055step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2055step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw2055step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2055 raw2055Labels = mixedMoment B node5036 node5036Labels := by
  calc
    mixedMoment B raw2055 raw2055Labels = mixedMoment B raw2055step0 raw2055step0Labels := by
      have ha : raw2055step0 = (fun i j => raw2055 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2055step0 raw2055; decide +kernel
      have hl : raw2055step0Labels = raw2055Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2055 raw2055Labels permutation152 permutation4
    mixedMoment B raw2055step0 raw2055step0Labels = mixedMoment B raw2055step1 raw2055step1Labels := by
      have ha : raw2055step1 = raw2055step0 := by apply Matrix.ext; unfold raw2055step1 raw2055step0; decide +kernel
      have hl : raw2055step0Labels = labelEmbedding7 ∘ raw2055step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2055step0 raw2055step0Labels raw2055step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5036 node5036Labels := by rfl

def raw2056 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw2056Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw2056step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2056 raw2056Labels = mixedMoment B node2428 node2428Labels := by
  calc
    mixedMoment B raw2056 raw2056Labels = mixedMoment B raw2056step0 raw2056step0Labels := by
      have ha : raw2056step0 = (fun i j => raw2056 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2056step0 raw2056; decide +kernel
      have hl : raw2056step0Labels = raw2056Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2056 raw2056Labels permutation152 permutation4
    _ = mixedMoment B node2428 node2428Labels := by rfl

def raw2057 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw2057Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw2057step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2057step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw2057step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2057step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw2057step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2057 raw2057Labels = mixedMoment B node3450 node3450Labels := by
  calc
    mixedMoment B raw2057 raw2057Labels = mixedMoment B raw2057step0 raw2057step0Labels := by
      have ha : raw2057step0 = (fun i j => raw2057 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2057step0 raw2057; decide +kernel
      have hl : raw2057step0Labels = raw2057Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2057 raw2057Labels permutation152 permutation6
    mixedMoment B raw2057step0 raw2057step0Labels = mixedMoment B raw2057step1 raw2057step1Labels := by
      have ha : raw2057step1 = -raw2057step0 := by apply Matrix.ext; change ∀ i j, raw2057step1 i j = -(raw2057step0 i j); unfold raw2057step1 raw2057step0; decide +kernel
      have hl : raw2057step1Labels = raw2057step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2057step1 raw2057step1Labels = mixedMoment B raw2057step2 raw2057step2Labels := by
      have ha : raw2057step2 = raw2057step1 := by apply Matrix.ext; unfold raw2057step2 raw2057step1; decide +kernel
      have hl : raw2057step1Labels = labelEmbedding1 ∘ raw2057step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2057step1 raw2057step1Labels raw2057step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3450 node3450Labels := by rfl

def raw2058 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw2058Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw2058step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2058step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw2058step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2058 raw2058Labels = mixedMoment B node5037 node5037Labels := by
  calc
    mixedMoment B raw2058 raw2058Labels = mixedMoment B raw2058step0 raw2058step0Labels := by
      have ha : raw2058step0 = (fun i j => raw2058 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2058step0 raw2058; decide +kernel
      have hl : raw2058step0Labels = raw2058Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2058 raw2058Labels permutation152 permutation4
    mixedMoment B raw2058step0 raw2058step0Labels = mixedMoment B raw2058step1 raw2058step1Labels := by
      have ha : raw2058step1 = raw2058step0 := by apply Matrix.ext; unfold raw2058step1 raw2058step0; decide +kernel
      have hl : raw2058step0Labels = labelEmbedding7 ∘ raw2058step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2058step0 raw2058step0Labels raw2058step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5037 node5037Labels := by rfl

def raw2059 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw2059Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2059step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw2059step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2059 raw2059Labels = mixedMoment B node2429 node2429Labels := by
  calc
    mixedMoment B raw2059 raw2059Labels = mixedMoment B raw2059step0 raw2059step0Labels := by
      have ha : raw2059step0 = (fun i j => raw2059 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2059step0 raw2059; decide +kernel
      have hl : raw2059step0Labels = raw2059Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2059 raw2059Labels permutation152 permutation4
    _ = mixedMoment B node2429 node2429Labels := by rfl

def raw2060 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw2060Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2060step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw2060step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2060step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw2060step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2060step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw2060step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2060 raw2060Labels = mixedMoment B node3455 node3455Labels := by
  calc
    mixedMoment B raw2060 raw2060Labels = mixedMoment B raw2060step0 raw2060step0Labels := by
      have ha : raw2060step0 = (fun i j => raw2060 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2060step0 raw2060; decide +kernel
      have hl : raw2060step0Labels = raw2060Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2060 raw2060Labels permutation152 permutation6
    mixedMoment B raw2060step0 raw2060step0Labels = mixedMoment B raw2060step1 raw2060step1Labels := by
      have ha : raw2060step1 = -raw2060step0 := by apply Matrix.ext; change ∀ i j, raw2060step1 i j = -(raw2060step0 i j); unfold raw2060step1 raw2060step0; decide +kernel
      have hl : raw2060step1Labels = raw2060step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2060step1 raw2060step1Labels = mixedMoment B raw2060step2 raw2060step2Labels := by
      have ha : raw2060step2 = raw2060step1 := by apply Matrix.ext; unfold raw2060step2 raw2060step1; decide +kernel
      have hl : raw2060step1Labels = labelEmbedding1 ∘ raw2060step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2060step1 raw2060step1Labels raw2060step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3455 node3455Labels := by rfl

def raw2061 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2061Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2061step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2061step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2061step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2061step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2061 raw2061Labels = mixedMoment B node5038 node5038Labels := by
  calc
    mixedMoment B raw2061 raw2061Labels = mixedMoment B raw2061step0 raw2061step0Labels := by
      have ha : raw2061step0 = (fun i j => raw2061 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2061step0 raw2061; decide +kernel
      have hl : raw2061step0Labels = raw2061Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2061 raw2061Labels permutation152 permutation4
    mixedMoment B raw2061step0 raw2061step0Labels = mixedMoment B raw2061step1 raw2061step1Labels := by
      have ha : raw2061step1 = raw2061step0 := by apply Matrix.ext; unfold raw2061step1 raw2061step0; decide +kernel
      have hl : raw2061step0Labels = labelEmbedding7 ∘ raw2061step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2061step0 raw2061step0Labels raw2061step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5038 node5038Labels := by rfl

def raw2062 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2062Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2062step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2062step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2062 raw2062Labels = mixedMoment B node2431 node2431Labels := by
  calc
    mixedMoment B raw2062 raw2062Labels = mixedMoment B raw2062step0 raw2062step0Labels := by
      have ha : raw2062step0 = (fun i j => raw2062 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2062step0 raw2062; decide +kernel
      have hl : raw2062step0Labels = raw2062Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2062 raw2062Labels permutation152 permutation4
    _ = mixedMoment B node2431 node2431Labels := by rfl

def raw2063 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2063Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2063step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw2063step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2063step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw2063step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2063step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw2063step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2063 raw2063Labels = mixedMoment B node3453 node3453Labels := by
  calc
    mixedMoment B raw2063 raw2063Labels = mixedMoment B raw2063step0 raw2063step0Labels := by
      have ha : raw2063step0 = (fun i j => raw2063 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2063step0 raw2063; decide +kernel
      have hl : raw2063step0Labels = raw2063Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2063 raw2063Labels permutation154 permutation6
    mixedMoment B raw2063step0 raw2063step0Labels = mixedMoment B raw2063step1 raw2063step1Labels := by
      have ha : raw2063step1 = -raw2063step0 := by apply Matrix.ext; change ∀ i j, raw2063step1 i j = -(raw2063step0 i j); unfold raw2063step1 raw2063step0; decide +kernel
      have hl : raw2063step1Labels = raw2063step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2063step1 raw2063step1Labels = mixedMoment B raw2063step2 raw2063step2Labels := by
      have ha : raw2063step2 = raw2063step1 := by apply Matrix.ext; unfold raw2063step2 raw2063step1; decide +kernel
      have hl : raw2063step1Labels = labelEmbedding1 ∘ raw2063step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2063step1 raw2063step1Labels raw2063step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3453 node3453Labels := by rfl

def raw2064 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2064Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2064step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2064step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2064step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2064step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2064 raw2064Labels = mixedMoment B node5039 node5039Labels := by
  calc
    mixedMoment B raw2064 raw2064Labels = mixedMoment B raw2064step0 raw2064step0Labels := by
      have ha : raw2064step0 = (fun i j => raw2064 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2064step0 raw2064; decide +kernel
      have hl : raw2064step0Labels = raw2064Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2064 raw2064Labels permutation152 permutation4
    mixedMoment B raw2064step0 raw2064step0Labels = mixedMoment B raw2064step1 raw2064step1Labels := by
      have ha : raw2064step1 = raw2064step0 := by apply Matrix.ext; unfold raw2064step1 raw2064step0; decide +kernel
      have hl : raw2064step0Labels = labelEmbedding7 ∘ raw2064step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2064step0 raw2064step0Labels raw2064step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5039 node5039Labels := by rfl

def raw2065 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2065Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2065step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2065step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2065 raw2065Labels = mixedMoment B node2432 node2432Labels := by
  calc
    mixedMoment B raw2065 raw2065Labels = mixedMoment B raw2065step0 raw2065step0Labels := by
      have ha : raw2065step0 = (fun i j => raw2065 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2065step0 raw2065; decide +kernel
      have hl : raw2065step0Labels = raw2065Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2065 raw2065Labels permutation152 permutation4
    _ = mixedMoment B node2432 node2432Labels := by rfl

def raw2066 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2066Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw2066step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2066step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw2066step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2066step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw2066step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2066 raw2066Labels = mixedMoment B node3456 node3456Labels := by
  calc
    mixedMoment B raw2066 raw2066Labels = mixedMoment B raw2066step0 raw2066step0Labels := by
      have ha : raw2066step0 = (fun i j => raw2066 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2066step0 raw2066; decide +kernel
      have hl : raw2066step0Labels = raw2066Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2066 raw2066Labels permutation152 permutation6
    mixedMoment B raw2066step0 raw2066step0Labels = mixedMoment B raw2066step1 raw2066step1Labels := by
      have ha : raw2066step1 = -raw2066step0 := by apply Matrix.ext; change ∀ i j, raw2066step1 i j = -(raw2066step0 i j); unfold raw2066step1 raw2066step0; decide +kernel
      have hl : raw2066step1Labels = raw2066step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2066step1 raw2066step1Labels = mixedMoment B raw2066step2 raw2066step2Labels := by
      have ha : raw2066step2 = raw2066step1 := by apply Matrix.ext; unfold raw2066step2 raw2066step1; decide +kernel
      have hl : raw2066step1Labels = labelEmbedding1 ∘ raw2066step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2066step1 raw2066step1Labels raw2066step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3456 node3456Labels := by rfl

def raw2067 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 2, -2], ![0, 2, -2]]
def raw2067Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw2067step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2067step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw2067step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2067 raw2067Labels = mixedMoment B node5045 node5045Labels := by
  calc
    mixedMoment B raw2067 raw2067Labels = mixedMoment B raw2067step0 raw2067step0Labels := by
      have ha : raw2067step0 = (fun i j => raw2067 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2067step0 raw2067; decide +kernel
      have hl : raw2067step0Labels = raw2067Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2067 raw2067Labels permutation152 permutation4
    mixedMoment B raw2067step0 raw2067step0Labels = mixedMoment B raw2067step1 raw2067step1Labels := by
      have ha : raw2067step1 = raw2067step0 := by apply Matrix.ext; unfold raw2067step1 raw2067step0; decide +kernel
      have hl : raw2067step0Labels = labelEmbedding7 ∘ raw2067step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2067step0 raw2067step0Labels raw2067step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5045 node5045Labels := by rfl

def raw2068 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 2, -2], ![0, 2, -2]]
def raw2068Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw2068step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2068 raw2068Labels = mixedMoment B node2444 node2444Labels := by
  calc
    mixedMoment B raw2068 raw2068Labels = mixedMoment B raw2068step0 raw2068step0Labels := by
      have ha : raw2068step0 = (fun i j => raw2068 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2068step0 raw2068; decide +kernel
      have hl : raw2068step0Labels = raw2068Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2068 raw2068Labels permutation152 permutation4
    _ = mixedMoment B node2444 node2444Labels := by rfl

def raw2069 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 2, -2], ![0, 2, -2]]
def raw2069Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw2069step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2069step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw2069step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2069step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw2069step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2069 raw2069Labels = mixedMoment B node3362 node3362Labels := by
  calc
    mixedMoment B raw2069 raw2069Labels = mixedMoment B raw2069step0 raw2069step0Labels := by
      have ha : raw2069step0 = (fun i j => raw2069 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2069step0 raw2069; decide +kernel
      have hl : raw2069step0Labels = raw2069Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2069 raw2069Labels permutation176 permutation6
    mixedMoment B raw2069step0 raw2069step0Labels = mixedMoment B raw2069step1 raw2069step1Labels := by
      have ha : raw2069step1 = -raw2069step0 := by apply Matrix.ext; change ∀ i j, raw2069step1 i j = -(raw2069step0 i j); unfold raw2069step1 raw2069step0; decide +kernel
      have hl : raw2069step1Labels = raw2069step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2069step1 raw2069step1Labels = mixedMoment B raw2069step2 raw2069step2Labels := by
      have ha : raw2069step2 = raw2069step1 := by apply Matrix.ext; unfold raw2069step2 raw2069step1; decide +kernel
      have hl : raw2069step1Labels = labelEmbedding1 ∘ raw2069step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2069step1 raw2069step1Labels raw2069step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3362 node3362Labels := by rfl

def raw2070 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 1, -2], ![0, 2, -2]]
def raw2070Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw2070step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2070step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw2070step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2070 raw2070Labels = mixedMoment B node5046 node5046Labels := by
  calc
    mixedMoment B raw2070 raw2070Labels = mixedMoment B raw2070step0 raw2070step0Labels := by
      have ha : raw2070step0 = (fun i j => raw2070 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2070step0 raw2070; decide +kernel
      have hl : raw2070step0Labels = raw2070Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2070 raw2070Labels permutation152 permutation4
    mixedMoment B raw2070step0 raw2070step0Labels = mixedMoment B raw2070step1 raw2070step1Labels := by
      have ha : raw2070step1 = raw2070step0 := by apply Matrix.ext; unfold raw2070step1 raw2070step0; decide +kernel
      have hl : raw2070step0Labels = labelEmbedding7 ∘ raw2070step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2070step0 raw2070step0Labels raw2070step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5046 node5046Labels := by rfl

def raw2071 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 1, -2], ![0, 2, -2]]
def raw2071Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw2071step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2071 raw2071Labels = mixedMoment B node2446 node2446Labels := by
  calc
    mixedMoment B raw2071 raw2071Labels = mixedMoment B raw2071step0 raw2071step0Labels := by
      have ha : raw2071step0 = (fun i j => raw2071 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2071step0 raw2071; decide +kernel
      have hl : raw2071step0Labels = raw2071Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2071 raw2071Labels permutation152 permutation4
    _ = mixedMoment B node2446 node2446Labels := by rfl

def raw2072 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 1, -2], ![0, 2, -2]]
def raw2072Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![1, 0, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw2072step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2072step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2072step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2072step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2072step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2072 raw2072Labels = mixedMoment B node3363 node3363Labels := by
  calc
    mixedMoment B raw2072 raw2072Labels = mixedMoment B raw2072step0 raw2072step0Labels := by
      have ha : raw2072step0 = (fun i j => raw2072 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2072step0 raw2072; decide +kernel
      have hl : raw2072step0Labels = raw2072Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2072 raw2072Labels permutation176 permutation6
    mixedMoment B raw2072step0 raw2072step0Labels = mixedMoment B raw2072step1 raw2072step1Labels := by
      have ha : raw2072step1 = -raw2072step0 := by apply Matrix.ext; change ∀ i j, raw2072step1 i j = -(raw2072step0 i j); unfold raw2072step1 raw2072step0; decide +kernel
      have hl : raw2072step1Labels = raw2072step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2072step1 raw2072step1Labels = mixedMoment B raw2072step2 raw2072step2Labels := by
      have ha : raw2072step2 = raw2072step1 := by apply Matrix.ext; unfold raw2072step2 raw2072step1; decide +kernel
      have hl : raw2072step1Labels = labelEmbedding1 ∘ raw2072step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2072step1 raw2072step1Labels raw2072step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3363 node3363Labels := by rfl

def raw2073 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw2073Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw2073step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2073step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw2073step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2073 raw2073Labels = mixedMoment B node5047 node5047Labels := by
  calc
    mixedMoment B raw2073 raw2073Labels = mixedMoment B raw2073step0 raw2073step0Labels := by
      have ha : raw2073step0 = (fun i j => raw2073 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2073step0 raw2073; decide +kernel
      have hl : raw2073step0Labels = raw2073Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2073 raw2073Labels permutation152 permutation4
    mixedMoment B raw2073step0 raw2073step0Labels = mixedMoment B raw2073step1 raw2073step1Labels := by
      have ha : raw2073step1 = raw2073step0 := by apply Matrix.ext; unfold raw2073step1 raw2073step0; decide +kernel
      have hl : raw2073step0Labels = labelEmbedding7 ∘ raw2073step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2073step0 raw2073step0Labels raw2073step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5047 node5047Labels := by rfl

def raw2074 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw2074Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw2074step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2074 raw2074Labels = mixedMoment B node2449 node2449Labels := by
  calc
    mixedMoment B raw2074 raw2074Labels = mixedMoment B raw2074step0 raw2074step0Labels := by
      have ha : raw2074step0 = (fun i j => raw2074 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2074step0 raw2074; decide +kernel
      have hl : raw2074step0Labels = raw2074Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2074 raw2074Labels permutation152 permutation4
    _ = mixedMoment B node2449 node2449Labels := by rfl

def raw2075 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw2075Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw2075step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2075step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw2075step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2075 raw2075Labels = mixedMoment B node3432 node3432Labels := by
  calc
    mixedMoment B raw2075 raw2075Labels = mixedMoment B raw2075step0 raw2075step0Labels := by
      have ha : raw2075step0 = (fun i j => raw2075 (permutation688 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2075step0 raw2075; decide +kernel
      have hl : raw2075step0Labels = raw2075Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2075 raw2075Labels permutation688 permutation6
    mixedMoment B raw2075step0 raw2075step0Labels = mixedMoment B raw2075step1 raw2075step1Labels := by
      have ha : raw2075step1 = raw2075step0 := by apply Matrix.ext; unfold raw2075step1 raw2075step0; decide +kernel
      have hl : raw2075step0Labels = labelEmbedding1 ∘ raw2075step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2075step0 raw2075step0Labels raw2075step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3432 node3432Labels := by rfl

def raw2076 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw2076Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2076step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2076step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2076step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2076step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2076 raw2076Labels = mixedMoment B node5050 node5050Labels := by
  calc
    mixedMoment B raw2076 raw2076Labels = mixedMoment B raw2076step0 raw2076step0Labels := by
      have ha : raw2076step0 = (fun i j => raw2076 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2076step0 raw2076; decide +kernel
      have hl : raw2076step0Labels = raw2076Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2076 raw2076Labels permutation152 permutation4
    mixedMoment B raw2076step0 raw2076step0Labels = mixedMoment B raw2076step1 raw2076step1Labels := by
      have ha : raw2076step1 = raw2076step0 := by apply Matrix.ext; unfold raw2076step1 raw2076step0; decide +kernel
      have hl : raw2076step0Labels = labelEmbedding7 ∘ raw2076step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2076step0 raw2076step0Labels raw2076step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5050 node5050Labels := by rfl

def raw2077 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw2077Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2077step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2077step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2077 raw2077Labels = mixedMoment B node2452 node2452Labels := by
  calc
    mixedMoment B raw2077 raw2077Labels = mixedMoment B raw2077step0 raw2077step0Labels := by
      have ha : raw2077step0 = (fun i j => raw2077 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2077step0 raw2077; decide +kernel
      have hl : raw2077step0Labels = raw2077Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2077 raw2077Labels permutation152 permutation4
    _ = mixedMoment B node2452 node2452Labels := by rfl

def raw2078 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw2078Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2078step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw2078step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2078step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2078step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2078step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2078step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2078 raw2078Labels = mixedMoment B node3433 node3433Labels := by
  calc
    mixedMoment B raw2078 raw2078Labels = mixedMoment B raw2078step0 raw2078step0Labels := by
      have ha : raw2078step0 = (fun i j => raw2078 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2078step0 raw2078; decide +kernel
      have hl : raw2078step0Labels = raw2078Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2078 raw2078Labels permutation152 permutation6
    mixedMoment B raw2078step0 raw2078step0Labels = mixedMoment B raw2078step1 raw2078step1Labels := by
      have ha : raw2078step1 = -raw2078step0 := by apply Matrix.ext; change ∀ i j, raw2078step1 i j = -(raw2078step0 i j); unfold raw2078step1 raw2078step0; decide +kernel
      have hl : raw2078step1Labels = raw2078step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2078step1 raw2078step1Labels = mixedMoment B raw2078step2 raw2078step2Labels := by
      have ha : raw2078step2 = raw2078step1 := by apply Matrix.ext; unfold raw2078step2 raw2078step1; decide +kernel
      have hl : raw2078step1Labels = labelEmbedding1 ∘ raw2078step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2078step1 raw2078step1Labels raw2078step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3433 node3433Labels := by rfl

def raw2079 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw2079Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw2079step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2079step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw2079step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2079 raw2079Labels = mixedMoment B node5055 node5055Labels := by
  calc
    mixedMoment B raw2079 raw2079Labels = mixedMoment B raw2079step0 raw2079step0Labels := by
      have ha : raw2079step0 = (fun i j => raw2079 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2079step0 raw2079; decide +kernel
      have hl : raw2079step0Labels = raw2079Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2079 raw2079Labels permutation152 permutation4
    mixedMoment B raw2079step0 raw2079step0Labels = mixedMoment B raw2079step1 raw2079step1Labels := by
      have ha : raw2079step1 = raw2079step0 := by apply Matrix.ext; unfold raw2079step1 raw2079step0; decide +kernel
      have hl : raw2079step0Labels = labelEmbedding7 ∘ raw2079step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2079step0 raw2079step0Labels raw2079step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5055 node5055Labels := by rfl

def raw2080 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw2080Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw2080step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2080 raw2080Labels = mixedMoment B node2458 node2458Labels := by
  calc
    mixedMoment B raw2080 raw2080Labels = mixedMoment B raw2080step0 raw2080step0Labels := by
      have ha : raw2080step0 = (fun i j => raw2080 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2080step0 raw2080; decide +kernel
      have hl : raw2080step0Labels = raw2080Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2080 raw2080Labels permutation152 permutation4
    _ = mixedMoment B node2458 node2458Labels := by rfl

def raw2081 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw2081Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw2081step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2081step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw2081step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2081 raw2081Labels = mixedMoment B node2458 node2458Labels := by
  calc
    mixedMoment B raw2081 raw2081Labels = mixedMoment B raw2081step0 raw2081step0Labels := by
      have ha : raw2081step0 = (fun i j => raw2081 (permutation688 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2081step0 raw2081; decide +kernel
      have hl : raw2081step0Labels = raw2081Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2081 raw2081Labels permutation688 permutation6
    mixedMoment B raw2081step0 raw2081step0Labels = mixedMoment B raw2081step1 raw2081step1Labels := by
      have ha : raw2081step1 = raw2081step0 := by apply Matrix.ext; unfold raw2081step1 raw2081step0; decide +kernel
      have hl : raw2081step0Labels = labelEmbedding1 ∘ raw2081step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2081step0 raw2081step0Labels raw2081step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2458 node2458Labels := by rfl

def raw2082 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw2082Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2082step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2082step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2082step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2082step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2082 raw2082Labels = mixedMoment B node5056 node5056Labels := by
  calc
    mixedMoment B raw2082 raw2082Labels = mixedMoment B raw2082step0 raw2082step0Labels := by
      have ha : raw2082step0 = (fun i j => raw2082 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2082step0 raw2082; decide +kernel
      have hl : raw2082step0Labels = raw2082Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2082 raw2082Labels permutation152 permutation4
    mixedMoment B raw2082step0 raw2082step0Labels = mixedMoment B raw2082step1 raw2082step1Labels := by
      have ha : raw2082step1 = raw2082step0 := by apply Matrix.ext; unfold raw2082step1 raw2082step0; decide +kernel
      have hl : raw2082step0Labels = labelEmbedding7 ∘ raw2082step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2082step0 raw2082step0Labels raw2082step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5056 node5056Labels := by rfl

def raw2083 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw2083Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2083step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw2083step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2083 raw2083Labels = mixedMoment B node2459 node2459Labels := by
  calc
    mixedMoment B raw2083 raw2083Labels = mixedMoment B raw2083step0 raw2083step0Labels := by
      have ha : raw2083step0 = (fun i j => raw2083 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2083step0 raw2083; decide +kernel
      have hl : raw2083step0Labels = raw2083Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2083 raw2083Labels permutation152 permutation4
    _ = mixedMoment B node2459 node2459Labels := by rfl

def raw2084 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw2084Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2084step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw2084step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2084step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2084step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2084step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2084step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2084 raw2084Labels = mixedMoment B node3429 node3429Labels := by
  calc
    mixedMoment B raw2084 raw2084Labels = mixedMoment B raw2084step0 raw2084step0Labels := by
      have ha : raw2084step0 = (fun i j => raw2084 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2084step0 raw2084; decide +kernel
      have hl : raw2084step0Labels = raw2084Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2084 raw2084Labels permutation152 permutation6
    mixedMoment B raw2084step0 raw2084step0Labels = mixedMoment B raw2084step1 raw2084step1Labels := by
      have ha : raw2084step1 = -raw2084step0 := by apply Matrix.ext; change ∀ i j, raw2084step1 i j = -(raw2084step0 i j); unfold raw2084step1 raw2084step0; decide +kernel
      have hl : raw2084step1Labels = raw2084step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2084step1 raw2084step1Labels = mixedMoment B raw2084step2 raw2084step2Labels := by
      have ha : raw2084step2 = raw2084step1 := by apply Matrix.ext; unfold raw2084step2 raw2084step1; decide +kernel
      have hl : raw2084step1Labels = labelEmbedding1 ∘ raw2084step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2084step1 raw2084step1Labels raw2084step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3429 node3429Labels := by rfl

def raw2085 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw2085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2085step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2085step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2085step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2085step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2085 raw2085Labels = mixedMoment B node5059 node5059Labels := by
  calc
    mixedMoment B raw2085 raw2085Labels = mixedMoment B raw2085step0 raw2085step0Labels := by
      have ha : raw2085step0 = (fun i j => raw2085 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2085step0 raw2085; decide +kernel
      have hl : raw2085step0Labels = raw2085Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2085 raw2085Labels permutation152 permutation4
    mixedMoment B raw2085step0 raw2085step0Labels = mixedMoment B raw2085step1 raw2085step1Labels := by
      have ha : raw2085step1 = raw2085step0 := by apply Matrix.ext; unfold raw2085step1 raw2085step0; decide +kernel
      have hl : raw2085step0Labels = labelEmbedding7 ∘ raw2085step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2085step0 raw2085step0Labels raw2085step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5059 node5059Labels := by rfl

def raw2086 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw2086Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2086step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2086 raw2086Labels = mixedMoment B node2462 node2462Labels := by
  calc
    mixedMoment B raw2086 raw2086Labels = mixedMoment B raw2086step0 raw2086step0Labels := by
      have ha : raw2086step0 = (fun i j => raw2086 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2086step0 raw2086; decide +kernel
      have hl : raw2086step0Labels = raw2086Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2086 raw2086Labels permutation152 permutation4
    _ = mixedMoment B node2462 node2462Labels := by rfl

def raw2087 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw2087Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw2087step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2087step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2087step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2087step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2087step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2087 raw2087Labels = mixedMoment B node3436 node3436Labels := by
  calc
    mixedMoment B raw2087 raw2087Labels = mixedMoment B raw2087step0 raw2087step0Labels := by
      have ha : raw2087step0 = (fun i j => raw2087 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2087step0 raw2087; decide +kernel
      have hl : raw2087step0Labels = raw2087Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2087 raw2087Labels permutation153 permutation6
    mixedMoment B raw2087step0 raw2087step0Labels = mixedMoment B raw2087step1 raw2087step1Labels := by
      have ha : raw2087step1 = -raw2087step0 := by apply Matrix.ext; change ∀ i j, raw2087step1 i j = -(raw2087step0 i j); unfold raw2087step1 raw2087step0; decide +kernel
      have hl : raw2087step1Labels = raw2087step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2087step1 raw2087step1Labels = mixedMoment B raw2087step2 raw2087step2Labels := by
      have ha : raw2087step2 = raw2087step1 := by apply Matrix.ext; unfold raw2087step2 raw2087step1; decide +kernel
      have hl : raw2087step1Labels = labelEmbedding1 ∘ raw2087step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2087step1 raw2087step1Labels raw2087step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3436 node3436Labels := by rfl

def raw2088 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2088step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2088step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2088step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2088step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2088 raw2088Labels = mixedMoment B node5070 node5070Labels := by
  calc
    mixedMoment B raw2088 raw2088Labels = mixedMoment B raw2088step0 raw2088step0Labels := by
      have ha : raw2088step0 = (fun i j => raw2088 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2088step0 raw2088; decide +kernel
      have hl : raw2088step0Labels = raw2088Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2088 raw2088Labels permutation152 permutation4
    mixedMoment B raw2088step0 raw2088step0Labels = mixedMoment B raw2088step1 raw2088step1Labels := by
      have ha : raw2088step1 = raw2088step0 := by apply Matrix.ext; unfold raw2088step1 raw2088step0; decide +kernel
      have hl : raw2088step0Labels = labelEmbedding7 ∘ raw2088step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2088step0 raw2088step0Labels raw2088step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5070 node5070Labels := by rfl

def raw2089 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2089Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2089step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2089step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2089 raw2089Labels = mixedMoment B node2477 node2477Labels := by
  calc
    mixedMoment B raw2089 raw2089Labels = mixedMoment B raw2089step0 raw2089step0Labels := by
      have ha : raw2089step0 = (fun i j => raw2089 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2089step0 raw2089; decide +kernel
      have hl : raw2089step0Labels = raw2089Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2089 raw2089Labels permutation152 permutation4
    _ = mixedMoment B node2477 node2477Labels := by rfl

def raw2090 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2090Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2090step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw2090step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2090step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2090step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2090step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2090step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2090 raw2090Labels = mixedMoment B node3444 node3444Labels := by
  calc
    mixedMoment B raw2090 raw2090Labels = mixedMoment B raw2090step0 raw2090step0Labels := by
      have ha : raw2090step0 = (fun i j => raw2090 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2090step0 raw2090; decide +kernel
      have hl : raw2090step0Labels = raw2090Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2090 raw2090Labels permutation158 permutation6
    mixedMoment B raw2090step0 raw2090step0Labels = mixedMoment B raw2090step1 raw2090step1Labels := by
      have ha : raw2090step1 = -raw2090step0 := by apply Matrix.ext; change ∀ i j, raw2090step1 i j = -(raw2090step0 i j); unfold raw2090step1 raw2090step0; decide +kernel
      have hl : raw2090step1Labels = raw2090step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2090step1 raw2090step1Labels = mixedMoment B raw2090step2 raw2090step2Labels := by
      have ha : raw2090step2 = raw2090step1 := by apply Matrix.ext; unfold raw2090step2 raw2090step1; decide +kernel
      have hl : raw2090step1Labels = labelEmbedding1 ∘ raw2090step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2090step1 raw2090step1Labels raw2090step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3444 node3444Labels := by rfl

def raw2091 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2091step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2091step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2091step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2091step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2091 raw2091Labels = mixedMoment B node5072 node5072Labels := by
  calc
    mixedMoment B raw2091 raw2091Labels = mixedMoment B raw2091step0 raw2091step0Labels := by
      have ha : raw2091step0 = (fun i j => raw2091 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2091step0 raw2091; decide +kernel
      have hl : raw2091step0Labels = raw2091Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2091 raw2091Labels permutation152 permutation4
    mixedMoment B raw2091step0 raw2091step0Labels = mixedMoment B raw2091step1 raw2091step1Labels := by
      have ha : raw2091step1 = raw2091step0 := by apply Matrix.ext; unfold raw2091step1 raw2091step0; decide +kernel
      have hl : raw2091step0Labels = labelEmbedding7 ∘ raw2091step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2091step0 raw2091step0Labels raw2091step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5072 node5072Labels := by rfl

def raw2092 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2092Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2092step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2092step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2092 raw2092Labels = mixedMoment B node2479 node2479Labels := by
  calc
    mixedMoment B raw2092 raw2092Labels = mixedMoment B raw2092step0 raw2092step0Labels := by
      have ha : raw2092step0 = (fun i j => raw2092 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2092step0 raw2092; decide +kernel
      have hl : raw2092step0Labels = raw2092Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2092 raw2092Labels permutation152 permutation4
    _ = mixedMoment B node2479 node2479Labels := by rfl

def raw2093 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2093Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2093step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw2093step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2093step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2093step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2093step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2093step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2093 raw2093Labels = mixedMoment B node3459 node3459Labels := by
  calc
    mixedMoment B raw2093 raw2093Labels = mixedMoment B raw2093step0 raw2093step0Labels := by
      have ha : raw2093step0 = (fun i j => raw2093 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2093step0 raw2093; decide +kernel
      have hl : raw2093step0Labels = raw2093Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2093 raw2093Labels permutation160 permutation6
    mixedMoment B raw2093step0 raw2093step0Labels = mixedMoment B raw2093step1 raw2093step1Labels := by
      have ha : raw2093step1 = -raw2093step0 := by apply Matrix.ext; change ∀ i j, raw2093step1 i j = -(raw2093step0 i j); unfold raw2093step1 raw2093step0; decide +kernel
      have hl : raw2093step1Labels = raw2093step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2093step1 raw2093step1Labels = mixedMoment B raw2093step2 raw2093step2Labels := by
      have ha : raw2093step2 = raw2093step1 := by apply Matrix.ext; unfold raw2093step2 raw2093step1; decide +kernel
      have hl : raw2093step1Labels = labelEmbedding1 ∘ raw2093step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2093step1 raw2093step1Labels raw2093step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3459 node3459Labels := by rfl

def raw2094 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2094Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2094step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2094step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2094step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2094 raw2094Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw2094 raw2094Labels = mixedMoment B raw2094step0 raw2094step0Labels := by
      have ha : raw2094step0 = (fun i j => raw2094 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2094step0 raw2094; decide +kernel
      have hl : raw2094step0Labels = raw2094Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2094 raw2094Labels permutation152 permutation4
    mixedMoment B raw2094step0 raw2094step0Labels = mixedMoment B raw2094step1 raw2094step1Labels := by
      have ha : raw2094step1 = raw2094step0 := by apply Matrix.ext; unfold raw2094step1 raw2094step0; decide +kernel
      have hl : raw2094step0Labels = labelEmbedding7 ∘ raw2094step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2094step0 raw2094step0Labels raw2094step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5073 node5073Labels := by rfl

def raw2095 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2095Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2095step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2095step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2095 raw2095Labels = mixedMoment B node2480 node2480Labels := by
  calc
    mixedMoment B raw2095 raw2095Labels = mixedMoment B raw2095step0 raw2095step0Labels := by
      have ha : raw2095step0 = (fun i j => raw2095 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2095step0 raw2095; decide +kernel
      have hl : raw2095step0Labels = raw2095Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2095 raw2095Labels permutation152 permutation4
    _ = mixedMoment B node2480 node2480Labels := by rfl

def raw2096 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2096Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2096step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw2096step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2096step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2096step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2096step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2096step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2096 raw2096Labels = mixedMoment B node3467 node3467Labels := by
  calc
    mixedMoment B raw2096 raw2096Labels = mixedMoment B raw2096step0 raw2096step0Labels := by
      have ha : raw2096step0 = (fun i j => raw2096 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2096step0 raw2096; decide +kernel
      have hl : raw2096step0Labels = raw2096Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2096 raw2096Labels permutation158 permutation6
    mixedMoment B raw2096step0 raw2096step0Labels = mixedMoment B raw2096step1 raw2096step1Labels := by
      have ha : raw2096step1 = -raw2096step0 := by apply Matrix.ext; change ∀ i j, raw2096step1 i j = -(raw2096step0 i j); unfold raw2096step1 raw2096step0; decide +kernel
      have hl : raw2096step1Labels = raw2096step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2096step1 raw2096step1Labels = mixedMoment B raw2096step2 raw2096step2Labels := by
      have ha : raw2096step2 = raw2096step1 := by apply Matrix.ext; unfold raw2096step2 raw2096step1; decide +kernel
      have hl : raw2096step1Labels = labelEmbedding1 ∘ raw2096step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2096step1 raw2096step1Labels raw2096step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3467 node3467Labels := by rfl

def raw2097 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw2097Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw2097step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2097step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw2097step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2097 raw2097Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw2097 raw2097Labels = mixedMoment B raw2097step0 raw2097step0Labels := by
      have ha : raw2097step0 = (fun i j => raw2097 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2097step0 raw2097; decide +kernel
      have hl : raw2097step0Labels = raw2097Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2097 raw2097Labels permutation32 permutation4
    mixedMoment B raw2097step0 raw2097step0Labels = mixedMoment B raw2097step1 raw2097step1Labels := by
      have ha : raw2097step1 = raw2097step0 := by apply Matrix.ext; unfold raw2097step1 raw2097step0; decide +kernel
      have hl : raw2097step0Labels = labelEmbedding7 ∘ raw2097step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2097step0 raw2097step0Labels raw2097step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5075 node5075Labels := by rfl

def raw2098 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw2098Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw2098step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2098 raw2098Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw2098 raw2098Labels = mixedMoment B raw2098step0 raw2098step0Labels := by
      have ha : raw2098step0 = (fun i j => raw2098 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2098step0 raw2098; decide +kernel
      have hl : raw2098step0Labels = raw2098Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2098 raw2098Labels permutation32 permutation4
    _ = mixedMoment B node2482 node2482Labels := by rfl

def raw2099 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw2099Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw2099step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw2099step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2099step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw2099step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2099 raw2099Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw2099 raw2099Labels = mixedMoment B raw2099step0 raw2099step0Labels := by
      have ha : raw2099step0 = (fun i j => raw2099 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2099step0 raw2099; decide +kernel
      have hl : raw2099step0Labels = raw2099Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2099 raw2099Labels permutation34 permutation6
    mixedMoment B raw2099step0 raw2099step0Labels = mixedMoment B raw2099step1 raw2099step1Labels := by
      have ha : raw2099step1 = -raw2099step0 := by apply Matrix.ext; change ∀ i j, raw2099step1 i j = -(raw2099step0 i j); unfold raw2099step1 raw2099step0; decide +kernel
      have hl : raw2099step1Labels = raw2099step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2099step1 raw2099step1Labels = mixedMoment B raw2099step2 raw2099step2Labels := by
      have ha : raw2099step2 = raw2099step1 := by apply Matrix.ext; unfold raw2099step2 raw2099step1; decide +kernel
      have hl : raw2099step1Labels = labelEmbedding1 ∘ raw2099step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2099step1 raw2099step1Labels raw2099step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3468 node3468Labels := by rfl

def raw2100 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2100step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2100step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2100step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2100step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2100 raw2100Labels = mixedMoment B node5076 node5076Labels := by
  calc
    mixedMoment B raw2100 raw2100Labels = mixedMoment B raw2100step0 raw2100step0Labels := by
      have ha : raw2100step0 = (fun i j => raw2100 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2100step0 raw2100; decide +kernel
      have hl : raw2100step0Labels = raw2100Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2100 raw2100Labels permutation152 permutation4
    mixedMoment B raw2100step0 raw2100step0Labels = mixedMoment B raw2100step1 raw2100step1Labels := by
      have ha : raw2100step1 = raw2100step0 := by apply Matrix.ext; unfold raw2100step1 raw2100step0; decide +kernel
      have hl : raw2100step0Labels = labelEmbedding7 ∘ raw2100step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2100step0 raw2100step0Labels raw2100step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5076 node5076Labels := by rfl

def raw2101 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2101Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2101step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2101step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2101 raw2101Labels = mixedMoment B node2483 node2483Labels := by
  calc
    mixedMoment B raw2101 raw2101Labels = mixedMoment B raw2101step0 raw2101step0Labels := by
      have ha : raw2101step0 = (fun i j => raw2101 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2101step0 raw2101; decide +kernel
      have hl : raw2101step0Labels = raw2101Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2101 raw2101Labels permutation152 permutation4
    _ = mixedMoment B node2483 node2483Labels := by rfl

def raw2102 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2102Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw2102step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2102step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2102step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2102step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2102step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2102 raw2102Labels = mixedMoment B node3477 node3477Labels := by
  calc
    mixedMoment B raw2102 raw2102Labels = mixedMoment B raw2102step0 raw2102step0Labels := by
      have ha : raw2102step0 = (fun i j => raw2102 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2102step0 raw2102; decide +kernel
      have hl : raw2102step0Labels = raw2102Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2102 raw2102Labels permutation170 permutation6
    mixedMoment B raw2102step0 raw2102step0Labels = mixedMoment B raw2102step1 raw2102step1Labels := by
      have ha : raw2102step1 = -raw2102step0 := by apply Matrix.ext; change ∀ i j, raw2102step1 i j = -(raw2102step0 i j); unfold raw2102step1 raw2102step0; decide +kernel
      have hl : raw2102step1Labels = raw2102step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2102step1 raw2102step1Labels = mixedMoment B raw2102step2 raw2102step2Labels := by
      have ha : raw2102step2 = raw2102step1 := by apply Matrix.ext; unfold raw2102step2 raw2102step1; decide +kernel
      have hl : raw2102step1Labels = labelEmbedding1 ∘ raw2102step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2102step1 raw2102step1Labels raw2102step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3477 node3477Labels := by rfl

def raw2103 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw2103Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw2103step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw2103step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2103 raw2103Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw2103 raw2103Labels = mixedMoment B raw2103step0 raw2103step0Labels := by
      have ha : raw2103step0 = (fun i j => raw2103 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2103step0 raw2103; decide +kernel
      have hl : raw2103step0Labels = raw2103Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2103 raw2103Labels permutation32 permutation4
    mixedMoment B raw2103step0 raw2103step0Labels = mixedMoment B raw2103step1 raw2103step1Labels := by
      have ha : raw2103step1 = raw2103step0 := by apply Matrix.ext; unfold raw2103step1 raw2103step0; decide +kernel
      have hl : raw2103step0Labels = labelEmbedding7 ∘ raw2103step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2103step0 raw2103step0Labels raw2103step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw2104 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw2104Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw2104step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2104 raw2104Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw2104 raw2104Labels = mixedMoment B raw2104step0 raw2104step0Labels := by
      have ha : raw2104step0 = (fun i j => raw2104 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2104step0 raw2104; decide +kernel
      have hl : raw2104step0Labels = raw2104Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2104 raw2104Labels permutation32 permutation4
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw2105 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw2105Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw2105step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw2105step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2105step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw2105step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2105 raw2105Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw2105 raw2105Labels = mixedMoment B raw2105step0 raw2105step0Labels := by
      have ha : raw2105step0 = (fun i j => raw2105 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2105step0 raw2105; decide +kernel
      have hl : raw2105step0Labels = raw2105Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2105 raw2105Labels permutation32 permutation6
    mixedMoment B raw2105step0 raw2105step0Labels = mixedMoment B raw2105step1 raw2105step1Labels := by
      have ha : raw2105step1 = -raw2105step0 := by apply Matrix.ext; change ∀ i j, raw2105step1 i j = -(raw2105step0 i j); unfold raw2105step1 raw2105step0; decide +kernel
      have hl : raw2105step1Labels = raw2105step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2105step1 raw2105step1Labels = mixedMoment B raw2105step2 raw2105step2Labels := by
      have ha : raw2105step2 = raw2105step1 := by apply Matrix.ext; unfold raw2105step2 raw2105step1; decide +kernel
      have hl : raw2105step1Labels = labelEmbedding1 ∘ raw2105step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2105step1 raw2105step1Labels raw2105step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3481 node3481Labels := by rfl

def raw2106 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2106Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2106step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2106step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2106 raw2106Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw2106 raw2106Labels = mixedMoment B raw2106step0 raw2106step0Labels := by
      have ha : raw2106step0 = (fun i j => raw2106 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2106step0 raw2106; decide +kernel
      have hl : raw2106step0Labels = raw2106Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2106 raw2106Labels permutation32 permutation4
    mixedMoment B raw2106step0 raw2106step0Labels = mixedMoment B raw2106step1 raw2106step1Labels := by
      have ha : raw2106step1 = raw2106step0 := by apply Matrix.ext; unfold raw2106step1 raw2106step0; decide +kernel
      have hl : raw2106step0Labels = labelEmbedding7 ∘ raw2106step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2106step0 raw2106step0Labels raw2106step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5080 node5080Labels := by rfl

def raw2107 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2107Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2107step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2107 raw2107Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw2107 raw2107Labels = mixedMoment B raw2107step0 raw2107step0Labels := by
      have ha : raw2107step0 = (fun i j => raw2107 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2107step0 raw2107; decide +kernel
      have hl : raw2107step0Labels = raw2107Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2107 raw2107Labels permutation32 permutation4
    _ = mixedMoment B node2488 node2488Labels := by rfl

def raw2108 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw2108Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw2108step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw2108step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2108step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw2108step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2108 raw2108Labels = mixedMoment B node3478 node3478Labels := by
  calc
    mixedMoment B raw2108 raw2108Labels = mixedMoment B raw2108step0 raw2108step0Labels := by
      have ha : raw2108step0 = (fun i j => raw2108 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2108step0 raw2108; decide +kernel
      have hl : raw2108step0Labels = raw2108Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2108 raw2108Labels permutation34 permutation6
    mixedMoment B raw2108step0 raw2108step0Labels = mixedMoment B raw2108step1 raw2108step1Labels := by
      have ha : raw2108step1 = -raw2108step0 := by apply Matrix.ext; change ∀ i j, raw2108step1 i j = -(raw2108step0 i j); unfold raw2108step1 raw2108step0; decide +kernel
      have hl : raw2108step1Labels = raw2108step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2108step1 raw2108step1Labels = mixedMoment B raw2108step2 raw2108step2Labels := by
      have ha : raw2108step2 = raw2108step1 := by apply Matrix.ext; unfold raw2108step2 raw2108step1; decide +kernel
      have hl : raw2108step1Labels = labelEmbedding1 ∘ raw2108step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2108step1 raw2108step1Labels raw2108step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3478 node3478Labels := by rfl

def raw2109 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2109Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2109step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2109step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2109 raw2109Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw2109 raw2109Labels = mixedMoment B raw2109step0 raw2109step0Labels := by
      have ha : raw2109step0 = (fun i j => raw2109 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2109step0 raw2109; decide +kernel
      have hl : raw2109step0Labels = raw2109Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2109 raw2109Labels permutation32 permutation4
    mixedMoment B raw2109step0 raw2109step0Labels = mixedMoment B raw2109step1 raw2109step1Labels := by
      have ha : raw2109step1 = raw2109step0 := by apply Matrix.ext; unfold raw2109step1 raw2109step0; decide +kernel
      have hl : raw2109step0Labels = labelEmbedding7 ∘ raw2109step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2109step0 raw2109step0Labels raw2109step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5081 node5081Labels := by rfl

def raw2110 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2110Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2110step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2110 raw2110Labels = mixedMoment B node2489 node2489Labels := by
  calc
    mixedMoment B raw2110 raw2110Labels = mixedMoment B raw2110step0 raw2110step0Labels := by
      have ha : raw2110step0 = (fun i j => raw2110 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2110step0 raw2110; decide +kernel
      have hl : raw2110step0Labels = raw2110Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2110 raw2110Labels permutation32 permutation4
    _ = mixedMoment B node2489 node2489Labels := by rfl

def raw2111 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2111Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw2111step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2111step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw2111step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2111step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw2111step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2111 raw2111Labels = mixedMoment B node3482 node3482Labels := by
  calc
    mixedMoment B raw2111 raw2111Labels = mixedMoment B raw2111step0 raw2111step0Labels := by
      have ha : raw2111step0 = (fun i j => raw2111 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2111step0 raw2111; decide +kernel
      have hl : raw2111step0Labels = raw2111Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2111 raw2111Labels permutation32 permutation6
    mixedMoment B raw2111step0 raw2111step0Labels = mixedMoment B raw2111step1 raw2111step1Labels := by
      have ha : raw2111step1 = -raw2111step0 := by apply Matrix.ext; change ∀ i j, raw2111step1 i j = -(raw2111step0 i j); unfold raw2111step1 raw2111step0; decide +kernel
      have hl : raw2111step1Labels = raw2111step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2111step1 raw2111step1Labels = mixedMoment B raw2111step2 raw2111step2Labels := by
      have ha : raw2111step2 = raw2111step1 := by apply Matrix.ext; unfold raw2111step2 raw2111step1; decide +kernel
      have hl : raw2111step1Labels = labelEmbedding1 ∘ raw2111step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2111step1 raw2111step1Labels raw2111step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3482 node3482Labels := by rfl

def raw2112 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw2112Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2112step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2112step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2112step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2112step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2112 raw2112Labels = mixedMoment B node5093 node5093Labels := by
  calc
    mixedMoment B raw2112 raw2112Labels = mixedMoment B raw2112step0 raw2112step0Labels := by
      have ha : raw2112step0 = (fun i j => raw2112 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2112step0 raw2112; decide +kernel
      have hl : raw2112step0Labels = raw2112Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2112 raw2112Labels permutation152 permutation4
    mixedMoment B raw2112step0 raw2112step0Labels = mixedMoment B raw2112step1 raw2112step1Labels := by
      have ha : raw2112step1 = raw2112step0 := by apply Matrix.ext; unfold raw2112step1 raw2112step0; decide +kernel
      have hl : raw2112step0Labels = labelEmbedding7 ∘ raw2112step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2112step0 raw2112step0Labels raw2112step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5093 node5093Labels := by rfl

def raw2113 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw2113Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2113step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2113step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2113 raw2113Labels = mixedMoment B node2503 node2503Labels := by
  calc
    mixedMoment B raw2113 raw2113Labels = mixedMoment B raw2113step0 raw2113step0Labels := by
      have ha : raw2113step0 = (fun i j => raw2113 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2113step0 raw2113; decide +kernel
      have hl : raw2113step0Labels = raw2113Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2113 raw2113Labels permutation152 permutation4
    _ = mixedMoment B node2503 node2503Labels := by rfl

def raw2114 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw2114Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2114step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2114step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2114step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2114step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2114step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2114step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2114 raw2114Labels = mixedMoment B node3446 node3446Labels := by
  calc
    mixedMoment B raw2114 raw2114Labels = mixedMoment B raw2114step0 raw2114step0Labels := by
      have ha : raw2114step0 = (fun i j => raw2114 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2114step0 raw2114; decide +kernel
      have hl : raw2114step0Labels = raw2114Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2114 raw2114Labels permutation152 permutation6
    mixedMoment B raw2114step0 raw2114step0Labels = mixedMoment B raw2114step1 raw2114step1Labels := by
      have ha : raw2114step1 = -raw2114step0 := by apply Matrix.ext; change ∀ i j, raw2114step1 i j = -(raw2114step0 i j); unfold raw2114step1 raw2114step0; decide +kernel
      have hl : raw2114step1Labels = raw2114step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2114step1 raw2114step1Labels = mixedMoment B raw2114step2 raw2114step2Labels := by
      have ha : raw2114step2 = raw2114step1 := by apply Matrix.ext; unfold raw2114step2 raw2114step1; decide +kernel
      have hl : raw2114step1Labels = labelEmbedding1 ∘ raw2114step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2114step1 raw2114step1Labels raw2114step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3446 node3446Labels := by rfl

def raw2115 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, 2, -3]]
def raw2115Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw2115step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw2115step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2115 raw2115Labels = mixedMoment B node5094 node5094Labels := by
  calc
    mixedMoment B raw2115 raw2115Labels = mixedMoment B raw2115step0 raw2115step0Labels := by
      have ha : raw2115step0 = (fun i j => raw2115 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2115step0 raw2115; decide +kernel
      have hl : raw2115step0Labels = raw2115Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2115 raw2115Labels permutation32 permutation4
    mixedMoment B raw2115step0 raw2115step0Labels = mixedMoment B raw2115step1 raw2115step1Labels := by
      have ha : raw2115step1 = raw2115step0 := by apply Matrix.ext; unfold raw2115step1 raw2115step0; decide +kernel
      have hl : raw2115step0Labels = labelEmbedding7 ∘ raw2115step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2115step0 raw2115step0Labels raw2115step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5094 node5094Labels := by rfl

def raw2116 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, 2, -3]]
def raw2116Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw2116step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2116 raw2116Labels = mixedMoment B node2504 node2504Labels := by
  calc
    mixedMoment B raw2116 raw2116Labels = mixedMoment B raw2116step0 raw2116step0Labels := by
      have ha : raw2116step0 = (fun i j => raw2116 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2116step0 raw2116; decide +kernel
      have hl : raw2116step0Labels = raw2116Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2116 raw2116Labels permutation32 permutation4
    _ = mixedMoment B node2504 node2504Labels := by rfl

def raw2117 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, 2, -3]]
def raw2117Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw2117step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw2117step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2117 raw2117Labels = mixedMoment B node2504 node2504Labels := by
  calc
    mixedMoment B raw2117 raw2117Labels = mixedMoment B raw2117step0 raw2117step0Labels := by
      have ha : raw2117step0 = (fun i j => raw2117 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2117step0 raw2117; decide +kernel
      have hl : raw2117step0Labels = raw2117Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2117 raw2117Labels permutation151 permutation6
    mixedMoment B raw2117step0 raw2117step0Labels = mixedMoment B raw2117step1 raw2117step1Labels := by
      have ha : raw2117step1 = raw2117step0 := by apply Matrix.ext; unfold raw2117step1 raw2117step0; decide +kernel
      have hl : raw2117step0Labels = labelEmbedding1 ∘ raw2117step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2117step0 raw2117step0Labels raw2117step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2504 node2504Labels := by rfl

def raw2118 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-2, 1, 1], ![1, 1, -2], ![0, 2, -2]]
def raw2118Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw2118step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw2118step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2118 raw2118Labels = mixedMoment B node5095 node5095Labels := by
  calc
    mixedMoment B raw2118 raw2118Labels = mixedMoment B raw2118step0 raw2118step0Labels := by
      have ha : raw2118step0 = (fun i j => raw2118 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2118step0 raw2118; decide +kernel
      have hl : raw2118step0Labels = raw2118Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2118 raw2118Labels permutation32 permutation4
    mixedMoment B raw2118step0 raw2118step0Labels = mixedMoment B raw2118step1 raw2118step1Labels := by
      have ha : raw2118step1 = raw2118step0 := by apply Matrix.ext; unfold raw2118step1 raw2118step0; decide +kernel
      have hl : raw2118step0Labels = labelEmbedding7 ∘ raw2118step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2118step0 raw2118step0Labels raw2118step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5095 node5095Labels := by rfl

def raw2119 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-2, 1, 1], ![1, 1, -2], ![0, 2, -2]]
def raw2119Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw2119step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2119 raw2119Labels = mixedMoment B node2505 node2505Labels := by
  calc
    mixedMoment B raw2119 raw2119Labels = mixedMoment B raw2119step0 raw2119step0Labels := by
      have ha : raw2119step0 = (fun i j => raw2119 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2119step0 raw2119; decide +kernel
      have hl : raw2119step0Labels = raw2119Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2119 raw2119Labels permutation32 permutation4
    _ = mixedMoment B node2505 node2505Labels := by rfl

def raw2120 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-2, 1, 1], ![1, 1, -2], ![0, 2, -2]]
def raw2120Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw2120step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2120step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2120step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2120step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2120step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2120 raw2120Labels = mixedMoment B node3448 node3448Labels := by
  calc
    mixedMoment B raw2120 raw2120Labels = mixedMoment B raw2120step0 raw2120step0Labels := by
      have ha : raw2120step0 = (fun i j => raw2120 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2120step0 raw2120; decide +kernel
      have hl : raw2120step0Labels = raw2120Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2120 raw2120Labels permutation32 permutation6
    mixedMoment B raw2120step0 raw2120step0Labels = mixedMoment B raw2120step1 raw2120step1Labels := by
      have ha : raw2120step1 = -raw2120step0 := by apply Matrix.ext; change ∀ i j, raw2120step1 i j = -(raw2120step0 i j); unfold raw2120step1 raw2120step0; decide +kernel
      have hl : raw2120step1Labels = raw2120step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2120step1 raw2120step1Labels = mixedMoment B raw2120step2 raw2120step2Labels := by
      have ha : raw2120step2 = raw2120step1 := by apply Matrix.ext; unfold raw2120step2 raw2120step1; decide +kernel
      have hl : raw2120step1Labels = labelEmbedding1 ∘ raw2120step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2120step1 raw2120step1Labels raw2120step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3448 node3448Labels := by rfl

def raw2121 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw2121Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2121step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2121step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2121step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2121step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2121 raw2121Labels = mixedMoment B node5098 node5098Labels := by
  calc
    mixedMoment B raw2121 raw2121Labels = mixedMoment B raw2121step0 raw2121step0Labels := by
      have ha : raw2121step0 = (fun i j => raw2121 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2121step0 raw2121; decide +kernel
      have hl : raw2121step0Labels = raw2121Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2121 raw2121Labels permutation152 permutation4
    mixedMoment B raw2121step0 raw2121step0Labels = mixedMoment B raw2121step1 raw2121step1Labels := by
      have ha : raw2121step1 = raw2121step0 := by apply Matrix.ext; unfold raw2121step1 raw2121step0; decide +kernel
      have hl : raw2121step0Labels = labelEmbedding7 ∘ raw2121step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2121step0 raw2121step0Labels raw2121step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5098 node5098Labels := by rfl

def raw2122 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw2122Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2122step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2122step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2122 raw2122Labels = mixedMoment B node2508 node2508Labels := by
  calc
    mixedMoment B raw2122 raw2122Labels = mixedMoment B raw2122step0 raw2122step0Labels := by
      have ha : raw2122step0 = (fun i j => raw2122 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2122step0 raw2122; decide +kernel
      have hl : raw2122step0Labels = raw2122Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2122 raw2122Labels permutation152 permutation4
    _ = mixedMoment B node2508 node2508Labels := by rfl

def raw2123 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw2123Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2123step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2123step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2123step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2123step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2123step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2123step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2123 raw2123Labels = mixedMoment B node3460 node3460Labels := by
  calc
    mixedMoment B raw2123 raw2123Labels = mixedMoment B raw2123step0 raw2123step0Labels := by
      have ha : raw2123step0 = (fun i j => raw2123 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2123step0 raw2123; decide +kernel
      have hl : raw2123step0Labels = raw2123Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2123 raw2123Labels permutation152 permutation6
    mixedMoment B raw2123step0 raw2123step0Labels = mixedMoment B raw2123step1 raw2123step1Labels := by
      have ha : raw2123step1 = -raw2123step0 := by apply Matrix.ext; change ∀ i j, raw2123step1 i j = -(raw2123step0 i j); unfold raw2123step1 raw2123step0; decide +kernel
      have hl : raw2123step1Labels = raw2123step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2123step1 raw2123step1Labels = mixedMoment B raw2123step2 raw2123step2Labels := by
      have ha : raw2123step2 = raw2123step1 := by apply Matrix.ext; unfold raw2123step2 raw2123step1; decide +kernel
      have hl : raw2123step1Labels = labelEmbedding1 ∘ raw2123step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2123step1 raw2123step1Labels raw2123step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3460 node3460Labels := by rfl

def raw2124 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 2, -3]]
def raw2124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw2124step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw2124step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2124 raw2124Labels = mixedMoment B node5099 node5099Labels := by
  calc
    mixedMoment B raw2124 raw2124Labels = mixedMoment B raw2124step0 raw2124step0Labels := by
      have ha : raw2124step0 = (fun i j => raw2124 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2124step0 raw2124; decide +kernel
      have hl : raw2124step0Labels = raw2124Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2124 raw2124Labels permutation32 permutation4
    mixedMoment B raw2124step0 raw2124step0Labels = mixedMoment B raw2124step1 raw2124step1Labels := by
      have ha : raw2124step1 = raw2124step0 := by apply Matrix.ext; unfold raw2124step1 raw2124step0; decide +kernel
      have hl : raw2124step0Labels = labelEmbedding7 ∘ raw2124step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2124step0 raw2124step0Labels raw2124step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5099 node5099Labels := by rfl

def raw2125 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 2, -3]]
def raw2125Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw2125step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2125 raw2125Labels = mixedMoment B node2509 node2509Labels := by
  calc
    mixedMoment B raw2125 raw2125Labels = mixedMoment B raw2125step0 raw2125step0Labels := by
      have ha : raw2125step0 = (fun i j => raw2125 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2125step0 raw2125; decide +kernel
      have hl : raw2125step0Labels = raw2125Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2125 raw2125Labels permutation32 permutation4
    _ = mixedMoment B node2509 node2509Labels := by rfl

def raw2126 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 2, -3]]
def raw2126Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw2126step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw2126step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2126 raw2126Labels = mixedMoment B node2704 node2704Labels := by
  calc
    mixedMoment B raw2126 raw2126Labels = mixedMoment B raw2126step0 raw2126step0Labels := by
      have ha : raw2126step0 = (fun i j => raw2126 (permutation145 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2126step0 raw2126; decide +kernel
      have hl : raw2126step0Labels = raw2126Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2126 raw2126Labels permutation145 permutation6
    mixedMoment B raw2126step0 raw2126step0Labels = mixedMoment B raw2126step1 raw2126step1Labels := by
      have ha : raw2126step1 = raw2126step0 := by apply Matrix.ext; unfold raw2126step1 raw2126step0; decide +kernel
      have hl : raw2126step0Labels = labelEmbedding1 ∘ raw2126step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2126step0 raw2126step0Labels raw2126step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2704 node2704Labels := by rfl

def raw2127 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw2127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw2127step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw2127step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2127 raw2127Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw2127 raw2127Labels = mixedMoment B raw2127step0 raw2127step0Labels := by
      have ha : raw2127step0 = (fun i j => raw2127 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2127step0 raw2127; decide +kernel
      have hl : raw2127step0Labels = raw2127Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2127 raw2127Labels permutation32 permutation4
    mixedMoment B raw2127step0 raw2127step0Labels = mixedMoment B raw2127step1 raw2127step1Labels := by
      have ha : raw2127step1 = raw2127step0 := by apply Matrix.ext; unfold raw2127step1 raw2127step0; decide +kernel
      have hl : raw2127step0Labels = labelEmbedding7 ∘ raw2127step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2127step0 raw2127step0Labels raw2127step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5102 node5102Labels := by rfl

def raw2128 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw2128Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw2128step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2128 raw2128Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw2128 raw2128Labels = mixedMoment B raw2128step0 raw2128step0Labels := by
      have ha : raw2128step0 = (fun i j => raw2128 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2128step0 raw2128; decide +kernel
      have hl : raw2128step0Labels = raw2128Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2128 raw2128Labels permutation32 permutation4
    _ = mixedMoment B node2512 node2512Labels := by rfl

def raw2129 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw2129Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw2129step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2129step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2129step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2129step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2129step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2129 raw2129Labels = mixedMoment B node3471 node3471Labels := by
  calc
    mixedMoment B raw2129 raw2129Labels = mixedMoment B raw2129step0 raw2129step0Labels := by
      have ha : raw2129step0 = (fun i j => raw2129 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2129step0 raw2129; decide +kernel
      have hl : raw2129step0Labels = raw2129Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2129 raw2129Labels permutation33 permutation6
    mixedMoment B raw2129step0 raw2129step0Labels = mixedMoment B raw2129step1 raw2129step1Labels := by
      have ha : raw2129step1 = -raw2129step0 := by apply Matrix.ext; change ∀ i j, raw2129step1 i j = -(raw2129step0 i j); unfold raw2129step1 raw2129step0; decide +kernel
      have hl : raw2129step1Labels = raw2129step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2129step1 raw2129step1Labels = mixedMoment B raw2129step2 raw2129step2Labels := by
      have ha : raw2129step2 = raw2129step1 := by apply Matrix.ext; unfold raw2129step2 raw2129step1; decide +kernel
      have hl : raw2129step1Labels = labelEmbedding1 ∘ raw2129step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2129step1 raw2129step1Labels raw2129step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3471 node3471Labels := by rfl

def raw2130 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw2130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2130step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2130step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2130 raw2130Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw2130 raw2130Labels = mixedMoment B raw2130step0 raw2130step0Labels := by
      have ha : raw2130step0 = (fun i j => raw2130 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2130step0 raw2130; decide +kernel
      have hl : raw2130step0Labels = raw2130Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2130 raw2130Labels permutation32 permutation4
    mixedMoment B raw2130step0 raw2130step0Labels = mixedMoment B raw2130step1 raw2130step1Labels := by
      have ha : raw2130step1 = raw2130step0 := by apply Matrix.ext; unfold raw2130step1 raw2130step0; decide +kernel
      have hl : raw2130step0Labels = labelEmbedding7 ∘ raw2130step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2130step0 raw2130step0Labels raw2130step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5105 node5105Labels := by rfl

def raw2131 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw2131Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2131step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2131 raw2131Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw2131 raw2131Labels = mixedMoment B raw2131step0 raw2131step0Labels := by
      have ha : raw2131step0 = (fun i j => raw2131 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2131step0 raw2131; decide +kernel
      have hl : raw2131step0Labels = raw2131Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2131 raw2131Labels permutation32 permutation4
    _ = mixedMoment B node2515 node2515Labels := by rfl

def raw2132 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw2132Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw2132step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2132step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw2132step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2132step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw2132step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2132 raw2132Labels = mixedMoment B node3479 node3479Labels := by
  calc
    mixedMoment B raw2132 raw2132Labels = mixedMoment B raw2132step0 raw2132step0Labels := by
      have ha : raw2132step0 = (fun i j => raw2132 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2132step0 raw2132; decide +kernel
      have hl : raw2132step0Labels = raw2132Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2132 raw2132Labels permutation36 permutation6
    mixedMoment B raw2132step0 raw2132step0Labels = mixedMoment B raw2132step1 raw2132step1Labels := by
      have ha : raw2132step1 = -raw2132step0 := by apply Matrix.ext; change ∀ i j, raw2132step1 i j = -(raw2132step0 i j); unfold raw2132step1 raw2132step0; decide +kernel
      have hl : raw2132step1Labels = raw2132step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2132step1 raw2132step1Labels = mixedMoment B raw2132step2 raw2132step2Labels := by
      have ha : raw2132step2 = raw2132step1 := by apply Matrix.ext; unfold raw2132step2 raw2132step1; decide +kernel
      have hl : raw2132step1Labels = labelEmbedding1 ∘ raw2132step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2132step1 raw2132step1Labels raw2132step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3479 node3479Labels := by rfl

def raw2133 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 1, -2], ![-2, 3, -1]]
def raw2133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2133step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw2133step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2133step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw2133step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2133 raw2133Labels = mixedMoment B node5109 node5109Labels := by
  calc
    mixedMoment B raw2133 raw2133Labels = mixedMoment B raw2133step0 raw2133step0Labels := by
      have ha : raw2133step0 = (fun i j => raw2133 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2133step0 raw2133; decide +kernel
      have hl : raw2133step0Labels = raw2133Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2133 raw2133Labels permutation8 permutation4
    mixedMoment B raw2133step0 raw2133step0Labels = mixedMoment B raw2133step1 raw2133step1Labels := by
      have ha : raw2133step1 = raw2133step0 := by apply Matrix.ext; unfold raw2133step1 raw2133step0; decide +kernel
      have hl : raw2133step0Labels = labelEmbedding7 ∘ raw2133step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2133step0 raw2133step0Labels raw2133step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5109 node5109Labels := by rfl

def raw2134 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 1, -2], ![-2, 3, -1]]
def raw2134Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2134step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw2134step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2134 raw2134Labels = mixedMoment B node2519 node2519Labels := by
  calc
    mixedMoment B raw2134 raw2134Labels = mixedMoment B raw2134step0 raw2134step0Labels := by
      have ha : raw2134step0 = (fun i j => raw2134 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2134step0 raw2134; decide +kernel
      have hl : raw2134step0Labels = raw2134Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2134 raw2134Labels permutation8 permutation4
    _ = mixedMoment B node2519 node2519Labels := by rfl

def raw2135 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![1, 1, -2], ![-2, 3, -1]]
def raw2135Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2135step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw2135step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2135step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def raw2135step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2135step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def raw2135step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2135 raw2135Labels = mixedMoment B node3486 node3486Labels := by
  calc
    mixedMoment B raw2135 raw2135Labels = mixedMoment B raw2135step0 raw2135step0Labels := by
      have ha : raw2135step0 = (fun i j => raw2135 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2135step0 raw2135; decide +kernel
      have hl : raw2135step0Labels = raw2135Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2135 raw2135Labels permutation9 permutation6
    mixedMoment B raw2135step0 raw2135step0Labels = mixedMoment B raw2135step1 raw2135step1Labels := by
      have ha : raw2135step1 = -raw2135step0 := by apply Matrix.ext; change ∀ i j, raw2135step1 i j = -(raw2135step0 i j); unfold raw2135step1 raw2135step0; decide +kernel
      have hl : raw2135step1Labels = raw2135step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2135step1 raw2135step1Labels = mixedMoment B raw2135step2 raw2135step2Labels := by
      have ha : raw2135step2 = raw2135step1 := by apply Matrix.ext; unfold raw2135step2 raw2135step1; decide +kernel
      have hl : raw2135step1Labels = labelEmbedding1 ∘ raw2135step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2135step1 raw2135step1Labels raw2135step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3486 node3486Labels := by rfl

def raw2136 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-2, 2, 0], ![1, 2, -3]]
def raw2136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2136step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw2136step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2136step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw2136step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2136 raw2136Labels = mixedMoment B node5110 node5110Labels := by
  calc
    mixedMoment B raw2136 raw2136Labels = mixedMoment B raw2136step0 raw2136step0Labels := by
      have ha : raw2136step0 = (fun i j => raw2136 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2136step0 raw2136; decide +kernel
      have hl : raw2136step0Labels = raw2136Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2136 raw2136Labels permutation8 permutation4
    mixedMoment B raw2136step0 raw2136step0Labels = mixedMoment B raw2136step1 raw2136step1Labels := by
      have ha : raw2136step1 = raw2136step0 := by apply Matrix.ext; unfold raw2136step1 raw2136step0; decide +kernel
      have hl : raw2136step0Labels = labelEmbedding7 ∘ raw2136step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2136step0 raw2136step0Labels raw2136step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5110 node5110Labels := by rfl

def raw2137 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-2, 2, 0], ![1, 2, -3]]
def raw2137Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2137step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw2137step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2137 raw2137Labels = mixedMoment B node2522 node2522Labels := by
  calc
    mixedMoment B raw2137 raw2137Labels = mixedMoment B raw2137step0 raw2137step0Labels := by
      have ha : raw2137step0 = (fun i j => raw2137 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2137step0 raw2137; decide +kernel
      have hl : raw2137step0Labels = raw2137Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2137 raw2137Labels permutation8 permutation4
    _ = mixedMoment B node2522 node2522Labels := by rfl

def raw2138 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -3, 2], ![0, -1, 1], ![-2, 2, 0], ![1, 2, -3]]
def raw2138Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2138step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw2138step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2138step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw2138step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2138 raw2138Labels = mixedMoment B node2685 node2685Labels := by
  calc
    mixedMoment B raw2138 raw2138Labels = mixedMoment B raw2138step0 raw2138step0Labels := by
      have ha : raw2138step0 = (fun i j => raw2138 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2138step0 raw2138; decide +kernel
      have hl : raw2138step0Labels = raw2138Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2138 raw2138Labels permutation31 permutation6
    mixedMoment B raw2138step0 raw2138step0Labels = mixedMoment B raw2138step1 raw2138step1Labels := by
      have ha : raw2138step1 = raw2138step0 := by apply Matrix.ext; unfold raw2138step1 raw2138step0; decide +kernel
      have hl : raw2138step0Labels = labelEmbedding1 ∘ raw2138step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2138step0 raw2138step0Labels raw2138step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2685 node2685Labels := by rfl

def raw2139 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw2139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2139step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw2139step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2139step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw2139step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2139 raw2139Labels = mixedMoment B node5114 node5114Labels := by
  calc
    mixedMoment B raw2139 raw2139Labels = mixedMoment B raw2139step0 raw2139step0Labels := by
      have ha : raw2139step0 = (fun i j => raw2139 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2139step0 raw2139; decide +kernel
      have hl : raw2139step0Labels = raw2139Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2139 raw2139Labels permutation152 permutation5
    mixedMoment B raw2139step0 raw2139step0Labels = mixedMoment B raw2139step1 raw2139step1Labels := by
      have ha : raw2139step1 = raw2139step0 := by apply Matrix.ext; unfold raw2139step1 raw2139step0; decide +kernel
      have hl : raw2139step0Labels = labelEmbedding8 ∘ raw2139step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2139step0 raw2139step0Labels raw2139step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5114 node5114Labels := by rfl

def raw2140 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw2140Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2140step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw2140step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2140 raw2140Labels = mixedMoment B node2896 node2896Labels := by
  calc
    mixedMoment B raw2140 raw2140Labels = mixedMoment B raw2140step0 raw2140step0Labels := by
      have ha : raw2140step0 = (fun i j => raw2140 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2140step0 raw2140; decide +kernel
      have hl : raw2140step0Labels = raw2140Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2140 raw2140Labels permutation153 permutation4
    _ = mixedMoment B node2896 node2896Labels := by rfl

def raw2141 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![-2, 2, 0]]
def raw2141Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 0, 2]]
def raw2141step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2141step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw2141step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2141step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw2141step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2141 raw2141Labels = mixedMoment B node3597 node3597Labels := by
  calc
    mixedMoment B raw2141 raw2141Labels = mixedMoment B raw2141step0 raw2141step0Labels := by
      have ha : raw2141step0 = (fun i j => raw2141 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2141step0 raw2141; decide +kernel
      have hl : raw2141step0Labels = raw2141Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2141 raw2141Labels permutation152 permutation3
    mixedMoment B raw2141step0 raw2141step0Labels = mixedMoment B raw2141step1 raw2141step1Labels := by
      have ha : raw2141step1 = -raw2141step0 := by apply Matrix.ext; change ∀ i j, raw2141step1 i j = -(raw2141step0 i j); unfold raw2141step1 raw2141step0; decide +kernel
      have hl : raw2141step1Labels = raw2141step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2141step1 raw2141step1Labels = mixedMoment B raw2141step2 raw2141step2Labels := by
      have ha : raw2141step2 = raw2141step1 := by apply Matrix.ext; unfold raw2141step2 raw2141step1; decide +kernel
      have hl : raw2141step1Labels = labelEmbedding1 ∘ raw2141step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2141step1 raw2141step1Labels raw2141step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3597 node3597Labels := by rfl

def raw2142 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw2142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2142step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw2142step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2142step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw2142step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2142 raw2142Labels = mixedMoment B node5117 node5117Labels := by
  calc
    mixedMoment B raw2142 raw2142Labels = mixedMoment B raw2142step0 raw2142step0Labels := by
      have ha : raw2142step0 = (fun i j => raw2142 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2142step0 raw2142; decide +kernel
      have hl : raw2142step0Labels = raw2142Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2142 raw2142Labels permutation152 permutation5
    mixedMoment B raw2142step0 raw2142step0Labels = mixedMoment B raw2142step1 raw2142step1Labels := by
      have ha : raw2142step1 = raw2142step0 := by apply Matrix.ext; unfold raw2142step1 raw2142step0; decide +kernel
      have hl : raw2142step0Labels = labelEmbedding8 ∘ raw2142step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2142step0 raw2142step0Labels raw2142step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5117 node5117Labels := by rfl

def raw2143 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw2143Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2143step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw2143step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2143 raw2143Labels = mixedMoment B node2893 node2893Labels := by
  calc
    mixedMoment B raw2143 raw2143Labels = mixedMoment B raw2143step0 raw2143step0Labels := by
      have ha : raw2143step0 = (fun i j => raw2143 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2143step0 raw2143; decide +kernel
      have hl : raw2143step0Labels = raw2143Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2143 raw2143Labels permutation153 permutation4
    _ = mixedMoment B node2893 node2893Labels := by rfl

def raw2144 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw2144Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2144step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, -1, 2]]
def raw2144step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2144step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw2144step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2144step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw2144step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2144 raw2144Labels = mixedMoment B node3599 node3599Labels := by
  calc
    mixedMoment B raw2144 raw2144Labels = mixedMoment B raw2144step0 raw2144step0Labels := by
      have ha : raw2144step0 = (fun i j => raw2144 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2144step0 raw2144; decide +kernel
      have hl : raw2144step0Labels = raw2144Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2144 raw2144Labels permutation154 permutation3
    mixedMoment B raw2144step0 raw2144step0Labels = mixedMoment B raw2144step1 raw2144step1Labels := by
      have ha : raw2144step1 = -raw2144step0 := by apply Matrix.ext; change ∀ i j, raw2144step1 i j = -(raw2144step0 i j); unfold raw2144step1 raw2144step0; decide +kernel
      have hl : raw2144step1Labels = raw2144step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2144step1 raw2144step1Labels = mixedMoment B raw2144step2 raw2144step2Labels := by
      have ha : raw2144step2 = raw2144step1 := by apply Matrix.ext; unfold raw2144step2 raw2144step1; decide +kernel
      have hl : raw2144step1Labels = labelEmbedding1 ∘ raw2144step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2144step1 raw2144step1Labels raw2144step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3599 node3599Labels := by rfl

def raw2145 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw2145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2145step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -2, 0]]
def raw2145step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2145step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -2, 0]]
def raw2145step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2145 raw2145Labels = mixedMoment B node5118 node5118Labels := by
  calc
    mixedMoment B raw2145 raw2145Labels = mixedMoment B raw2145step0 raw2145step0Labels := by
      have ha : raw2145step0 = (fun i j => raw2145 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2145step0 raw2145; decide +kernel
      have hl : raw2145step0Labels = raw2145Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2145 raw2145Labels permutation152 permutation5
    mixedMoment B raw2145step0 raw2145step0Labels = mixedMoment B raw2145step1 raw2145step1Labels := by
      have ha : raw2145step1 = raw2145step0 := by apply Matrix.ext; unfold raw2145step1 raw2145step0; decide +kernel
      have hl : raw2145step0Labels = labelEmbedding8 ∘ raw2145step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2145step0 raw2145step0Labels raw2145step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5118 node5118Labels := by rfl

def raw2146 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw2146Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2146step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2146step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2146 raw2146Labels = mixedMoment B node2891 node2891Labels := by
  calc
    mixedMoment B raw2146 raw2146Labels = mixedMoment B raw2146step0 raw2146step0Labels := by
      have ha : raw2146step0 = (fun i j => raw2146 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2146step0 raw2146; decide +kernel
      have hl : raw2146step0Labels = raw2146Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2146 raw2146Labels permutation152 permutation4
    _ = mixedMoment B node2891 node2891Labels := by rfl

def raw2147 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw2147Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2147step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![0, -2, 2], ![-2, 1, 1]]
def raw2147step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2147step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![2, -1, -1]]
def raw2147step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2147step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![2, -1, -1]]
def raw2147step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2147 raw2147Labels = mixedMoment B node3598 node3598Labels := by
  calc
    mixedMoment B raw2147 raw2147Labels = mixedMoment B raw2147step0 raw2147step0Labels := by
      have ha : raw2147step0 = (fun i j => raw2147 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2147step0 raw2147; decide +kernel
      have hl : raw2147step0Labels = raw2147Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2147 raw2147Labels permutation155 permutation3
    mixedMoment B raw2147step0 raw2147step0Labels = mixedMoment B raw2147step1 raw2147step1Labels := by
      have ha : raw2147step1 = -raw2147step0 := by apply Matrix.ext; change ∀ i j, raw2147step1 i j = -(raw2147step0 i j); unfold raw2147step1 raw2147step0; decide +kernel
      have hl : raw2147step1Labels = raw2147step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2147step1 raw2147step1Labels = mixedMoment B raw2147step2 raw2147step2Labels := by
      have ha : raw2147step2 = raw2147step1 := by apply Matrix.ext; unfold raw2147step2 raw2147step1; decide +kernel
      have hl : raw2147step1Labels = labelEmbedding1 ∘ raw2147step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2147step1 raw2147step1Labels raw2147step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3598 node3598Labels := by rfl

def raw2148 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![-1, 2, -1]]
def raw2148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2148step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw2148step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2148step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw2148step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2148 raw2148Labels = mixedMoment B node5119 node5119Labels := by
  calc
    mixedMoment B raw2148 raw2148Labels = mixedMoment B raw2148step0 raw2148step0Labels := by
      have ha : raw2148step0 = (fun i j => raw2148 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2148step0 raw2148; decide +kernel
      have hl : raw2148step0Labels = raw2148Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2148 raw2148Labels permutation152 permutation5
    mixedMoment B raw2148step0 raw2148step0Labels = mixedMoment B raw2148step1 raw2148step1Labels := by
      have ha : raw2148step1 = raw2148step0 := by apply Matrix.ext; unfold raw2148step1 raw2148step0; decide +kernel
      have hl : raw2148step0Labels = labelEmbedding8 ∘ raw2148step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2148step0 raw2148step0Labels raw2148step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5119 node5119Labels := by rfl

def raw2149 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![-1, 2, -1]]
def raw2149Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw2149step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2149 raw2149Labels = mixedMoment B node2845 node2845Labels := by
  calc
    mixedMoment B raw2149 raw2149Labels = mixedMoment B raw2149step0 raw2149step0Labels := by
      have ha : raw2149step0 = (fun i j => raw2149 (permutation177 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2149step0 raw2149; decide +kernel
      have hl : raw2149step0Labels = raw2149Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2149 raw2149Labels permutation177 permutation4
    _ = mixedMoment B node2845 node2845Labels := by rfl

def raw2150 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![-1, 2, -1]]
def raw2150Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2150step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, -1, 2]]
def raw2150step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2150step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw2150step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2150step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw2150step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2150 raw2150Labels = mixedMoment B node3604 node3604Labels := by
  calc
    mixedMoment B raw2150 raw2150Labels = mixedMoment B raw2150step0 raw2150step0Labels := by
      have ha : raw2150step0 = (fun i j => raw2150 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2150step0 raw2150; decide +kernel
      have hl : raw2150step0Labels = raw2150Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2150 raw2150Labels permutation160 permutation3
    mixedMoment B raw2150step0 raw2150step0Labels = mixedMoment B raw2150step1 raw2150step1Labels := by
      have ha : raw2150step1 = -raw2150step0 := by apply Matrix.ext; change ∀ i j, raw2150step1 i j = -(raw2150step0 i j); unfold raw2150step1 raw2150step0; decide +kernel
      have hl : raw2150step1Labels = raw2150step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2150step1 raw2150step1Labels = mixedMoment B raw2150step2 raw2150step2Labels := by
      have ha : raw2150step2 = raw2150step1 := by apply Matrix.ext; unfold raw2150step2 raw2150step1; decide +kernel
      have hl : raw2150step1Labels = labelEmbedding1 ∘ raw2150step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2150step1 raw2150step1Labels raw2150step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3604 node3604Labels := by rfl

def raw2151 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw2151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2151step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -2, 0]]
def raw2151step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2151step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -2, 0]]
def raw2151step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2151 raw2151Labels = mixedMoment B node5120 node5120Labels := by
  calc
    mixedMoment B raw2151 raw2151Labels = mixedMoment B raw2151step0 raw2151step0Labels := by
      have ha : raw2151step0 = (fun i j => raw2151 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2151step0 raw2151; decide +kernel
      have hl : raw2151step0Labels = raw2151Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2151 raw2151Labels permutation152 permutation5
    mixedMoment B raw2151step0 raw2151step0Labels = mixedMoment B raw2151step1 raw2151step1Labels := by
      have ha : raw2151step1 = raw2151step0 := by apply Matrix.ext; unfold raw2151step1 raw2151step0; decide +kernel
      have hl : raw2151step0Labels = labelEmbedding8 ∘ raw2151step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2151step0 raw2151step0Labels raw2151step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5120 node5120Labels := by rfl

def raw2152 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw2152Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2152step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw2152step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2152 raw2152Labels = mixedMoment B node2844 node2844Labels := by
  calc
    mixedMoment B raw2152 raw2152Labels = mixedMoment B raw2152step0 raw2152step0Labels := by
      have ha : raw2152step0 = (fun i j => raw2152 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2152step0 raw2152; decide +kernel
      have hl : raw2152step0Labels = raw2152Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2152 raw2152Labels permutation176 permutation4
    _ = mixedMoment B node2844 node2844Labels := by rfl

def raw2153 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw2153Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2153step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]
def raw2153step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2153step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw2153step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2153step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw2153step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2153 raw2153Labels = mixedMoment B node3609 node3609Labels := by
  calc
    mixedMoment B raw2153 raw2153Labels = mixedMoment B raw2153step0 raw2153step0Labels := by
      have ha : raw2153step0 = (fun i j => raw2153 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2153step0 raw2153; decide +kernel
      have hl : raw2153step0Labels = raw2153Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2153 raw2153Labels permutation168 permutation3
    mixedMoment B raw2153step0 raw2153step0Labels = mixedMoment B raw2153step1 raw2153step1Labels := by
      have ha : raw2153step1 = -raw2153step0 := by apply Matrix.ext; change ∀ i j, raw2153step1 i j = -(raw2153step0 i j); unfold raw2153step1 raw2153step0; decide +kernel
      have hl : raw2153step1Labels = raw2153step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2153step1 raw2153step1Labels = mixedMoment B raw2153step2 raw2153step2Labels := by
      have ha : raw2153step2 = raw2153step1 := by apply Matrix.ext; unfold raw2153step2 raw2153step1; decide +kernel
      have hl : raw2153step1Labels = labelEmbedding1 ∘ raw2153step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2153step1 raw2153step1Labels raw2153step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3609 node3609Labels := by rfl

def raw2154 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2154step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2154step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2154step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2154step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2154 raw2154Labels = mixedMoment B node5123 node5123Labels := by
  calc
    mixedMoment B raw2154 raw2154Labels = mixedMoment B raw2154step0 raw2154step0Labels := by
      have ha : raw2154step0 = (fun i j => raw2154 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2154step0 raw2154; decide +kernel
      have hl : raw2154step0Labels = raw2154Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2154 raw2154Labels permutation152 permutation4
    mixedMoment B raw2154step0 raw2154step0Labels = mixedMoment B raw2154step1 raw2154step1Labels := by
      have ha : raw2154step1 = raw2154step0 := by apply Matrix.ext; unfold raw2154step1 raw2154step0; decide +kernel
      have hl : raw2154step0Labels = labelEmbedding7 ∘ raw2154step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2154step0 raw2154step0Labels raw2154step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5123 node5123Labels := by rfl

def raw2155 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2155Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2155step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2155step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2155 raw2155Labels = mixedMoment B node2536 node2536Labels := by
  calc
    mixedMoment B raw2155 raw2155Labels = mixedMoment B raw2155step0 raw2155step0Labels := by
      have ha : raw2155step0 = (fun i j => raw2155 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2155step0 raw2155; decide +kernel
      have hl : raw2155step0Labels = raw2155Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2155 raw2155Labels permutation152 permutation4
    _ = mixedMoment B node2536 node2536Labels := by rfl

def raw2156 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw2156Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2156step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw2156step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2156step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2156step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2156step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2156step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2156 raw2156Labels = mixedMoment B node3370 node3370Labels := by
  calc
    mixedMoment B raw2156 raw2156Labels = mixedMoment B raw2156step0 raw2156step0Labels := by
      have ha : raw2156step0 = (fun i j => raw2156 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2156step0 raw2156; decide +kernel
      have hl : raw2156step0Labels = raw2156Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2156 raw2156Labels permutation176 permutation6
    mixedMoment B raw2156step0 raw2156step0Labels = mixedMoment B raw2156step1 raw2156step1Labels := by
      have ha : raw2156step1 = -raw2156step0 := by apply Matrix.ext; change ∀ i j, raw2156step1 i j = -(raw2156step0 i j); unfold raw2156step1 raw2156step0; decide +kernel
      have hl : raw2156step1Labels = raw2156step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2156step1 raw2156step1Labels = mixedMoment B raw2156step2 raw2156step2Labels := by
      have ha : raw2156step2 = raw2156step1 := by apply Matrix.ext; unfold raw2156step2 raw2156step1; decide +kernel
      have hl : raw2156step1Labels = labelEmbedding1 ∘ raw2156step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2156step1 raw2156step1Labels raw2156step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3370 node3370Labels := by rfl

def raw2157 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 0, 2], ![0, 2, -2], ![0, 2, -2]]
def raw2157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw2157step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2157step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw2157step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2157 raw2157Labels = mixedMoment B node5125 node5125Labels := by
  calc
    mixedMoment B raw2157 raw2157Labels = mixedMoment B raw2157step0 raw2157step0Labels := by
      have ha : raw2157step0 = (fun i j => raw2157 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2157step0 raw2157; decide +kernel
      have hl : raw2157step0Labels = raw2157Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2157 raw2157Labels permutation32 permutation4
    mixedMoment B raw2157step0 raw2157step0Labels = mixedMoment B raw2157step1 raw2157step1Labels := by
      have ha : raw2157step1 = raw2157step0 := by apply Matrix.ext; unfold raw2157step1 raw2157step0; decide +kernel
      have hl : raw2157step0Labels = labelEmbedding7 ∘ raw2157step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2157step0 raw2157step0Labels raw2157step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5125 node5125Labels := by rfl

def raw2158 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 0, 2], ![0, 2, -2], ![0, 2, -2]]
def raw2158Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw2158step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2158 raw2158Labels = mixedMoment B node2539 node2539Labels := by
  calc
    mixedMoment B raw2158 raw2158Labels = mixedMoment B raw2158step0 raw2158step0Labels := by
      have ha : raw2158step0 = (fun i j => raw2158 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2158step0 raw2158; decide +kernel
      have hl : raw2158step0Labels = raw2158Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2158 raw2158Labels permutation32 permutation4
    _ = mixedMoment B node2539 node2539Labels := by rfl

def raw2159 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-2, 0, 2], ![0, 2, -2], ![0, 2, -2]]
def raw2159Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw2159step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2159step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2159step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2159step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2159 raw2159Labels = mixedMoment B node3372 node3372Labels := by
  calc
    mixedMoment B raw2159 raw2159Labels = mixedMoment B raw2159step0 raw2159step0Labels := by
      have ha : raw2159step0 = (fun i j => raw2159 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2159step0 raw2159; decide +kernel
      have hl : raw2159step0Labels = raw2159Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2159 raw2159Labels permutation38 permutation6
    mixedMoment B raw2159step0 raw2159step0Labels = mixedMoment B raw2159step1 raw2159step1Labels := by
      have ha : raw2159step1 = -raw2159step0 := by apply Matrix.ext; change ∀ i j, raw2159step1 i j = -(raw2159step0 i j); unfold raw2159step1 raw2159step0; decide +kernel
      have hl : raw2159step1Labels = raw2159step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2159step1 raw2159step1Labels = mixedMoment B raw2159step2 raw2159step2Labels := by
      have ha : raw2159step2 = raw2159step1 := by apply Matrix.ext; unfold raw2159step2 raw2159step1; decide +kernel
      have hl : raw2159step1Labels = labelEmbedding1 ∘ raw2159step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2159step1 raw2159step1Labels raw2159step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3372 node3372Labels := by rfl

def raw2160 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2]]
def raw2160Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2160step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2160step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2160step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2160step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2160 raw2160Labels = mixedMoment B node5126 node5126Labels := by
  calc
    mixedMoment B raw2160 raw2160Labels = mixedMoment B raw2160step0 raw2160step0Labels := by
      have ha : raw2160step0 = (fun i j => raw2160 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2160step0 raw2160; decide +kernel
      have hl : raw2160step0Labels = raw2160Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2160 raw2160Labels permutation152 permutation4
    mixedMoment B raw2160step0 raw2160step0Labels = mixedMoment B raw2160step1 raw2160step1Labels := by
      have ha : raw2160step1 = raw2160step0 := by apply Matrix.ext; unfold raw2160step1 raw2160step0; decide +kernel
      have hl : raw2160step0Labels = labelEmbedding7 ∘ raw2160step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2160step0 raw2160step0Labels raw2160step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5126 node5126Labels := by rfl

def raw2161 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2]]
def raw2161Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2161step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2161step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2161 raw2161Labels = mixedMoment B node2541 node2541Labels := by
  calc
    mixedMoment B raw2161 raw2161Labels = mixedMoment B raw2161step0 raw2161step0Labels := by
      have ha : raw2161step0 = (fun i j => raw2161 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2161step0 raw2161; decide +kernel
      have hl : raw2161step0Labels = raw2161Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2161 raw2161Labels permutation152 permutation4
    _ = mixedMoment B node2541 node2541Labels := by rfl

def raw2162 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2]]
def raw2162Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2162step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw2162step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2162step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2162step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2162step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2162step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2162 raw2162Labels = mixedMoment B node3487 node3487Labels := by
  calc
    mixedMoment B raw2162 raw2162Labels = mixedMoment B raw2162step0 raw2162step0Labels := by
      have ha : raw2162step0 = (fun i j => raw2162 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2162step0 raw2162; decide +kernel
      have hl : raw2162step0Labels = raw2162Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2162 raw2162Labels permutation182 permutation6
    mixedMoment B raw2162step0 raw2162step0Labels = mixedMoment B raw2162step1 raw2162step1Labels := by
      have ha : raw2162step1 = -raw2162step0 := by apply Matrix.ext; change ∀ i j, raw2162step1 i j = -(raw2162step0 i j); unfold raw2162step1 raw2162step0; decide +kernel
      have hl : raw2162step1Labels = raw2162step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2162step1 raw2162step1Labels = mixedMoment B raw2162step2 raw2162step2Labels := by
      have ha : raw2162step2 = raw2162step1 := by apply Matrix.ext; unfold raw2162step2 raw2162step1; decide +kernel
      have hl : raw2162step1Labels = labelEmbedding1 ∘ raw2162step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2162step1 raw2162step1Labels raw2162step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3487 node3487Labels := by rfl

def raw2163 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw2163Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2163step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2163step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2163step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2163step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2163 raw2163Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw2163 raw2163Labels = mixedMoment B raw2163step0 raw2163step0Labels := by
      have ha : raw2163step0 = (fun i j => raw2163 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2163step0 raw2163; decide +kernel
      have hl : raw2163step0Labels = raw2163Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2163 raw2163Labels permutation152 permutation4
    mixedMoment B raw2163step0 raw2163step0Labels = mixedMoment B raw2163step1 raw2163step1Labels := by
      have ha : raw2163step1 = raw2163step0 := by apply Matrix.ext; unfold raw2163step1 raw2163step0; decide +kernel
      have hl : raw2163step0Labels = labelEmbedding7 ∘ raw2163step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2163step0 raw2163step0Labels raw2163step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

def raw2164 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw2164Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2164step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw2164step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2164 raw2164Labels = mixedMoment B node2553 node2553Labels := by
  calc
    mixedMoment B raw2164 raw2164Labels = mixedMoment B raw2164step0 raw2164step0Labels := by
      have ha : raw2164step0 = (fun i j => raw2164 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2164step0 raw2164; decide +kernel
      have hl : raw2164step0Labels = raw2164Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2164 raw2164Labels permutation152 permutation4
    _ = mixedMoment B node2553 node2553Labels := by rfl

def raw2165 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw2165Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2165step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw2165step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2165step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2165step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2165step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw2165step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2165 raw2165Labels = mixedMoment B node3514 node3514Labels := by
  calc
    mixedMoment B raw2165 raw2165Labels = mixedMoment B raw2165step0 raw2165step0Labels := by
      have ha : raw2165step0 = (fun i j => raw2165 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2165step0 raw2165; decide +kernel
      have hl : raw2165step0Labels = raw2165Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2165 raw2165Labels permutation176 permutation6
    mixedMoment B raw2165step0 raw2165step0Labels = mixedMoment B raw2165step1 raw2165step1Labels := by
      have ha : raw2165step1 = -raw2165step0 := by apply Matrix.ext; change ∀ i j, raw2165step1 i j = -(raw2165step0 i j); unfold raw2165step1 raw2165step0; decide +kernel
      have hl : raw2165step1Labels = raw2165step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2165step1 raw2165step1Labels = mixedMoment B raw2165step2 raw2165step2Labels := by
      have ha : raw2165step2 = raw2165step1 := by apply Matrix.ext; unfold raw2165step2 raw2165step1; decide +kernel
      have hl : raw2165step1Labels = labelEmbedding1 ∘ raw2165step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2165step1 raw2165step1Labels raw2165step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3514 node3514Labels := by rfl

def raw2166 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2166Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2166step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2166step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2166step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2166 raw2166Labels = mixedMoment B node5137 node5137Labels := by
  calc
    mixedMoment B raw2166 raw2166Labels = mixedMoment B raw2166step0 raw2166step0Labels := by
      have ha : raw2166step0 = (fun i j => raw2166 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2166step0 raw2166; decide +kernel
      have hl : raw2166step0Labels = raw2166Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2166 raw2166Labels permutation152 permutation4
    mixedMoment B raw2166step0 raw2166step0Labels = mixedMoment B raw2166step1 raw2166step1Labels := by
      have ha : raw2166step1 = raw2166step0 := by apply Matrix.ext; unfold raw2166step1 raw2166step0; decide +kernel
      have hl : raw2166step0Labels = labelEmbedding7 ∘ raw2166step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2166step0 raw2166step0Labels raw2166step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5137 node5137Labels := by rfl

def raw2167 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2167Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2167step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2167step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2167 raw2167Labels = mixedMoment B node2556 node2556Labels := by
  calc
    mixedMoment B raw2167 raw2167Labels = mixedMoment B raw2167step0 raw2167step0Labels := by
      have ha : raw2167step0 = (fun i j => raw2167 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2167step0 raw2167; decide +kernel
      have hl : raw2167step0Labels = raw2167Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2167 raw2167Labels permutation152 permutation4
    _ = mixedMoment B node2556 node2556Labels := by rfl

def raw2168 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2168Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2168step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw2168step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2168step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2168step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2168step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2168step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2168 raw2168Labels = mixedMoment B node3521 node3521Labels := by
  calc
    mixedMoment B raw2168 raw2168Labels = mixedMoment B raw2168step0 raw2168step0Labels := by
      have ha : raw2168step0 = (fun i j => raw2168 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2168step0 raw2168; decide +kernel
      have hl : raw2168step0Labels = raw2168Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2168 raw2168Labels permutation176 permutation6
    mixedMoment B raw2168step0 raw2168step0Labels = mixedMoment B raw2168step1 raw2168step1Labels := by
      have ha : raw2168step1 = -raw2168step0 := by apply Matrix.ext; change ∀ i j, raw2168step1 i j = -(raw2168step0 i j); unfold raw2168step1 raw2168step0; decide +kernel
      have hl : raw2168step1Labels = raw2168step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2168step1 raw2168step1Labels = mixedMoment B raw2168step2 raw2168step2Labels := by
      have ha : raw2168step2 = raw2168step1 := by apply Matrix.ext; unfold raw2168step2 raw2168step1; decide +kernel
      have hl : raw2168step1Labels = labelEmbedding1 ∘ raw2168step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2168step1 raw2168step1Labels raw2168step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3521 node3521Labels := by rfl

def raw2169 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![-1, 2, -1], ![0, 2, -2]]
def raw2169Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw2169step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw2169step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2169 raw2169Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw2169 raw2169Labels = mixedMoment B raw2169step0 raw2169step0Labels := by
      have ha : raw2169step0 = (fun i j => raw2169 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2169step0 raw2169; decide +kernel
      have hl : raw2169step0Labels = raw2169Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2169 raw2169Labels permutation32 permutation4
    mixedMoment B raw2169step0 raw2169step0Labels = mixedMoment B raw2169step1 raw2169step1Labels := by
      have ha : raw2169step1 = raw2169step0 := by apply Matrix.ext; unfold raw2169step1 raw2169step0; decide +kernel
      have hl : raw2169step0Labels = labelEmbedding7 ∘ raw2169step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2169step0 raw2169step0Labels raw2169step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

def raw2170 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![-1, 2, -1], ![0, 2, -2]]
def raw2170Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw2170step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2170 raw2170Labels = mixedMoment B node2561 node2561Labels := by
  calc
    mixedMoment B raw2170 raw2170Labels = mixedMoment B raw2170step0 raw2170step0Labels := by
      have ha : raw2170step0 = (fun i j => raw2170 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2170step0 raw2170; decide +kernel
      have hl : raw2170step0Labels = raw2170Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2170 raw2170Labels permutation32 permutation4
    _ = mixedMoment B node2561 node2561Labels := by rfl

def raw2171 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -3, 2], ![1, -1, 0], ![-1, 0, 1], ![-1, 2, -1], ![0, 2, -2]]
def raw2171Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw2171step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw2171step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2171step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw2171step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2171 raw2171Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw2171 raw2171Labels = mixedMoment B raw2171step0 raw2171step0Labels := by
      have ha : raw2171step0 = (fun i j => raw2171 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2171step0 raw2171; decide +kernel
      have hl : raw2171step0Labels = raw2171Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2171 raw2171Labels permutation38 permutation6
    mixedMoment B raw2171step0 raw2171step0Labels = mixedMoment B raw2171step1 raw2171step1Labels := by
      have ha : raw2171step1 = -raw2171step0 := by apply Matrix.ext; change ∀ i j, raw2171step1 i j = -(raw2171step0 i j); unfold raw2171step1 raw2171step0; decide +kernel
      have hl : raw2171step1Labels = raw2171step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2171step1 raw2171step1Labels = mixedMoment B raw2171step2 raw2171step2Labels := by
      have ha : raw2171step2 = raw2171step1 := by apply Matrix.ext; unfold raw2171step2 raw2171step1; decide +kernel
      have hl : raw2171step1Labels = labelEmbedding1 ∘ raw2171step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2171step1 raw2171step1Labels raw2171step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3522 node3522Labels := by rfl

def raw2172 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2]]
def raw2172Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2172step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw2172step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2172step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw2172step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2172 raw2172Labels = mixedMoment B node5142 node5142Labels := by
  calc
    mixedMoment B raw2172 raw2172Labels = mixedMoment B raw2172step0 raw2172step0Labels := by
      have ha : raw2172step0 = (fun i j => raw2172 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2172step0 raw2172; decide +kernel
      have hl : raw2172step0Labels = raw2172Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2172 raw2172Labels permutation152 permutation5
    mixedMoment B raw2172step0 raw2172step0Labels = mixedMoment B raw2172step1 raw2172step1Labels := by
      have ha : raw2172step1 = raw2172step0 := by apply Matrix.ext; unfold raw2172step1 raw2172step0; decide +kernel
      have hl : raw2172step0Labels = labelEmbedding8 ∘ raw2172step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2172step0 raw2172step0Labels raw2172step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5142 node5142Labels := by rfl

def raw2173 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2]]
def raw2173Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw2173step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2173 raw2173Labels = mixedMoment B node2913 node2913Labels := by
  calc
    mixedMoment B raw2173 raw2173Labels = mixedMoment B raw2173step0 raw2173step0Labels := by
      have ha : raw2173step0 = (fun i j => raw2173 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2173step0 raw2173; decide +kernel
      have hl : raw2173step0Labels = raw2173Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2173 raw2173Labels permutation152 permutation4
    _ = mixedMoment B node2913 node2913Labels := by rfl

def raw2174 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2]]
def raw2174Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2174step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw2174step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2174step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw2174step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2174step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw2174step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2174 raw2174Labels = mixedMoment B node3610 node3610Labels := by
  calc
    mixedMoment B raw2174 raw2174Labels = mixedMoment B raw2174step0 raw2174step0Labels := by
      have ha : raw2174step0 = (fun i j => raw2174 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2174step0 raw2174; decide +kernel
      have hl : raw2174step0Labels = raw2174Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2174 raw2174Labels permutation168 permutation3
    mixedMoment B raw2174step0 raw2174step0Labels = mixedMoment B raw2174step1 raw2174step1Labels := by
      have ha : raw2174step1 = -raw2174step0 := by apply Matrix.ext; change ∀ i j, raw2174step1 i j = -(raw2174step0 i j); unfold raw2174step1 raw2174step0; decide +kernel
      have hl : raw2174step1Labels = raw2174step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2174step1 raw2174step1Labels = mixedMoment B raw2174step2 raw2174step2Labels := by
      have ha : raw2174step2 = raw2174step1 := by apply Matrix.ext; unfold raw2174step2 raw2174step1; decide +kernel
      have hl : raw2174step1Labels = labelEmbedding1 ∘ raw2174step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2174step1 raw2174step1Labels raw2174step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3610 node3610Labels := by rfl

def raw2175 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -3, 1], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw2175Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2175step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw2175step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2175step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw2175step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2175 raw2175Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw2175 raw2175Labels = mixedMoment B raw2175step0 raw2175step0Labels := by
      have ha : raw2175step0 = (fun i j => raw2175 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2175step0 raw2175; decide +kernel
      have hl : raw2175step0Labels = raw2175Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2175 raw2175Labels permutation152 permutation5
    mixedMoment B raw2175step0 raw2175step0Labels = mixedMoment B raw2175step1 raw2175step1Labels := by
      have ha : raw2175step1 = raw2175step0 := by apply Matrix.ext; unfold raw2175step1 raw2175step0; decide +kernel
      have hl : raw2175step0Labels = labelEmbedding8 ∘ raw2175step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2175step0 raw2175step0Labels raw2175step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
